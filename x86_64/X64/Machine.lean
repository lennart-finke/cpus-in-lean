import X64.State
import X64.Dev

namespace X64

/-- Architectural machine state. The application proof layer can ignore devices under
an explicit invariant; it uses the same instruction semantics as the system runner. -/
structure Machine where
  cpu : Cpu := {}
  mem : ByteArray
  pic0 : Pic := { vecBase := 8 }
  pic1 : Pic := { vecBase := 0x70 }
  pit : Pit := {}
  uart : Uart := {}
  cmosIdx : UInt8 := 0
  cmos : ByteArray := cmosInit
  icount : UInt64 := 0
  timerAt : UInt64 := 0xFFFFFFFFFFFFFFFF
  intr : Bool := false
  fatal : Option Fault := none
  deriving Inhabited

abbrev M := EStateM Fault Machine
@[inline] def cpu : M Cpu := fun m => .ok m.cpu m
@[inline] def modCpu (f : Cpu → Cpu) : M Unit := fun m => .ok () { m with cpu := f m.cpu }
@[inline] def getM : M Machine := get
@[inline] def modM (f : Machine → Machine) : M Unit := fun m => .ok () (f m)
@[inline] def exc (v : UInt8) (err : Option UInt64 := none) : M α := throw (.exc v err 0)
@[inline] def gp (e : UInt64 := 0) : M α := exc Vec.GP (some e)
@[inline] def ud : M α := exc Vec.UD
@[inline] def unsupported (s : String) : M α := throw (.unsupported s)
@[inline] def getReg (r : UInt8) : M UInt64 := fun m => .ok (m.cpu.getReg r) m
@[noinline] def setReg (r : UInt8) (v : UInt64) : M Unit := modCpu (·.setReg r v)
@[inline] def rdReg (sz : Sz) (r : UInt8) (rex : Bool := false) : M UInt64 :=
  fun m => .ok (m.cpu.rdReg sz r rex) m
@[noinline] def wrReg (sz : Sz) (r : UInt8) (v : UInt64) (rex : Bool := false) : M Unit :=
  modCpu (·.wrReg sz r v rex)
@[inline] def getFlags : M UInt64 := fun m => .ok m.cpu.rflags m
@[inline] def setFlags (mask v : UInt64) : M Unit := modCpu (·.setFlags mask v)
@[inline] def getCpl : M UInt64 := fun m => .ok m.cpu.cpl m
@[inline] def flag (f : UInt64) : M Bool := fun m => .ok (m.cpu.flag f) m
@[inline] def physRd (p n : UInt64) : M UInt64 := fun m => .ok (rdBytes m.mem p n) m
@[inline] def physWr (p n v : UInt64) : M Unit :=
  fun m => .ok () { m with mem := wrBytes m.mem p n v }

inductive Access where
  | read | write | fetch
  deriving BEq, Repr

@[inline] def pfErr (a : Access) (user present reserved : Bool) : UInt64 :=
  (if present then 1 else 0) ||| (if a == .write then 2 else 0) |||
  (if user then 4 else 0) ||| (if reserved then 8 else 0) ||| (if a == .fetch then 16 else 0)

/-- Permissions accumulated from all traversed page-table entries. -/
@[inline] def pageAllowed (writable users nx : Bool) (a : Access) (user wp : Bool) : Bool :=
  !((user && !users) || (a == .write && !writable && (user || wp)) || (a == .fetch && nx))

/-- Four-level paging, 4 KiB / 2 MiB / 1 GiB pages, 40 physical address bits.
NX, CR0.WP and permissions from every level are checked. No cached translations:
this is the architectural choice of immediately evicting all TLB entries. -/
def translate (lin : UInt64) (a : Access) (user : Bool) : M UInt64 := do
  if !canonical lin then gp 0
  let c ← cpu
  if c.cr0 &&& CR0.PG == 0 then return lin
  if c.efer &&& 0x400 == 0 || c.cr4 &&& 0x20 == 0 then
    unsupported "paging outside four-level IA-32e mode"
  if c.cr4 &&& 0x1000 != 0 then unsupported "five-level paging"
  let fail (present reserved : Bool) : M UInt64 :=
    throw (.exc Vec.PF (some (pfErr a user present reserved)) lin)
  let mut table := c.cr3 &&& 0xFFFFFFF000
  let mut writable := true
  let mut users := true
  let mut nx := false
  for shift in [39, 30, 21, 12] do
    let addr := table + (((lin >>> shift) &&& 0x1FF) * 8)
    let entry ← physRd addr 8
    if entry &&& 1 == 0 then return ← fail false false
    let large := shift != 12 && entry &&& 0x80 != 0
    if entry &&& 0x000FFF0000000000 != 0 ||
       (entry >>> 63 != 0 && c.efer &&& 0x800 == 0) ||
       (shift == 39 && large) then return ← fail true true
    writable := writable && entry &&& 2 != 0
    users := users && entry &&& 4 != 0
    nx := nx || entry >>> 63 != 0
    if large || shift == 12 then
      let mask := ((1 : UInt64) <<< shift) - 1
      -- Bit 12 is PAT for large leaves, not an address bit.
      if large && entry &&& (mask &&& ~~~(0x1FFF : UInt64)) != 0 then return ← fail true true
      if !pageAllowed writable users nx a user (c.cr0 &&& CR0.WP != 0) then return ← fail true false
      let updated := entry ||| 0x20 ||| (if a == .write then 0x40 else 0)
      if updated != entry then physWr addr 8 updated
      return (entry &&& 0xFFFFFFF000 &&& ~~~mask) ||| (lin &&& mask)
    else
      if entry &&& 0x20 == 0 then physWr addr 8 (entry ||| 0x20)
      table := entry &&& 0xFFFFFFF000
  unsupported "page walk did not reach a leaf"

/-- Read after translating both ends; RMW reads request write access. -/
def linRd (lin n : UInt64) (user : Bool) (access : Access := .read) : M UInt64 := do
  let p ← translate lin access user
  if (lin &&& 0xFFF) + n ≤ 4096 then physRd p n
  else
    let last ← translate ((lin + n - 1) &&& ~~~(0xFFF : UInt64)) access user
    let mut v := 0
    for k in [0:n.toNat] do
      let a := lin + k.toUInt64
      let q := if a &&& ~~~(0xFFF : UInt64) == lin &&& ~~~(0xFFF : UInt64) then p + k.toUInt64
               else (last &&& ~~~(0xFFF : UInt64)) ||| (a &&& 0xFFF)
      v := v ||| ((← physRd q 1) <<< (k.toUInt64 * 8))
    return v

def linWr (lin n v : UInt64) (user : Bool) : M Unit := do
  let p ← translate lin .write user
  if (lin &&& 0xFFF) + n ≤ 4096 then physWr p n v
  else
    let last ← translate ((lin + n - 1) &&& ~~~(0xFFF : UInt64)) .write user
    for k in [0:n.toNat] do
      let a := lin + k.toUInt64
      let q := if a &&& ~~~(0xFFF : UInt64) == lin &&& ~~~(0xFFF : UInt64) then p + k.toUInt64
               else (last &&& ~~~(0xFFF : UInt64)) ||| (a &&& 0xFFF)
      physWr q 1 (v >>> (k.toUInt64 * 8))

def segAddr (s : UInt8) (off n : UInt64) : M UInt64 := do
  let c ← cpu
  let base := if s == SegN.FS then c.fsBase else if s == SegN.GS then c.gsBase else 0
  let addr := base + off
  if !canonical addr || !canonical (addr + n - 1) then
    exc (if s == SegN.SS then Vec.SS else Vec.GP) (some 0)
  return addr

/-- RMW operands use write permission from the first access. -/
def rdMem (s : UInt8) (off n : UInt64) (write : Bool := false) : M UInt64 := do
  linRd (← segAddr s off n) n ((← getCpl) == 3) (if write then .write else .read)
def wrMem (s : UInt8) (off n v : UInt64) : M Unit := do
  linWr (← segAddr s off n) n v ((← getCpl) == 3)
def sysRd (lin n : UInt64) : M UInt64 := linRd lin n false
def sysWr (lin n v : UInt64) : M Unit := linWr lin n v false
@[inline] def fetch8 (rip : UInt64) : M UInt64 := do linRd rip 1 ((← getCpl) == 3) .fetch

end X64
