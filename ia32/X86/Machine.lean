import X86.State
import X86.Dev
/-!
# The machine and the semantic monad

`M` is a state/exception monad over the whole machine. An instruction either completes
(`.ok`) or raises a `Fault`. On a fault `execInstr` restores the CPU snapshot,
except for completed POPA register loads. Completed writes from multi-store
instructions can remain visible; each individual write checks its whole range
before committing (see `Exec`).

## Paging

Two-level 32-bit paging with optional 4 MiB pages (CR4.PSE). Accessed/dirty bits are
set during the walk. Translations are cached in a direct-mapped TLB, like hardware
does. The TLB is architecturally visible exactly as on real hardware: software must
use INVLPG / MOV CR3 after changing a present PTE.
-/
namespace X86

def tlbSize : Nat := 1024

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
  /-- Instruction count at which the PIT channel 0 output next rises (cached from `pit`). -/
  timerAt : UInt64 := 0xFFFFFFFFFFFFFFFF
  /-- The PIC pair asserts INTR (cached from `pic0`/`pic1`). -/
  intr : Bool := false
  /-- Set when the simulation cannot continue (shutdown or unsupported behaviour). -/
  fatal : Option Fault := none
  /-- TLB tags: linear page address ||| 1 when valid. -/
  tlbTag : Array UInt32 := Array.replicate tlbSize 0
  /-- TLB data: physical page ||| permission bits (see `Tlb`). -/
  tlbVal : Array UInt32 := Array.replicate tlbSize 0
  deriving Inhabited

namespace Tlb
/-- user access allowed -/
def U  : UInt32 := 1
/-- user write allowed -/
def UW : UInt32 := 2
/-- supervisor write allowed -/
def SW : UInt32 := 4
/-- dirty bit already set in the PTE -/
def D  : UInt32 := 8
end Tlb

abbrev M := EStateM Fault Machine

@[inline] def cpu : M Cpu := fun m => .ok m.cpu m
@[inline] def modCpu (f : Cpu → Cpu) : M Unit := fun m => .ok () { m with cpu := f m.cpu }
@[inline] def getM : M Machine := get
@[inline] def modM (f : Machine → Machine) : M Unit := fun m => .ok () (f m)

@[inline] def exc (v : UInt8) (err : Option UInt32 := none) : M α := throw (.exc v err 0)
@[inline] def gp (e : UInt32 := 0) : M α := throw (.exc Vec.GP (some e) 0)
@[inline] def ud : M α := throw (.exc Vec.UD none 0)
@[inline] def unsupported (s : String) : M α := throw (.unsupported s)

@[inline] def getReg (r : UInt8) : M UInt32 := fun m => .ok (m.cpu.getReg r) m
@[inline] def setReg (r : UInt8) (v : UInt32) : M Unit := modCpu (·.setReg r v)
@[inline] def rdReg (sz : Sz) (r : UInt8) : M UInt32 := fun m => .ok (m.cpu.rdReg sz r) m
@[inline] def wrReg (sz : Sz) (r : UInt8) (v : UInt32) : M Unit := modCpu (·.wrReg sz r v)
@[inline] def getFlags : M UInt32 := fun m => .ok m.cpu.eflags m
@[inline] def setFlags (mask v : UInt32) : M Unit := modCpu (·.setFlags mask v)
@[inline] def flag (f : UInt32) : M Bool := fun m => .ok (m.cpu.eflags &&& f != 0) m
@[inline] def getCpl : M UInt32 := fun m => .ok m.cpu.cpl m
@[inline] def getEip : M UInt32 := fun m => .ok m.cpu.eip m
@[inline] def setEip (v : UInt32) : M Unit := modCpu fun c => { c with eip := v }

/-! ## Physical memory -/

@[inline] def physRd (p n : UInt32) : M UInt32 := fun m => .ok (rdBytes m.mem p n) m
@[inline] def physWr (p n v : UInt32) : M Unit :=
  fun m => .ok () { m with mem := wrBytes m.mem p n v }

/-! ## Paging -/

def flushTlb : M Unit := modM fun m =>
  { m with tlbTag := Array.replicate tlbSize 0 }

def flushTlbPage (lin : UInt32) : M Unit := modM fun m =>
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  { m with tlbTag := m.tlbTag.set! idx 0 }

@[inline] def pfErr (write user : Bool) (prot : Bool) : UInt32 :=
  (if prot then 1 else 0) ||| (if write then 2 else 0) ||| (if user then 4 else 0)

/-- Physical address of the page-directory entry for `lin`. -/
@[inline] def pdeAddr (c : Cpu) (lin : UInt32) : UInt32 := (c.cr3 &&& 0xFFFFF000) + ((lin >>> 22) <<< 2)
/-- Physical address of the page-table entry for `lin` given its PDE. -/
@[inline] def pteAddr (pde lin : UInt32) : UInt32 := (pde &&& 0xFFFFF000) + (((lin >>> 12) &&& 0x3FF) <<< 2)

/-- Paging permission check for an access through a PDE (and PTE unless `large`):
`true` if the access is allowed. User accesses need U/S set at every level; writes need
R/W set at every level, unless it is a supervisor write with CR0.WP clear. -/
@[inline] def pageAllowed (pde pte : UInt32) (large write user wp : Bool) : Bool :=
  let perm := if large then pde else pde &&& pte
  !((user && perm &&& 4 == 0) || (write && perm &&& 2 == 0 && (user || wp)))

/-- Page-table walk; sets A/D bits and fills the TLB. -/
def walk (lin : UInt32) (write user : Bool) : M UInt32 := fun m =>
  let c := m.cpu
  let wp := c.cr0 &&& CR0.WP != 0
  let pdeA : UInt32 := pdeAddr c lin
  let pde := rdBytes m.mem pdeA 4
  if pde &&& 1 == 0 then .error (.exc Vec.PF (some (pfErr write user false)) lin) m else
  let large := pde &&& 0x80 != 0 && c.cr4 &&& CR4.PSE != 0
  let pteA : UInt32 := pteAddr pde lin
  let pte := if large then pde else rdBytes m.mem pteA 4
  if pte &&& 1 == 0 then .error (.exc Vec.PF (some (pfErr write user false)) lin) m else
  if !pageAllowed pde pte large write user wp then
    .error (.exc Vec.PF (some (pfErr write user true)) lin) m
  else
    let perm := if large then pde else pde &&& pte
    let mem := m.mem
    let npde := pde ||| 0x20 ||| (if large && write then 0x40 else 0)
    let mem := if npde != pde then wrBytes mem pdeA 4 npde else mem
    let (mem, pte) :=
      if large then (mem, npde) else
        let npte := pte ||| 0x20 ||| (if write then 0x40 else 0)
        (if npte != pte then wrBytes mem pteA 4 npte else mem, npte)
    let phys := if large then (pde &&& 0xFFC00000) ||| (lin &&& 0x3FF000)
                else pte &&& 0xFFFFF000
    let bits :=
      (if perm &&& 4 != 0 then Tlb.U else 0) |||
      (if perm &&& 6 == 6 then Tlb.UW else 0) |||
      (if perm &&& 2 != 0 || !wp then Tlb.SW else 0) |||
      (if pte &&& 0x40 != 0 then Tlb.D else 0)
    let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
    .ok (phys ||| (lin &&& 0xFFF))
      { m with mem := mem,
               tlbTag := m.tlbTag.set! idx ((lin &&& 0xFFFFF000) ||| 1),
               tlbVal := m.tlbVal.set! idx (phys ||| bits) }

/-- Translate a linear address. `user` selects user-mode permission checking. -/
@[inline] def translate (lin : UInt32) (write user : Bool) : M UInt32 := fun m =>
  if m.cpu.cr0 &&& CR0.PG == 0 then .ok lin m else
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let tag := m.tlbTag[idx]!
  if tag == ((lin &&& 0xFFFFF000) ||| 1) then
    let v := m.tlbVal[idx]!
    let ok :=
      (!user || v &&& Tlb.U != 0) &&
      (!write || (v &&& Tlb.D != 0 && (if user then v &&& Tlb.UW != 0 else v &&& Tlb.SW != 0)))
    if ok then .ok ((v &&& 0xFFFFF000) ||| (lin &&& 0xFFF)) m else walk lin write user m
  else walk lin write user m

/-- Read `n` (1, 2 or 4) bytes at a linear address. -/
def linRd (lin n : UInt32) (user : Bool) (write : Bool := false) : M UInt32 := do
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physRd (← translate lin write user) n
  else
    let p0 ← translate lin write user
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 write user
    let mut v : UInt32 := 0
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF) else p0 + (a - lin)
      v := v ||| ((← physRd p 1) <<< (k.toUInt32 * 8))
    return v

/-- Write `n` (1, 2 or 4) bytes at a linear address. Both pages are checked before any byte is written. -/
def linWr (lin n v : UInt32) (user : Bool) : M Unit := do
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physWr (← translate lin true user) n v
  else
    let p0 ← translate lin true user
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 true user
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF) else p0 + (a - lin)
      physWr p 1 (v >>> (k.toUInt32 * 8))

/-- Check that a linear range is writable (used by instructions with several writes). -/
def linProbeWr (lin n : UInt32) (user : Bool) : M Unit := do
  let _ ← translate lin true user
  let _ ← translate (lin + n - 1) true user

/-! ## Segmentation -/

/-- Segment type and limit check for an `n`-byte access at offset `off`: the segment
must be usable, writes need a writable data segment, reads of code need a readable code
segment, and the access must lie within the limit (expand-down segments: above the limit). -/
@[inline] def segAllowed (sr : SegReg) (off n : UInt32) (write : Bool) : Bool :=
  let t := sr.attr
  let code := t &&& 0x8 != 0
  let last := off.toUInt64 + n.toUInt64 - 1
  t &&& 0x80 != 0 &&
  !(write && (code || t &&& 2 == 0)) &&
  !(!write && code && t &&& 2 == 0) &&
  (if !code && t &&& 4 != 0 then
     off > sr.limit && last ≤ (if sr.big then 0xFFFFFFFF else 0xFFFF)
   else last ≤ sr.limit.toUInt64)

/-- Linear address of an `n`-byte access at offset `off` of segment register `s`,
with protected-mode type and limit checks. -/
@[inline] def segAddr (s : UInt8) (off n : UInt32) (write : Bool) : M UInt32 := fun m =>
  let sr := m.cpu.getSeg s
  if segAllowed sr off n write then .ok (sr.base + off) m
  else .error (.exc (if s == SegN.SS then Vec.SS else Vec.GP) (some 0) 0) m

@[inline] def isUser : M Bool := fun m => .ok (m.cpu.cpl == 3) m

/-- Read `n` bytes at `seg:off`; RMW operands use write permission from the first access. -/
@[inline] def rdMem (s : UInt8) (off n : UInt32) (write : Bool := false) : M UInt32 := do
  let lin ← segAddr s off n write
  linRd lin n (← isUser) write

/-- Write `n` bytes at `seg:off`. -/
@[inline] def wrMem (s : UInt8) (off n v : UInt32) : M Unit := do
  let lin ← segAddr s off n true
  linWr lin n v (← isUser)

/-- Supervisor-mode (implicit) linear accesses, used for descriptor tables and the TSS. -/
@[inline] def sysRd (lin n : UInt32) : M UInt32 := linRd lin n false
@[inline] def sysWr (lin n v : UInt32) : M Unit := linWr lin n v false

/-- Fetch one code byte at `CS:eip`. -/
@[inline] def fetch8 (eip : UInt32) : M UInt32 := fun m =>
  let cs := m.cpu.cs
  if eip > cs.limit then .error (.exc Vec.GP (some 0) 0) m else
  (do linRd (cs.base + eip) 1 (← isUser)) m

end X86
