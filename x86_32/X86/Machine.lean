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

Two-level 32-bit paging with optional 4 MiB pages (CR4.PSE), and PAE paging (CR4.PAE) with
2 MiB pages and execute-disable (EFER.NXE). Accessed/dirty bits are set during the walk. Translations are cached in a direct-mapped TLB, like hardware
does. The TLB is architecturally visible exactly as on real hardware: software must
use INVLPG / MOV CR3 after changing a present PTE.
-/
namespace X86

def tlbSize : Nat := 1024

/-- One store to physical memory: `n` (1, 2 or 4) bytes of `val` at `addr`. -/
structure Store where
  addr : UInt32
  n : UInt32
  val : UInt32
  deriving Repr, Inhabited, BEq

/-- The physical accesses of one step, recorded while `Machine.tso` is `some` (see `X86.Tso`):
reads as (address, size), stores in program order. -/
structure TsoLog where
  reads : Array (UInt32 × UInt32) := #[]
  writes : Array Store := #[]
  deriving Repr, Inhabited

/-- Machine state beyond the integer core: local APIC, debug-event bookkeeping, SMI and APM latches.
A parent of `Machine` for the same reason as `CpuExt`. -/
structure MachineExt where
  apic : Apic := {}
  /-- Some TLB entry may come from a large page (INVLPG then scans for its other slices). -/
  tlbLarge : Bool := false
  /-- DR6.B0..B3 bits of data and I/O breakpoints matched by the current instruction (or event delivery). -/
  dbHit : UInt32 := 0
  /-- Debug-trap DR6 bits held over an instruction boundary: after MOV SS / POP SS (which delay
  debug traps past the next instruction), or raised while delivering an event. Delivered as #DB at
  the next instruction boundary that is not in an interrupt shadow. -/
  dbPend : UInt32 := 0
  /-- Set by a task switch once it has committed: a later fault of the same instruction or event
  is delivered in the new task, so the CPU state is not rolled back. -/
  keepCpu : Bool := false
  /-- A system-management interrupt is latched (taken at the next instruction boundary outside SMM). -/
  smiPending : Bool := false
  /-- APM control (port 0xB2: writing it raises an SMI) and status (0xB3) registers. -/
  apmCnt : UInt8 := 0
  apmSts : UInt8 := 0
  deriving Inhabited

structure Machine extends MachineExt where
  cpu : Cpu := {}
  mem : ByteArray
  pic0 : Pic := { vecBase := 8 }
  pic1 : Pic := { vecBase := 0x70 }
  pit : Pit := {}
  uart : Uart := {}
  cmosIdx : UInt8 := 0
  cmos : ByteArray := cmosInit
  icount : UInt64 := 0
  /-- Instruction count of the next timer event: PIT channel 0 output edge or APIC timer expiry
  (cached from `pit` and `apic`). -/
  timerAt : UInt64 := 0xFFFFFFFFFFFFFFFF
  /-- A maskable interrupt is pending: the PIC pair through LINT0, or the local APIC (cached). -/
  intr : Bool := false
  /-- Set when the simulation cannot continue (shutdown or unsupported behaviour). -/
  fatal : Option Fault := none
  /-- TLB tags: linear page address ||| 1 when valid. -/
  tlbTag : Array UInt32 := Array.replicate tlbSize 0
  /-- TLB data: physical page ||| permission bits (see `Tlb`). -/
  tlbVal : Array UInt64 := Array.replicate tlbSize 0
  /-- Physical RAM accesses recorded for the multiprocessor TSO semantics. -/
  tso : Option TsoLog := none
  deriving Inhabited

namespace Tlb
/-- user access allowed -/
def U  : UInt64 := 1
/-- user write allowed -/
def UW : UInt64 := 2
/-- supervisor write allowed -/
def SW : UInt64 := 4
/-- dirty bit already set in the PTE -/
def D  : UInt64 := 8
/-- execute disabled (XD with EFER.NXE) -/
def NX : UInt64 := 16
/-- part of a 4 MiB or 2 MiB page -/
def L  : UInt64 := 32
end Tlb

namespace Machine

/-- Highest-priority request of the master PIC, including the cascade input. -/
def masterHighest (m : Machine) : Option UInt8 :=
  m.pic0.highest (if (m.pic1.highest).isSome then 4 else 0)

/-- Recompute the cached INTR line: the PIC's output (the slave's INT drives master input 2) if it
passes the local APIC's LINT0, or a fixed interrupt the APIC presents. -/
def syncIntr (m : Machine) : Machine :=
  { m with intr := (m.apic.picPasses && m.masterHighest.isSome) || m.apic.pending.isSome }

/-- Recompute the next timer event. -/
def syncTimer (m : Machine) : Machine :=
  let pit := match m.pit.ch0.nextFire with
    | some t => tickToIcount t
    | none => 0xFFFFFFFFFFFFFFFF
  { m with timerAt := min pit m.apic.timerNext }

/-- Write to the local APIC's register page. -/
def apicWrite (m : Machine) (off v : UInt32) : Machine :=
  { m with apic := m.apic.write off v m.icount }.syncTimer.syncIntr

end Machine

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

/-! ## Debug breakpoints

DR7 enables breakpoint k with L_k/G_k; R/W_k selects instruction execution (0), data writes (1),
I/O accesses (2, with CR4.DE) or data reads and writes (3); LEN_k selects 1, 2, 8 or 4 bytes
(encodings 0, 1, 2, 3), and the address in DRk is aligned down to that length. -/

/-- DR6.B0..B3 bits of the enabled breakpoints whose R/W type satisfies `ty` and whose range
overlaps the `n` bytes at `addr`. -/
def bpHits (c : Cpu) (addr n : UInt32) (ty : UInt32 → Bool) : UInt32 := Id.run do
  let dr7 := c.dr7
  let mut hits : UInt32 := 0
  for k in [0:4] do
    let k32 := k.toUInt32
    if (dr7 >>> (2 * k32)) &&& 3 != 0 && ty ((dr7 >>> (16 + 4 * k32)) &&& 3) then
      let len := (dr7 >>> (18 + 4 * k32)) &&& 3
      let size : UInt64 := if len == 0 then 1 else if len == 1 then 2 else if len == 3 then 4 else 8
      let dr := match k with | 0 => c.dr0 | 1 => c.dr1 | 2 => c.dr2 | _ => c.dr3
      let a := dr.toUInt64 &&& ~~~(size - 1)
      let lo := addr.toUInt64
      if a < lo + n.toUInt64 && lo < a + size then hits := hits ||| ((1 : UInt32) <<< k32)
  return hits

/-- Record data breakpoints matched by an `n`-byte access at linear address `lin`. -/
@[inline] def dbData (lin n : UInt32) (write : Bool) : M Unit := fun m =>
  if !m.cpu.bpOn then .ok () m
  else .ok () { m with dbHit := m.dbHit ||| bpHits m.cpu lin n (fun t => t == 3 || (write && t == 1)) }

/-- Record I/O breakpoints (CR4.DE) matched by an access to `n` ports at `port`. -/
@[inline] def dbIo (port n : UInt32) : M Unit := fun m =>
  if !m.cpu.bpOn || m.cpu.cr4 &&& CR4.DE == 0 then .ok () m
  else .ok () { m with dbHit := m.dbHit ||| bpHits m.cpu port n (· == 2) }

/-! ## Physical memory

Physical addresses are 64-bit: PAE paging reaches a 36-bit physical address space. RAM is the
`mem` array; addresses beyond it read as open bus (all ones) and ignore writes. -/

@[inline] def openBus (n : UInt32) : UInt32 :=
  if n == 1 then 0xFF else if n == 2 then 0xFFFF else 0xFFFFFFFF

/-- The local APIC claims the 4 KiB page at its base while globally enabled. -/
@[inline] def isApic (m : Machine) (a : UInt32) : Bool := a &&& 0xFFFFF000 == m.apic.base && m.apic.enabled

@[inline] def physRd (p : UInt64) (n : UInt32) : M UInt32 := fun m =>
  if p >>> 32 != 0 then .ok (openBus n) m else
  let a := p.toUInt32
  if isApic m a then
    if m.tso.isSome then .error (.unsupported "TSO: APIC MMIO") m else
    let v := m.apic.read (a &&& 0xFF0) m.icount >>> ((a &&& 3) * 8)
    .ok (if n == 4 then v else v &&& ((1 <<< (n * 8)) - 1)) m
  else match m.tso with
    | none => .ok (rdBytes m.mem a n) m
    | some l => .ok (rdBytes m.mem a n) { m with tso := some { l with reads := l.reads.push (a, n) } }
/-- Physical write; APIC registers take aligned 32-bit writes only (others are ignored). -/
@[inline] def physWr (p : UInt64) (n v : UInt32) : M Unit := fun m =>
  if p >>> 32 != 0 then .ok () m else
  let a := p.toUInt32
  if isApic m a then
    if m.tso.isSome then .error (.unsupported "TSO: APIC MMIO") m
    else .ok () (if n == 4 && a &&& 3 == 0 then m.apicWrite (a &&& 0xFF0) v else m)
  else match m.tso with
    | none => .ok () { m with mem := wrBytes m.mem a n v }
    | some l => .ok () { m with mem := wrBytes m.mem a n v,
                                tso := some { l with writes := l.writes.push ⟨a, n, v⟩ } }

/-- A 64-bit paging-structure entry at physical address `p` (open bus above 4 GiB). -/
@[inline] def rd64 (mem : ByteArray) (p : UInt64) : UInt64 :=
  if p >>> 32 != 0 then 0xFFFFFFFFFFFFFFFF
  else (rdBytes mem p.toUInt32 4).toUInt64 ||| ((rdBytes mem (p.toUInt32 + 4) 4).toUInt64 <<< 32)

/-! ## Paging

Two paging modes: 32-bit paging (CR4.PAE = 0; 4 KiB pages and, with CR4.PSE, 4 MiB pages) and
PAE paging (CR4.PAE = 1; four PDPTE registers, 64-bit entries, 4 KiB and 2 MiB pages, and the
execute-disable bit when EFER.NXE = 1). MAXPHYADDR is 36. -/

def flushTlb : M Unit := modM fun m =>
  { m with tlbTag := Array.replicate tlbSize 0, tlbLarge := false }

/-- INVLPG: drop the translation of the page containing `lin`, including every cached 4 KiB slice
of a large page that contains it. -/
def flushTlbPage (lin : UInt32) : M Unit := modM fun m =>
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let m := { m with tlbTag := m.tlbTag.set! idx 0 }
  if !m.tlbLarge then m else
  let mask : UInt32 := if m.cpu.cr4 &&& CR4.PAE != 0 then 0xFFE00000 else 0xFFC00000
  let region := lin &&& mask
  { m with tlbTag := Id.run do
      let mut t := m.tlbTag
      for k in [0:tlbSize] do
        if m.tlbVal[k]! &&& Tlb.L != 0 && t[k]! &&& 1 != 0 && t[k]! &&& mask == region then
          t := t.set! k 0
      return t }

/-- Page-fault error code: P (protection violation), W/R, U/S, RSVD (reserved bit set in a
paging-structure entry) and I/D (instruction fetch with PAE paging and EFER.NXE). -/
@[inline] def pfErr (write user : Bool) (prot : Bool) (rsvd idf : Bool := false) : UInt32 :=
  (if prot then 1 else 0) ||| (if write then 2 else 0) ||| (if user then 4 else 0) |||
  (if rsvd then 8 else 0) ||| (if idf then 0x10 else 0)

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

/-- Store a translation in the TLB. -/
@[inline] def tlbFill (m : Machine) (lin : UInt32) (phys : UInt64) (bits : UInt64) (large : Bool) : Machine :=
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  { m with tlbTag := m.tlbTag.set! idx ((lin &&& 0xFFFFF000) ||| 1),
           tlbVal := m.tlbVal.set! idx (phys ||| bits ||| (if large then Tlb.L else 0)),
           tlbLarge := m.tlbLarge || large }

/-- TLB permission bits for combined U/S, R/W bits `perm` and the PTE (or large PDE) dirty bit. -/
@[inline] def tlbBits (perm : UInt32) (dirty wp : Bool) : UInt64 :=
  (if perm &&& 4 != 0 then Tlb.U else 0) |||
  (if perm &&& 6 == 6 then Tlb.UW else 0) |||
  (if perm &&& 2 != 0 || !wp then Tlb.SW else 0) |||
  (if dirty then Tlb.D else 0)

/-- Reserved bits of a 32-bit PDE that maps a 4 MiB page: 21:13, as CPUID reports no PSE-36
(SDM vol. 3 table 4-4 with M = 32). -/
def pse4mRsvd : UInt32 := 0x3FE000

/-- Set the accessed flag of a directory entry that references a page table, once the walk uses it
to read the next level (SDM 4.8: "whenever the processor uses a paging-structure entry as part of
linear-address translation, it sets the accessed flag"), even if the translation then faults on the
page-table entry. Leaf entries get A (and D) only for accesses that are allowed. -/
@[inline] def setTableA (m : Machine) (a : UInt32) (e : UInt32) : Machine :=
  if e &&& 0x20 != 0 then m else { m with mem := wrBytes m.mem a 4 (e ||| 0x20) }

/-- 32-bit paging walk; sets A/D bits and fills the TLB. -/
def walk32 (lin : UInt32) (write user : Bool) : M UInt64 := fun m =>
  let c := m.cpu
  let wp := c.cr0 &&& CR0.WP != 0
  let pdeA : UInt32 := pdeAddr c lin
  let pde := rdBytes m.mem pdeA 4
  if pde &&& 1 == 0 then .error (.exc Vec.PF (some (pfErr write user false)) lin) m else
  let large := pde &&& 0x80 != 0 && c.cr4 &&& CR4.PSE != 0
  if large && pde &&& pse4mRsvd != 0 then .error (.exc Vec.PF (some (pfErr write user true true)) lin) m else
  let m := if large then m else setTableA m pdeA pde
  let pde := if large then pde else pde ||| 0x20
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
    .ok (phys.toUInt64 ||| (lin &&& 0xFFF).toUInt64)
      (tlbFill { m with mem } lin phys.toUInt64 (tlbBits perm (pte &&& 0x40 != 0) wp) large)

/-- Physical-address bits 35:12 of a PAE entry. -/
def paeAddr : UInt64 := 0xFFFFFF000
/-- Reserved bits of PAE PDEs and PTEs (MAXPHYADDR = 36): bits 62:36, and bit 63 unless it is
the XD bit (EFER.NXE = 1). -/
@[inline] def paeRsvd (nxe : Bool) : UInt64 := if nxe then 0x7FFFFFF000000000 else 0xFFFFFFF000000000
/-- Reserved bits of a present PDPTE: 2:1, 8:5 and 63:36. -/
def pdpteRsvd : UInt64 := 0xFFFFFFF0000001E6

/-- PAE permission check: the 32-bit paging rules for U/S and R/W on the PDE (and PTE), and with
EFER.NXE no instruction fetch from a page whose PDE or PTE has XD (bit 63) set. -/
@[inline] def paeAllowed (pde pte : UInt64) (large write user wp fetch nxe : Bool) : Bool :=
  let xd := nxe && (if large then pde else pde ||| pte) >>> 63 != 0
  pageAllowed pde.toUInt32 pte.toUInt32 large write user wp && !(fetch && xd)

/-- PAE paging walk; sets A/D bits and fills the TLB. -/
def walkPae (lin : UInt32) (write user fetch : Bool) : M UInt64 := fun m =>
  let c := m.cpu
  let wp := c.cr0 &&& CR0.WP != 0
  let nxe := c.efer &&& EFER.NXE != 0
  let fault := fun (prot rsvd : Bool) =>
    Fault.exc Vec.PF (some (pfErr write user prot rsvd (fetch && nxe))) lin
  let pdpte := c.pdpte[(lin >>> 30).toNat]!
  if pdpte &&& 1 == 0 then .error (fault false false) m else
  let rsv := paeRsvd nxe
  let pdeA := (pdpte &&& paeAddr) + (((lin >>> 21) &&& 0x1FF).toUInt64 <<< 3)
  let pde := rd64 m.mem pdeA
  if pde &&& 1 == 0 then .error (fault false false) m else
  let large := pde &&& 0x80 != 0
  if pde &&& rsv != 0 || (large && pde &&& 0x1FE000 != 0) then .error (fault true true) m else
  let m := if large then m else setTableA m pdeA.toUInt32 pde.toUInt32
  let pde := if large then pde else pde ||| 0x20
  let pteA := (pde &&& paeAddr) + (((lin >>> 12) &&& 0x1FF).toUInt64 <<< 3)
  let pte := if large then pde else rd64 m.mem pteA
  if pte &&& 1 == 0 then .error (fault false false) m else
  if pte &&& rsv != 0 then .error (fault true true) m else
  if !paeAllowed pde pte large write user wp fetch nxe then .error (fault true false) m else
  let mem := m.mem
  let npde := pde ||| 0x20 ||| (if large && write then 0x40 else 0)
  let mem := if npde != pde then wrBytes mem pdeA.toUInt32 4 npde.toUInt32 else mem
  let (mem, pte) :=
    if large then (mem, npde) else
      let npte := pte ||| 0x20 ||| (if write then 0x40 else 0)
      (if npte != pte then wrBytes mem pteA.toUInt32 4 npte.toUInt32 else mem, npte)
  let phys := if large then (pde &&& 0xFFFE00000) ||| (lin &&& 0x1FF000).toUInt64 else pte &&& paeAddr
  let perm := (if large then pde else pde &&& pte).toUInt32
  let xd := nxe && (if large then pde else pde ||| pte) >>> 63 != 0
  let bits := tlbBits perm (pte &&& 0x40 != 0) wp ||| (if xd then Tlb.NX else 0)
  .ok (phys ||| (lin &&& 0xFFF).toUInt64) (tlbFill { m with mem } lin phys bits large)

/-- Page-table walk in the current paging mode. -/
@[inline] def walk (lin : UInt32) (write user fetch : Bool) : M UInt64 := fun m =>
  if m.cpu.cr4 &&& CR4.PAE != 0 then walkPae lin write user fetch m else walk32 lin write user m

/-- Translate a linear address. `user` selects user-mode permission checking; `fetch` marks an
instruction fetch (checked against execute-disable). -/
@[inline] def translate (lin : UInt32) (write user : Bool) (fetch : Bool := false) : M UInt64 := fun m =>
  if m.cpu.cr0 &&& CR0.PG == 0 then .ok lin.toUInt64 m else
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let tag := m.tlbTag[idx]!
  if tag == ((lin &&& 0xFFFFF000) ||| 1) then
    let v := m.tlbVal[idx]!
    let ok :=
      (!user || v &&& Tlb.U != 0) &&
      (!write || (v &&& Tlb.D != 0 && (if user then v &&& Tlb.UW != 0 else v &&& Tlb.SW != 0))) &&
      (!fetch || v &&& Tlb.NX == 0)
    if ok then .ok ((v &&& ~~~0xFFF) ||| (lin &&& 0xFFF).toUInt64) m else walk lin write user fetch m
  else walk lin write user fetch m

/-- The PDPTE registers for PAE paging with the given CR3: #GP(0) if a present entry has reserved bits set. -/
def readPdptes (cr3 : UInt32) : M (Array UInt64) := fun m =>
  let base := (cr3 &&& 0xFFFFFFE0).toUInt64
  let es := #[rd64 m.mem base, rd64 m.mem (base + 8), rd64 m.mem (base + 16), rd64 m.mem (base + 24)]
  if es.any (fun e => e &&& 1 != 0 && e &&& pdpteRsvd != 0) then .error (.exc Vec.GP (some 0) 0) m
  else .ok es m

/-- Read `n` (1, 2 or 4) bytes at a linear address. -/
def linRd (lin n : UInt32) (user : Bool) (write : Bool := false) : M UInt32 := do
  dbData lin n false
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physRd (← translate lin write user) n
  else
    let p0 ← translate lin write user
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 write user
    let mut v : UInt32 := 0
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF).toUInt64 else p0 + (a - lin).toUInt64
      v := v ||| ((← physRd p 1) <<< (k.toUInt32 * 8))
    return v

/-- Write `n` (1, 2 or 4) bytes at a linear address. Both pages are checked before any byte is written. -/
def linWr (lin n v : UInt32) (user : Bool) : M Unit := do
  dbData lin n true
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physWr (← translate lin true user) n v
  else
    let p0 ← translate lin true user
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 true user
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF).toUInt64 else p0 + (a - lin).toUInt64
      physWr p 1 (v >>> (k.toUInt32 * 8))

/-- Check that a linear range is writable (used by instructions with several writes). A fault on the
second page reports its first byte in CR2, as `linWr` does. -/
def linProbeWr (lin n : UInt32) (user : Bool) : M Unit := do
  let _ ← translate lin true user
  let _ ← translate ((lin + n - 1) &&& 0xFFFFF000) true user

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
  (do physRd (← translate (cs.base + eip) false (← isUser) (fetch := true)) 1) m

end X86
