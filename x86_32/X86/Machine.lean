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

/-- Another CPU's local APIC and INIT state, reachable by interrupt messages while that CPU is not the
running one (`Machine.peers`; the rest of its state is kept by the scheduler, `X86/Mp.lean`). -/
structure Peer where
  apic : Apic := {}
  /-- The CPU waits for a STARTUP IPI (its `Cpu.smpx.waitSipi`). -/
  waitSipi : Bool := false
  deriving Inhabited

/-- Machine state beyond the integer core: local APIC, debug-event bookkeeping, SMI and APM latches.
A parent of `Machine` for the same reason as `CpuExt`. -/
structure MachineExt where
  apic : Apic := {}
  /-- Some TLB entry may come from a large page (INVLPG then scans for its other slices). -/
  tlbLarge : Bool := false
  /-- The 4 MiB / 2 MiB regions (linear address of the large page) whose slices may be in the TLB:
  INVLPG scans the TLB only for an address in one of them (Linux maps its kernel with large pages
  and issues many INVLPGs elsewhere). Superset of the cached regions. -/
  tlbLargeRegions : Array UInt32 := #[]
  /-- Some TLB entry may be global (`Tlb.G`): a CR3 load then scans for the entries it keeps. -/
  tlbGlobal : Bool := false
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
  /-- Multiprocessor (`X86/Mp.lean`): the local APICs of the other CPUs, indexed by CPU number (the
  entry of the running CPU `cur` is unused); empty for a single CPU. -/
  peers : Array Peer := #[]
  cur : Nat := 0
  /-- The I/O APIC (shared). -/
  ioapic : IoApic := {}
  /-- The running CPU has an NMI, INIT or STARTUP message pending or waits for STARTUP (cached from
  `apic` and `cpu`, see `Machine.syncXev`): `step` then takes the slow path `smpEvent?`. -/
  xev : Bool := false
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
/-- global translation (G = 1 in the leaf entry with CR4.PGE = 1): kept by CR3 loads -/
def G  : UInt64 := 64
end Tlb

namespace Machine

/-- Highest-priority request of the master PIC, including the cascade input. -/
def masterHighest (m : Machine) : Option UInt8 :=
  m.pic0.highest (if (m.pic1.highest).isSome then 4 else 0)

/-- Recompute the cached `xev` flag of the running CPU. -/
@[inline] def syncXev (m : Machine) : Machine :=
  { m with xev := m.apic.nmi || m.apic.init || m.apic.sipi.isSome || m.cpu.smpx.waitSipi }

/-- An SMI the running CPU's APIC passed to the core becomes the SMI latch `smiPending`. -/
@[inline] def syncSmi (m : Machine) : Machine :=
  if m.apic.smi then { m with smiPending := true, apic := { m.apic with smi := false } } else m

/-- LINT0 in fixed, SMI or NMI mode (APM 16.4.2): the PIC's INTR output is the input pin (active low
with the polarity bit 13). An edge-triggered entry (SMI and NMI always are) raises its interrupt on
each assertion; a level-triggered fixed entry while asserted with remote IRR (bit 14) clear, setting
remote IRR (cleared by an EOI for its vector, `Apic.eoiVec`). -/
def lint0Sync (m : Machine) : Machine :=
  let a := m.apic
  let e := a.lvt[3]!
  let lvl := m.masterHighest.isSome != (e &&& 0x2000 != 0)
  let levelFixed := e &&& 0x8000 != 0 && (e >>> 8) &&& 7 == 0
  let fire := lvl && (if levelFixed then e &&& 0x4000 == 0 else !a.lint0In)
  let a := { a with lint0In := lvl }
  let a := if !fire then a
    else if levelFixed then
      let a' := a.localInt 3 true
      { a' with lvt := a'.lvt.set! 3 (a'.lvt[3]! ||| 0x4000) }
    else a.localInt 3
  { m with apic := a }.syncSmi.syncXev

/-- Recompute the cached INTR line: the PIC's output (the slave's INT drives master input 2) if it
passes the local APIC's LINT0, an external-interrupt message, or a fixed interrupt the APIC
presents. -/
def syncIntr (m : Machine) : Machine :=
  let m := if m.apic.lint0Live then m.lint0Sync else m
  { m with intr := (m.apic.picPasses && m.masterHighest.isSome) || m.apic.extInt || m.apic.pending.isSome }

/-- Recompute the next timer event. -/
def syncTimer (m : Machine) : Machine :=
  let pit := match m.pit.ch0.nextFire with
    | some t => tickToIcount t
    | none => 0xFFFFFFFFFFFFFFFF
  { m with timerAt := min pit m.apic.timerNext }

/-- After a change of the running CPU's APIC: SMI latch, `xev`, INTR. -/
@[inline] def syncApic (m : Machine) : Machine := m.syncSmi.syncXev.syncIntr

/-! ### Interrupt messages between the APICs (AMD APM vol. 2, 16.5–16.6)

Messages are delivered at once to every targeted APIC: the running CPU's (`apic`) or another CPU's
(`peers`). Fixed and lowest-priority messages enter IRR; SMI, NMI, INIT, STARTUP and ExtINT become
messages to the target's core, taken when that CPU next reaches an instruction boundary. -/

/-- Number of CPUs. -/
@[inline] def ncpu (m : Machine) : Nat := max 1 m.peers.size

/-- The local APIC of CPU `k`. -/
def apicAt (m : Machine) (k : Nat) : Apic :=
  if k == m.cur then m.apic else (m.peers[k]?.map (·.apic)).getD {}

/-- Change the local APIC of CPU `k`. -/
def modApicAt (m : Machine) (k : Nat) (f : Apic → Apic) : Machine :=
  if k == m.cur then { m with apic := f m.apic }
  else if k < m.peers.size then { m with peers := m.peers.modify k fun p => { p with apic := f p.apic } }
  else m

/-- CPU `k` waits for a STARTUP IPI. -/
def waitSipiAt (m : Machine) (k : Nat) : Bool :=
  if k == m.cur then m.cpu.smpx.waitSipi else (m.peers[k]?.map (·.waitSipi)).getD false

/-- HOOK for the NMI architecture (system workstream B), RECONCILE AT MERGE: latch an NMI for CPU `k`.
Here the latch is the APIC's `nmi` message to the core; `smpEvent?` (`X86/Step.lean`) delivers it as
a minimal placeholder (vector 2 at the next boundary, after SMI and debug traps, outside SMM; NMI
blocking until IRET is system B's). Every NMI source of the SMP work (NMI IPIs and I/O APIC entries)
goes through this function; LVT entries in NMI mode set the same flag (`Apic.lvtFire`). -/
def latchNmi (m : Machine) (k : Nat) : Machine := m.modApicAt k fun a => { a with nmi := true }

/-- Lowest-priority arbitration among `cands` for vector `v` (APM 16.6.2): a focus CPU (the vector
in its ISR or IRR, with focus checking enabled by its SVR bit 9 = 0) accepts it, the one with the
highest APIC ID if there are several (the APM leaves this open); otherwise the APIC with the lowest
arbitration priority (APR), ties going to the highest APIC ID. -/
def lowestPri (m : Machine) (v : UInt32) (cands : List Nat) : Option Nat :=
  let higherId := fun (j k : Nat) => (m.apicAt j).physId > (m.apicAt k).physId
  let focus := cands.filter fun k =>
    let a := m.apicAt k
    a.svr &&& 0x200 == 0 && (Apic.getBit a.isr v || Apic.getBit a.irr v)
  match focus with
  | f :: fs => some (fs.foldl (fun b k => if higherId k b then k else b) f)
  | [] =>
    match cands with
    | c :: cs => some (cs.foldl (fun b k =>
        let x := (m.apicAt k).apr
        let y := (m.apicAt b).apr
        if x < y || (x == y && higherId k b) then k else b) c)
    | [] => none

/-- CPU `k`'s APIC receives `msg` (any type but lowest priority and remote read). An INIT
de-assert (trigger mode level, level 0) has no effect on the CPU; a STARTUP is accepted only by a
CPU in (or entering) the INIT state, and the first one wins. -/
def recv (m : Machine) (k : Nat) (msg : Msg) : Machine :=
  match msg.mode with
  | 0 => m.modApicAt k (·.acceptFixed msg.vec msg.level)
  | 2 => m.modApicAt k fun a => { a with smi := true }
  | 4 => m.latchNmi k
  | 5 => if msg.level && !msg.assert then m else m.modApicAt k fun a => { a with init := true, sipi := none }
  | 6 =>
    if m.waitSipiAt k || (m.apicAt k).init then
      m.modApicAt k fun a => if a.sipi.isSome then a else { a with sipi := some msg.vec }
    else m
  | 7 => m.modApicAt k fun a => { a with extInt := true }
  | _ => m

/-- Deliver `msg` to every APIC it targets; `false` if it targets none. The running CPU's derived
state is not synchronized (callers use `syncApic`). -/
def deliver (m : Machine) (msg : Msg) : Machine × Bool :=
  let ts := (List.range m.ncpu).filter fun k => msg.targets k (m.apicAt k)
  if ts.isEmpty then (m, false) else
  if msg.mode == 1 then
    match m.lowestPri msg.vec (ts.filter fun k => (m.apicAt k).swEnabled) with
    | some k => (m.modApicAt k (·.acceptFixed msg.vec msg.level), true)
    | none => (m, true)
  else (ts.foldl (fun m k => m.recv k msg) m, true)

/-- The message the ICR describes (xAPIC: destination ICR[63:56]; x2APIC: ICR[63:32]). -/
def icrMsg (a : Apic) (src : Nat) : Msg :=
  let lo := a.icrLo
  { mode := (lo >>> 8) &&& 7, vec := lo &&& 0xFF, level := lo &&& 0x8000 != 0,
    assert := lo &&& 0x4000 != 0, dest := if a.x2 then a.icrHi else a.icrHi >>> 24,
    logical := lo &&& 0x800 != 0, sh := (lo >>> 18) &&& 3, x2 := a.x2, src := some src }

/-- Remote read (message type 011b, APM 16.5): the register at offset VEC·16 of the APIC named by a
physical destination is copied to the remote read register; ICR.RRS = 10b (valid) or 00b (no such
APIC, a broadcast, shorthand or logical destination, or an unimplemented register). -/
def remoteRead (m : Machine) (msg : Msg) : Machine :=
  let tgt := if msg.sh != 0 || msg.logical || msg.dest &&& 0xFF == 0xFF then none
    else (List.range m.ncpu).find? fun k => msg.targets k (m.apicAt k)
  let v := tgt.bind fun k => (m.apicAt k).read (msg.vec <<< 4) m.icount
  let a := m.apic
  let lo := a.icrLo &&& ~~~0x30000
  match v with
  | some v => { m with apic := { a with rrr := v, icrLo := lo ||| 0x20000 } }
  | none => { m with apic := { a with icrLo := lo } }

/-- The running CPU sends the IPI its ICR describes (a write to ICR low, or to the x2APIC ICR or
SELF IPI register). Fixed and lowest-priority messages with vectors 0..15 record SIV (and are sent);
an IPI no APIC matches records SAE. -/
def sendIcr (m : Machine) : Machine :=
  let msg := icrMsg m.apic m.cur
  if msg.mode == 3 then m.remoteRead msg else
  let m := if (msg.mode == 0 || msg.mode == 1) && msg.vec < 16 then { m with apic := m.apic.error Esr.SIV } else m
  let (m, ok) := m.deliver msg
  if ok then m else { m with apic := m.apic.error Esr.SAE }

/-! ### I/O APIC -/

/-- Redirection entry `p` sends its message; a level-triggered entry sets remote IRR. -/
def ioapicSend (m : Machine) (p : Nat) : Machine :=
  let s := m.ioapic
  let e := s.entry p
  let m := if e &&& 0x8000 != 0 then { m with ioapic := { s with redir := s.redir.set! p (e ||| 0x4000) } } else m
  (m.deliver (s.msg p)).1.syncApic

/-- A level-triggered entry sends its message while its pin is asserted, it is unmasked and its
remote IRR is clear. -/
def ioapicService (m : Machine) (p : Nat) : Machine :=
  let s := m.ioapic
  let e := s.entry p
  if e &&& 0x10000 == 0 && e &&& 0x8000 != 0 && e &&& 0x4000 == 0 && s.asserted p then m.ioapicSend p else m

/-- Input pin `p` of the I/O APIC goes to `level`. -/
def ioapicPin (m : Machine) (p : Nat) (level : Bool) : Machine :=
  let s := m.ioapic
  let bit : UInt32 := 1 <<< p.toUInt32
  if (s.lines &&& bit != 0) == level then m else
  let was := s.asserted p
  let s := { s with lines := if level then s.lines ||| bit else s.lines &&& ~~~bit }
  let m := { m with ioapic := s }
  let e := s.entry p
  if e &&& 0x10000 != 0 then m
  else if e &&& 0x8000 == 0 then (if !was && s.asserted p then m.ioapicSend p else m)
  else m.ioapicService p

/-- EOI message for vector `v` from a local APIC: every level-triggered entry with that vector and
remote IRR set has it cleared, and sends again if its pin is still asserted. -/
def ioapicEoi (m : Machine) (v : UInt32) : Machine :=
  (List.range IoApic.pins).foldl (fun m p =>
    let e := m.ioapic.entry p
    if e &&& 0x4000 != 0 && (e &&& 0xFF).toUInt32 == v then
      { m with ioapic := { m.ioapic with redir := m.ioapic.redir.set! p (e &&& ~~~0x4000) } }.ioapicService p
    else m) m

/-- ISA interrupt line `irq` (0..15) goes to `level`: the PIC pair and the I/O APIC (IRQ 0 drives
pin 2). -/
def setIrq (m : Machine) (irq : Nat) (level : Bool) : Machine :=
  let m := if irq < 8 then { m with pic0 := m.pic0.setLine irq.toUInt8 level }
           else { m with pic1 := m.pic1.setLine (irq - 8).toUInt8 level }
  m.ioapicPin (if irq == 0 then 2 else irq) level

/-- I/O APIC register page: read at physical address `a` (IOREGSEL at 00h, IOWIN at 10h). -/
def ioapicRead (m : Machine) (a : UInt32) : UInt32 :=
  match a &&& 0xFC with
  | 0x00 => m.ioapic.sel
  | 0x10 => m.ioapic.readWin
  | _ => 0

/-- I/O APIC register page: write of `n` bytes at `a`. IOREGSEL takes any write to offset 00h, IOWIN
aligned 32-bit writes; a redirection entry written with a level-triggered, asserted, unmasked pin
sends at once. -/
def ioapicWrite (m : Machine) (a n v : UInt32) : Machine :=
  match a &&& 0xFF with
  | 0x00 => { m with ioapic := { m.ioapic with sel := v &&& 0xFF } }
  | 0x10 =>
    if n != 4 then m else
    let (s, p) := m.ioapic.writeWin v
    let m := { m with ioapic := s }
    match p with
    | some p => m.ioapicService p
    | none => m
  | _ => m

/-! ### Local APIC registers -/

/-- EOI (APM 16.6.4): a level-triggered vector also sends an EOI message to the I/O APIC. -/
def apicEoiVec (m : Machine) (r : Apic × Option UInt32) : Machine :=
  let m := { m with apic := r.1 }
  (match r.2 with | some v => m.ioapicEoi v | none => m).syncApic

/-- Register read of the running CPU's APIC (xAPIC layout); an unimplemented register reads 0 and
records IRA. -/
def apicRead (m : Machine) (off : UInt32) : UInt32 × Machine :=
  match m.apic.read off m.icount with
  | some v => (v, m)
  | none => (0, { m with apic := m.apic.error Esr.IRA }.syncApic)

/-- Register write to the running CPU's APIC (xAPIC layout): EOI, ICR low (sends the IPI; the
read-only remote-read status is kept), SEOI (with SN: EOI of the written vector, APM 16.7.1), the
others through `Apic.write`; an unimplemented register records IRA. -/
def apicWrite (m : Machine) (off v : UInt32) : Machine :=
  match off with
  | 0xB0 => m.apicEoiVec m.apic.eoi
  | 0x300 =>
    { m with apic := { m.apic with icrLo := (v &&& 0xCCFFF) ||| (m.apic.icrLo &&& 0x30000) } }.sendIcr.syncApic
  | 0x420 => if m.apic.extCtl &&& 2 == 0 then m else m.apicEoiVec (m.apic.eoiVec (v &&& 0xFF))
  | _ =>
    match m.apic.write off v m.icount with
    | some a => { m with apic := a }.syncTimer.syncApic
    | none => { m with apic := m.apic.error Esr.IRA }.syncApic

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

/-- The local APIC claims the 4 KiB page at its base while globally enabled in xAPIC mode
(`Apic.mmio`). -/
@[inline] def isApic (m : Machine) (a : UInt32) : Bool := a &&& 0xFFFFF000 == m.apic.mmio

/-- The device pages: the local APIC's and the I/O APIC's (`ioApicBase`). -/
@[inline] def isMmio (m : Machine) (a : UInt32) : Bool :=
  isApic m a || a &&& 0xFFFFF000 == ioApicBase

/-- Read of `n` bytes in a device page (the local APIC takes precedence over the I/O APIC). -/
def mmioRd (a n : UInt32) : M UInt32 := fun m =>
  if m.tso.isSome then .error (.unsupported "TSO: APIC MMIO") m else
  let (v, m) := if isApic m a then m.apicRead (a &&& 0xFF0) else (m.ioapicRead a, m)
  let v := v >>> ((a &&& 3) * 8)
  .ok (if n == 4 then v else v &&& ((1 <<< (n * 8)) - 1)) m

/-- Write of `n` bytes in a device page: the local APIC takes aligned 32-bit writes only (others are
ignored), for the I/O APIC see `Machine.ioapicWrite`. -/
def mmioWr (a n v : UInt32) : M Unit := fun m =>
  if m.tso.isSome then .error (.unsupported "TSO: APIC MMIO") m
  else if isApic m a then .ok () (if n == 4 && a &&& 3 == 0 then m.apicWrite (a &&& 0xFF0) v else m)
  else .ok () (m.ioapicWrite a n v)

@[inline] def physRd (p : UInt64) (n : UInt32) : M UInt32 := fun m =>
  if p >>> 32 != 0 then .ok (openBus n) m else
  let a := p.toUInt32
  if isMmio m a then mmioRd a n m
  else match m.tso with
    | none => .ok (rdBytes m.mem a n) m
    | some l => .ok (rdBytes m.mem a n) { m with tso := some { l with reads := l.reads.push (a, n) } }
/-- Physical write (device pages: `mmioWr`). -/
@[inline] def physWr (p : UInt64) (n v : UInt32) : M Unit := fun m =>
  if p >>> 32 != 0 then .ok () m else
  let a := p.toUInt32
  if isMmio m a then mmioWr a n v m
  else match m.tso with
    | none => .ok () { m with mem := wrBytes m.mem a n v }
    | some l => .ok () { m with mem := wrBytes m.mem a n v,
                                tso := some { l with writes := l.writes.push ⟨a, n, v⟩ } }

/-- A 64-bit paging-structure entry at physical address `p` (open bus above 4 GiB). -/
@[inline] def rd64 (mem : ByteArray) (p : UInt64) : UInt64 :=
  if p >>> 32 != 0 then 0xFFFFFFFFFFFFFFFF
  else (rdBytes mem p.toUInt32 4).toUInt64 ||| ((rdBytes mem (p.toUInt32 + 4) 4).toUInt64 <<< 32)

/-! ## Paging

Two paging modes: 32-bit paging (CR4.PAE = 0; 4 KiB pages and, with CR4.PSE, 4 MiB pages whose PDE
bits 20:13 hold physical-address bits 39:32, PSE-36) and PAE paging (CR4.PAE = 1; four PDPTE
registers, 64-bit entries, 4 KiB and 2 MiB pages, and the execute-disable bit when EFER.NXE = 1).
MAXPHYADDR is 48 (`maxPhysAddr`, CPUID Fn8000_0008_EAX[PhysAddrSize] of the EPYC 7742). Physical
addresses at or above 4 GiB are open bus (`physRd`).

Protection: the U/S and R/W bits with CR0.WP (`pageAllowed`), execute-disable (`paeAllowed`), and
for supervisor accesses to user pages SMEP and SMAP (`smAllowed`). Global pages (G with CR4.PGE)
survive CR3 loads (`flushTlb`); every other TLB invalidation drops them too (`flushTlbAll`). -/

/-- Physical-address width (AMD APM vol. 2, 5.2.3: PAE entries hold physical-address bits up to
the implementation's maximum, CPUID Fn8000_0008_EAX[7:0] = 0x30 on the EPYC 7742, `Cpuid.raw`). -/
def maxPhysAddr : Nat := 48

/-- Invalidate every TLB entry, including global ones (AMD APM vol. 2, 5.5.3 "Implicit
Invalidations": changes of CR0.PG, CR4.PAE/PSE/PGE, SMM entry and RSM, MTRR writes). -/
def flushTlbAll : M Unit := modM fun m =>
  { m with tlbTag := Array.replicate tlbSize 0, tlbLarge := false, tlbGlobal := false, tlbLargeRegions := #[] }

/-- A CR3 load (MOV CR3, task switch): invalidate every TLB entry except global ones (AMD APM vol. 2,
5.5.2). Without global entries this is `flushTlbAll`. -/
def flushTlb : M Unit := modM fun m =>
  if !m.tlbGlobal then
    { m with tlbTag := Array.replicate tlbSize 0, tlbLarge := false, tlbLargeRegions := #[] }
  else
    { m with tlbTag := Id.run do
        let mut t := m.tlbTag
        for k in [0:tlbSize] do
          if m.tlbVal[k]! &&& Tlb.G == 0 then t := t.set! k 0
        return t }

/-- INVLPG: drop the translation of the page containing `lin`, global or not (AMD APM vol. 2, 5.5.2),
including every cached 4 KiB slice of a large page that contains it. -/
def flushTlbPage (lin : UInt32) : M Unit := modM fun m =>
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let m := { m with tlbTag := m.tlbTag.set! idx 0 }
  if !m.tlbLarge then m else
  let mask : UInt32 := if m.cpu.cr4 &&& CR4.PAE != 0 then 0xFFE00000 else 0xFFC00000
  let region := lin &&& mask
  if !m.tlbLargeRegions.contains region then m else
  { m with tlbLargeRegions := m.tlbLargeRegions.filter (· != region), tlbTag := Id.run do
      let mut t := m.tlbTag
      for k in [0:tlbSize] do
        if m.tlbVal[k]! &&& Tlb.L != 0 && t[k]! &&& 1 != 0 && t[k]! &&& mask == region then
          t := t.set! k 0
      return t }

/-- Page-fault error code: P (protection violation), W/R, U/S, RSVD (reserved bit set in a
paging-structure entry) and I/D (instruction fetch, reported with PAE paging and EFER.NXE, or with
CR4.SMEP: see `walk32`). -/
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

/-- SMEP and SMAP for a supervisor access to a user page (AMD APM vol. 2, 5.6.5, 5.6.6): with
CR4.SMEP no instruction fetch; with CR4.SMAP no data access, unless it is an explicit access (not
`implicit`, i.e. not a descriptor-table, IDT or TSS access) made with EFLAGS.AC = 1. An explicit
supervisor access is made at CPL 0..2, so this is AMD's "CPL 0, 1 or 2 and RFLAGS.AC = 0" rule;
implicit supervisor accesses are checked regardless of AC (and of CPL). -/
@[inline] def smPass (cr4 eflags : UInt32) (fetch implicit : Bool) : Bool :=
  if fetch then cr4 &&& CR4.SMEP == 0
  else cr4 &&& CR4.SMAP == 0 || (!implicit && eflags &&& Flag.AC != 0)

/-- SMEP/SMAP check of an access through entries with combined U/S, R/W bits `perm`: user accesses
and accesses to supervisor pages (U/S = 0 at some level) pass; see `smPass` for the others. -/
@[inline] def smAllowed (perm cr4 eflags : UInt32) (user fetch implicit : Bool) : Bool :=
  user || perm &&& 4 == 0 || smPass cr4 eflags fetch implicit

/-- Store a translation in the TLB. -/
@[inline] def tlbFill (m : Machine) (lin : UInt32) (phys : UInt64) (bits : UInt64) (large : Bool) : Machine :=
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let region := lin &&& (if m.cpu.cr4 &&& CR4.PAE != 0 then 0xFFE00000 else 0xFFC00000)
  { m with tlbTag := m.tlbTag.set! idx ((lin &&& 0xFFFFF000) ||| 1),
           tlbVal := m.tlbVal.set! idx (phys ||| bits ||| (if large then Tlb.L else 0)),
           tlbLarge := m.tlbLarge || large,
           tlbLargeRegions := if large && !m.tlbLargeRegions.contains region then m.tlbLargeRegions.push region
                              else m.tlbLargeRegions,
           tlbGlobal := m.tlbGlobal || bits &&& Tlb.G != 0 }

/-- TLB permission bits for combined U/S, R/W bits `perm` and the PTE (or large PDE) dirty bit. -/
@[inline] def tlbBits (perm : UInt32) (dirty wp : Bool) : UInt64 :=
  (if perm &&& 4 != 0 then Tlb.U else 0) |||
  (if perm &&& 6 == 6 then Tlb.UW else 0) |||
  (if perm &&& 2 != 0 || !wp then Tlb.SW else 0) |||
  (if dirty then Tlb.D else 0)

/-- Reserved bit of a 32-bit PDE that maps a 4 MiB page: bit 21. Bits 20:13 are physical-address
bits 39:32 (PSE-36, CPUID Fn0000_0001_EDX[PSE36]; AMD APM vol. 2, 5.2.2, figure 5-8: "bits 20:13 hold
eight additional high-order physical-address bits. Bit 21 is reserved and must be cleared to 0"). -/
def pse4mRsvd : UInt32 := 0x200000

/-- Physical page of a 4 MiB PDE: bits 31:22, and bits 39:32 from PDE bits 20:13 (PSE-36). -/
@[inline] def pse36Base (pde : UInt32) : UInt64 :=
  (pde &&& 0xFFC00000).toUInt64 ||| (((pde >>> 13) &&& 0xFF).toUInt64 <<< 32)

/-- Global-page bit of a leaf entry (bit 8), effective with CR4.PGE (AMD APM vol. 2, 5.4.1 "Global Page
(G) Bit"). -/
@[inline] def globalBit (cr4 leaf : UInt32) : UInt64 :=
  if cr4 &&& CR4.PGE != 0 && leaf &&& 0x100 != 0 then Tlb.G else 0

/-- Set the accessed flag of a directory entry that references a page table, once the walk uses it
to read the next level (SDM 4.8: "whenever the processor uses a paging-structure entry as part of
linear-address translation, it sets the accessed flag"), even if the translation then faults on the
page-table entry. Leaf entries get A (and D) only for accesses that are allowed. -/
@[inline] def setTableA (m : Machine) (a : UInt32) (e : UInt32) : Machine :=
  if e &&& 0x20 != 0 then m else { m with mem := wrBytes m.mem a 4 (e ||| 0x20) }

/-- 32-bit paging walk; sets A/D bits and fills the TLB. The I/D bit of the error code is set for
instruction fetches when CR4.SMEP = 1: AMD defines it only with PAE and EFER.NXE (APM vol. 2, 8.4.2),
Intel also with SMEP (SDM vol. 3, 4.7), which this follows (as QEMU does). -/
def walk32 (lin : UInt32) (write user fetch implicit : Bool) : M UInt64 := fun m =>
  let c := m.cpu
  let wp := c.cr0 &&& CR0.WP != 0
  let idf := fetch && c.cr4 &&& CR4.SMEP != 0
  let pdeA : UInt32 := pdeAddr c lin
  let pde := rdBytes m.mem pdeA 4
  if pde &&& 1 == 0 then .error (.exc Vec.PF (some (pfErr write user false false idf)) lin) m else
  let large := pde &&& 0x80 != 0 && c.cr4 &&& CR4.PSE != 0
  if large && pde &&& pse4mRsvd != 0 then .error (.exc Vec.PF (some (pfErr write user true true idf)) lin) m else
  let m := if large then m else setTableA m pdeA pde
  let pde := if large then pde else pde ||| 0x20
  let pteA : UInt32 := pteAddr pde lin
  let pte := if large then pde else rdBytes m.mem pteA 4
  if pte &&& 1 == 0 then .error (.exc Vec.PF (some (pfErr write user false false idf)) lin) m else
  let perm := if large then pde else pde &&& pte
  if !pageAllowed pde pte large write user wp || !smAllowed perm c.cr4 c.eflags user fetch implicit then
    .error (.exc Vec.PF (some (pfErr write user true false idf)) lin) m
  else
    let mem := m.mem
    let npde := pde ||| 0x20 ||| (if large && write then 0x40 else 0)
    let mem := if npde != pde then wrBytes mem pdeA 4 npde else mem
    let (mem, pte) :=
      if large then (mem, npde) else
        let npte := pte ||| 0x20 ||| (if write then 0x40 else 0)
        (if npte != pte then wrBytes mem pteA 4 npte else mem, npte)
    let phys := if large then pse36Base pde ||| (lin &&& 0x3FF000).toUInt64
                else (pte &&& 0xFFFFF000).toUInt64
    let bits := tlbBits perm (pte &&& 0x40 != 0) wp ||| globalBit c.cr4 pte
    .ok (phys ||| (lin &&& 0xFFF).toUInt64) (tlbFill { m with mem } lin phys bits large)

/-- Physical-address bits 47:12 of a PAE entry (MAXPHYADDR = 48). -/
def paeAddr : UInt64 := 0xFFFFFFFFF000
/-- Reserved bits of PAE PDEs and PTEs (MAXPHYADDR = 48; AMD APM vol. 2, figures 5-11, 5-12, 5-15:
bits 62:52 and the unimplemented address bits 51:48), and bit 63 unless it is the NX bit
(EFER.NXE = 1). -/
@[inline] def paeRsvd (nxe : Bool) : UInt64 := if nxe then 0x7FFF000000000000 else 0xFFFF000000000000
/-- Reserved bits of a present PDPTE: 2:1, 8:5 and 63:48 (AMD APM vol. 2, figures 5-10, 5-14). -/
def pdpteRsvd : UInt64 := 0xFFFF0000000001E6

/-- PAE permission check: the 32-bit paging rules for U/S and R/W on the PDE (and PTE), and with
EFER.NXE no instruction fetch from a page whose PDE or PTE has XD (bit 63) set. -/
@[inline] def paeAllowed (pde pte : UInt64) (large write user wp fetch nxe : Bool) : Bool :=
  let xd := nxe && (if large then pde else pde ||| pte) >>> 63 != 0
  pageAllowed pde.toUInt32 pte.toUInt32 large write user wp && !(fetch && xd)

/-- PAE paging walk; sets A/D bits and fills the TLB. -/
def walkPae (lin : UInt32) (write user fetch implicit : Bool) : M UInt64 := fun m =>
  let c := m.cpu
  let wp := c.cr0 &&& CR0.WP != 0
  let nxe := c.efer &&& EFER.NXE != 0
  let fault := fun (prot rsvd : Bool) =>
    Fault.exc Vec.PF (some (pfErr write user prot rsvd (fetch && (nxe || c.cr4 &&& CR4.SMEP != 0)))) lin
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
  let perm := (if large then pde else pde &&& pte).toUInt32
  if !paeAllowed pde pte large write user wp fetch nxe || !smAllowed perm c.cr4 c.eflags user fetch implicit then
    .error (fault true false) m else
  let mem := m.mem
  let npde := pde ||| 0x20 ||| (if large && write then 0x40 else 0)
  let mem := if npde != pde then wrBytes mem pdeA.toUInt32 4 npde.toUInt32 else mem
  let (mem, pte) :=
    if large then (mem, npde) else
      let npte := pte ||| 0x20 ||| (if write then 0x40 else 0)
      (if npte != pte then wrBytes mem pteA.toUInt32 4 npte.toUInt32 else mem, npte)
  let phys := if large then (pde &&& 0xFFFFFFE00000) ||| (lin &&& 0x1FF000).toUInt64 else pte &&& paeAddr
  let xd := nxe && (if large then pde else pde ||| pte) >>> 63 != 0
  let bits := tlbBits perm (pte &&& 0x40 != 0) wp ||| (if xd then Tlb.NX else 0) |||
    globalBit c.cr4 pte.toUInt32
  .ok (phys ||| (lin &&& 0xFFF).toUInt64) (tlbFill { m with mem } lin phys bits large)

/-- Page-table walk in the current paging mode. -/
@[inline] def walk (lin : UInt32) (write user fetch : Bool) (implicit : Bool := false) : M UInt64 := fun m =>
  if m.cpu.cr4 &&& CR4.PAE != 0 then walkPae lin write user fetch implicit m
  else walk32 lin write user fetch implicit m

/-- Translate a linear address. `user` selects user-mode permission checking; `fetch` marks an
instruction fetch (checked against execute-disable and SMEP); `implicit` marks an implicit
supervisor access (descriptor tables, IDT, TSS: `sysRd`/`sysWr`), which EFLAGS.AC does not exempt
from SMAP. A TLB hit is used only if it permits the access under the current CR4/EFLAGS; otherwise
the walk decides (and faults). -/
@[inline] def translate (lin : UInt32) (write user : Bool) (fetch : Bool := false) (implicit : Bool := false) :
    M UInt64 := fun m =>
  if m.cpu.cr0 &&& CR0.PG == 0 then .ok lin.toUInt64 m else
  let idx := ((lin >>> 12) % tlbSize.toUInt32).toNat
  let tag := m.tlbTag[idx]!
  if tag == ((lin &&& 0xFFFFF000) ||| 1) then
    let v := m.tlbVal[idx]!
    let ok :=
      (if user then v &&& Tlb.U != 0
       else v &&& Tlb.U == 0 || smPass m.cpu.cr4 m.cpu.eflags fetch implicit) &&
      (!write || (v &&& Tlb.D != 0 && (if user then v &&& Tlb.UW != 0 else v &&& Tlb.SW != 0))) &&
      (!fetch || v &&& Tlb.NX == 0)
    if ok then .ok ((v &&& ~~~0xFFF) ||| (lin &&& 0xFFF).toUInt64) m else walk lin write user fetch implicit m
  else walk lin write user fetch implicit m

/-- The PDPTE registers for PAE paging with the given CR3: #GP(0) if a present entry has reserved bits set. -/
def readPdptes (cr3 : UInt32) : M (Array UInt64) := fun m =>
  let base := (cr3 &&& 0xFFFFFFE0).toUInt64
  let es := #[rd64 m.mem base, rd64 m.mem (base + 8), rd64 m.mem (base + 16), rd64 m.mem (base + 24)]
  if es.any (fun e => e &&& 1 != 0 && e &&& pdpteRsvd != 0) then .error (.exc Vec.GP (some 0) 0) m
  else .ok es m

/-- Read `n` (1, 2 or 4) bytes at a linear address. -/
def linRd (lin n : UInt32) (user : Bool) (write : Bool := false) (implicit : Bool := false) : M UInt32 := do
  dbData lin n false
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physRd (← translate lin write user false implicit) n
  else
    let p0 ← translate lin write user false implicit
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 write user false implicit
    let mut v : UInt32 := 0
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF).toUInt64 else p0 + (a - lin).toUInt64
      v := v ||| ((← physRd p 1) <<< (k.toUInt32 * 8))
    return v

/-- Write `n` (1, 2 or 4) bytes at a linear address. Both pages are checked before any byte is written. -/
def linWr (lin n v : UInt32) (user : Bool) (implicit : Bool := false) : M Unit := do
  dbData lin n true
  if (lin &&& 0xFFF) + n ≤ 0x1000 then
    physWr (← translate lin true user false implicit) n v
  else
    let p0 ← translate lin true user false implicit
    let lin1 := (lin + n - 1) &&& 0xFFFFF000
    let p1 ← translate lin1 true user false implicit
    for k in [0:n.toNat] do
      let a := lin + k.toUInt32
      let p := if a &&& 0xFFFFF000 == lin1 then p1 + (a &&& 0xFFF).toUInt64 else p0 + (a - lin).toUInt64
      physWr p 1 (v >>> (k.toUInt32 * 8))

/-- Check that a linear range is writable (used by instructions with several writes). A fault on the
second page reports its first byte in CR2, as `linWr` does. -/
def linProbeWr (lin n : UInt32) (user : Bool) : M Unit := do
  let _ ← translate lin true user
  let _ ← translate ((lin + n - 1) &&& 0xFFFFF000) true user

/-! ## Alignment check

#AC(0) (AMD APM vol. 2, 8.2.17): with CR0.AM = 1 and EFLAGS.AC = 1, a data access at CPL 3 to an
operand that is not aligned to its type's boundary (table 8-7: word 2, doubleword 4, quadword 8,
64-bit media 8, 128-bit media 16, x87 single 4, double and extended 8, x87 save areas 2 or 4, segment
selector 2, far pointers by their parts, bit strings by the operand size). Accesses that are
supervisor accesses regardless of CPL (descriptor tables, IDT, TSS: `sysRd`/`sysWr`) and instruction
fetches are never checked (SDM vol. 3, 6.15: "memory references that default to privilege level 0,
such as segment descriptor loads, do not generate alignment-check exceptions"). The check is on the
linear address, after the segment checks and before paging (Bochs does the same; real hardware's
order between #AC and #PF is not documented).

`rdMem`/`wrMem` check an access against its own size by default (`al := n`), which is the table's
requirement for single accesses; instructions whose operand is made of several accesses pass the
operand's requirement for the first part and `al := 1` for the rest. Only a misaligned access at
CPL 3 reaches `acCheck`, so aligned accesses pay one test. -/

/-- Alignment checking is enabled: CR0.AM = 1, EFLAGS.AC = 1 and CPL 3 (the one definition, also used
by `Simd.misalignExc` for misaligned SSE operands with MXCSR.MM). -/
@[inline] def Cpu.acEnabled (c : Cpu) : Bool :=
  c.cr0 &&& CR0.AM != 0 && c.eflags &&& Flag.AC != 0 && c.cpl == 3

/-- #AC(0) if alignment checking is enabled; the caller has established that the access is a
misaligned CPL-3 access. -/
@[inline] def acCheck : M Unit := fun m =>
  if m.cpu.acEnabled then .error (.exc Vec.AC (some 0) 0) m else .ok () m

/-- Alignment check of an access (or operand) at linear address `lin` with required alignment `al`
(a power of two) made with CPL 3 (`user`). -/
@[inline] def acChk (lin al : UInt32) (user : Bool) : M Unit :=
  if user && lin &&& (al - 1) != 0 then acCheck else pure ()

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

/-- Read `n` bytes at `seg:off`; RMW operands use write permission from the first access. `al` is the
alignment the access must have at CPL 3 with alignment checking (see `acChk`). -/
@[inline] def rdMem (s : UInt8) (off n : UInt32) (write : Bool := false) (al : UInt32 := n) : M UInt32 := do
  let lin ← segAddr s off n write
  let u ← isUser
  acChk lin al u
  linRd lin n u write

/-- Write `n` bytes at `seg:off` (`al` as for `rdMem`). -/
@[inline] def wrMem (s : UInt8) (off n v : UInt32) (al : UInt32 := n) : M Unit := do
  let lin ← segAddr s off n true
  let u ← isUser
  acChk lin al u
  linWr lin n v u

/-- Implicit supervisor-mode linear accesses (descriptor tables, IDT, TSS): supervisor accesses
whatever the CPL, subject to SMAP regardless of EFLAGS.AC, never alignment-checked. -/
@[inline] def sysRd (lin n : UInt32) : M UInt32 := linRd lin n false (implicit := true)
@[inline] def sysWr (lin n v : UInt32) : M Unit := linWr lin n v false (implicit := true)

/-- Fetch one code byte at `CS:eip`. -/
@[inline] def fetch8 (eip : UInt32) : M UInt32 := fun m =>
  let cs := m.cpu.cs
  if eip > cs.limit then .error (.exc Vec.GP (some 0) 0) m else
  (do physRd (← translate (cs.base + eip) false (← isUser) (fetch := true)) 1) m

end X86
