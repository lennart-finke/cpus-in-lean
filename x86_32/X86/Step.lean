import X86.Dispatch
/-!
# The step function

`step` performs one architectural step: it accepts a pending external interrupt,
idles while halted, or fetches, decodes and executes one instruction. A faulting
instruction leaves completed multi-store writes visible (see `Exec`); most register effects are discarded
by restoring the CPU snapshot, and the exception is delivered with EIP pointing at the
faulting instruction. POPA retains completed general-register loads.
-/
namespace X86

def maxU64 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Machine state for delivering fault `vec` of an instruction: CR2 for #PF, the DR6 bits for #DB
(both carried in `addr`), and RF set in the EFLAGS image of a fault-class exception, so that the
restarted instruction does not re-trigger an instruction breakpoint (SDM 17.3.1.1;
instruction-breakpoint faults are raised by `step` instead). -/
def faultState (m : Machine) (vec : UInt8) (addr : UInt32) : Machine :=
  let c := m.cpu
  let c := if vec == Vec.PF then { c with cr2 := addr } else c
  let c := if vec == Vec.DB then { c with dr6 := c.dr6 ||| addr } else c
  { m with cpu := { c with eflags := c.eflags ||| Flag.RF } }

/-- Deliver an exception from a consistent state; a fault during delivery escalates to
#DF, and a fault while delivering #DF shuts the machine down. A fault after a task switch through a
task gate has committed is an exception in the new task (`fuel` bounds such chains). -/
def raiseExcF : Nat → Machine → UInt8 → Option UInt32 → Bool → Machine
  | 0, m, vec, _, _ => { m with fatal := some (.shutdown s!"exception loop delivering vector {vec}") }
  | fuel + 1, m, vec, err, ext =>
    -- entering the #DB handler clears DR7.GD, so the handler can access the debug registers
    let m := if vec == Vec.DB then { m with cpu := { m.cpu with dr7 := m.cpu.dr7 &&& ~~~0x2000 } } else m
    let saved := m.cpu
    match deliver vec err false ext { m with keepCpu := false } with
    | .ok _ m => { m with keepCpu := false }
    | .error f m =>
      if m.keepCpu then
        let m := { m with keepCpu := false }
        match f with
        | .exc v e a => raiseExcF fuel (faultState m v a) v e false
        | f => { m with fatal := some f }
      else
      let m := { m with cpu := saved }
      if vec == Vec.DF then { m with fatal := some (.shutdown s!"triple fault ({repr f})") }
      else match f with
        | .exc _ _ _ => raiseExcF fuel m Vec.DF (some 0) false
        | f => { m with fatal := some f }

@[inline] def raiseExc (m : Machine) (vec : UInt8) (err : Option UInt32) (ext : Bool) : Machine :=
  raiseExcF 4 m vec err ext

/-- Deliver the fault of an instruction (see `faultState`). -/
def handleFault (m : Machine) (f : Fault) : Machine :=
  match f with
  | .exc vec err addr => raiseExc (faultState m vec addr) vec err false
  | f => { m with fatal := some f }

/-- LOCK is only permitted on read-modify-write instructions with a memory destination (and, with
AltMovCr8, on MOV CR). -/
def lockOk (i : Inst) : Bool :=
  i.isMem &&
  (let op := i.op
   (op < 0x40 && op &&& 7 < 2 && op &&& 0x38 != 0x38) ||
   ((op == 0x80 || op == 0x81 || op == 0x82 || op == 0x83) && i.reg != 7) ||
   op == 0x86 || op == 0x87 ||
   ((op == 0xF6 || op == 0xF7) && (i.reg == 2 || i.reg == 3)) ||
   ((op == 0xFE || op == 0xFF) && i.reg < 2) ||
   op == 0x1AB || op == 0x1B3 || op == 0x1BB || (op == 0x1BA && i.reg ≥ 5) ||
   op == 0x1B0 || op == 0x1B1 || op == 0x1C0 || op == 0x1C1 || (op == 0x1C7 && i.reg == 1)) ||
  -- AltMovCr8 (AMD): LOCK MOV CR0 accesses CR8 (`Sys.op0F?`)
  (implemented .altMovCr8 && !i.vex && (i.op == 0x120 || i.op == 0x122))

/-- Restore instruction-start state on a fault, except for POPA's completed
register loads and MXCSR: the exception flags of an unmasked SIMD exception are set when it is
raised (#XM), and no instruction changes MXCSR before another fault can occur.
ESP and EIP always retain their restart values. -/
def faultCpu (saved current : Cpu) (i : Inst) : Cpu :=
  if i.op == 0x61 then
    { saved with
      sse := { saved.sse with mxcsr := current.mxcsr }
      eax := current.eax
      ecx := current.ecx
      edx := current.edx
      ebx := current.ebx
      ebp := current.ebp
      esi := current.esi
      edi := current.edi }
  else if saved.mxcsr == current.mxcsr then saved
  else { saved with sse := { saved.sse with mxcsr := current.mxcsr } }

/-- Fetch/decode/execute one instruction, including fault-state restoration.
Callers must retain the returned fault state: POPA can commit register loads,
and multi-store instructions can commit memory before a later page fault.
Only the CPU snapshot is kept, never `m` itself: a live reference to `m` would share its memory with
the running instruction and turn every store into a copy of the whole memory. -/
def execInstr : M Inst := fun m =>
  -- RF is cleared at the start of every instruction (after the instruction-breakpoint check)
  let m := if m.cpu.eflags &&& Flag.RF != 0 then
    { m with cpu := { m.cpu with eflags := m.cpu.eflags &&& ~~~Flag.RF } } else m
  let saved := m.cpu
  match decode m with
  | .error f m' => .error f { m' with cpu := saved }
  | .ok i m' =>
    let action : M Inst := do
      if i.lock && !lockOk i then ud
      let c ← cpu
      let next := c.eip + i.len
      setEip (if c.cs.big then next else next &&& 0xFFFF)
      exec i
      return i
    match action m' with
    | .ok i m'' => .ok i { m'' with keepCpu := false }
    | .error f m'' =>
      -- after a committed task switch the fault belongs to the new task: keep its state
      if m''.keepCpu then .error f { m'' with keepCpu := false }
      else .error f { m'' with cpu := faultCpu saved m''.cpu i }

/-- Instructions after which no single-step trap is taken: software interrupts (their handler
is entered with TF clear) and MOV/POP SS (the trap is deferred past the next instruction). -/
def noStepTrap (i : Inst) : Bool :=
  i.op == 0xCC || i.op == 0xCD || i.op == 0xCE || i.op == 0xF1 ||
  i.op == 0x17 || (i.op == 0x8E && i.reg == SegN.SS)

/-- Debug trap: #DB with the given DR6 status bits (B0..B3 replace the previous breakpoint bits). -/
def dbTrap (m : Machine) (bits : UInt32) : Machine :=
  let c := m.cpu
  let dr6 := if bits &&& 0xF != 0 then (c.dr6 &&& ~~~0xF) ||| bits else c.dr6 ||| bits
  let m := raiseExc { m with dbPend := 0, cpu := { c with dr6 } } Vec.DB none false
  { m with dbHit := 0 }

/-- Breakpoints hit while delivering an event become pending: their #DB is taken at the first
instruction of the handler. -/
@[inline] def pendHits (m : Machine) : Machine :=
  if m.dbHit == 0 then m else { m with dbPend := m.dbPend ||| m.dbHit, dbHit := 0 }

/-! ## INIT, STARTUP and NMI messages (SMP workstream)

What the local APIC passes to the core (`Apic.init`, `sipi`, `nmi`; cached in `Machine.xev`) is
taken at an instruction boundary by `smpEvent?`, before everything else in `step`:
* INIT (held pending in SMM): the INIT state of AMD APM vol. 2, table 14-1 (`Cpu.afterInit`) and the
  APIC's reset values except base, mode and ID (`Apic.reset`); an application processor then waits for
  a STARTUP IPI, the boot processor (BSC) starts at the reset vector FFFF:FFF0 as after RESET (there is
  no firmware in the model: open bus);
* in the INIT state the CPU executes nothing and holds every other event pending (APM 16.5: "the
  target APIC is responsive only to the STARTUP IPI. All other interrupts (including SMI and NMI) are
  held pending until the STARTUP IPI has been accepted"); a STARTUP IPI with vector VV starts it in real
  mode at VV00:0000 (CS base VV000h);
* a STARTUP IPI outside the INIT state is ignored;
* NMI: PLACEHOLDER until system B's NMI architecture is merged (RECONCILE AT MERGE): vector 2 through
  the IDT at the first boundary without a pending SMI or debug trap, outside SMM and the interrupt
  shadow, waking HLT; NMI blocking until IRET is not modelled here. -/

/-- The CPU state after INIT (AMD APM vol. 2, table 14-1 "Value after INIT", table 14-2 attributes):
real mode at F000:FFF0 with CS base FFFF_0000h, CR0 = 10h with CD and NW kept, CR2–CR4, EFER, the
general registers (EDX = processor signature `sig`), DR0–DR3, DR6, DR7 at their reset values; x87,
MMX and SSE state, MSRs, TSC, SMBASE and XCR0 are not modified. -/
def Cpu.afterInit (c : Cpu) (sig : UInt32) (bsp : Bool) : Cpu :=
  let seg : SegReg := { sel := 0, base := 0, limit := 0xFFFF, attr := 0x92 }
  { c with
    eax := 0, ebx := 0, ecx := 0, edx := sig, esp := 0, ebp := 0, esi := 0, edi := 0,
    eip := 0xFFF0, eflags := 2,
    cs := { sel := 0xF000, base := 0xFFFF0000, limit := 0xFFFF, attr := 0x9A },
    ds := seg, es := seg, fs := seg, gs := seg, ss := seg,
    ldtr := { attr := 0x82 }, tr := { attr := 0x83 },
    gdtBase := 0, gdtLimit := 0xFFFF, idtBase := 0, idtLimit := 0xFFFF,
    cr0 := 0x10 ||| (c.cr0 &&& (CR0.CD ||| CR0.NW)), cr2 := 0, cr3 := 0, cr4 := 0,
    dr0 := 0, dr1 := 0, dr2 := 0, dr3 := 0, dr6 := 0xFFFF0FF0, dr7 := 0x400, bpOn := false,
    efer := 0, halted := !bsp, shadow := false,
    -- long mode: EFER = 0 (LME, LMA); RIP/RSP bits 63:32 = 0, FS/GS base 0 (the segment loads clear
    -- the 64-bit bases); R11 and KernelGSbase (an MSR) are not modified
    lmx := { c.lmx with ripHi := 0, rspHi := 0, fsBase := none, gsBase := none, entry := "" },
    smpx := { c.smpx with waitSipi := !bsp, mwait := none } }

/-- INIT of the running CPU. -/
def Machine.initCpu (m : Machine) : Machine :=
  let sig := (cpuid m.cpu 1 0).1
  { m with cpu := m.cpu.afterInit sig m.apic.bsp, apic := { m.apic with init := false }.reset,
           dbPend := 0 }.syncTimer.syncApic

/-- A STARTUP IPI with vector `v` ends the INIT state: real mode at `v`00:0000. -/
def Machine.startCpu (m : Machine) (v : UInt32) : Machine :=
  { m with cpu := { m.cpu with cs := { sel := (v <<< 8).toUInt16, base := v <<< 12, limit := 0xFFFF, attr := 0x9A },
                               eip := 0, halted := false, smpx := { m.cpu.smpx with waitSipi := false } },
           apic := { m.apic with sipi := none } }.syncXev

/-- Deliver a latched NMI (placeholder, see above). -/
def Machine.deliverNmi (m : Machine) : Machine :=
  let m := { m with apic := { m.apic with nmi := false }, cpu := { m.cpu with halted := false } }.syncXev
  pendHits (raiseExc m 2 none true)

/-- The slow path of `smpEvent?`. -/
def smpEventSlow (m : Machine) : Option Machine :=
  let a := m.apic
  if a.init && !m.cpu.smm then some m.initCpu
  else if m.cpu.smpx.waitSipi then
    match a.sipi with
    | some v => some (m.startCpu v)
    | none => some m
  else if a.sipi.isSome then some { m with apic := { a with sipi := none } }.syncXev
  else if a.nmi && !m.smiPending && m.dbPend == 0 && !m.cpu.shadow && !m.cpu.smm then some m.deliverNmi
  else none

/-- INIT, STARTUP, the INIT state and NMI at an instruction boundary; `none`: nothing to do here. -/
@[inline] def smpEvent? (m : Machine) : Option Machine := if m.xev then smpEventSlow m else none

/-- One step at an instruction boundary, in priority order: INIT/STARTUP (and the INIT state) and
NMI (`smpEvent?`, NMI after SMI and debug traps), SMI, debug traps held from the previous
boundary, external interrupts, HLT, instruction-breakpoint faults, then the instruction itself
followed by its debug traps (data/I/O breakpoints, single-step). Traps raised by MOV SS / POP SS are
held past the next instruction (it executes in the interrupt shadow). -/
def step (m : Machine) : Machine :=
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  match smpEvent? m with
  | some m => m
  | none =>
  if m.smiPending && !m.cpu.smm && !m.cpu.shadow then
    -- SMI: above debug traps and interrupts; another SMI stays latched until RSM
    match smmEnter { m with smiPending := false } with
    | .ok _ m => m
    | .error f m => { m with fatal := some f }
  else if m.dbPend != 0 && !m.cpu.shadow then
    dbTrap { m with cpu := { m.cpu with halted := false } } m.dbPend
  else if m.intr && m.cpu.eflags &&& Flag.IF != 0 && !m.cpu.shadow then
    let m := { m with cpu := { m.cpu with halted := false } }
    let (vec, m) := m.intAck
    pendHits (raiseExc m vec none true)
  else if m.cpu.halted then
    { m with icount := if m.timerAt == maxU64 then m.icount else max (m.icount + 1) m.timerAt }
  else
    let c := m.cpu
    let ibp := if c.bpOn && c.eflags &&& Flag.RF == 0 then
      bpHits c (c.cs.base + c.eip) 1 (· == 0) else 0
    if ibp != 0 then
      dbTrap { m with icount := m.icount + 1, cpu := { c with shadow := false } } ibp
    else
    let tf := c.eflags &&& Flag.TF != 0
    let m := { m with cpu := { c with shadow := false }, dbHit := 0 }
    match execInstr m with
    | .ok i m =>
      let m := { m with icount := m.icount + 1 }
      let bits := m.dbHit ||| (if tf && !noStepTrap i then DR6.BS else 0)
      if bits == 0 && m.dbPend == 0 then m
      else if m.cpu.shadow && i.op != 0xFB then { m with dbPend := m.dbPend ||| bits, dbHit := 0 }
      else dbTrap m (bits ||| m.dbPend)
    | .error f m => pendHits (handleFault { m with icount := m.icount + 1, dbHit := 0 } f)

/-- `true` if the machine can make no progress without external input. -/
def Machine.idle (m : Machine) : Bool :=
  m.cpu.halted && m.dbPend == 0 && !m.smiPending && m.timerAt == maxU64 && !(m.intr && m.cpu.eflags &&& Flag.IF != 0)

/-- Run until the instruction count reaches `limit`, the machine is idle, or a fatal stop. -/
partial def Machine.runUntil (m : Machine) (limit : UInt64) : Machine :=
  if m.icount ≥ limit || m.fatal.isSome || m.idle then m
  else (step m).runUntil limit

end X86
