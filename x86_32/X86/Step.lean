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

/-- Deliver event `vec` from a consistent state: an exception (`intr = false`; its class for
double faults is `SysB.excClass vec`) or an external interrupt or NMI (`intr = true`, benign). `ext`
sets the EXT bit of the error codes of faults raised while delivering it: every event other than a
software interrupt (whose delivery is part of the INT n/INT3/INTO instruction, `Exec`) is external
to the program (SDM vol. 3, 6.13; AMD APM vol. 2, 8.4.1). A fault during the delivery is handled by
the double-fault table `SysB.onSecond` (AMD APM vol. 2, 8.2.9): serially (the second exception is
delivered instead, from the state before the delivery), as #DF (error code 0), or by shutting down
(triple fault). A fault after a task switch through a task gate has committed is an exception in the
new task, classified the same way (`fuel` bounds such chains). -/
def raiseExcF : Nat → Machine → UInt8 → Option UInt32 → Bool → Bool → Machine
  | 0, m, vec, _, _, _ => { m with fatal := some (.shutdown s!"exception loop delivering vector {vec}") }
  | fuel + 1, m, vec, err, ext, intr =>
    -- entering the #DB handler clears DR7.GD, so the handler can access the debug registers
    let m := if vec == Vec.DB && !intr then { m with cpu := { m.cpu with dr7 := m.cpu.dr7 &&& ~~~0x2000 } } else m
    let saved := m.cpu
    match deliver vec err false ext { m with keepCpu := false } with
    | .ok _ m => { m with keepCpu := false }
    | .error f m =>
      let keep := m.keepCpu
      -- after a committed task switch the fault belongs to the new task: keep its state
      let m := if keep then { m with keepCpu := false } else { m with keepCpu := false, cpu := saved }
      match f with
      | .exc v e a =>
        match SysB.onSecond (if intr then .benign else SysB.excClass vec) v with
        | .serial => raiseExcF fuel (faultState m v a) v e true false
        | .doubleFault =>
          -- a page fault converted to #DF has still loaded CR2 (SDM vol. 3, 4.7)
          let m := if v == Vec.PF then { m with cpu := { m.cpu with cr2 := a } } else m
          raiseExcF fuel m Vec.DF (some 0) true false
        | .shutdown => { m with fatal := some (.shutdown s!"triple fault ({repr f})") }
      | f => { m with fatal := some f }

/-- Deliver an exception (`intr = false`) or an external interrupt or NMI (`intr = true`). -/
@[inline] def raiseExc (m : Machine) (vec : UInt8) (err : Option UInt32) (ext : Bool) (intr : Bool := false) : Machine :=
  raiseExcF 4 m vec err ext intr

/-- Deliver the fault of an instruction (see `faultState`); faults are external to the program for
the EXT bit of nested faults. -/
def handleFault (m : Machine) (f : Fault) : Machine :=
  match f with
  | .exc vec err addr => raiseExc (faultState m vec addr) vec err true
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

/-- IRET ends the blocking of NMIs when it completes, or, for a return to another task, once the
outgoing task's state is saved (the task switch has committed). A fault before that leaves NMIs
blocked: "the occurrence of an NMI masks further NMIs until an IRET instruction is executed to
completion or, in the event of a task switch, to the completion of the outgoing TSS update. An
exception raised during execution of the IRET prior to these points will result in NMI continuing to
be masked for the duration of the exception handler" (AMD APM vol. 2, 8.1.4). The Intel SDM differs
(vol. 3, 7.7.2: unblocked "even if the execution subsequently encounters a fault"); AMD is followed. -/
@[inline] def iretUnblock (i : Inst) (m : Machine) : Machine :=
  if i.op == 0xCF && !i.vex then { m with cpu := { m.cpu with sysbx := { m.cpu.sysbx with nmiBlocked := false } } }
  else m

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
    | .ok i m'' => .ok i (iretUnblock i { m'' with keepCpu := false })
    | .error f m'' =>
      -- after a committed task switch the fault belongs to the new task: keep its state
      if m''.keepCpu then .error f (iretUnblock i { m'' with keepCpu := false })
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
  let m := raiseExc { m with dbPend := 0, cpu := { c with dr6 } } Vec.DB none true
  { m with dbHit := 0 }

/-- Breakpoints hit while delivering an event become pending: their #DB is taken at the first
instruction of the handler. -/
@[inline] def pendHits (m : Machine) : Machine :=
  if m.dbHit == 0 then m else { m with dbPend := m.dbPend ||| m.dbHit, dbHit := 0 }

/-! ## INIT, STARTUP and NMI messages (SMP workstream; NMI: system workstream B)

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
* NMI: the APIC's `nmi` message (an NMI IPI, an LVT or I/O APIC entry in NMI mode: `Machine.latchNmi`)
  enters the CPU's NMI latch (`Cpu.latchNmi`, `SysBState.nmiPending`) at the CPU's next instruction
  boundary outside the INIT state (`takeNmi`), from where `nextEvent` delivers it with the NMI
  blocking rules of system B. A CPU in the INIT state holds it pending in the APIC. -/

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

/-- The APIC's NMI message enters the CPU's NMI latch (a second NMI while one is latched is lost). -/
@[inline] def Machine.takeNmi (m : Machine) : Machine :=
  if m.apic.nmi then { m with apic := { m.apic with nmi := false }, cpu := m.cpu.latchNmi }.syncXev else m

/-- The slow path of `smpEvent?`. -/
def smpEventSlow (m : Machine) : Option Machine :=
  let a := m.apic
  if a.init && !m.cpu.smm then some m.initCpu
  else if m.cpu.smpx.waitSipi then
    match a.sipi with
    | some v => some (m.startCpu v)
    | none => some m
  else if a.sipi.isSome then some { m with apic := { a with sipi := none } }.syncXev
  else none

/-- INIT, STARTUP and the INIT state at an instruction boundary; `none`: nothing to do here. -/
@[inline] def smpEvent? (m : Machine) : Option Machine := if m.xev then smpEventSlow m else none

/-- Add `n` instruction slots of `icount` in which no instruction retired (IRPerf, `SysB`). -/
@[inline] def addNotRetired (m : Machine) (n : UInt64) : Machine :=
  { m with cpu := { m.cpu with sysbx := { m.cpu.sysbx with notRetired := m.cpu.sysbx.notRetired + n } } }

/-- MOVS, CMPS, STOS, LODS, SCAS, INS, OUTS. -/
@[inline] def isStringOp (i : Inst) : Bool :=
  !i.vex && ((0xA4 ≤ i.op && i.op ≤ 0xA7) || (0xAA ≤ i.op && i.op ≤ 0xAF) || (0x6C ≤ i.op && i.op ≤ 0x6F))

/-- An instruction completed that advanced `icount` itself (from `ic`; REP iterations, MWAIT waits):
those slots retired nothing, and a REP string instruction that stopped with EIP still on it
(`eip0`: interrupted or restarted after a fault) has not retired either. -/
def retireLong (ic : UInt64) (eip0 : UInt32) (i : Inst) (m : Machine) : Machine :=
  let unfinished := i.rep != 0 && isStringOp i && m.cpu.eip == eip0
  addNotRetired { m with icount := m.icount + 1 } (m.icount - ic + (if unfinished then 1 else 0))

/-- Deliver a latched NMI through vector 2 (an external, benign event; AMD APM vol. 2, 8.2.3): it
wakes a halted processor and blocks further NMIs until the next IRET. -/
def deliverNmi (m : Machine) : Machine :=
  let c := m.cpu
  let m := { m with cpu := { c with halted := false,
                                    sysbx := { c.sysbx with nmiPending := false, nmiBlocked := true } } }
  pendHits (raiseExc m Vec.NMI none true true)

/-- The instruction part of a step: idle while halted, an instruction-breakpoint fault, or the
instruction followed by its debug traps (data/I/O breakpoints, single-step). Traps raised by MOV SS /
POP SS are held past the next instruction (it executes in the interrupt shadow). -/
@[inline] def stepInstr (m : Machine) : Machine :=
  if m.cpu.halted then
    let t := if m.timerAt == maxU64 then m.icount else max (m.icount + 1) m.timerAt
    addNotRetired { m with icount := t } (t - m.icount)
  else
    let c := m.cpu
    let ibp := if c.bpOn && c.eflags &&& Flag.RF == 0 then
      bpHits c (c.cs.base + c.eip) 1 (· == 0) else 0
    if ibp != 0 then
      dbTrap (addNotRetired { m with icount := m.icount + 1, cpu := { c with shadow := false } } 1) ibp
    else
    let tf := c.eflags &&& Flag.TF != 0
    let ic := m.icount
    let m := { m with cpu := { c with shadow := false }, dbHit := 0 }
    match execInstr m with
    | .ok i m =>
      let m := if m.icount == ic then { m with icount := m.icount + 1 } else retireLong ic c.eip i m
      let bits := m.dbHit ||| (if tf && !noStepTrap i then DR6.BS else 0)
      if bits == 0 && m.dbPend == 0 then m
      else if m.cpu.shadow && i.op != 0xFB then { m with dbPend := m.dbPend ||| bits, dbHit := 0 }
      else dbTrap m (bits ||| m.dbPend)
    | .error f m =>
      let m := addNotRetired { m with icount := m.icount + 1, dbHit := 0 } (m.icount + 1 - ic)
      pendHits (handleFault m f)

/-- The event a step takes at an instruction boundary (`nextEvent`). -/
inductive Event where
  | smi | dbTrap | nmi | intr | nmiDelay | instr
  deriving DecidableEq, Repr

/-- The event to take at this instruction boundary, in the priority order of AMD APM vol. 2, 8.5
(table 8-9, "Simultaneous Interrupt Priorities"), for the events the model has (no reset or machine
checks; the table's priority numbers in brackets). INIT and STARTUP [1] come first, in `smpEvent?`
(`step`); then:

1. [1] SMI (external processor-initiated, like INIT; held while in SMM, and not taken in an
   interrupt shadow);
2. [2] debug traps of the previous instruction (DR6 bits held in `dbPend`: single-step, data and
   I/O breakpoints, the TSS T flag, and those held across MOV SS/POP SS);
3. [3] NMI (`SysBState.nmiPending`, unless NMIs are blocked or in an interrupt shadow);
4. [4] INTR (maskable interrupts with EFLAGS.IF = 1, not in an interrupt shadow);
5. [5-7] the instruction (`stepInstr`): an instruction-breakpoint fault [5], or its fetch [5],
   decode [6] and execution [7] faults, or a halted processor's wait. `nmiDelay` is the same, while
   the model-only NMI test hook still delays a latched NMI.

The interrupt shadow (`Cpu.shadow`, after MOV SS/POP SS and after an STI that sets IF) holds NMIs
too: after MOV SS the processor "does not allow external interrupts" until the next instruction
completes (AMD APM vol. 2, 8.1.4; NMI is an external interrupt there); after STI, "NMI interrupts (and
SMIs) may be blocked for one instruction" (AMD 15.13.2; SDM vol. 3, 7.8.1 likewise), and the model
blocks them. A halted processor is woken by any of 1-4 (INTR only with IF = 1). -/
@[inline] def nextEvent (m : Machine) : Event :=
  let c := m.cpu
  if m.smiPending && !c.smm && !c.shadow then .smi
  else if m.dbPend != 0 && !c.shadow then .dbTrap
  else
  let s := c.sysbx
  if !s.nmiPending then
    if m.intr && c.eflags &&& Flag.IF != 0 && !c.shadow then .intr else .instr
  else if s.nmiDelay == 0 && !s.nmiBlocked && !c.shadow then .nmi
  else if m.intr && c.eflags &&& Flag.IF != 0 && !c.shadow then .intr
  else if s.nmiDelay != 0 then .nmiDelay
  else .instr

/-- One step at an instruction boundary after the timers have been updated: the event `nextEvent`
selects. -/
def stepAt (m : Machine) : Machine :=
  match nextEvent m with
  | .smi =>
    -- another SMI stays latched until RSM
    match smmEnter { m with smiPending := false } with
    | .ok _ m => m
    | .error f m => { m with fatal := some f }
  | .dbTrap => dbTrap { m with cpu := { m.cpu with halted := false } } m.dbPend
  | .nmi => deliverNmi m
  | .intr =>
    let m := { m with cpu := { m.cpu with halted := false } }
    let (vec, m) := m.intAck
    pendHits (raiseExc m vec none true true)
  | .nmiDelay =>
    let c := m.cpu
    stepInstr { m with cpu := { c with sysbx := { c.sysbx with nmiDelay := c.sysbx.nmiDelay - 1 } } }
  | .instr => stepInstr m

/-- One architectural step: timer events due; INIT, STARTUP and the INIT state (`smpEvent?`: INIT is
above SMI in AMD's table 8-9, and a CPU waiting for STARTUP holds every other event pending); then the
APIC's NMI message enters the NMI latch (`Machine.takeNmi`) and `stepAt` takes the event `nextEvent`
selects. -/
def step (m : Machine) : Machine :=
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  match smpEvent? m with
  | some m => m
  | none => stepAt (if m.xev then m.takeNmi else m)

/-- `true` if the machine can make no progress without external input. -/
def Machine.idle (m : Machine) : Bool :=
  m.cpu.halted && m.dbPend == 0 && !m.smiPending && m.timerAt == maxU64 &&
    !(m.intr && m.cpu.eflags &&& Flag.IF != 0) &&
    !((m.cpu.sysbx.nmiPending || m.apic.nmi) && (!m.cpu.sysbx.nmiBlocked || m.cpu.sysbx.nmiDelay != 0))

/-- Run until the instruction count reaches `limit`, the machine is idle, or a fatal stop. -/
partial def Machine.runUntil (m : Machine) (limit : UInt64) : Machine :=
  if m.icount ≥ limit || m.fatal.isSome || m.idle then m
  else (step m).runUntil limit

end X86
