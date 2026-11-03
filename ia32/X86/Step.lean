import X86.Exec
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

/-- Deliver an exception from a consistent state; a fault during delivery escalates to
#DF, and a fault while delivering #DF shuts the machine down. -/
def raiseExc (m : Machine) (vec : UInt8) (err : Option UInt32) (ext : Bool) : Machine :=
  let saved := m.cpu
  match deliver vec err false ext m with
  | .ok _ m => m
  | .error f m =>
    let m := { m with cpu := saved }
    if vec == Vec.DF then { m with fatal := some (.shutdown s!"triple fault ({repr f})") }
    else match f with
      | .exc _ _ _ =>
        match deliver Vec.DF (some 0) false false m with
        | .ok _ m => m
        | .error f2 m => { m with cpu := saved, fatal := some (.shutdown
            s!"triple fault: vector {vec} (error {repr err}) raised {repr f}, then #DF raised {repr f2}") }
      | f => { m with fatal := some f }

def handleFault (m : Machine) (f : Fault) : Machine :=
  match f with
  | .exc vec err addr =>
    let m := if vec == Vec.PF then { m with cpu := { m.cpu with cr2 := addr } } else m
    raiseExc m vec err false
  | f => { m with fatal := some f }

/-- LOCK is only permitted on read-modify-write instructions with a memory destination. -/
def lockOk (i : Inst) : Bool :=
  i.isMem &&
  (let op := i.op
   (op < 0x40 && op &&& 7 < 2 && op &&& 0x38 != 0x38) ||
   ((op == 0x80 || op == 0x81 || op == 0x82 || op == 0x83) && i.reg != 7) ||
   op == 0x86 || op == 0x87 ||
   ((op == 0xF6 || op == 0xF7) && (i.reg == 2 || i.reg == 3)) ||
   ((op == 0xFE || op == 0xFF) && i.reg < 2) ||
   op == 0x1AB || op == 0x1B3 || op == 0x1BB || (op == 0x1BA && i.reg ≥ 5) ||
   op == 0x1B0 || op == 0x1B1 || op == 0x1C0 || op == 0x1C1 || (op == 0x1C7 && i.reg == 1))

/-- Restore instruction-start state on a fault, except for POPA's completed
register loads. ESP and EIP always retain their restart values. -/
def faultCpu (saved current : Cpu) (i : Inst) : Cpu :=
  if i.op == 0x61 then
    { saved with
      eax := current.eax
      ecx := current.ecx
      edx := current.edx
      ebx := current.ebx
      ebp := current.ebp
      esi := current.esi
      edi := current.edi }
  else saved

/-- Fetch/decode/execute one instruction, including fault-state restoration.
Callers must retain the returned fault state: POPA can commit register loads,
and multi-store instructions can commit memory before a later page fault.
Only the CPU snapshot is kept, never `m` itself: a live reference to `m` would share its memory with
the running instruction and turn every store into a copy of the whole memory. -/
def execInstr : M Inst := fun m =>
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
    | .ok i m'' => .ok i m''
    | .error f m'' => .error f { m'' with cpu := faultCpu saved m''.cpu i }

/-- Instructions after which no single-step trap is taken: software interrupts (their handler
is entered with TF clear) and MOV/POP SS (the trap is deferred past the next instruction). -/
def noStepTrap (i : Inst) : Bool :=
  i.op == 0xCC || i.op == 0xCD || i.op == 0xCE || i.op == 0xF1 ||
  i.op == 0x17 || (i.op == 0x8E && i.reg == SegN.SS)

/-- Single-step trap (#DB with DR6.BS) after an instruction that began with EFLAGS.TF set. -/
def stepTrap (m : Machine) : Machine :=
  raiseExc { m with cpu := { m.cpu with dr6 := m.cpu.dr6 ||| 0x4000 } } Vec.DB none false

def step (m : Machine) : Machine :=
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  if m.intr && m.cpu.eflags &&& Flag.IF != 0 && !m.cpu.shadow then
    let m := { m with cpu := { m.cpu with halted := false } }
    let (vec, m) := m.intAck
    raiseExc m vec none true
  else if m.cpu.halted then
    { m with icount := if m.timerAt == maxU64 then m.icount else max (m.icount + 1) m.timerAt }
  else
    let tf := m.cpu.eflags &&& Flag.TF != 0
    let m := { m with cpu := { m.cpu with shadow := false } }
    match execInstr m with
    | .ok i m =>
      let m := { m with icount := m.icount + 1 }
      if tf && !noStepTrap i then stepTrap m else m
    | .error f m => handleFault { m with icount := m.icount + 1 } f

/-- `true` if the machine can make no progress without external input. -/
def Machine.idle (m : Machine) : Bool :=
  m.cpu.halted && m.timerAt == maxU64 && !(m.intr && m.cpu.eflags &&& Flag.IF != 0)

/-- Run until the instruction count reaches `limit`, the machine is idle, or a fatal stop. -/
partial def Machine.runUntil (m : Machine) (limit : UInt64) : Machine :=
  if m.icount ≥ limit || m.fatal.isSome || m.idle then m
  else (step m).runUntil limit

end X86
