import X86.Step
/-!
# Several CPUs in the sequential model

`MpMachine` runs N logical CPUs, each with its full `Cpu` state, its own local APIC and TLB, on
shared physical memory and devices (PIC, PIT, UART, CMOS, I/O APIC). The running CPU is held in the
same `Machine` fields as on a single-CPU machine (`cpu`, `apic`, the TLB arrays, `dbPend`,
`smiPending`), so `X86.step` executes it unchanged; the other CPUs' local APICs are in
`Machine.peers` (interrupt messages reach them from inside an instruction), the rest of their state is
here in `cores`, and CPUs are swapped in and out at quantum boundaries (`switchTo`). With one CPU
(`cores = #[]`) `step` is exactly `X86.step` (theorems `MpMachine.step_single`,
`MpMachine.steps_single` in `Proofs/ExtSmp.lean`) and `runUntil` is `Machine.runUntil`.

## Determinism contract

The machine is a function of its state; nothing depends on the host:
* **Schedule**: round robin with a fixed quantum (`quantum` steps, default 1000). The running CPU
  takes steps while it is *runnable* (`runnableState`: not halted, or an event `X86.step` would take:
  INIT, STARTUP, an NMI that is not blocked (system B's latch, or the APIC's NMI message), SMI, a
  pending debug trap, or INTR with IF = 1; a CPU in the INIT state only for
  INIT or STARTUP) and its quantum lasts. Then (`resched`) due timers are fired, MWAIT waits whose
  monitored line another CPU changed end, and the next runnable CPU in the order cur+1, cur+2, …, cur
  (cyclically) runs a new quantum. Halted and waiting CPUs are skipped; a CPU woken by an IPI or an
  interrupt runs at the next quantum boundary.
* **Time**: one global virtual clock, `Machine.icount`: every instruction of any CPU advances it by
  one, so with k CPUs busy each runs at 1/k of the nominal 100M instructions per virtual second.
  Only when no CPU is runnable does time skip to the next timer event (the PIT, or any CPU's APIC
  timer); a halted CPU never skips time while another runs. The PIT and the running CPU's APIC timer
  fire at the instruction where they are due, the other CPUs' APIC timers at the next quantum
  boundary (at most a quantum late, as their CPU would not run before it anyway).
* **TSC**: every CPU's TSC is `icount` plus its own offset (`SysState.tscOff`, WRMSR 10h): the TSCs
  are synchronized and invariant, as on the 7742. `retired` counts each CPU's executed instructions
  (statistics only).
* **Atomicity**: an instruction (including its memory accesses, page walks and A/D updates, and an
  interrupt or exception delivery) executes entirely within one step of one CPU, and memory is a
  single array without store buffers. Every instruction is therefore atomic with respect to the
  other CPUs and the memory order is sequentially consistent; LOCK adds nothing (its #UD rules
  still apply). This is stronger than the hardware (x86-TSO lets loads pass buffered stores), which
  is what the separate store-buffer model `X86/Tso.lean` (`TMachine`, nondeterministic, single-CPU
  steps with logged stores) describes; the two models are kept apart: `MpMachine` gives one
  deterministic, sequentially consistent execution of a whole platform (devices, paging, APICs),
  `TMachine` all TSO executions of programs within its supported subset.
* **What the quantum may change.** A CPU that does not run is, architecturally, a CPU stalled in its
  current instruction, which hardware permits for any length of time. Every message to it is accepted
  by its local APIC at once and in arrival order (fixed and lowest-priority vectors enter IRR with
  their TMR bit; STARTUP is accepted in, or while entering, the INIT state; `Machine.recv`); its APIC
  timer fires at its due instruction as far as other CPUs can observe it (before arbitration and remote
  reads, `Machine.peersTimers`); I/O APIC remote IRR and EOIs are immediate; a store to a line it
  monitors is recorded when it happens (`Machine.watch`). Its core takes the resulting events at its
  next instruction boundary in the priority order of APM table 8-9, as a core receiving them during one
  long instruction would: INIT before SMI before NMI before INTR, a STARTUP accepted after the INIT is
  taken after it, NMI and SMI wait until STARTUP, and events of one kind coalesce as hardware coalesces
  them (one IRR bit per vector, one NMI and one SMI latch, the PIC acknowledged when the core takes the
  ExtINT). So the quantum changes only (a) the interleaving of the CPUs' instructions, hence the
  outcome of racy programs, (b) how many of several identical events (same fixed vector, NMIs, SMIs,
  ExtINTs, timer expiries) that reach a CPU while it does not run are taken, as for events arriving
  during one instruction, and (c) the instruction counts and TSC values at which things happen.
  Quantum-independent: which CPUs an INIT/STARTUP sequence starts and at which vector, the state INIT
  leaves, the APIC state other CPUs observe, lowest-priority arbitration, remote IRR, and every
  MWAIT wake-up; the transcripts of `t_smp.c` (quanta 1 to 10^6) and of the SMP Linux boot and
  workload (quanta 100 to 10^6, `guest/smp-check.sh` with `QUANTA`) are identical.
* **MONITOR/MWAIT**: an MWAIT in progress (`SmpState.mwait`, set by `Gpr.mwait`) ends when a store
  writes its monitored 64-byte line (any store, also one that writes the same value or is undone
  later: `physWr` records it in `Machine.watchHit` while the waiting CPU does not run) or the line
  holds other contents than at MONITOR; the waiting CPU resumes at the next quantum boundary. Not
  counted: A/D-bit updates of the page walker. (Between MONITOR and MWAIT the single-CPU rule of
  `Gpr.mwait` applies: the line's contents are compared.)
-/
namespace X86

/-- The part of a non-running CPU's state the scheduler keeps (its APIC is `Machine.peers`). -/
structure MpCore where
  cpu : Cpu := {}
  tlbTag : Array UInt32 := #[]
  tlbVal : Array UInt64 := #[]
  tlbLarge : Bool := false
  tlbLargeRegions : Array UInt32 := #[]
  tlbGlobal : Bool := false
  dbPend : UInt32 := 0
  deriving Inhabited

/-- N CPUs: the running one in `m` (`m.cur`), the others in `cores` (empty for one CPU). -/
structure MpMachine where
  m : Machine
  cores : Array MpCore := #[]
  quantum : Nat := 1000
  /-- Steps left in the running CPU's quantum. -/
  qleft : Nat := 0
  /-- Instructions executed per CPU (N ≥ 2), up to the last switch, and `icount` at that switch. -/
  retired : Array UInt64 := #[]
  since : UInt64 := 0
  deriving Inhabited

namespace MpMachine

/-- Number of CPUs. -/
@[inline] def ncpu (s : MpMachine) : Nat := max 1 s.cores.size

/-- Whether a CPU in this state does something in its next `X86.step` (rather than idling): see the
module documentation. `intr`: the CPU's INTR line. -/
def runnableState (c : Cpu) (a : Apic) (smi : Bool) (dbPend : UInt32) (intr : Bool) : Bool :=
  if c.smpx.waitSipi then a.init || a.sipi.isSome
  -- SVM guest mode or GIF = 0 (`Step.stepAtSvm`, `Machine.svmIdle`)
  else if c.svmx.guest || !c.svmx.gif then
    let s := c.svmx
    !c.halted || s.inject &&& 0x80000000 != 0 || (s.gif && a.init && !c.smm) || a.sipi.isSome ||
    (s.gif && (a.nmi || c.sysbx.nmiPending) && (!c.sysbx.nmiBlocked || c.sysbx.nmiDelay != 0)) ||
    (s.gif && smi && !c.smiHeld) || (if s.gif then dbPend else dbPend &&& ~~~0xF) != 0 ||
    (s.gif && intr && c.physIntrOk) || c.vintrReady
  else !c.halted || (a.init && !c.smm) || a.sipi.isSome ||
    ((a.nmi || c.sysbx.nmiPending) && (!c.sysbx.nmiBlocked || c.sysbx.nmiDelay != 0)) || (smi && !c.smiHeld) ||
    dbPend != 0 || (intr && c.eflags &&& Flag.IF != 0)

/-- CPU `k` is runnable. -/
def runnableAt (s : MpMachine) (k : Nat) : Bool :=
  let m := s.m
  if k == m.cur then runnableState m.cpu m.apic (m.smiPending || m.apic.smi) m.dbPend m.intr
  else
    let c := s.cores[k]!
    let a := m.peers[k]!.apic
    runnableState c.cpu a a.smi c.dbPend ((a.picPasses && m.masterHighest.isSome) || a.extInt || a.pending.isSome)

/-- The 16 dwords of the 64-byte line at `p` (as `Gpr.lineData`). -/
def lineData (mem : ByteArray) (p : UInt64) : Array UInt32 :=
  (List.range 16).toArray.map fun k =>
    if p >>> 32 != 0 then 0xFFFFFFFF else rdBytes mem (p.toUInt32 + 4 * k.toUInt32) 4

/-- An MWAIT ends when a store wrote its monitored line (`hits`: `Machine.watchHit`, recorded by
`physWr` while the CPU did not run) or the line's contents changed (APM MWAIT: a store to the
monitored range is a wake-up event; the instruction after MWAIT runs next). A monitor armed by
MONITOR whose line was written is triggered: the next MWAIT does not wait (`Gpr.mwait` finds no armed
line), as when the store comes between MONITOR and MWAIT on hardware. -/
def mwaitWake (mem : ByteArray) (hits : Array UInt64) (c : Cpu) : Cpu :=
  let c := match c.gprx.monLine with
    | some l => if hits.contains l then { c with gprx := { c.gprx with monLine := none, monData := #[] } } else c
    | none => c
  match c.smpx.mwait with
  | some (line, d) =>
    if c.halted && (hits.contains line || lineData mem line != d) then
      { c with halted := false, smpx := { c.smpx with mwait := none } }
    else c
  | none => c

/-- The lines that stores must be watched for (`Machine.watch`): the monitored lines of the CPUs other
than `cur`, of an MWAIT in progress or armed by MONITOR. -/
def watchLines (cores : Array MpCore) (cur : Nat) : Array UInt64 :=
  cores.zipIdx.foldl (fun acc (c, k) =>
    if k == cur then acc else
    let acc := match c.cpu.smpx.mwait with
      | some (l, _) => if c.cpu.halted then acc.push l else acc
      | none => acc
    match c.cpu.gprx.monLine with
    | some l => acc.push l
    | none => acc) #[]

/-- Make CPU `k` the running one (no-op if it is). -/
def switchTo (s : MpMachine) (k : Nat) : MpMachine :=
  let m := s.m
  let j := m.cur
  if k == j || k ≥ s.cores.size then s else
  let c := s.cores[k]!
  let p := m.peers[k]!
  let out : MpCore := { cpu := m.cpu, tlbTag := m.tlbTag, tlbVal := m.tlbVal, tlbLarge := m.tlbLarge,
                        tlbLargeRegions := m.tlbLargeRegions, tlbGlobal := m.tlbGlobal, dbPend := m.dbPend }
  let outPeer : Peer := { apic := { m.apic with smi := m.apic.smi || m.smiPending }, waitSipi := m.cpu.smpx.waitSipi }
  let cores := (s.cores.set! k {}).set! j out
  let peers := (m.peers.set! k {}).set! j outPeer
  let m := { m with peers, cur := k, cpu := c.cpu, apic := { p.apic with smi := false }, watch := watchLines cores k,
                    smiPending := p.apic.smi, tlbTag := c.tlbTag, tlbVal := c.tlbVal, tlbLarge := c.tlbLarge,
                    tlbLargeRegions := c.tlbLargeRegions, tlbGlobal := c.tlbGlobal, dbPend := c.dbPend,
                    dbHit := 0, keepCpu := false }
  let m := m.syncTimer.syncXev.syncIntr
  { s with m, cores, retired := s.retired.modify j (· + (m.icount - s.since)), since := m.icount }

/-- The next runnable CPU in round-robin order after the running one (which comes last). -/
def nextRunnable (s : MpMachine) : Option Nat :=
  let n := s.ncpu
  ((List.range n).map fun j => (s.m.cur + 1 + j) % n).find? s.runnableAt

/-- Earliest timer event of any CPU (the PIT, the running CPU's and the other CPUs' APIC timers). -/
def nextTimer (s : MpMachine) : UInt64 :=
  s.m.peers.foldl (fun t p => min t p.apic.timerNext) s.m.timerAt

/-- Quantum boundary or idle running CPU: fire due timers, end MWAITs on changed lines, and switch
to the next runnable CPU; if there is none, skip time to the next timer event. -/
def resched (s : MpMachine) : MpMachine :=
  let m := s.m
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  let now := m.icount
  let peers := m.peers.mapIdx fun k p =>
    if k != m.cur && p.apic.timerNext ≤ now then { p with apic := p.apic.timerDue now } else p
  let m := { m with peers, cpu := mwaitWake m.mem m.watchHit m.cpu }
  let cores := s.cores.mapIdx fun k c => if k == m.cur then c else { c with cpu := mwaitWake m.mem m.watchHit c.cpu }
  let m := { m with watch := watchLines cores m.cur, watchHit := #[] }
  let s := { s with m, cores }
  match s.nextRunnable with
  | some k => { s.switchTo k with qleft := s.quantum }
  | none =>
    let t := s.nextTimer
    if t == maxU64 then s else
    let t := max (s.m.icount + 1) t
    { s with m := { s.m with icount := t }, since := s.since + (t - s.m.icount) }

/-- The running CPU is runnable. -/
@[inline] def runnableCur (m : Machine) : Bool :=
  runnableState m.cpu m.apic (m.smiPending || m.apic.smi) m.dbPend m.intr

/-- One step of the multiprocessor. (The state is taken apart first so that the machine is not
shared while `X86.step` writes its memory.) -/
def step (s : MpMachine) : MpMachine :=
  let ⟨m, cores, quantum, qleft, retired, since⟩ := s
  if cores.isEmpty then ⟨X86.step m, cores, quantum, qleft, retired, since⟩
  else if qleft != 0 && runnableCur m then
    let m := X86.step m
    let m := if !m.cpu.halted && m.cpu.smpx.mwait.isSome then
      { m with cpu := { m.cpu with smpx := { m.cpu.smpx with mwait := none } } } else m
    ⟨m, cores, quantum, qleft - 1, retired, since⟩
  else resched ⟨m, cores, quantum, qleft, retired, since⟩

/-- `step` when the running CPU is runnable with quantum left (`step`'s second case, without its tests). -/
@[inline] def stepRunning (s : MpMachine) : MpMachine :=
  let ⟨m, cores, quantum, qleft, retired, since⟩ := s
  let m := X86.step m
  let m := if !m.cpu.halted && m.cpu.smpx.mwait.isSome then
    { m with cpu := { m.cpu with smpx := { m.cpu.smpx with mwait := none } } } else m
  ⟨m, cores, quantum, qleft - 1, retired, since⟩

/-- `true` if no CPU can make progress without external input. The running CPU is tested first: while
it is runnable (nearly every step) the cost does not depend on the number of CPUs. -/
def idle (s : MpMachine) : Bool :=
  if s.cores.isEmpty then s.m.idle else
  !runnableCur s.m && s.nextTimer == maxU64 && !(List.range s.ncpu).any s.runnableAt &&
  (s.m.cpu.smpx.mwait.isNone || (mwaitWake s.m.mem s.m.watchHit s.m.cpu).halted) &&
  s.cores.all fun c => c.cpu.smpx.mwait.isNone || (mwaitWake s.m.mem s.m.watchHit c.cpu).halted

/-- Run until the instruction count reaches `limit`, the machine is idle, or a fatal stop. -/
partial def runUntil (s : MpMachine) (limit : UInt64) : MpMachine :=
  if s.cores.isEmpty then
    let ⟨m, cores, quantum, qleft, retired, since⟩ := s
    ⟨m.runUntil limit, cores, quantum, qleft, retired, since⟩
  else if s.m.icount ≥ limit || s.m.fatal.isSome then s
  -- the common case: the running CPU is runnable (then the machine is not idle, and `step` is
  -- `stepRunning`); its cost does not depend on the number of CPUs
  else if s.qleft != 0 && runnableCur s.m then (stepRunning s).runUntil limit
  else if s.idle then s
  else s.step.runUntil limit

/-- Instructions executed by each CPU so far. -/
def retiredNow (s : MpMachine) : Array UInt64 :=
  if s.cores.isEmpty then #[s.m.icount] else s.retired.modify s.m.cur (· + (s.m.icount - s.since))

/-- The machine `m` (its CPU is CPU 0, the boot processor) with `n` logical CPUs: CPUs 1..n−1 are
application processors in the state RESET leaves them in (`Cpu.atReset`: CR0 = 6000_0010h, x87 control
word 0040h and tag word 5555h, AMD APM vol. 2, table 14-1), waiting for a STARTUP IPI, with their
local APIC at its power-up values (AE = 1, software-disabled, LVT masked) and initial APIC ID = CPU
number; their SMBASE is the boot processor's (as firmware relocates it). The boot processor is in the
state the loader gives it (`x86run`: the Linux 32-bit boot protocol; `x86sys`: the multiboot handoff,
CR0 = PE|ET = 11h as QEMU's multiboot option ROM leaves it; the x87 state of FNINIT, 037Fh, as QEMU's
reset), not RESET: the firmware has run. CPUID reports the topology of `n` CPUs (`Cpuid.topo`). -/
def ofMachine (m : Machine) (n : Nat) (quantum : Nat := 1000) : MpMachine :=
  let m := { m with cpu := { m.cpu with smpx := { m.cpu.smpx with ncpu := n.toUInt32, apicId := 0 } } }
  if n ≤ 1 then { m, quantum } else
  let sig := (cpuid m.cpu 1 0).1
  let ap := fun (k : Nat) =>
    -- power-up: RESET (CR0 = 6000_0010h, the RESET x87 state), then the INIT state of an AP waiting
    -- for STARTUP, which keeps CR0.CD/NW and the x87 state (APM vol. 2, table 14-1)
    let c : Cpu := Cpu.atReset.afterInit sig false
    ({ cpu := { c with smbase := m.cpu.smbase, smpx := { c.smpx with apicId := k.toUInt32, ncpu := n.toUInt32 } },
       tlbTag := Array.replicate tlbSize 0, tlbVal := Array.replicate tlbSize 0 } : MpCore)
  let cores := (Array.range n).map fun k => if k == 0 then {} else ap k
  let peers := (Array.range n).map fun k =>
    if k == 0 then {} else ({ apic := Apic.powerUp k, waitSipi := true } : Peer)
  { m := { m with peers, cur := 0 }.syncXev, cores, quantum, qleft := quantum,
    retired := Array.replicate n 0, since := m.icount }

end MpMachine
end X86
