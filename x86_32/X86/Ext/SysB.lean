import X86.Exec
/-!
# System extensions B: NMI, exception classes, IRPerf

Owner: system workstream B. The instruction semantics of this workstream live where the core
implements the instructions (as `EXTENDING.md` assigns them): CR4.VME/PVI in `X86/Sys.lean`
(`vmeInt`, IRET) and `X86/Exec.lean` (PUSHF, POPF, CLI, STI, INT n), NMI delivery, NMI blocking and
the event priorities in `X86/Step.lean`. This module has what those use and the MSRs:

* the exception classes and the double-fault table (`excClass`, `onSecond`; AMD APM vol. 2, 8.2.9),
  used by `Step.raiseExcF`;
* IRPerf, the instructions-retired counter (MSR C000_00E9h, HWCR[IRPerfEn]; `retired`, `irPerf`);
* the HWCR (C001_0015h) bits of this workstream, McStatusWrEn (18) and IRPerfEn (30), which the Gpr
  module's HWCR implementation stores here (`hwcrBits`, `hwcrWrite`);
* `msr?` (reached through `Gpr.msr?`): IRPerfCount and the model-only NMI test hook.

State: `SysBState` (`Cpu.sysbx`) in `X86/State.lean`.

Machine checks: the model has no error sources, so #MC (vector 18) is never raised and needs no
delivery path. CR4.MCE is stored only; with CR4.MCE = 0 a machine check would put the processor in
the shutdown state ("A machine-check condition that occurs while CR4[MCE] is cleared will result in
the processor core entering the shutdown state", AMD APM vol. 2, 9.4). Shutdown itself (after a
triple fault) stops the simulation (`Fault.shutdown`); AMD lets an NMI, INIT or RESET restart a
processor in shutdown (8.2.9), which the model does not do.

## IRPerf: what counts as retired

`IRPerfCount` counts the instructions that retire while HWCR.IRPerfEn = 1 (AMD APM vol. 2, 13.2.1,
"Instructions Retired Performance Counter"). The manuals do not define retirement for the corner
cases; the model counts an instruction when it completes, at the instruction boundary after it:

* every instruction that completes counts once, including INT n/INT3/INTO (their delivery is part of
  the instruction), HLT and MWAIT (once, not the time spent waiting), RSM and IRET;
* an instruction that faults does not count (its fault is delivered instead; also a fault after a
  committed task switch), nor one stopped by an instruction-breakpoint #DB;
* a REP string instruction counts once, when it completes; the iterations, and the partial runs
  after which it is interrupted or restarted (EIP still on the instruction), do not count;
* event deliveries (interrupts, NMI, SMI, debug traps) are not instructions and do not count;
* RDMSR of IRPerfCount reads the count before itself; WRMSR to it (or to HWCR) takes effect for the
  instructions after it, and the WRMSR itself counts if IRPerfEn = 1 after it (so the WRMSR that sets
  IRPerfEn counts and the one that clears it does not).

The count is derived without work on the instruction path: `Machine.icount` advances by one per step
that executes or faults an instruction, and by more for HLT/MWAIT waits and REP iterations; `step`
adds the slots in which nothing retired to `SysBState.notRetired` (only on those cold paths), so
`retired = icount - notRetired`. `irBase` and `irAt` latch the counter when it is enabled, disabled
or written.
-/
namespace X86
namespace SysB

/-! ## Exception classes and double faults (AMD APM vol. 2, 8.2.9) -/

/-- The class of an event being delivered, for double-fault generation (AMD APM vol. 2, table 8-2
and table 8-3, "Double-Fault Exception Conditions", first interrupting event). -/
inductive ExcClass where
  | benign | contributory | pageFault | doubleFault
  deriving DecidableEq, Repr

/-- The class of exception vector `v` as the first event: contributory #DE, #TS, #NP, #SS, #GP; #PF;
#DF; every other exception is benign (#DB, NMI, #BP, #OF, #BR, #UD, #NM, #MF, #AC, #MC, #XF; the
contributory #CP, #VC and #SX of AMD's table 8-2 do not exist on the model). External interrupts
and NMI are benign whatever their vector (`Step.raiseExcF`). -/
def excClass (v : UInt8) : ExcClass :=
  if v == 0 || v == 10 || v == 11 || v == 12 || v == 13 then .contributory
  else if v == 14 then .pageFault
  else if v == 8 then .doubleFault
  else .benign

/-- What happens when exception `second` is raised while the processor delivers `first`. -/
inductive DfAction where
  /-- the exceptions are handled serially: the second is delivered (the first is abandoned) -/
  | serial
  /-- a double-fault exception (#DF, error code 0) is delivered -/
  | doubleFault
  /-- triple fault: the processor shuts down -/
  | shutdown
  deriving DecidableEq, Repr

/-- The double-fault table (AMD APM vol. 2, table 8-3): while delivering a contributory exception,
a second #TS, #NP, #SS or #GP gives #DF; while delivering a page fault, a second #PF, #TS, #NP, #SS
or #GP gives #DF; any event while transferring control to the #DF handler shuts the processor down
("If a third interrupting event occurs while transferring control to the #DF handler, the processor
shuts down"); everything else is handled serially. #DE as the second event (which event delivery
cannot raise) is not in AMD's table; the Intel SDM's table 7-5, which counts it, differs only there
and in the benign event during #DF delivery (Intel: serially). -/
def onSecond (first : ExcClass) (second : UInt8) : DfAction :=
  let c := second == 10 || second == 11 || second == 12 || second == 13
  match first with
  | .benign => .serial
  | .contributory => if c then .doubleFault else .serial
  | .pageFault => if c || second == 14 then .doubleFault else .serial
  | .doubleFault => .shutdown

/-! ## HWCR bits and IRPerf -/

/-- HWCR bits stored by this module: McStatusWrEn (18), IRPerfEn (30). -/
def hwcrMcStatusWrEn : UInt64 := 1 <<< 18
def hwcrIrPerfEn : UInt64 := 1 <<< 30
def hwcrMask : UInt64 := hwcrMcStatusWrEn ||| hwcrIrPerfEn

/-- IRPerfCount: bits 63:0 (AMD Open-Source Register Reference for family 17h models 00h-2Fh, pub.
56255, MSRC000_00E9; the model 31h PPR was not available). -/
def irPerfMask : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Instructions retired so far (see the module documentation). -/
@[inline] def retired (m : Machine) : UInt64 := m.icount - m.cpu.sysbx.notRetired

/-- The value of IRPerfCount. -/
def irPerf (m : Machine) : UInt64 :=
  let s := m.cpu.sysbx
  if s.hwcr &&& hwcrIrPerfEn != 0 then (s.irBase + (retired m - s.irAt)) &&& irPerfMask else s.irBase

@[inline] def modS (f : SysBState → SysBState) : M Unit := modCpu fun c => { c with sysbx := f c.sysbx }

/-- The HWCR bits of this module, for the HWCR read of `Gpr.msr?`. -/
def hwcrBits : M UInt64 := do return (← cpu).sysbx.hwcr

/-- HWCR write (from `Gpr.msr?`): keep bits 18 and 30; enabling or disabling IRPerf latches the
counter. -/
def hwcrWrite (v : UInt64) : M Unit := modM fun m =>
  let now := irPerf m
  let r := retired m
  { m with cpu := { m.cpu with sysbx := { m.cpu.sysbx with hwcr := v &&& hwcrMask, irBase := now, irAt := r } } }

/-! ## MSRs -/

/-- MSR of the model-only NMI test hook (ASCII "NMI1"); present only with `SysBState.testHooks`,
which `x86sys` sets for the system tests (QEMU has no software NMI source besides the local APIC,
whose NMI delivery modes the SMP workstream owns). WRMSR with EAX = n latches an NMI that becomes
deliverable after n further instruction boundaries (0: the next boundary; see `Step.step`).
RDMSR returns bit 0 = NMI latched, bit 1 = NMIs blocked, bits 63:32 = the remaining delay. -/
def nmiHookMsr : UInt32 := 0x4E4D4931

def msr? (n : UInt32) : Option MsrImpl :=
  if n == 0xC00000E9 then
    if !implemented .irPerf then none else
    some { rd := fun m => .ok (irPerf m) m
           wr := fun v => modM fun m =>
             let r := retired m
             { m with cpu := { m.cpu with sysbx := { m.cpu.sysbx with irBase := v &&& irPerfMask, irAt := r } } } }
  else if n == nmiHookMsr then
    some { rd := do
             let s := (← cpu).sysbx
             if !s.testHooks then gp 0
             return (if s.nmiPending then 1 else 0) ||| (if s.nmiBlocked then 2 else 0) |||
                    (s.nmiDelay.toUInt64 <<< 32)
           wr := fun v => do
             if !(← cpu).sysbx.testHooks then gp 0
             modS fun s => { s with nmiPending := true, nmiDelay := v.toUInt32 } }
  else none

end SysB
end X86
