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

/-! ## SVM guest mode: exceptions, intercepts and EXITINTINFO (owner: the SVM workstream)

AMD APM vol. 2, 15.7.2, 15.7.3, 15.12, 15.14.3. In guest mode (`Cpu.svmOn`) an event the guest
delivers through its IDT goes through `raiseG` instead of `raiseExcF`: an exception (type 3) is
first checked for its exception intercept (unless the caller has done so, `chk = false`); a #VMEXIT
during the delivery records the event in EXITINTINFO (vector, type: 0 INTR, 2 NMI, 3 exception, 4
software interrupt, the error code); an exception raised by the delivery is checked for its intercept
before it is combined with the event (#VMEXIT with this event in EXITINTINFO), then combined as by
`SysB.onSecond`; a resulting #DF is checked for the #DF intercept, a triple fault for the shutdown
intercept (#VMEXIT(SHUTDOWN), 7Fh). `soft = some r`: an injected software interrupt or INT3/INTO-like
exception, delivered with return address `r` and the gate DPL check. -/
def raiseG : Nat → Machine → UInt8 → Option UInt32 → Bool → UInt64 → Bool → Option UInt32 → Machine
  | 0, m, vec, _, _, _, _, _ =>
    if Svm.bit m.cpu.svmx.i3 31 then Svm.vmexitM m { code := 0x7F }
    else { m with fatal := some (.shutdown s!"exception loop delivering vector {vec}") }
  | fuel + 1, m, vec, err, ext, ty, chk, soft =>
    if chk && ty == 3 && Svm.excIntercepted m.cpu vec then
      Svm.vmexitM m { code := 0x40 + vec.toUInt64, info1 := (err.getD 0).toUInt64 }
    else
    let m := if vec == Vec.DB && ty == 3 then { m with cpu := { m.cpu with dr7 := m.cpu.dr7 &&& ~~~0x2000 } } else m
    let info := Svm.intInfo vec ty err
    let saved := m.cpu
    let m' := match soft with
      | some r => { m with keepCpu := false, cpu := { m.cpu with eip := r } }
      | none => { m with keepCpu := false }
    match deliver vec err soft.isSome ext m' with
    | .ok _ m =>
      -- the handler's first instruction is not in an interrupt shadow (the instruction that raised
      -- the event, or the VMCB's shadow of an injected event, no longer applies)
      { m with keepCpu := false, cpu := { m.cpu with shadow := false } }
    | .error f m =>
      let keep := m.keepCpu
      let m := if keep then { m with keepCpu := false } else { m with keepCpu := false, cpu := saved }
      match f with
      | .vmexit e =>
        Svm.vmexitM m (if e.intInfo &&& 0x80000000 != 0 then e else { e with intInfo := info })
      | .exc v e a =>
        if Svm.excIntercepted m.cpu v then
          Svm.vmexitM m { code := 0x40 + v.toUInt64, info1 := (e.getD 0).toUInt64,
                          info2 := if v == Vec.PF then a.toUInt64 else 0, intInfo := info }
        else
        match SysB.onSecond (if ty == 3 then SysB.excClass vec else .benign) v with
        | .serial => raiseG fuel (faultState m v a) v e true 3 false none
        | .doubleFault =>
          let m := if v == Vec.PF then { m with cpu := { m.cpu with cr2 := a } } else m
          if Svm.excIntercepted m.cpu Vec.DF then Svm.vmexitM m { code := 0x48, intInfo := info }
          else raiseG fuel m Vec.DF (some 0) true 3 false none
        | .shutdown =>
          if Svm.bit m.cpu.svmx.i3 31 then Svm.vmexitM m { code := 0x7F, intInfo := info }
          else { m with fatal := some (.shutdown s!"triple fault ({repr f})") }
      | f => { m with fatal := some f }

/-- Deliver an exception (`intr = false`) or an external interrupt or NMI (`intr = true`). In SVM
guest mode through `raiseG` (exceptions checked for their intercept). -/
@[inline] def raiseExc (m : Machine) (vec : UInt8) (err : Option UInt32) (ext : Bool) (intr : Bool := false) : Machine :=
  if m.cpu.svmOn then raiseG 4 m vec err ext (if !intr then 3 else if vec == Vec.NMI then 2 else 0) (!intr) none
  else raiseExcF 4 m vec err ext intr

/-- The fault of a guest instruction (SVM): the exception intercept before the exception writes
any state except DR6 for #DB (15.12.2: "both #DB faults and traps are permitted to write DR6 and
DR7 before the intercept"; #PF: "tested before CR2 is written"; EXITINFO1 the error code,
EXITINFO2 the #PF address), then `raiseG`. -/
def handleFaultG (m : Machine) (vec : UInt8) (err : Option UInt32) (addr : UInt32) : Machine :=
  if Svm.excIntercepted m.cpu vec then
    let m := if vec == Vec.DB then { m with cpu := { m.cpu with dr6 := m.cpu.dr6 ||| addr } } else m
    Svm.vmexitM m { code := 0x40 + vec.toUInt64, info1 := (err.getD 0).toUInt64,
                    info2 := if vec == Vec.PF then addr.toUInt64 else 0 }
  else raiseG 4 (faultState m vec addr) vec err true 3 false none

/-- Deliver the fault of an instruction (see `faultState`); faults are external to the program for
the EXT bit of nested faults. An intercept of an SVM guest (`Fault.vmexit`) is the #VMEXIT. -/
def handleFault (m : Machine) (f : Fault) : Machine :=
  match f with
  | .exc vec err addr =>
    if m.cpu.svmOn then handleFaultG m vec err addr else raiseExc (faultState m vec addr) vec err true
  | .vmexit e => Svm.vmexitM m e
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
register loads, the vector registers of an AVX2 gather (VEX.0F38 90..93: the elements loaded before
the faulting one stay in the destination with their mask elements cleared, so that the instruction can
be restarted; SDM VPGATHERDD, AMD APM vol. 4 VGATHERDPS; `Ext/Avx2.lean`) and MXCSR: the exception
flags of an unmasked SIMD exception are set when it is raised (#XM), and no instruction changes MXCSR
before another fault can occur.
ESP and EIP always retain their restart values.

The x87-to-MMX transition (TOP = 0, all registers valid) is kept when MASKMOVQ faults on its store
(#PF, #AC) and when a conversion that uses an MMX register (CVTPI2PS/PD xmm, mm; CVT(T)PS2PI and
CVT(T)PD2PI mm, xmm/m) raises #XM: the EPYC 7742 enters MMX operation before these faults (native
`enc_fuzz`, `code16`: 30 cases); a fault on the memory operand of a conversion leaves the x87 state
unchanged. -/
def mmxFaultKeeps (i : Inst) (vec : UInt8) : Bool :=
  !i.vex && i.map == 1 && (
    (i.byte == 0xF7 && i.pp == 0 && !i.isMem) ||
    (vec == Vec.XM && (i.pp == 0 || i.pp == 1) &&
      ((i.byte == 0x2A && !i.isMem) || i.byte == 0x2C || i.byte == 0x2D)))

def faultCpu (saved current : Cpu) (i : Inst) (vec : UInt8 := 0) : Cpu :=
  let r := faultCpu0 saved current i
  if mmxFaultKeeps i vec then
    { r with fempty := current.fempty, fsw := (r.fsw &&& ~~~0x3800) ||| (current.fsw &&& 0x3800) }
  else r
where faultCpu0 (saved current : Cpu) (i : Inst) : Cpu :=
  if i.vex && i.op ≥ 0x290 && i.op ≤ 0x293 then { saved with sse := current.sse }
  else if i.op == 0x61 then
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
      else .error f { m'' with cpu := faultCpu saved m''.cpu i (match f with | .exc v _ _ => v | _ => 0) }

/-- Instructions after which no single-step trap is taken: software interrupts (their handler
is entered with TF clear) and MOV/POP SS (the trap is deferred past the next instruction). -/
def noStepTrap (i : Inst) : Bool :=
  i.op == 0xCC || i.op == 0xCD || i.op == 0xCE || i.op == 0xF1 ||
  i.op == 0x17 || (i.op == 0x8E && i.reg == SegN.SS) ||
  -- VMRUN: the host's trace trap follows the #VMEXIT (`Svm.exitToHost`); SKINIT honours no trace
  -- trap (AMD APM vol. 2, 15.5.1, 15.27.6)
  (i.op == 0x101 && !i.vex && (i.modrm == 0xD8 || i.modrm == 0xDE))

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
* a STARTUP IPI outside the INIT state is ignored; one that arrives while an INIT is still pending
  (the target has not reached an instruction boundary since) is accepted and taken right after the
  INIT (`Machine.initCpu`), so INIT and STARTUP sent back to back start the CPU whatever the schedule;
* NMI: the APIC's `nmi` message (an NMI IPI, an LVT or I/O APIC entry in NMI mode: `Machine.latchNmi`)
  enters the CPU's NMI latch (`Cpu.latchNmi`, `SysBState.nmiPending`) at the CPU's next instruction
  boundary outside the INIT state (`takeNmi`), from where `nextEvent` delivers it with the NMI
  blocking rules of system B. A CPU in the INIT state holds it pending in the APIC. -/

/-- The CPU state after INIT (AMD APM vol. 2, rev. 3.39, §14.1.3, table 14-1 "Initial Processor
State", column "after INIT"; segment attributes from table 14-2). `sig` is the processor signature
(CPUID 1:EAX), `bsp` selects the boot processor (which starts at the reset vector; an application
processor waits for STARTUP, §16.5). Every piece of state the model has, with the row of table 14-1
it follows:

| state (model field) | after INIT | table 14-1 row / source |
|---|---|---|
| CR0 (`cr0`) | CD, NW unchanged, bit 4 (ET) = 1, all others 0 | CR0 |
| CR2, CR3, CR4 | 0 | CR2, CR3, CR4 |
| CR8 = TPR[7:4] (`Apic.tpr`) | 0 (`Apic.reset`, `Machine.initCpu`) | CR8; table 16-2 |
| RFLAGS (`eflags`) | 2 | RFLAGS |
| EFER (`efer`, so LME = LMA = 0) | 0 | EFER |
| RIP (`eip`, `lmx.ripHi`) | FFF0h, bits 63:32 = 0 | RIP |
| CS | F000h, base FFFF_0000h, limit FFFFh, P, DPL 0, S, type 1010b | CS; table 14-2 |
| DS, ES, FS, GS, SS | 0, base 0, limit FFFFh, P, DPL 0, S, type 0010b; FS/GS bases bits 63:32 = 0 (`lmx.fsBase`, `gsBase`) | DS, ES, FS, GS, SS; table 14-2 |
| GDTR, IDTR | base 0, limit FFFFh | GDTR, IDTR |
| LDTR, TR | 0, base 0, limit FFFFh, LDT (type 0010b), busy 16-bit TSS (0011b) | LDTR, TR; table 14-2 |
| RAX, RBX, RCX, RBP, RSP, RDI, RSI | 0 (RSP bits 63:32: `lmx.rspHi` = 0) | RAX ("0" after INIT, no BIST), RBX..RSI |
| RDX (`edx`) | family/model/stepping (`sig`) | RDX |
| R8–R15 | 0: R11 (`lmx.r11`), the only one the model keeps | R8–R15 |
| x87 state (`fpr`, `fcw`, `fsw`, `fempty`, `fip`, `fcs`, `fop`, `fdp`, `fds`) | not modified | x87 floating-point state; §14.2.3 |
| MMX registers (aliases of `fpr`) | not modified | 64-bit media state |
| XMM, YMM bits 255:128, MXCSR (`sse`) | not modified (YMM: no row; the SDM's table 12-1 leaves YMM_H unchanged) | SSE state |
| XCR0 (`xcr0`), IA32_XSS (`xss`), XINUSE tracking (`xsx`) | not modified | XCR0; other MSRs |
| DR0–DR3, DR6, DR7 | 0, FFFF_0FF0h, 400h (breakpoints off: `bpOn`) | DR0–DR3, DR6, DR7 |
| TSC (`sysx.tscOff`) | not modified | Time-Stamp Counter |
| performance counters (`gprx.perfCtr`/`perfEvtSel`, MPERF/APERF, IRPerf `sysbx.irBase`/`notRetired`) | not modified | Performance-Monitor Resources |
| MTRRs, PAT, MCA banks, SYSCFG and the other MSRs (`msrs`), SYSENTER/STAR/LSTAR/CSTAR/SFMASK (`sysx`), TSC_AUX, HWCR bits (`gprx`, `sysbx.hwcr`), KernelGSbase (`lmx.kernelGsBase`), VM_HSAVE_PA, SVM_KEY, TSC_RATIO, IGNNE (`svmx`), PATCH_LEVEL | not modified | Memory-Type Range Registers, Machine-Check Registers, Other Model-Specific Registers |
| SMBASE (`smbase`) | not modified | SMBASE |
| EFER.SVME | 0 (with EFER) | EFER |
| VM_CR (`svmx.vmCr`) | SVMDIS cleared when LOCK = 0, the other bits (LOCK, R_INIT, DIS_A20M, DPD) not modified | APM vol. 2, 15.30.1 ("cleared by INIT when LOCK is cleared to 0") |
| GIF (`svmx.gif`) | 1 | no row (open): the model sets it as at RESET, so the started CPU takes interrupts; QEMU's `do_cpu_init` likewise sets GIF |
| guest mode, the cached VMCB controls, host save area, pending injection, nested-paging state, host TLB stash (`svmx`) | ended / discarded (`SvmState.afterInit`): the CPU restarts at the reset vector as the host; PAT and SPEC_CTRL, which VMRUN replaced by the guest's, get the host's values back (`Svm.initRestore`), and the guest's TLB entries are dropped (`Machine.initCpu`) | no row: INIT in a guest is taken only when not intercepted (15.13.4, table 15-12); without the INIT intercept it resets the CPU, so no guest state survives |
| INIT itself with VM_CR.R_INIT = 1 | not an INIT: #SX (vector 30, error code 1) instead (`initEvent`) | APM vol. 2, 15.28 |
| local APIC | reset except base, AE, EXTD and ID (`Apic.reset` in `Machine.initCpu`) | APIC "Enabled, see Table 16-2"; §16.10 |
| TLB (`Machine.tlb*`) and PAE PDPTE registers (`pdpte`) | not modified (the table: caches and TLBs not modified by INIT; with CR0.PG = 0 neither is used, and enabling paging reloads them) | Instruction and Data TLBs |
| halted, waiting for STARTUP (`halted`, `smpx.waitSipi`) | an application processor waits for STARTUP, the BSP runs | §16.5 |
| MWAIT in progress (`smpx.mwait`) | ended | APM vol. 3 MWAIT: INIT ends the monitor event pending state |
| interrupt shadow (`shadow`) | cleared | no row: the INIT state executes nothing before its first instruction |
| NMI latch and blocking (`sysbx.nmiPending`, `nmiBlocked`), SMM (`smm`) | not modified (a pending NMI is held until STARTUP, §16.5; INIT is not recognized in SMM, §10.3.3) | no row: neither the APM nor the SDM's table 12-1 says whether INIT ends NMI blocking (QEMU's TCG clears it) — an open question, the model leaves it |
| armed MONITOR (`gprx.monLine`) | not modified | no row (open: not specified) |
| pending debug traps (`Machine.dbPend`) | discarded (`Machine.initCpu`) | no row |

RESET differs in CR0 (6000_0010h), the x87 state, the SSE state, XCR0, the TSC, SMBASE, the MSRs
and the caches/TLBs (`Cpu.atReset`). -/
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
    efer := 0, halted := !bsp, shadow := false, svmx := c.svmx.afterInit,
    -- long mode: RIP/RSP bits 63:32 = 0, R8–R15 = 0 (R11 is the one the model keeps), FS/GS base
    -- 63:32 = 0 (the segment loads clear the 64-bit bases); KernelGSbase (an MSR) is not modified
    lmx := { c.lmx with ripHi := 0, rspHi := 0, r11 := 0, fsBase := none, gsBase := none, entry := "" },
    smpx := { c.smpx with waitSipi := !bsp, mwait := none } }

/-- The state of a CPU after RESET where it differs from `afterInit` (AMD APM vol. 2, table 14-1,
column "after RESET"): CR0 = 6000_0010h (CD = NW = 1), the x87 state FPR0–7 = 0, control word 0040h,
status word 0, tag word 5555h (every register holds a zero: none is empty), pointers and opcode 0;
MMX 0; XMM 0, MXCSR 1F80h; XCR0 = 1; TSC = 0; SMBASE = 3_0000h; the MSRs at their reset values. The
model's default `Cpu` has these except CR0 and the x87 control and tag words (its defaults are the
FNINIT values, as the firmware leaves the boot processor). Applying `afterInit` to it gives the RESET
state of every row (the two columns agree elsewhere). -/
def Cpu.atReset : Cpu := { ({} : Cpu) with cr0 := 0x60000010, fcw := 0x0040, fsw := 0, fempty := 0 }

/-- The local APIC's part of INIT (`Machine.initCpu`). A STARTUP IPI the APIC accepted while the INIT was pending (`Machine.recv`:
the APIC accepts STARTUP in, or while entering, the INIT state, APM vol. 2, 16.5) survives the APIC
reset and is taken at the next boundary: a CPU that does not run while INIT and STARTUP arrive (it is
not scheduled, or still finishing an instruction) ends up started, as one that took the INIT at once.
QEMU likewise keeps a pending SIPI across INIT (`do_cpu_init` preserves `CPU_INTERRUPT_SIPI`). -/
def Apic.afterInit (a : Apic) : Apic := { ({ a with init := false } : Apic).reset with sipi := a.sipi }

def Machine.initCpu (m : Machine) : Machine :=
  let sig := (cpuid m.cpu 1 0).1
  -- INIT in an SVM guest: the host's PAT and SPEC_CTRL back (`Svm.initRestore`), and the guest's
  -- TLB entries (its ASID's) are dropped: the processor continues as the host (ASID 0)
  let m := if m.cpu.svmx.guest then
      { m with cpu := Svm.initRestore m.cpu, tlbTag := Array.replicate tlbSize 0, tlbLarge := false,
               tlbGlobal := false, tlbLargeRegions := #[] }
    else m
  { m with cpu := m.cpu.afterInit sig m.apic.bsp, apic := m.apic.afterInit, dbPend := 0 }.syncTimer.syncApic

/-- A STARTUP IPI with vector `v` ends the INIT state: real mode at `v`00:0000. -/
def Machine.startCpu (m : Machine) (v : UInt32) : Machine :=
  { m with cpu := { m.cpu with cs := { sel := (v <<< 8).toUInt16, base := v <<< 12, limit := 0xFFFF, attr := 0x9A },
                               eip := 0, halted := false, smpx := { m.cpu.smpx with waitSipi := false } },
           apic := { m.apic with sipi := none } }.syncXev

/-- The APIC's NMI message enters the CPU's NMI latch (a second NMI while one is latched is lost). -/
@[inline] def Machine.takeNmi (m : Machine) : Machine :=
  if m.apic.nmi then { m with apic := { m.apic with nmi := false }, cpu := m.cpu.latchNmi }.syncXev else m

/-- INIT taken at an instruction boundary with GIF = 1 (AMD APM vol. 2, table 15-12): in a guest
with the INIT intercept a #VMEXIT(INIT) (63h) that leaves INIT pending (GIF is 0 after it); otherwise
with VM_CR.R_INIT the INIT is redirected to #SX (vector 30, error code 1; 15.28) and is no longer
pending; else the INIT itself. -/
def initEvent (m : Machine) : Machine :=
  if m.cpu.svmOn && Svm.bit m.cpu.svmx.i3 3 then Svm.vmexitM m { code := 0x63 }
  else if m.cpu.svmx.vmCr &&& 2 != 0 then
    let m := { m with apic := { m.apic with init := false }, cpu := { m.cpu with halted := false } }.syncXev
    pendHits (raiseExc m Vec.SX (some 1) true)
  else m.initCpu

/-- The slow path of `smpEvent?`. INIT is held pending while GIF = 0 (table 15-10). -/
def smpEventSlow (m : Machine) : Option Machine :=
  let a := m.apic
  if a.init && !m.cpu.smm && m.cpu.svmx.gif then some (initEvent m)
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

/-- The instruction-breakpoint matches (DR6 B0-B3) at the current CS:EIP, checked before the
instruction: none with RF set, in 64-bit mode (the CS base is ignored there: the 64-bit executor's
check, the model stops in `decode` without checking, as comparing CS.base + EIP would invent or lose a
#DB), or with GIF = 0 (SVM: a breakpoint-register match is ignored and discarded, AMD APM vol. 2,
15.17, table 15-10). -/
@[inline] def instrBp (c : Cpu) : UInt32 :=
  if c.bpOn && c.eflags &&& Flag.RF == 0 && !LongMode.in64 c && c.svmx.gif then
    bpHits c (c.cs.base + c.eip) 1 (· == 0) else 0

/-- The instruction part of a step: idle while halted, an instruction-breakpoint fault, or the
instruction followed by its debug traps (data/I/O breakpoints, single-step). Traps raised by MOV SS /
POP SS are held past the next instruction (it executes in the interrupt shadow). -/
@[inline] def stepInstr (m : Machine) : Machine :=
  if m.cpu.halted then
    let t := if m.timerAt == maxU64 then m.icount else max (m.icount + 1) m.timerAt
    addNotRetired { m with icount := t } (t - m.icount)
  else
    let c := m.cpu
    let ibp := instrBp c
    if ibp != 0 then
      dbTrap (addNotRetired { m with icount := m.icount + 1, cpu := { c with shadow := false } } 1) ibp
    else
    let tf := c.eflags &&& Flag.TF != 0
    let ic := m.icount
    let m := { m with cpu := { c with shadow := false }, dbHit := 0 }
    match execInstr m with
    | .ok i m =>
      let m := if m.icount == ic then { m with icount := m.icount + 1 } else retireLong ic c.eip i m
      let m := if m.dbHit != 0 && !m.cpu.svmx.gif then { m with dbHit := 0 } else m
      let bits := m.dbHit ||| (if tf && !noStepTrap i then DR6.BS else 0)
      if bits == 0 && m.dbPend == 0 then m
      else if m.cpu.shadow && i.op != 0xFB then { m with dbPend := m.dbPend ||| bits, dbHit := 0 }
      else dbTrap m (bits ||| m.dbPend)
    | .error f m =>
      let m := addNotRetired { m with icount := m.icount + 1, dbHit := 0 } (m.icount + 1 - ic)
      -- a guest instruction that ends in a #VMEXIT (its intercept, an intercepted exception it raises,
      -- or one raised while delivering that exception): the VMCB gets the interrupt shadow and
      -- RFLAGS.RF the instruction started with (`execInstr` clears RF at the start), the state "as of
      -- the moment the intercept triggers" (15.7.1, 15.21.5); a delivery that completes clears the
      -- shadow (`raiseG`) and pushes RF = 1 for a fault (`faultState`)
      let m := if c.svmOn then
          { m with cpu := { m.cpu with shadow := c.shadow,
                                       eflags := (m.cpu.eflags &&& ~~~Flag.RF) ||| (c.eflags &&& Flag.RF) } }
        else m
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
  if m.smiPending && !c.smiHeld && !c.shadow then .smi
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

/-! ## SVM: events in guest mode and with GIF = 0 (owner: the SVM workstream)

AMD APM vol. 2, 15.13, 15.17 (table 15-10), 15.20, 15.21, 15.22. While the CPU is in guest mode or
GIF = 0, `stepAtSvm` replaces `stepAt` (`step`); otherwise nothing changes. In order:

1. an event injected by VMRUN (EVENTINJ), taken unconditionally before the first guest instruction
   (`injectEvent`; not subject to intercepts, its secondary exceptions are);
2. SMI (GIF = 1, outside SMM and SMM_CTL ENTER): #VMEXIT(SMI) (62h, EXITINFO1 bit 0 = 1, an
   external SMI, still pending) with the SMI intercept, else (outside the interrupt shadow) SMM entry in
   the guest's context, which flushes the TLB entries of all ASIDs (15.16.1); SMIs are held while
   GIF = 0;
3. debug traps: breakpoint matches (DR6.B0-B3) are discarded while GIF = 0, trace traps are taken;
4. NMI (GIF = 1): #VMEXIT(NMI) (61h, still latched) with the NMI intercept, else delivered;
5. physical INTR (GIF = 1; masked by EFLAGS.IF, or by the host's IF at VMRUN in a guest with
   V_INTR_MASKING, 15.21.1): #VMEXIT(INTR) (60h, not acknowledged) with the INTR intercept, else
   delivered through the guest's IDT;

   the guest's interrupt shadow holds the events of 2, 4 and 5 only when they are delivered to the
   guest: an intercepted SMI, NMI or INTR exits also in the shadow, which the VMCB then records
   (15.21.5: the shadow is a property of the guest's instruction stream; KVM likewise, "vmexits
   aren't blocked by the interrupt shadow"; QEMU's TCG holds them);
6. a virtual interrupt (V_IRQ with V_INTR_PRIO > V_TPR or V_IGN_TPR, guest EFLAGS.IF, the virtual
   GIF, not in a shadow; 15.21.4): #VMEXIT(VINTR) (64h, V_IRQ stays set) with the VINTR intercept,
   else V_IRQ is cleared and V_INTR_VECTOR delivered as an external interrupt;
7. the instruction (`stepInstr`). -/

/-- The event injected by VMRUN (15.20): INTR (type 0) and NMI (type 2; an injected NMI does not
block NMIs) as external events, exceptions (type 3) with their error code when EV = 1 (never in real
mode), software interrupts (type 4) and the INT3/INTO-like exceptions (type 3, vectors 3 and 4) with
the gate DPL check and the VMCB's nRIP as return address. -/
def injectEvent (m : Machine) : Machine :=
  let c := m.cpu
  let e := c.svmx.inject
  let m := { m with cpu := { c with halted := false, svmx := { c.svmx with inject := 0 } } }
  let ty := (e >>> 8) &&& 7
  let vec := (e &&& 0xFF).toUInt8
  let err := if e &&& 0x800 != 0 && c.pe then some (e >>> 32).toUInt32 else none
  if ty == 2 then pendHits (raiseG 4 m Vec.NMI none true 2 false none)
  else if ty == 0 then pendHits (raiseG 4 m vec none true 0 false none)
  else if ty == 4 || (vec == Vec.BP || vec == Vec.OF) then
    pendHits (raiseG 4 m vec (if ty == 3 then err else none) false ty false (some c.svmx.injNrip))
  else pendHits (raiseG 4 m vec err true 3 false none)

/-- One step at an instruction boundary in guest mode or with GIF = 0 (see above). -/
def stepAtSvm (m : Machine) : Machine :=
  let c := m.cpu
  let s := c.svmx
  if s.inject &&& 0x80000000 != 0 then injectEvent m else
  let g := c.svmOn
  if s.gif && m.smiPending && !c.smiHeld && (!c.shadow || (g && Svm.bit s.i3 2)) then
    if g && Svm.bit s.i3 2 then Svm.vmexitM m { code := 0x62, info1 := 1 }
    else
      let m := if g then { m with cpu := { c with svmx := { s with hostTlb := {} } } } else m
      match smmEnter { m with smiPending := false } with
      | .ok _ m => m
      | .error f m => { m with fatal := some f }
  else
  let dp := if s.gif then m.dbPend else m.dbPend &&& ~~~0xF
  let m := if dp == m.dbPend then m else { m with dbPend := dp }
  if dp != 0 && !c.shadow then dbTrap { m with cpu := { m.cpu with halted := false } } dp
  else
  let n := c.sysbx
  if s.gif && n.nmiPending && n.nmiDelay == 0 && !n.nmiBlocked && (!c.shadow || (g && Svm.bit s.i3 1)) then
    if g && Svm.bit s.i3 1 then Svm.vmexitM m { code := 0x61 } else deliverNmi m
  else if s.gif && m.intr && c.physIntrOk && (!c.shadow || (g && Svm.bit s.i3 0)) then
    if g && Svm.bit s.i3 0 then Svm.vmexitM m { code := 0x60 }
    else
      let m := { m with cpu := { m.cpu with halted := false } }
      let (vec, m) := m.intAck
      pendHits (raiseExc m vec none true true)
  else if c.vintrReady then
    if Svm.bit s.i3 4 then Svm.vmexitM m { code := 0x64 }
    else
      let m := { m with cpu := { c with halted := false, svmx := { s with vIrq := false } } }
      pendHits (raiseG 4 m s.vVec.toUInt8 none true 0 false none)
  else if n.nmiPending && n.nmiDelay != 0 then
    stepInstr { m with cpu := { m.cpu with sysbx := { n with nmiDelay := n.nmiDelay - 1 } } }
  else stepInstr m

/-- One architectural step: timer events due; INIT, STARTUP and the INIT state (`smpEvent?`: INIT is
above SMI in AMD's table 8-9, and a CPU waiting for STARTUP holds every other event pending); then the
APIC's NMI message enters the NMI latch (`Machine.takeNmi`) and `stepAt` takes the event `nextEvent`
selects (`stepAtSvm` in SVM guest mode or with GIF = 0). -/
def step (m : Machine) : Machine :=
  let m := if m.icount ≥ m.timerAt then m.timerFire else m
  match smpEvent? m with
  | some m => m
  | none =>
    let m := if m.xev then m.takeNmi else m
    if m.cpu.svmx.guest || !m.cpu.svmx.gif then stepAtSvm m else stepAt m

/-- `Machine.idle` in SVM guest mode or with GIF = 0 (the events of `stepAtSvm`). -/
def Machine.svmIdle (m : Machine) : Bool :=
  let c := m.cpu
  let s := c.svmx
  let n := c.sysbx
  c.halted && s.inject &&& 0x80000000 == 0 && (if s.gif then m.dbPend else m.dbPend &&& ~~~0xF) == 0 &&
    !(s.gif && m.smiPending && !c.smiHeld) && m.timerAt == maxU64 &&
    !(s.gif && m.intr && c.physIntrOk) && !c.vintrReady &&
    !(s.gif && (n.nmiPending || m.apic.nmi) && (!n.nmiBlocked || n.nmiDelay != 0)) &&
    !(s.gif && m.apic.init && !c.smm)

/-- `true` if the machine can make no progress without external input. -/
def Machine.idle (m : Machine) : Bool :=
  if m.cpu.svmx.guest || !m.cpu.svmx.gif then m.svmIdle else
  m.cpu.halted && m.dbPend == 0 && !(m.smiPending && !m.cpu.smiHeld) && m.timerAt == maxU64 &&
    !(m.intr && m.cpu.eflags &&& Flag.IF != 0) &&
    !((m.cpu.sysbx.nmiPending || m.apic.nmi) && (!m.cpu.sysbx.nmiBlocked || m.cpu.sysbx.nmiDelay != 0))

/-- Run until the instruction count reaches `limit`, the machine is idle, or a fatal stop. -/
partial def Machine.runUntil (m : Machine) (limit : UInt64) : Machine :=
  if m.icount ≥ limit || m.fatal.isSome || m.idle then m
  else (step m).runUntil limit

end X86
