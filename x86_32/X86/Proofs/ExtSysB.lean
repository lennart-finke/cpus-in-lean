import X86.Step
import X86.Proofs.Basic
import X86.Proofs.State
import X86.Proofs.ExtSmp
import Std.Tactic.BVDecide
/-!
# System workstream B: exception classes, NMI, VME/PVI, IRPerf, PATCH_LEVEL

* `excClass_spec`, `onSecond_table`: the double-fault classification (AMD APM vol. 2, tables 8-2
  and 8-3) as a decidable statement over every vector, and `raiseExcF_triple`: a contributory
  exception or page fault while delivering #DF shuts the processor down; `raiseExcF_double`: one
  while delivering a contributory exception raises #DF.
* `nextEvent_nmi_blocked`, `nextEvent_nmi_shadow`: an NMI is not taken while NMIs are blocked or in an
  interrupt shadow; `nextEvent_smi_first`, `nextEvent_nmi_before_intr`: the priorities SMI > NMI > INTR;
  `stepAt_nmi`: a deliverable NMI is delivered; `execInstr_iret_unblocks`: an IRET that completes
  ends the blocking of NMIs; `takeNmi_latches`: an NMI from the local APIC enters the CPU's latch;
  `step_waitSipi_nmi`: a CPU waiting for STARTUP holds it pending.
* `cli_if_cpl3`, `sti_if_cpl3`, `popfMask_if_cpl3`, `vmePopFlags_if`, `vmeIntFlags_if`: with VME or
  PVI (or without), virtual-8086 / CPL-3 code with IOPL < 3 cannot change EFLAGS.IF through CLI, STI,
  POPF, IRET or a redirected INT n; `vmeActive_cpl3`: VME applies only at CPL 3.
* `intN_noVme`: outside virtual-8086 mode or with CR4.VME = 0, INT n is the plain software interrupt
  (no access to the TSS interrupt-redirection bitmap); `leaveV86_cpl`: an event from virtual-8086
  mode pushes its frame at CPL 0 (supervisor accesses).
* `irPerf_disabled`: with HWCR.IRPerfEn = 0 IRPerfCount does not move.
* `patchLevel_amd_wr`, `patchLevel_amd_rd`, `coreMsr_patchLevel`: on the AMD identity (the model's) MSR
  0x8B is read-only (WRMSR #GP(0)) and reads 0.
-/
namespace X86
open SysB

/-! ## Exception classes and double faults -/

/-- The class of the first event as a function of the vector (AMD APM vol. 2, table 8-3, first
column; table 8-2 for #DF and the contributory #SX, vector 30). -/
def firstClass (n : Nat) : ExcClass :=
  if n = 0 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 30 then .contributory
  else if n = 14 then .pageFault else if n = 8 then .doubleFault else .benign

theorem excClass_spec_nat : ∀ n, n < 256 → excClass n.toUInt8 = firstClass n := by decide +kernel

/-- The classes of the first event, for every vector. -/
theorem excClass_spec (v : UInt8) : excClass v = firstClass v.toNat := by
  have := excClass_spec_nat v.toNat v.toNat_lt
  simpa using this

/-- The class of the second event in AMD's table 8-3: #TS, #NP, #SS, #GP contributory, #PF page
fault; nothing else (in particular not #DE) produces a double fault. -/
def secondClass (n : Nat) : ExcClass :=
  if n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 then .contributory else if n = 14 then .pageFault else .benign

/-- AMD APM vol. 2, table 8-3 as a matrix over (first class, second class). -/
def dfTable : ExcClass → ExcClass → DfAction
  | .contributory, .contributory => .doubleFault
  | .pageFault, .contributory => .doubleFault
  | .pageFault, .pageFault => .doubleFault
  | .doubleFault, _ => .shutdown
  | _, _ => .serial

theorem onSecond_table_nat : ∀ f ∈ [ExcClass.benign, .contributory, .pageFault, .doubleFault],
    ∀ n, n < 256 → onSecond f n.toUInt8 = dfTable f (secondClass n) := by decide +kernel

/-- The double-fault decision is AMD's table, for every first class and every second vector. -/
theorem onSecond_table (f : ExcClass) (v : UInt8) : onSecond f v = dfTable f (secondClass v.toNat) := by
  have hf : f ∈ [ExcClass.benign, .contributory, .pageFault, .doubleFault] := by cases f <;> simp
  have := onSecond_table_nat f hf v.toNat v.toNat_lt
  simpa using this

/-- Every exception raised while delivering an interrupt, NMI or benign exception is handled
serially. -/
theorem onSecond_benign (v : UInt8) : onSecond .benign v = .serial := rfl

/-- A contributory exception or page fault while delivering #DF: shutdown (triple fault). -/
theorem raiseExcF_triple {n : Nat} {m m' : Machine} {ext : Bool} {v : UInt8} {e : Option UInt32} {a : UInt32}
    (h : deliver Vec.DF (some 0) false ext { m with keepCpu := false } = .error (.exc v e a) m') :
    ∃ why, (raiseExcF (n + 1) m Vec.DF (some 0) ext false).fatal = some (.shutdown why) := by
  have hdb : (Vec.DF == Vec.DB) = false := by decide
  have hc : excClass Vec.DF = .doubleFault := by decide
  simp only [raiseExcF, hdb, Bool.false_and, Bool.false_eq_true, ite_false, h, hc, onSecond]
  exact ⟨_, rfl⟩

/-- A contributory exception (#TS, #NP, #SS, #GP) raised while delivering a contributory exception
`vec` (from a consistent state) raises #DF with error code 0. -/
theorem raiseExcF_double {n : Nat} {m m' : Machine} {ext : Bool} {vec v : UInt8} {err e : Option UInt32}
    {a : UInt32} (hv : excClass vec = .contributory) (hs : v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13)
    (h : deliver vec err false ext { m with keepCpu := false } = .error (.exc v e a) m')
    (hk : m'.keepCpu = false) (hdb : vec ≠ Vec.DB) :
    raiseExcF (n + 1) m vec err ext false =
      raiseExcF n { m' with keepCpu := false, cpu := m.cpu } Vec.DF (some 0) true false := by
  have hdb' : (vec == Vec.DB) = false := by simpa using hdb
  have hpf : (v == Vec.PF) = false := by rcases hs with h | h | h | h <;> subst h <;> decide
  have hc : (v == 10 || v == 11 || v == 12 || v == 13) = true := by
    rcases hs with h | h | h | h <;> subst h <;> decide
  simp only [raiseExcF, hdb', Bool.false_and, ite_false, h, hk, Bool.false_eq_true, onSecond, hv, hc,
    ite_true, hpf]

/-! ## INT n and the interrupt redirection bitmap -/

/-- Outside virtual-8086 mode, or with CR4.VME = 0, INT n is the plain software interrupt
(`intPlain`): it does not read the TSS interrupt redirection bitmap (no TSS access, no fault from
the TSS limit or the I/O map base). -/
theorem intN_noVme (n : UInt8) (m : Machine)
    (h : (m.cpu.vm86 && m.cpu.cr4 &&& CR4.VME != 0) = false) : intN n m = intPlain n m := by
  simp only [intN, cpu, bind, EStateM.bind, h, Bool.false_eq_true, ite_false, EStateM.pure]

/-- An interrupt or exception from virtual-8086 mode (protected mode, `deliver`) pushes its frame at
CPL 0: supervisor accesses, not user accesses, and not alignment-checked. -/
theorem leaveV86_cpl (c : Cpu) (ss : SegReg) (esp : UInt32) (d : Desc) (sel : UInt16) (h : c.pe = true) :
    (c.leaveV86 ss esp (d.toSeg (sel &&& 0xFFFC))).cpl = 0 := by
  have hv0 : c.eflags &&& ~~~Flag.VM &&& Flag.VM = 0 := by
    simp only [Flag.VM]; generalize c.eflags = e; bv_decide
  have hv : (c.eflags &&& ~~~Flag.VM &&& Flag.VM != 0) = false := by simp [hv0]
  have hs : sel.toUInt32 &&& 65532 &&& 3 = 0 := by bv_decide
  simp [Cpu.cpl, Cpu.leaveV86, Cpu.vm86, Cpu.pe, Desc.toSeg, hv, hs, show c.cr0 &&& CR0.PE != 0 from h]

/-! ## NMI -/

/-- No NMI is taken while NMIs are blocked (from an NMI's delivery until the next IRET, and in SMM). -/
theorem nextEvent_nmi_blocked {m : Machine} (h : m.cpu.sysbx.nmiBlocked = true) : nextEvent m ≠ .nmi := by
  unfold nextEvent
  simp only [h]
  repeat' split
  all_goals simp_all

/-- No NMI is taken in an interrupt shadow (after MOV SS / POP SS / STI). -/
theorem nextEvent_nmi_shadow {m : Machine} (h : m.cpu.shadow = true) : nextEvent m ≠ .nmi := by
  unfold nextEvent
  simp only [h]
  repeat' split
  all_goals simp_all

/-- An SMI outside SMM (and outside SMM_CTL's ENTER..EXIT, `Cpu.smiHeld`) and outside a shadow is
taken before anything else. -/
theorem nextEvent_smi_first {m : Machine} (h : m.smiPending = true) (hs : m.cpu.smm = false)
    (hc : m.cpu.svmx.smmCtlIn = false) (hsh : m.cpu.shadow = false) : nextEvent m = .smi := by
  simp [nextEvent, Cpu.smiHeld, h, hs, hc, hsh]

/-- A deliverable NMI is taken before a maskable interrupt (and after SMIs and debug traps). -/
theorem nextEvent_nmi_before_intr {m : Machine} (hsmi : m.smiPending = false) (hdb : m.dbPend = 0)
    (hp : m.cpu.sysbx.nmiPending = true) (hd : m.cpu.sysbx.nmiDelay = 0)
    (hb : m.cpu.sysbx.nmiBlocked = false) (hsh : m.cpu.shadow = false) : nextEvent m = .nmi := by
  simp [nextEvent, hsmi, hdb, hp, hd, hb, hsh]

/-- The NMI event delivers the NMI. -/
theorem stepAt_nmi {m : Machine} (h : nextEvent m = .nmi) : stepAt m = deliverNmi m := by
  simp [stepAt, h]

/-- NMI delivery latches the NMI as taken and blocks further NMIs before the handler is entered:
the machine handed to the delivery has `nmiPending = false` and `nmiBlocked = true`. -/
theorem deliverNmi_blocks (m : Machine) :
    let s := { m.cpu.sysbx with nmiPending := false, nmiBlocked := true }
    deliverNmi m = pendHits (raiseExc { m with cpu := { m.cpu with halted := false, sysbx := s } }
      Vec.NMI none true true) := rfl

/-- An NMI from the local APIC (NMI IPI, LVT or I/O APIC entry in NMI mode) enters the CPU's NMI latch
when the CPU reaches an instruction boundary. -/
theorem takeNmi_latches {m : Machine} (h : m.apic.nmi = true) :
    (m.takeNmi).cpu.sysbx.nmiPending = true ∧ (m.takeNmi).apic.nmi = false := by
  simp [Machine.takeNmi, h, Cpu.latchNmi, Machine.syncXev]

/-- A CPU waiting for STARTUP holds an NMI from its APIC pending (`step_waitSipi`): nothing changes. -/
theorem step_waitSipi_nmi (m : Machine) (ht : m.icount < m.timerAt) (hx : m.xev = true)
    (hw : m.cpu.smpx.waitSipi = true) (hi : m.apic.init = false) (hs : m.apic.sipi = none) :
    (step m).apic.nmi = m.apic.nmi ∧ (step m).cpu.sysbx = m.cpu.sysbx := by
  rw [step_waitSipi m ht hx hw hi hs]; exact ⟨rfl, rfl⟩

/-- An IRET that completes ends the blocking of NMIs. -/
theorem execInstr_iret_unblocks {m m' : Machine} {i : Inst} (h : execInstr m = .ok i m')
    (hop : i.op = 0xCF) (hv : i.vex = false) : m'.cpu.sysbx.nmiBlocked = false := by
  unfold execInstr at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp only [EStateM.Result.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [iretUnblock, hop, hv]
    · split at h <;> simp at h

/-! ## VME and PVI cannot change EFLAGS.IF at CPL 3 with IOPL < 3 -/

/-- VME applies only in virtual-8086 mode, i.e. at CPL 3 (with CR0.PE). -/
theorem vmeActive_cpl3 (c : Cpu) (hpe : c.pe = true) (h : c.vmeActive = true) : c.cpl = 3 := by
  simp [Cpu.vmeActive] at h
  exact cpl_vm86 c hpe h.1.1

/-- CLI at CPL 3 with IOPL < 3 does not change IF (with VME/PVI it clears VIF, else #GP(0)). -/
theorem cli_if_cpl3 {m m' : Machine} (hpe : m.cpu.pe = true) (hcpl : m.cpu.cpl = 3) (hio : m.cpu.iopl < 3)
    (h : cli m = .ok () m') : m'.cpu.eflags &&& Flag.IF = m.cpu.eflags &&& Flag.IF := by
  have hgt : m.cpu.cpl > m.cpu.iopl := by rw [hcpl]; exact hio
  unfold cli at h
  simp only [cpu, bind, EStateM.bind, hpe, hgt, decide_true, Bool.and_self, ite_true] at h
  split at h
  · simp only [X86.setFlags, modCpu, EStateM.Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Cpu.setFlags]
    generalize m.cpu.eflags = f
    simp only [Flag.VIF, Flag.IF]; bv_decide
  · simp [gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

/-- STI at CPL 3 with IOPL < 3 does not change IF (with VME/PVI it sets VIF or raises #GP(0) with
VIP, else #GP(0)). -/
theorem sti_if_cpl3 {m m' : Machine} (hpe : m.cpu.pe = true) (hcpl : m.cpu.cpl = 3) (hio : m.cpu.iopl < 3)
    (h : sti m = .ok () m') : m'.cpu.eflags &&& Flag.IF = m.cpu.eflags &&& Flag.IF := by
  have hgt : m.cpu.cpl > m.cpu.iopl := by rw [hcpl]; exact hio
  unfold sti at h
  simp only [cpu, bind, EStateM.bind, hpe, hgt, decide_true, Bool.and_self, ite_true] at h
  split at h
  · simp [gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at h
  · simp only [X86.setFlags, modCpu, EStateM.Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Cpu.setFlags]
    generalize m.cpu.eflags = f
    simp only [Flag.VIF, Flag.IF]; bv_decide

/-- POPF at CPL 3 with IOPL < 3 (protected mode, with or without PVI) does not load IF. -/
theorem popfMask_if_cpl3 (c : Cpu) (opsz : Sz) (hcpl : c.cpl = 3) (hio : c.iopl < 3) :
    popfMask c opsz &&& Flag.IF = 0 := by
  have h1 : ¬ c.cpl ≤ c.iopl := by rw [hcpl]; exact Nat.not_le.mpr hio
  have h0 : (c.cpl == 0) = false := by rw [hcpl]; decide
  simp only [popfMask, h0, h1, Bool.false_eq_true, ite_false]
  split <;> simp only [Flag.IF, Flag.CF, Flag.PF, Flag.AF, Flag.ZF, Flag.SF, Flag.TF, Flag.DF, Flag.OF,
    Flag.NT, Flag.AC, Flag.ID] <;> decide

/-- The 16-bit POPF and IRET under VME keep IF (the popped IF goes to VIF). -/
theorem vmePopFlags_if (old v : UInt32) : vmePopFlags old v &&& Flag.IF = old &&& Flag.IF := by
  unfold vmePopFlags
  simp only [Flag.IF, Flag.IOPL, Flag.VIF, Flag.valid]
  by_cases hv : (v &&& 512 != 0) = true <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
    bv_decide

/-- A redirected INT n with IOPL < 3 keeps IF (it clears VIF). -/
theorem vmeIntFlags_if (fl : UInt32) (hio : (fl >>> 12) &&& 3 ≠ 3) :
    vmeIntFlags fl &&& Flag.IF = fl &&& Flag.IF := by
  simp only [vmeIntFlags, ite_false, Flag.IF, Flag.TF, Flag.RF, Flag.VIF]
  bv_decide

/-! ## IRPerf -/

/-- With HWCR.IRPerfEn = 0 the counter holds its value. -/
theorem irPerf_disabled {m : Machine} (h : m.cpu.sysbx.hwcr &&& hwcrIrPerfEn = 0) :
    irPerf m = m.cpu.sysbx.irBase := by
  simp [irPerf, h]

/-! ## PATCH_LEVEL (MSR 0x8B) -/

/-- On the AMD identity WRMSR to PATCH_LEVEL raises #GP(0) and changes nothing. -/
theorem patchLevel_amd_wr (v : UInt64) (m : Machine) :
    (patchLevelMsr .epyc7742).wr v m = .error (.exc Vec.GP (some 0) 0) m := rfl

/-- On the AMD identity PATCH_LEVEL reads 0 (no microcode patch loaded). -/
theorem patchLevel_amd_rd (m : Machine) : (patchLevelMsr .epyc7742).rd m = .ok 0 m := rfl

/-- The model's MSR 8Bh is the AMD PATCH_LEVEL (the final identity is the EPYC 7742). -/
theorem coreMsr_patchLevel : coreMsr? 0x8B = some (patchLevelMsr .epyc7742) := rfl

/-! ## Restated system theorems -/

/-- RSM outside SMM (`rsm_outside_smm`) also leaves the NMI state alone. -/
theorem rsm_outside_smm_nmi {m : Machine} (h : m.cpu.smm = false) :
    ∃ m', rsm m = .error (.exc Vec.UD none 0) m' ∧ m'.cpu.sysbx = m.cpu.sysbx :=
  ⟨m, rsm_outside_smm h, rfl⟩

end X86
