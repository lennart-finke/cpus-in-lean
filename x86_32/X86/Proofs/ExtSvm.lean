import Std.Tactic.BVDecide
import X86.Step
import X86.Proofs.Basic
import X86.Proofs.Ext
/-!
# SVM (`X86/Ext/Svm.lean`, `X86/Ext/SvmBase.lean`; AMD APM vol. 2, chapter 15)

* `vmrun_nosvme`, `vmload_nosvme`, `vmsave_nosvme`, `clgi_nosvme`, `invlpga_nosvme`,
  `vmmcall_nosvme`: with EFER.SVME = 0 these raise #UD before touching any state. STGI and SKINIT
  are #UD with SVME = 0 only on processors without SVM-Lock and SKINIT (vol. 3 STGI, SKINIT); the
  7742 has both (`svmLockOrSkinit_true`), so they are #UD there only outside protected mode
  (`stgi_real`, `skinit_real`).
* `vmrun_cpl`: VMRUN at CPL > 0 (EFER.SVME = 1, protected mode) raises #GP(0) before any state change.
* `stepAtSvm_gif0`, `instrBp_gif0`: with GIF = 0 (no injected event pending, no trace trap pending,
  no model-only NMI test delay) a step is exactly the instruction step with the pending breakpoint
  bits cleared: no INTR, NMI, SMI or virtual interrupt, and no instruction breakpoint is checked.
* `icpt3_on`, `icpt4_on`, `crRead_on`: an intercepted instruction ends with its #VMEXIT before it
  changes anything (the machine is unchanged, EXITCODE and nRIP as the APM specifies); instances for
  CPUID, HLT and RDTSC are the bits 18, 24 and 14 (`cpuid_icpt`, `hlt_icpt`, `rdtsc_icpt`).
* `icpt3_off`, `icpt4_off`, `msr_off`, `ioio_off` and the other `*_off`: outside guest mode (or in
  SMM) every SVM hook is the identity (intercept checks, exception intercepts, TSC scaling and
  offset, TPR virtualization, physical/virtual interrupt masking); `step_host`: outside guest mode
  with GIF = 1 a step is `stepAt`, whose hooks are those. (No separately written SVM-free step is
  compared: this hook-by-hook statement is what is proved.)
* `withHost_hostOf`: #VMEXIT restores exactly the host state VMRUN saved (segments ES/CS/SS/DS,
  GDTR, IDTR, EFER, CR0 (PE forced), CR3, CR4, RFLAGS (VM and RF cleared), RIP, RSP, RAX, DR6, DR7
  with the breakpoints disabled, SPEC_CTRL), whatever the guest did to the CPU state.
* `enterGuestTlb_empty`, `enterGuestTlb_saves`, `leaveGuest_tlb`, `vmrun_exit_tlb`,
  `translate_emptyTlb`, `leaveGuest_invalid_tlb`, `initCpu_guest_tlb`: VMRUN sets the host's TLB
  entries aside and the guest starts with an empty TLB, so its first lookups walk the tables (no
  lookup in guest mode is served by an entry made outside it); #VMEXIT reinstates exactly the host's
  entries of VMRUN (end to end, modulo the documented invalidations of the set-aside entries); a
  VMEXIT_INVALID leaves the TLB alone; INIT in a guest drops the guest's entries.
* `leaveGuest_pat`, `leaveGuest_cpu`, `initCpu_guest_pat`: #VMEXIT and INIT in a nested-paging
  guest give the host its PAT back; #VMEXIT reloads `withHost` of the saved host state.
* `nestedWalk_above4g`, `nestedWalk_pde_np`: the nested walk with 32-bit or PAE nested tables maps
  nothing at or above 4 GiB, and with 32-bit tables succeeds only through a present entry of the page
  directory at nCR3 (what the walk can reach starts at nCR3).
* `cpuid_svm_reachable`: with the legacy identity CPUID reports SVM (8000_0001 ECX bit 2) and the
  SVM leaf 8000_000A is reachable (the maximum extended leaf is 8000_000A; SVM revision 1).
* `smmSave_host`, `smmSave_guest`: SMM entry outside guest mode writes every SVM field of the AMD64
  state-save map as 0; in guest mode SVM Guest = 1 and the VMCB address (15.22, table 10-1).
* `rd32p_above`: a 32-bit nested-table entry above 4 GiB reads as open bus (nCR3 is not truncated).
* `svmIdle_inject_v`: a stale EVENTINJ without V does not affect idle detection.
* `svmMsr_wr_keeps`, `svmMsr_keeps_svmOn`, `wrmsrGuest_keeps`: no SVM MSR write (SMM_CTL included)
  changes SMM, guest mode or nested paging, so a guest keeps its intercepts and nested paging.
-/
namespace X86
open Svm

theorem bind_err {α β : Type} {x : M α} {f : α → M β} {m m' : Machine} {e : Fault}
    (h : x m = .error e m') : (x >>= f) m = .error e m' := by
  simp [bind, EStateM.bind, h]

theorem pre_nosvme {m : Machine} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.pre m = .error (.exc Vec.UD none 0) m := by
  simp [Svm.pre, Svm.svme, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vmrun_nosvme {m : Machine} {i : Inst} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.vmrun i m = .error (.exc Vec.UD none 0) m := by
  unfold Svm.vmrun; exact bind_err (pre_nosvme h)

theorem vmload_nosvme {m : Machine} {i : Inst} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.vmloadSave i false m = .error (.exc Vec.UD none 0) m := by
  unfold Svm.vmloadSave; exact bind_err (pre_nosvme h)

theorem vmsave_nosvme {m : Machine} {i : Inst} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.vmloadSave i true m = .error (.exc Vec.UD none 0) m := by
  unfold Svm.vmloadSave; exact bind_err (pre_nosvme h)

theorem invlpga_nosvme {m : Machine} {i : Inst} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.invlpga i m = .error (.exc Vec.UD none 0) m := by
  unfold Svm.invlpga; exact bind_err (pre_nosvme h)

theorem clgi_nosvme {m : Machine} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.stgiClgi false m = .error (.exc Vec.UD none 0) m := by
  simp [Svm.stgiClgi, Svm.svme, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vmmcall_nosvme {m : Machine} (h : m.cpu.efer &&& EFER.SVME = 0) :
    Svm.vmmcall m = .error (.exc Vec.UD none 0) m := by
  simp [Svm.vmmcall, Svm.svme, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- The 7742 reports SVM-Lock (8000_000A:EDX[SVML]) and SKINIT, so STGI and SKINIT execute with
EFER.SVME = 0 in protected mode (vol. 3 STGI, SKINIT). -/
theorem svmLockOrSkinit_true : Svm.svmLockOrSkinit = true := by decide

theorem stgi_real {m : Machine} (h : m.cpu.cr0 &&& CR0.PE = 0) :
    Svm.stgiClgi true m = .error (.exc Vec.UD none 0) m := by
  simp [Svm.stgiClgi, Cpu.pe, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem skinit_real {m : Machine} (h : m.cpu.cr0 &&& CR0.PE = 0) :
    Svm.skinit m = .error (.exc Vec.UD none 0) m := by
  simp [Svm.skinit, Cpu.pe, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- VMRUN at CPL > 0 raises #GP(0) (vol. 3 VMRUN) before touching any state. -/
theorem vmrun_cpl {m : Machine} {i : Inst} (h1 : m.cpu.efer &&& EFER.SVME ≠ 0) (h2 : m.cpu.pe = true)
    (h3 : m.cpu.vm86 = false) (h4 : m.cpu.cpl ≠ 0) :
    Svm.vmrun i m = .error (.exc Vec.GP (some 0) 0) m := by
  unfold Svm.vmrun
  apply bind_err
  simp [Svm.pre, Svm.svme, cpu, h1, h2, h3, h4, bind, EStateM.bind, gp, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw, pure, EStateM.pure]

/-! ## GIF -/

/-- With GIF = 0 no INTR, NMI, SMI or virtual interrupt is taken (table 15-10), and breakpoint
matches are discarded: unless VMRUN left an event to inject, a trace trap is pending or the
model-only NMI test delay runs, the step is exactly the instruction step of the machine with the
pending debug traps (only breakpoint bits B0-B3 can remain) cleared. -/
theorem stepAtSvm_gif0 {m : Machine} (hg : m.cpu.svmx.gif = false)
    (hi : m.cpu.svmx.inject &&& 0x80000000 = 0) (hd : m.dbPend &&& ~~~0xF = 0)
    (hn : (m.cpu.sysbx.nmiPending && m.cpu.sysbx.nmiDelay != 0) = false) :
    stepAtSvm m = stepInstr { m with dbPend := 0 } := by
  unfold stepAtSvm
  simp only [hg, hi, hd, Cpu.vintrReady, bne_self_eq_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : m.dbPend = 0
  · have : ({ m with dbPend := 0 } : Machine) = m := by rw [← h0]
    simp only [h0, beq_self_eq_true, ↓reduceIte, this, hn, Bool.false_eq_true]
  · have h0' : ((0 : UInt32) == m.dbPend) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => h0 h.symm
    simp only [h0', Bool.false_eq_true, ↓reduceIte, hn]

/-- With GIF = 0 no instruction breakpoint is checked (table 15-10: "ignored and discarded"). -/
theorem instrBp_gif0 {c : Cpu} (hg : c.svmx.gif = false) : instrBp c = 0 := by
  unfold instrBp; rw [hg]; simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-! ## Intercepts -/

/-- An intercepted instruction of vector 3 exits before it changes anything: the machine is
returned unchanged with EXITCODE 60h + b and nRIP the next instruction (15.7.1). -/
theorem icpt3_on {m : Machine} {b : UInt32} (h : m.cpu.svmOn = true) (hb : Svm.bit m.cpu.svmx.i3 b = true) :
    Svm.icpt3 b m = .error (.vmexit { code := 0x60 + b.toUInt64, nrip := m.cpu.eip.toUInt64 }) m := by
  simp [Svm.icpt3, h, hb, Svm.exitInstr]

theorem icpt4_on {m : Machine} {b : UInt32} (h : m.cpu.svmOn = true) (hb : Svm.bit m.cpu.svmx.i4 b = true) :
    Svm.icpt4 b m = .error (.vmexit { code := 0x80 + b.toUInt64, nrip := m.cpu.eip.toUInt64 }) m := by
  simp [Svm.icpt4, h, hb, Svm.exitInstr]

theorem crRead_on {m : Machine} {n : UInt32} {info : UInt64} (h : m.cpu.svmOn = true)
    (hb : Svm.bit m.cpu.svmx.icr n = true) :
    Svm.crRead n info m = .error (.vmexit { code := n.toUInt64, info1 := info, nrip := m.cpu.eip.toUInt64 }) m := by
  simp [Svm.crRead, h, hb, Svm.exitInstr]

/-- CPUID (bit 18), HLT (bit 24), RDTSC (bit 14): exit codes 72h, 78h, 6Eh. -/
theorem cpuid_icpt {m : Machine} (h : m.cpu.svmOn = true) (hb : Svm.bit m.cpu.svmx.i3 18 = true) :
    Svm.icpt3 18 m = .error (.vmexit { code := 0x72, nrip := m.cpu.eip.toUInt64 }) m := icpt3_on h hb
theorem hlt_icpt {m : Machine} (h : m.cpu.svmOn = true) (hb : Svm.bit m.cpu.svmx.i3 24 = true) :
    Svm.icpt3 24 m = .error (.vmexit { code := 0x78, nrip := m.cpu.eip.toUInt64 }) m := icpt3_on h hb
theorem rdtsc_icpt {m : Machine} (h : m.cpu.svmOn = true) (hb : Svm.bit m.cpu.svmx.i3 14 = true) :
    Svm.icpt3 14 m = .error (.vmexit { code := 0x6E, nrip := m.cpu.eip.toUInt64 }) m := icpt3_on h hb

/-- Outside guest mode (or in SMM) the intercept checks change nothing. -/
theorem icpt3_off {m : Machine} {b : UInt32} (h : m.cpu.svmOn = false) : Svm.icpt3 b m = .ok () m := by
  simp [Svm.icpt3, h]
theorem icpt4_off {m : Machine} {b : UInt32} (h : m.cpu.svmOn = false) : Svm.icpt4 b m = .ok () m := by
  simp [Svm.icpt4, h]
theorem msr_off {m : Machine} {n : UInt32} {w : Bool} (h : m.cpu.svmOn = false) : Svm.msr n w m = .ok () m := by
  simp [Svm.msr, h]
theorem ioio_off {m : Machine} {p : UInt32} {sz : Sz} {a b c : Bool} {s : UInt8} {ad : Sz}
    (h : m.cpu.svmOn = false) : Svm.ioio p sz a b c s ad m = .ok () m := by
  simp [Svm.ioio, h]

theorem crRead_off {m : Machine} {n : UInt32} {i : UInt64} (h : m.cpu.svmOn = false) : Svm.crRead n i m = .ok () m := by
  simp [Svm.crRead, h]
theorem crWrite_off {m : Machine} {n : UInt32} {i : UInt64} (h : m.cpu.svmOn = false) : Svm.crWrite n i m = .ok () m := by
  simp [Svm.crWrite, h]
theorem cr0Write_off {m : Machine} {o n : UInt32} {i : UInt64} {l : Bool} (h : m.cpu.svmOn = false) :
    Svm.cr0Write o n i l m = .ok () m := by
  simp [Svm.cr0Write, h]
theorem drRead_off {m : Machine} {n g : UInt8} (h : m.cpu.svmOn = false) : Svm.drRead n g m = .ok () m := by
  simp [Svm.drRead, h]
theorem drWrite_off {m : Machine} {n g : UInt8} (h : m.cpu.svmOn = false) : Svm.drWrite n g m = .ok () m := by
  simp [Svm.drWrite, h]
theorem icpt5_off {m : Machine} {b : UInt32} {c : UInt64} (h : m.cpu.svmOn = false) : Svm.icpt5 b c m = .ok () m := by
  simp [Svm.icpt5, h]
theorem swint_off {m : Machine} {n : UInt8} (h : m.cpu.svmOn = false) : Svm.swint n m = .ok () m := by
  simp [Svm.swint, h]
theorem invlpg_off {m : Machine} {a : UInt32} (h : m.cpu.svmOn = false) : Svm.invlpg a m = .ok () m := by
  simp [Svm.invlpg, h]
theorem excInstr_off {m : Machine} {v : UInt8} (h : m.cpu.svmOn = false) : Svm.excInstr v m = .ok () m := by
  simp [Svm.excInstr, h]
theorem pause_off {m : Machine} (h : m.cpu.svmOn = false) : Svm.pause m = .ok () m := by
  simp [Svm.pause, h]
theorem mwait_off {m : Machine} {a : Bool} (h : m.cpu.svmOn = false) : Svm.mwait a m = .ok () m := by
  simp [Svm.mwait, h]
theorem taskSwitch_off {m : Machine} {sel : UInt16} {a b : Bool} {e : Option UInt32} (h : m.cpu.svmOn = false) :
    Svm.taskSwitch sel a b e m = .ok () m := by
  simp [Svm.taskSwitch, h]
theorem ferrFreeze_off {m : Machine} (h : m.cpu.svmOn = false) : Svm.ferrFreeze m = .ok () m := by
  simp [Svm.ferrFreeze, h]
theorem deliverAs_off {m : Machine} {i : UInt64} {act : M Unit} (h : m.cpu.svmOn = false) :
    Svm.deliverAs i act m = act m := by
  simp [Svm.deliverAs, h]
theorem wrmsrGuest_off {m : Machine} {n : UInt32} (h : m.cpu.svmOn = false) : Svm.wrmsrGuest n m = .ok () m := by
  simp [Svm.wrmsrGuest, h]
theorem guestTsc_off {c : Cpu} {t : UInt64} (h : c.svmOn = false) : Svm.guestTsc c t = t := by
  simp [Svm.guestTsc, h]
theorem guestScaled_off {c : Cpu} {t : UInt64} (h : c.svmOn = false) : Svm.guestScaled c t = t := by
  simp [Svm.guestScaled, h]
theorem vTprOn_off {c : Cpu} (h : c.svmOn = false) : Svm.vTprOn c = false := by
  simp [Svm.vTprOn, h]
theorem setVTpr_off {m : Machine} {v : UInt32} (h : m.cpu.svmOn = false) : Svm.setVTpr v m = .ok () m := by
  simp [Svm.setVTpr, modCpu, modM, h]
theorem excIntercepted_off {c : Cpu} {v : UInt8} (h : c.svmOn = false) : Svm.excIntercepted c v = false := by
  simp [Svm.excIntercepted, h]
theorem physIntrOk_off {c : Cpu} (h : c.svmOn = false) : c.physIntrOk = (c.eflags &&& Flag.IF != 0) := by
  simp [Cpu.physIntrOk, h]
theorem vintrReady_off {c : Cpu} (h : c.svmOn = false) : c.vintrReady = false := by
  simp [Cpu.vintrReady, h]

/-- Outside guest mode with GIF = 1 (and no timer, INIT/STARTUP or NMI message due) a step is
`stepAt`, the step of the event priorities, in which every SVM hook is the identity (the `*_off`
theorems above: an instruction's intercept checks, exception intercepts, TSC scaling and offset,
TPR virtualization, physical/virtual interrupt masking). This is the precise sense in which SVM
"changes nothing" outside guest mode; GIF = 0 outside guest mode is reached by CLGI (which needs
EFER.SVME) or SKINIT, and then `stepAtSvm` holds events (`stepAtSvm_gif0`). -/
theorem step_host {m : Machine} (ht : m.icount < m.timerAt) (hx : m.xev = false)
    (hg : m.cpu.svmx.guest = false) (hgif : m.cpu.svmx.gif = true) : step m = stepAt m := by
  have hle : ¬ (m.icount ≥ m.timerAt) := by
    intro h'; exact absurd ht (UInt64.not_lt.mpr h')
  simp [step, hle, smpEvent?, hx, hg, hgif]

/-! ## #VMEXIT restores the host state VMRUN saved -/

theorem withHost_hostOf (g c : Cpu) :
    let r := withHost g (hostOf c)
    r.es = c.es ∧ r.cs = c.cs ∧ r.ss = c.ss ∧ r.ds = c.ds ∧
    r.gdtBase = c.gdtBase ∧ r.gdtLimit = c.gdtLimit ∧ r.idtBase = c.idtBase ∧ r.idtLimit = c.idtLimit ∧
    r.efer = c.efer ∧ r.cr0 = c.cr0 ||| CR0.PE ∧ r.cr3 = c.cr3 ∧ r.cr4 = c.cr4 ∧
    r.eflags = c.eflags &&& ~~~(Flag.VM ||| Flag.RF) ∧ r.eip = c.eip ∧ r.esp = c.esp ∧ r.eax = c.eax ∧
    r.dr6 = c.dr6 ∧ r.dr7 = c.dr7 &&& ~~~0xFF ∧ specCtrlOf r = specCtrlOf c ∧
    r.svmx.guest = false ∧ r.svmx.gif = false := by
  simp [withHost, hostOf, withSpecCtrl, specCtrlOf, Cpu.setDr7]

/-! ## TLB: host and guest translations never meet -/

theorem enterGuestTlb_empty (m : Machine) (b : Bool) :
    (enterGuestTlb m b).tlbTag = Array.replicate tlbSize 0 := rfl

theorem enterGuestTlb_saves (m : Machine) :
    (enterGuestTlb m false).cpu.svmx.hostTlb.tag = m.tlbTag ∧
    (enterGuestTlb m false).cpu.svmx.hostTlb.val = m.tlbVal := ⟨rfl, rfl⟩

/-- #VMEXIT from guest mode reinstates the set-aside host entries and drops the guest's. -/
theorem leaveGuest_tlb {m : Machine} (hg : m.cpu.svmx.guest = true) (h1 : m.cpu.svmx.hostTlb.tag.size = tlbSize)
    (h2 : m.cpu.svmx.hostTlb.val.size = tlbSize) :
    (leaveGuest m).tlbTag = m.cpu.svmx.hostTlb.tag ∧ (leaveGuest m).tlbVal = m.cpu.svmx.hostTlb.val := by
  simp [leaveGuest, hg, h1, h2]

/-- End to end: after VMRUN set the host's TLB aside (`enterGuestTlb`, without the TLB_CONTROL flush)
and the guest ran — whatever it did to the machine's TLB, as long as the set-aside entries were not
touched (only INVLPGA of ASID 0, a guest write of a translation-affecting MSR and an SMI in the guest
change them, each a documented invalidation) — #VMEXIT gives the host exactly the TLB it had at
VMRUN. -/
theorem vmrun_exit_tlb {m m2 : Machine} (h1 : m.tlbTag.size = tlbSize) (h2 : m.tlbVal.size = tlbSize)
    (hg : m2.cpu.svmx.guest = true) (hs : m2.cpu.svmx.hostTlb = (enterGuestTlb m false).cpu.svmx.hostTlb) :
    (leaveGuest m2).tlbTag = m.tlbTag ∧ (leaveGuest m2).tlbVal = m.tlbVal := by
  have e := enterGuestTlb_saves m
  have ht : m2.cpu.svmx.hostTlb.tag = m.tlbTag := by rw [hs]; exact e.1
  have hv : m2.cpu.svmx.hostTlb.val = m.tlbVal := by rw [hs]; exact e.2
  have := leaveGuest_tlb (m := m2) hg (by rw [ht]; exact h1) (by rw [hv]; exact h2)
  rw [this.1, this.2, ht, hv]; exact ⟨rfl, rfl⟩

/-- #VMEXIT from a nested-paging guest gives the host its PAT back (gPAT replaced it at VMRUN), and
the host state VMRUN saved (`withHost_hostOf`); GIF = 0, guest mode ends. -/
theorem leaveGuest_pat {m : Machine} (hg : m.cpu.svmx.guest = true) (hn : m.cpu.svmx.np = true) :
    (leaveGuest m).cpu.sysx.pat = m.cpu.svmx.hostPat := by
  simp [leaveGuest, hg, hn, withHost, withSpecCtrl, Cpu.setDr7]

theorem leaveGuest_cpu (m : Machine) :
    ∃ g, (leaveGuest m).cpu = withHost g m.cpu.svmx.host := ⟨_, rfl⟩

/-- A VMEXIT_INVALID (VMRUN's consistency checks failed, not yet in guest mode) leaves the host's
TLB as it is. -/
theorem leaveGuest_invalid_tlb {m : Machine} (hg : m.cpu.svmx.guest = false) :
    (leaveGuest m).tlbTag = m.tlbTag ∧ (leaveGuest m).tlbVal = m.tlbVal := by
  simp [leaveGuest, hg]

theorem syncSmi_tc (m : Machine) : m.syncSmi.tlbTag = m.tlbTag ∧ m.syncSmi.cpu = m.cpu := by
  unfold Machine.syncSmi; split <;> exact ⟨rfl, rfl⟩
theorem lint0Sync_tc (m : Machine) : m.lint0Sync.tlbTag = m.tlbTag ∧ m.lint0Sync.cpu = m.cpu := by
  unfold Machine.lint0Sync; dsimp only
  simp only [Machine.syncXev]
  split <;> (try split) <;> simp [syncSmi_tc]
theorem syncIntr_tc (m : Machine) : m.syncIntr.tlbTag = m.tlbTag ∧ m.syncIntr.cpu = m.cpu := by
  unfold Machine.syncIntr; split <;> simp [lint0Sync_tc]
theorem syncApic_tc (m : Machine) : m.syncApic.tlbTag = m.tlbTag ∧ m.syncApic.cpu = m.cpu := by
  simp [Machine.syncApic, syncIntr_tc, Machine.syncXev, syncSmi_tc]

/-- INIT in a guest (not intercepted): the guest's TLB entries are gone and, with nested paging, the
host's PAT is back (`Svm.initRestore`; INIT itself changes neither, table 14-1). -/
theorem initCpu_guest_tlb {m : Machine} (hg : m.cpu.svmx.guest = true) :
    m.initCpu.tlbTag = Array.replicate tlbSize 0 := by
  simp [Machine.initCpu, hg, Machine.syncTimer, syncApic_tc]

theorem initCpu_guest_pat {m : Machine} (hg : m.cpu.svmx.guest = true) (hn : m.cpu.svmx.np = true) :
    m.initCpu.cpu.sysx.pat = m.cpu.svmx.hostPat := by
  simp [Machine.initCpu, hg, hn, Machine.syncTimer, syncApic_tc, Cpu.afterInit, initRestore, withSpecCtrl]

/-- With an empty TLB (a guest after VMRUN) a lookup always walks the tables. -/
theorem translate_emptyTlb {lin : UInt32} {w u f i : Bool} {m : Machine} (h1 : m.cpu.cr0 &&& CR0.PG ≠ 0)
    (ht : m.tlbTag = Array.replicate tlbSize 0) : translate lin w u f i m = walk lin w u f i m := by
  have hz : ∀ j : Nat, (Array.replicate tlbSize (0 : UInt32))[j]! = 0 := by
    intro j
    by_cases hj : j < tlbSize
    · rw [getElem!_pos (Array.replicate tlbSize (0 : UInt32)) j (by simpa using hj)]; simp
    · rw [getElem!_neg (Array.replicate tlbSize (0 : UInt32)) j (by simpa using hj)]; rfl
  have hne : ((0 : UInt32) == ((lin &&& 0xFFFFF000) ||| 1)) = false := by
    simp only [beq_eq_false_iff_ne]; bv_decide
  have h1' : (m.cpu.cr0 &&& CR0.PG == 0) = false := by simpa using h1
  simp only [translate, h1', ht, hz, hne, Bool.false_eq_true, ↓reduceIte]

/-! ## Nested walk -/

/-- 32-bit and PAE nested tables map nothing at or above 4 GiB. -/
theorem nestedWalk_above4g {m : Machine} {gpa : UInt64} {w f : Bool} {k : UInt64}
    (hm : m.cpu.svmx.nMode ≤ 2) (hg : (gpa >>> 32 != 0) = true) : ∃ e, nestedWalk gpa w f k m = .error e m := by
  unfold nestedWalk
  by_cases h1 : m.cpu.svmx.nMode ≤ 1
  · simp only [h1, decide_true, ↓reduceIte, hg]; exact ⟨_, rfl⟩
  · have h2 : m.cpu.svmx.nMode = 2 := by
      have := UInt8.le_iff_toNat_le.mp hm
      have h1' : ¬ m.cpu.svmx.nMode.toNat ≤ 1 := fun h => h1 (UInt8.le_iff_toNat_le.mpr h)
      apply UInt8.toNat_inj.mp; simp at this h1' ⊢; omega
    simp only [h1, h2, decide_false, Bool.false_eq_true, ↓reduceIte, hg]; exact ⟨_, rfl⟩

/-- With 32-bit nested tables the walk of a guest-physical address below 4 GiB fails unless the
entry of the nested page directory at nCR3 (a full system-physical address) that maps it is present. -/
theorem nestedWalk_pde_np {m : Machine} {gpa : UInt64} {w f : Bool} {k : UInt64}
    (hm : m.cpu.svmx.nMode ≤ 1) (hg : gpa >>> 32 = 0)
    (hp : rd32p m.mem ((m.cpu.svmx.ncr3 &&& 0xFFFFFFFFF000) + ((gpa.toUInt32 >>> 22) <<< 2).toUInt64) &&& 1 = 0) :
    ∃ e, nestedWalk gpa w f k m = .error e m := by
  have hp' : (rd32p m.mem ((m.cpu.svmx.ncr3 &&& 0xFFFFFFFFF000) + ((gpa.toUInt32 >>> 22) <<< 2).toUInt64) &&& 1
      == 0) = true := by simpa using hp
  have hg' : (gpa >>> 32 != 0) = false := by simpa using hg
  unfold nestedWalk
  simp only [hm, decide_true, ↓reduceIte, hg', Bool.false_eq_true, hp']
  exact ⟨_, rfl⟩

/-- A nested-table entry above 4 GiB reads as open bus (all ones), never as the memory at its low
alias: nCR3 is not truncated to 32 bits. -/
theorem rd32p_above {mem : ByteArray} {a : UInt64} (h : (a >>> 32 != 0) = true) : rd32p mem a = 0xFFFFFFFF := by
  unfold rd32p; rw [if_pos h]

/-! ## CPUID and SMM -/

theorem cpuid_svm_reachable (c : Cpu) :
    (cpuid c 0x80000001 0).2.2.1 &&& 4 ≠ 0 ∧ (cpuid c 0x80000000 0).1 = 0x8000000A ∧
    (cpuid c 0x8000000A 0).1 = 1 := by
  rw [cpuid_former, cpuid_former, cpuid_former]
  refine ⟨?_, ?_, ?_⟩
  · simp only [presentCpuid, sysALeaf]; simp [Cpuid.topoEcx81]; split <;> decide
  · simp [presentCpuid, sysALeaf]
  · simp [presentCpuid, sysALeaf]

theorem smmSave_host (c : Cpu) (h : c.svmx.guest = false) : ∀ p ∈ Svm.smmSave c, p.2 = 0 := by
  simp [Svm.smmSave, h]

theorem smmSave_guest (c : Cpu) (h : c.svmx.guest = true) :
    (Svm.smmSave c).lookup 0x7ED8 = some 1 ∧ (Svm.smmSave c).lookup 0x7EE0 = some c.svmx.vmcb := by
  simp [Svm.smmSave, h, List.lookup]

/-! ## Idle detection and EVENTINJ -/

/-- Only a valid EVENTINJ (V, bit 31) is an event: a stale value with V = 0 does not keep a halted
guest from being idle (`Machine.svmIdle`), as it is not taken by `stepAtSvm`. -/
theorem svmIdle_inject_v {m : Machine} (h : m.cpu.svmx.inject &&& 0x80000000 = 0) :
    m.svmIdle = ({ m with cpu := { m.cpu with svmx := { m.cpu.svmx with inject := 0 } } } : Machine).svmIdle := by
  simp [Machine.svmIdle, h, Cpu.physIntrOk, Cpu.vintrReady, Cpu.svmOn, Cpu.smiHeld]

/-! ## SVM MSRs cannot leave guest mode -/

/-- A computation that keeps SMM, guest mode and nested paging as they are. -/
def KeepsG (x : M α) : Prop :=
  ∀ m r m', x m = .ok r m' → m'.cpu.smm = m.cpu.smm ∧ m'.cpu.svmx.guest = m.cpu.svmx.guest ∧
    m'.cpu.svmx.np = m.cpu.svmx.np

theorem KeepsG.bind {x : M α} {f : α → M β} (hx : KeepsG x) (hf : ∀ a, KeepsG (f a)) : KeepsG (x >>= f) := by
  intro m r m' h
  change EStateM.bind x f m = _ at h
  unfold EStateM.bind at h
  split at h
  · rename_i a m1 h1
    obtain ⟨a1, a2, a3⟩ := hx _ _ _ h1
    obtain ⟨b1, b2, b3⟩ := hf a _ _ _ h
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩
  · cases h

theorem KeepsG.pure (a : α) : KeepsG (Pure.pure a : M α) := by
  intro m r m' h; simp [Pure.pure, EStateM.pure] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩

theorem KeepsG.rdCpu : KeepsG X86.cpu := by
  intro m r m' h; cases h; exact ⟨rfl, rfl, rfl⟩

theorem KeepsG.rdSvmx : KeepsG Svm.svmx := by
  intro m r m' h; cases h; exact ⟨rfl, rfl, rfl⟩

theorem KeepsG.gp {e : UInt32} : KeepsG (gp e : M α) := by
  intro m r m' h; cases h

theorem KeepsG.ite {c : Prop} [Decidable c] {x y : M α} (hx : KeepsG x) (hy : KeepsG y) :
    KeepsG (if c then x else y) := by
  split <;> assumption

theorem KeepsG.modCpu {f : Cpu → Cpu}
    (hf : ∀ c, (f c).smm = c.smm ∧ (f c).svmx.guest = c.svmx.guest ∧ (f c).svmx.np = c.svmx.np) :
    KeepsG (modCpu f) := by
  intro m r m' h; cases h; exact hf m.cpu

theorem KeepsG.modS {f : SvmState → SvmState} (hf : ∀ s, (f s).guest = s.guest ∧ (f s).np = s.np) :
    KeepsG (Svm.modS f) :=
  KeepsG.modCpu fun c => ⟨rfl, (hf c.svmx).1, (hf c.svmx).2⟩

theorem KeepsG.modM {f : Machine → Machine} (hf : ∀ m, (f m).cpu = m.cpu) : KeepsG (X86.modM f) := by
  intro m r m' h; cases h; rw [hf]; exact ⟨rfl, rfl, rfl⟩

/-- Every SVM MSR write (VM_CR, IGNNE, SMM_CTL, VM_HSAVE_PA, SVM_KEY, TSC_RATIO) keeps SMM, guest mode
and nested paging. -/
theorem svmMsr_wr_keeps {n : UInt32} {impl : MsrImpl} (v : UInt64) (hn : Svm.msr? n = some impl) :
    KeepsG (impl.wr v) := by
  simp only [Svm.msr?] at hn
  repeat' split at hn
  all_goals first | cases hn | skip
  all_goals
    simp only [Svm.vmCrMsr, Svm.ignneMsr, Svm.smmCtlMsr, Svm.hsaveMsr, Svm.svmKeyMsr, Svm.tscRatioMsr]
    repeat' first
      | apply KeepsG.bind | apply KeepsG.ite | exact KeepsG.gp | exact KeepsG.pure _ | exact KeepsG.rdCpu
      | exact KeepsG.rdSvmx | (apply KeepsG.modS; intro s; exact ⟨rfl, rfl⟩)
      | (apply KeepsG.modCpu; intro c; exact ⟨rfl, rfl, rfl⟩) | (apply KeepsG.modM; intro m; rfl)
      | intro _

/-- No write of an SVM MSR changes SMM, guest mode or nested paging, so a guest that may write them
(no MSR intercept) keeps its intercepts (`Cpu.svmOn`) and nested paging (`Cpu.npOn`); in particular
SMM_CTL's ENTER does not enter SMM. (The other writers of these fields: `Cpu.smm` by SMI entry and
RSM, `guest`/`np` by VMRUN, #VMEXIT (`withHost`), INIT (`SvmState.afterInit`) and SKINIT, none an MSR
write.) -/
theorem svmMsr_keeps_svmOn {n : UInt32} {impl : MsrImpl} {v : UInt64} {m m' : Machine} {r : Unit}
    (hn : Svm.msr? n = some impl) (hw : impl.wr v m = .ok r m') :
    m'.cpu.svmOn = m.cpu.svmOn ∧ m'.cpu.npOn = m.cpu.npOn := by
  obtain ⟨h1, h2, h3⟩ := svmMsr_wr_keeps v hn m r m' hw
  simp [Cpu.svmOn, Cpu.npOn, h1, h2, h3]

/-- A guest write of a translation-affecting MSR only drops the host's set-aside TLB entries. -/
theorem wrmsrGuest_keeps (n : UInt32) : KeepsG (Svm.wrmsrGuest n) := by
  intro m r m' h; simp only [Svm.wrmsrGuest] at h; split at h <;> (cases h; exact ⟨rfl, rfl, rfl⟩)

end X86
