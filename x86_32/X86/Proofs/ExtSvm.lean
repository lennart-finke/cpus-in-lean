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
* `stepAtSvm_gif0`: with GIF = 0 (no injected event pending, no trace trap pending) a step takes no
  INTR, NMI, SMI or virtual interrupt: it is the instruction step.
* `icpt3_on`, `icpt4_on`, `crRead_on`: an intercepted instruction ends with its #VMEXIT before it
  changes anything (the machine is unchanged, EXITCODE and nRIP as the APM specifies); instances for
  CPUID, HLT and RDTSC are the bits 18, 24 and 14 (`cpuid_icpt`, `hlt_icpt`, `rdtsc_icpt`).
* `icpt3_off`, `icpt4_off`, `msr_off`, `ioio_off`: outside guest mode every intercept check is a
  no-op; `step_host`: outside guest mode with GIF = 1 a step is the pre-SVM `stepAt`.
* `withHost_hostOf`: #VMEXIT restores exactly the host state VMRUN saved (segments ES/CS/SS/DS,
  GDTR, IDTR, EFER, CR0 (PE forced), CR3, CR4, RFLAGS (VM and RF cleared), RIP, RSP, RAX, DR6, DR7
  with the breakpoints disabled, SPEC_CTRL), whatever the guest did to the CPU state.
* `enterGuestTlb_empty`, `enterGuestTlb_saves`, `restoreHostTlb_tags`, `translate_emptyTlb`: VMRUN
  sets the host's TLB entries aside and the guest starts with an empty TLB, so its first lookups walk
  the tables; #VMEXIT reinstates exactly the host's entries. Host and guest translations never meet
  in the machine's TLB.
* `nestedWalk_above4g`, `nestedWalk_pde_np`: the nested walk with 32-bit or PAE nested tables maps
  nothing at or above 4 GiB, and with 32-bit tables succeeds only through a present entry of the page
  directory at nCR3 (what the walk can reach starts at nCR3).
* `cpuid_svm_reachable`: with the legacy identity CPUID reports SVM (8000_0001 ECX bit 2) and the
  SVM leaf 8000_000A is reachable (the maximum extended leaf is 8000_000A; SVM revision 1).
* `smmSave_host`, `smmSave_guest`: SMM entry outside guest mode writes every SVM field of the AMD64
  state-save map as 0; in guest mode SVM Guest = 1 and the VMCB address (15.22, table 10-1).
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

/-- With GIF = 0 no INTR, NMI, SMI or virtual interrupt is taken (table 15-10): unless VMRUN left an
event to inject or a trace trap is pending, the step is the instruction step. -/
theorem stepAtSvm_gif0 {m : Machine} (hg : m.cpu.svmx.gif = false)
    (hi : m.cpu.svmx.inject &&& 0x80000000 = 0) (hd : m.dbPend &&& ~~~0xF = 0) :
    ∃ m', stepAtSvm m = stepInstr m' := by
  unfold stepAtSvm
  simp only [hg, hi, hd, Cpu.vintrReady, bne_self_eq_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  split <;> exact ⟨_, rfl⟩

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

/-- Outside guest mode with GIF = 1 (and no timer, INIT/STARTUP or NMI message due) a step is the
pre-SVM step `stepAt` of the event priorities. -/
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

theorem restoreHostTlb_tags {m : Machine} (h1 : m.cpu.svmx.hostTlb.tag.size = tlbSize)
    (h2 : m.cpu.svmx.hostTlb.val.size = tlbSize) :
    ∃ m', restoreHostTlb m = .ok () m' ∧ m'.tlbTag = m.cpu.svmx.hostTlb.tag ∧
      m'.tlbVal = m.cpu.svmx.hostTlb.val := by
  simp [restoreHostTlb, modM, h1, h2]

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
entry of the nested page directory at nCR3 that maps it is present. -/
theorem nestedWalk_pde_np {m : Machine} {gpa : UInt64} {w f : Bool} {k : UInt64}
    (hm : m.cpu.svmx.nMode ≤ 1) (hg : gpa >>> 32 = 0)
    (hp : rdBytes m.mem ((m.cpu.svmx.ncr3.toUInt32 &&& 0xFFFFF000) + ((gpa.toUInt32 >>> 22) <<< 2)) 4 &&& 1 = 0) :
    ∃ e, nestedWalk gpa w f k m = .error e m := by
  have hp' : (rdBytes m.mem ((m.cpu.svmx.ncr3.toUInt32 &&& 0xFFFFF000) + ((gpa.toUInt32 >>> 22) <<< 2)) 4 &&& 1
      == 0) = true := by simpa using hp
  have hg' : (gpa >>> 32 != 0) = false := by simpa using hg
  unfold nestedWalk
  simp only [hm, decide_true, ↓reduceIte, hg', Bool.false_eq_true, hp']
  exact ⟨_, rfl⟩

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

end X86
