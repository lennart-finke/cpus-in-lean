import X86.Dispatch
import Std.Tactic.BVDecide
import X86.Proofs.Basic
/-!
# System extensions A (`X86/Ext/Sys.lean`, paging and alignment in `X86/Machine.lean`)

* SMEP/SMAP decision (`smAllowed`): `smAllowed_user` (user accesses are never restricted),
  `smAllowed_smep` (with CR4.SMEP no supervisor fetch from a user page), `smAllowed_smap` (with
  CR4.SMAP a supervisor data access to a user page needs an explicit access with EFLAGS.AC = 1),
  `smAllowed_smap_implicit` (implicit accesses are checked whatever AC is), `smAllowed_off`.
* Through the TLB: `translate_hit_smep`, `translate_hit_smap` (a cached user translation never
  satisfies a supervisor fetch with SMEP, or a supervisor data access refused by SMAP: `translate`
  walks the tables, which fault).
* Through the walk: `walk32_large_smep` (a 4 MiB user page: a supervisor fetch with SMEP faults
  with P = 1 and I/D = 1).
* UMIP: `umipCheck_gp` (#GP(0) at CPL > 0 with CR4.UMIP, nothing changed), `umipCheck_cpl0`.
* SYSENTER/SYSEXIT/SYSCALL/SYSRET: `sysenter_real` (#UD), `sysenter_null` (#GP(0)),
  `sysenter_cpl0` (lands at CPL 0 with IF = VM = 0), `sysexit_cpl` (#GP(0) at CPL > 0),
  `sysexit_cpl3` (returns to CPL 3), `syscall_nosce`/`sysret_nosce` (#UD with EFER.SCE = 0),
  `syscall_cpl0`, `sysret_cpl` (#GP(0) at CPL > 0), `sysret_cpl3`.
* CLAC/STAC: `clacStac_cpl` (#UD at CPL > 0), `clac_clears`.
* #AC: `acChk_super` (never for supervisor/implicit accesses), `acChk_aligned` (never for an aligned
  operand), `acChk_fault` (#AC(0) for a misaligned CPL-3 access with CR0.AM and EFLAGS.AC),
  `acChk_disabled`.
-/
namespace X86

/-! ## SMEP / SMAP -/

theorem smAllowed_user (perm cr4 fl : UInt32) (f i : Bool) : smAllowed perm cr4 fl true f i = true := by
  simp [smAllowed]

/-- With CR4.SMEP, a supervisor instruction fetch is only allowed from a supervisor page. -/
theorem smAllowed_smep {perm cr4 fl : UInt32} {i : Bool} (h : smAllowed perm cr4 fl false true i = true)
    (hs : cr4 &&& CR4.SMEP ≠ 0) : perm &&& 4 = 0 := by
  simp [smAllowed, smPass, hs] at h
  exact h

/-- With CR4.SMAP, a supervisor data access to a user page is allowed only as an explicit access with
EFLAGS.AC = 1. -/
theorem smAllowed_smap {perm cr4 fl : UInt32} {i : Bool} (h : smAllowed perm cr4 fl false false i = true)
    (hs : cr4 &&& CR4.SMAP ≠ 0) (hu : perm &&& 4 ≠ 0) : i = false ∧ fl &&& Flag.AC ≠ 0 := by
  simp [smAllowed, smPass, hs, hu] at h
  exact h

/-- Implicit supervisor accesses (descriptor tables, IDT, TSS) to user pages are refused with SMAP
whatever EFLAGS.AC is (AMD APM vol. 2, 5.6.6). -/
theorem smAllowed_smap_implicit (perm cr4 fl : UInt32) (hs : cr4 &&& CR4.SMAP ≠ 0) (hu : perm &&& 4 ≠ 0) :
    smAllowed perm cr4 fl false false true = false := by
  simp [smAllowed, smPass, hs, hu]

/-- Without SMEP and SMAP nothing is restricted. -/
theorem smAllowed_off (perm cr4 fl : UInt32) (u f i : Bool) (h : cr4 &&& (CR4.SMEP ||| CR4.SMAP) = 0) :
    smAllowed perm cr4 fl u f i = true := by
  have h1 : cr4 &&& CR4.SMEP = 0 := by simp [CR4.SMEP, CR4.SMAP] at *; bv_decide
  have h2 : cr4 &&& CR4.SMAP = 0 := by simp [CR4.SMEP, CR4.SMAP] at *; bv_decide
  cases f <;> simp [smAllowed, smPass, h1, h2]

/-- The TLB never satisfies a supervisor instruction fetch from a cached user translation while
CR4.SMEP is set: `translate` walks the page tables instead (which raise the #PF). -/
theorem translate_hit_smep {lin : UInt32} {w i : Bool} {m : Machine}
    (hpg : m.cpu.cr0 &&& CR0.PG ≠ 0)
    (htag : m.tlbTag[((lin >>> 12) % tlbSize.toUInt32).toNat]! = ((lin &&& 0xFFFFF000) ||| 1))
    (hu : m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.U ≠ 0)
    (hs : m.cpu.cr4 &&& CR4.SMEP ≠ 0) :
    translate lin w false true i m = walk lin w false true i m := by
  have h1 : (m.cpu.cr0 &&& CR0.PG == 0) = false := by simpa using hpg
  have h2 : (m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.U == 0) = false := by simpa using hu
  have h3 : (m.cpu.cr4 &&& CR4.SMEP == 0) = false := by simpa using hs
  simp only [translate, h1, htag, h2, smPass, h3, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    Bool.false_or, Bool.false_and]

/-- The TLB never satisfies a supervisor data access to a cached user translation that SMAP refuses
(an implicit access, or EFLAGS.AC = 0): `translate` walks the page tables instead. -/
theorem translate_hit_smap {lin : UInt32} {w i : Bool} {m : Machine}
    (hpg : m.cpu.cr0 &&& CR0.PG ≠ 0)
    (htag : m.tlbTag[((lin >>> 12) % tlbSize.toUInt32).toNat]! = ((lin &&& 0xFFFFF000) ||| 1))
    (hu : m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.U ≠ 0)
    (hs : m.cpu.cr4 &&& CR4.SMAP ≠ 0) (hac : i = true ∨ m.cpu.eflags &&& Flag.AC = 0) :
    translate lin w false false i m = walk lin w false false i m := by
  have h1 : (m.cpu.cr0 &&& CR0.PG == 0) = false := by simpa using hpg
  have h2 : (m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.U == 0) = false := by simpa using hu
  have h3 : (m.cpu.cr4 &&& CR4.SMAP == 0) = false := by simpa using hs
  have h4 : (!i && m.cpu.eflags &&& Flag.AC != 0) = false := by
    rcases hac with h | h <;> simp [h]
  simp only [translate, h1, htag, h2, smPass, h3, h4, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    Bool.false_or, Bool.false_and, Bool.or_false]

/-- A supervisor instruction fetch through a present 4 MiB user PDE (U/S = 1, bit 21 clear) with
CR4.PSE and CR4.SMEP faults: #PF with P = 1 (protection) and I/D = 1, and the machine is unchanged. -/
theorem walk32_large_smep {lin : UInt32} {w i : Bool} {m : Machine}
    (hpde1 : rdBytes m.mem (pdeAddr m.cpu lin) 4 &&& 1 ≠ 0)
    (hps : rdBytes m.mem (pdeAddr m.cpu lin) 4 &&& 0x80 ≠ 0)
    (hrsv : rdBytes m.mem (pdeAddr m.cpu lin) 4 &&& pse4mRsvd = 0)
    (huser : rdBytes m.mem (pdeAddr m.cpu lin) 4 &&& 4 ≠ 0)
    (hpse : m.cpu.cr4 &&& CR4.PSE ≠ 0) (hsmep : m.cpu.cr4 &&& CR4.SMEP ≠ 0) :
    ∃ e, walk32 lin w false true i m = .error (.exc Vec.PF (some e) lin) m ∧ e &&& 0x11 = 0x11 := by
  generalize hp : rdBytes m.mem (pdeAddr m.cpu lin) 4 = pde at *
  have a1 : (pde &&& 1 == 0) = false := by simpa using hpde1
  have a2 : (pde &&& 0x80 != 0) = true := by simpa using hps
  have a3 : (m.cpu.cr4 &&& CR4.PSE != 0) = true := by simpa using hpse
  have a4 : (pde &&& pse4mRsvd != 0) = false := by simpa using hrsv
  have a5 : (pde &&& 4 == 0) = false := by simpa using huser
  have a6 : (m.cpu.cr4 &&& CR4.SMEP == 0) = false := by simpa using hsmep
  have a7 : (m.cpu.cr4 &&& CR4.SMEP != 0) = true := by simpa using hsmep
  refine ⟨pfErr w false true false true, ?_, ?_⟩
  · simp only [walk32, hp, a1, a2, a3, a4, a7, Bool.and_self, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, smAllowed, smPass, a5, a6, Bool.false_or, Bool.not_false, Bool.or_true]
  · cases w <;> simp [pfErr] <;> decide

/-! ## UMIP -/

theorem umipCheck_gp {m : Machine} (hu : m.cpu.cr4 &&& CR4.UMIP ≠ 0) (hc : m.cpu.cpl ≠ 0) :
    umipCheck m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [umipCheck, cpu, bind, EStateM.bind, hu, hc, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem umipCheck_cpl0 {m : Machine} (hc : m.cpu.cpl = 0) : umipCheck m = .ok () m := by
  simp [umipCheck, cpu, bind, EStateM.bind, hc, pure, EStateM.pure]

/-! ## SYSENTER / SYSEXIT / SYSCALL / SYSRET -/

namespace Sys

theorem sysenter_real {m : Machine} (h : m.cpu.pe = false) :
    sysenter m = .error (.exc Vec.UD none 0) m := by
  simp [sysenter, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem sysenter_null {m : Machine} (hp : m.cpu.pe = true) (h : m.cpu.sysx.sysenterCs &&& 0xFFFC = 0) :
    sysenter m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [sysenter, cpu, bind, EStateM.bind, hp, h, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- SYSENTER enters CPL 0 (the RPL of the new CS is 0) with interrupts disabled, outside virtual-8086
mode, at SYSENTER_EIP. -/
theorem sysenter_cpl0 {m m' : Machine} (h : sysenter m = .ok () m') :
    m'.cpu.cs.sel.toUInt32 &&& 3 = 0 ∧ m'.cpu.eflags &&& (Flag.IF ||| Flag.VM) = 0 ∧
      m'.cpu.eip = m.cpu.sysx.sysenterEip ∧ m'.cpu.esp = m.cpu.sysx.sysenterEsp := by
  by_cases hp : m.cpu.pe = true
  · by_cases hn : m.cpu.sysx.sysenterCs &&& 0xFFFC = 0
    · simp [sysenter, cpu, bind, EStateM.bind, hp, hn, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    · simp [sysenter, cpu, bind, EStateM.bind, hp, hn, modCpu] at h
      subst h
      simp only [flatCode]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> (try simp only [Flag.IF, Flag.VM, Flag.RF]) <;> bv_decide
  · simp [sysenter, cpu, bind, EStateM.bind, hp, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

theorem sysexit_cpl {m : Machine} (h : m.cpu.cpl ≠ 0) :
    sysexit m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [sysexit, cpu, bind, EStateM.bind, h, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- SYSEXIT returns to CPL 3 (RPL 3 of the new CS and SS) at EDX with ESP = ECX. -/
theorem sysexit_cpl3 {m m' : Machine} (h : sysexit m = .ok () m') :
    m'.cpu.cs.sel.toUInt32 &&& 3 = 3 ∧ m'.cpu.ss.sel.toUInt32 &&& 3 = 3 ∧ m'.cpu.eip = m.cpu.edx ∧
      m'.cpu.esp = m.cpu.ecx := by
  by_cases hp : (!m.cpu.pe || m.cpu.vm86 || m.cpu.cpl != 0) = true
  · simp [sysexit, cpu, bind, EStateM.bind, hp, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · by_cases hn : m.cpu.sysx.sysenterCs &&& 0xFFFC = 0
    · simp [sysexit, cpu, bind, EStateM.bind, hp, hn, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    · simp only [Bool.not_eq_true] at hp
      simp [sysexit, cpu, bind, EStateM.bind, hp, hn, modCpu] at h
      subst h
      simp only [flatCode, flatStack]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> bv_decide

theorem syscall_nosce {m : Machine} (h : m.cpu.efer &&& EFER.SCE = 0) :
    syscall m = .error (.exc Vec.UD none 0) m := by
  simp [syscall, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem sysret_nosce {m : Machine} (h : m.cpu.efer &&& EFER.SCE = 0) :
    sysret m = .error (.exc Vec.UD none 0) m := by
  simp [sysret, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- SYSCALL enters CPL 0 at STAR[31:0] with interrupts disabled and the return address in ECX. -/
theorem syscall_cpl0 {m m' : Machine} (h : syscall m = .ok () m') :
    m'.cpu.cs.sel.toUInt32 &&& 3 = 0 ∧ m'.cpu.eflags &&& (Flag.IF ||| Flag.VM) = 0 ∧
      m'.cpu.ecx = m.cpu.eip ∧ m'.cpu.eip = m.cpu.sysx.star.toUInt32 := by
  by_cases hs : m.cpu.efer &&& EFER.SCE = 0
  · simp [syscall, cpu, bind, EStateM.bind, hs, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · simp [syscall, cpu, bind, EStateM.bind, hs, modCpu] at h
    subst h
    simp only [flatCode]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> (try simp only [Flag.IF, Flag.VM, Flag.RF]) <;> bv_decide

theorem sysret_cpl {m : Machine} (hs : m.cpu.efer &&& EFER.SCE ≠ 0) (h : m.cpu.cpl ≠ 0) :
    sysret m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [sysret, cpu, bind, EStateM.bind, hs, h, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- SYSRET returns to CPL 3 at ECX with interrupts enabled. -/
theorem sysret_cpl3 {m m' : Machine} (h : sysret m = .ok () m') :
    m'.cpu.cs.sel.toUInt32 &&& 3 = 3 ∧ m'.cpu.eflags &&& Flag.IF ≠ 0 ∧ m'.cpu.eip = m.cpu.ecx := by
  by_cases hs : m.cpu.efer &&& EFER.SCE = 0
  · simp [sysret, cpu, bind, EStateM.bind, hs, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · by_cases hp : (!m.cpu.pe || m.cpu.vm86 || m.cpu.cpl != 0) = true
    · simp [sysret, cpu, bind, EStateM.bind, hs, hp, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    · simp only [Bool.not_eq_true] at hp
      simp [sysret, cpu, bind, EStateM.bind, hs, hp, modCpu] at h
      subst h
      simp only [flatCode]
      refine ⟨?_, ?_, ?_⟩ <;> (try trivial) <;> (try simp only [Flag.IF, Flag.RF]) <;> bv_decide

/-! ## CLAC / STAC -/

theorem clacStac_cpl {m : Machine} {s : Bool} (h : m.cpu.cpl ≠ 0) :
    clacStac s m = .error (.exc Vec.UD none 0) m := by
  simp [clacStac, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem clac_clears {m m' : Machine} (h : clacStac false m = .ok () m') : m'.cpu.eflags &&& Flag.AC = 0 := by
  by_cases hp : (m.cpu.vm86 || m.cpu.cpl != 0) = true
  · simp [clacStac, cpu, bind, EStateM.bind, hp, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · simp only [Bool.not_eq_true] at hp
    simp [clacStac, cpu, bind, EStateM.bind, hp, setFlags, modCpu, Cpu.setFlags] at h
    subst h
    simp only [Flag.AC]; bv_decide

end Sys

/-! ## Alignment check -/

/-- Supervisor accesses (CPL 0..2, and implicit accesses at any CPL, which pass `user = false`) are
never alignment-checked. -/
theorem acChk_super (lin al : UInt32) (m : Machine) : acChk lin al false m = .ok () m := by
  simp [acChk, pure, EStateM.pure]

theorem acChk_aligned {lin al : UInt32} {u : Bool} (m : Machine) (h : lin &&& (al - 1) = 0) :
    acChk lin al u m = .ok () m := by
  simp [acChk, h, pure, EStateM.pure]

theorem acChk_disabled {lin al : UInt32} {u : Bool} {m : Machine}
    (h : m.cpu.cr0 &&& CR0.AM = 0 ∨ m.cpu.eflags &&& Flag.AC = 0) : acChk lin al u m = .ok () m := by
  unfold acChk
  split
  · rcases h with h | h <;> simp [acCheck, h]
  · rfl

/-- A misaligned access at CPL 3 with CR0.AM = EFLAGS.AC = 1 raises #AC(0) before anything changes. -/
theorem acChk_fault {lin al : UInt32} {m : Machine} (ha : lin &&& (al - 1) ≠ 0)
    (hm : m.cpu.cr0 &&& CR0.AM ≠ 0) (hf : m.cpu.eflags &&& Flag.AC ≠ 0) :
    acChk lin al true m = .error (.exc Vec.AC (some 0) 0) m := by
  simp [acChk, acCheck, ha, hm, hf]

end X86
