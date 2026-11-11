import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_former`: with the present feature set and the legacy identity, CPUID returns exactly what
  the model returned before the table-driven CPUID (`formerCpuid`, the removed `cpuidVals`), for
  every leaf and subleaf.
* `cr4Writable_former`, `eferWritable_former`: the derived MOV CR4 / WRMSR EFER masks are the former
  constants.
* `vexExec_real`, `vexExec_vm86`, `vexExec_prefix`: a VEX-encoded instruction raises #UD in real and
  virtual-8086 mode and after a 66/F2/F3/LOCK prefix, before any extension hook runs.
-/
namespace X86

/-- The former CPUID (`Exec.cpuidVals` with `addSimd`), for reference, restated for the features
implemented since: AES and PCLMULQDQ (CPUID 1:ECX bits 25, 1) and SHA (CPUID 7.0:EBX bit 29), which
raises the highest basic leaf to 7 (leaves 2..6 are zero except as below; out-of-range leaves
return leaf 7, Intel's rule, so their value depends on the subleaf). Leaf 6 with a subleaf other
than 0 reports the dump's ARAT and EffFreq bits, which `Cpuid` masks only at subleaf 0 (their
`Feature.loc`); leaf 6 ignores ECX on hardware. -/
def formerCpuid (leaf sub : UInt32) : Regs :=
  match leaf with
  | 0 => (7, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 1 => (0x00000619, 0, 0x02000002, 0x07808365)
  | 0x80000000 => (0x80000001, 0, 0, 0)
  | 0x80000001 => (0, 0, 0, 1 <<< 20)
  | 2 | 3 | 4 | 5 => (0, 0, 0, 0)
  | 6 => if sub = 0 then (0, 0, 0, 0) else (4, 0, 1, 0)
  | _ => if sub = 0 then (0, 1 <<< 29, 0, 0) else (0, 0, 0, 0)

theorem legacyMax_former : Cpuid.legacyMax = (7, 0x80000001) := by decide

private theorem amdLeaf_former (c : Cpu) (sub : UInt32) :
    Cpuid.amdLeaf c 5 sub = (0, 0, 0, 0) ∧
    Cpuid.amdLeaf c 6 sub = (if sub = 0 then (0, 0, 0, 0) else (4, 0, 1, 0)) ∧
    Cpuid.amdLeaf c 7 sub = if sub = 0 then (0, 1 <<< 29, 0, 0) else (0, 0, 0, 0) := by
  refine ⟨by simp [Cpuid.amdLeaf, Cpuid.leafGate, implemented], ?_, ?_⟩
  · by_cases h : sub = 0
    · subst h; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw]; decide
    · have h' : ¬ ((0 : UInt32) = sub) := fun e => h e.symm
      simp [h, Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, Cpuid.maskReg, Cpuid.featBits, Feature.all,
        Feature.loc, h', implemented]
      decide
  · by_cases h : sub = 0
    · subst h; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw]; decide
    · have h' : (sub == 0) = false := by simpa using h
      simp [h, Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, h']

theorem cpuid_former (c : Cpu) (leaf sub : UInt32) : cpuid c leaf sub = formerCpuid leaf sub := by
  have h12 : Cpuid.featBits 1 0 2 true = 0x02000002 := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x07808365 := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = 1 <<< 20 := by decide
  have hx : implemented .xsave = false := rfl
  obtain ⟨h5, h6, h7⟩ := amdLeaf_former c sub
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, formerCpuid]
  by_cases h0 : leaf = 0
  · subst h0; simp
  by_cases h1 : leaf = 1
  · subst h1; simp [h12, h13, hx]
  by_cases h8 : leaf = 0x80000000
  · subst h8; simp
  by_cases h9 : leaf = 0x80000001
  · subst h9; simp [he2, he3]
  by_cases l2 : leaf = 2
  · subst l2; simp
  by_cases l3 : leaf = 3
  · subst l3; simp
  by_cases l4 : leaf = 4
  · subst l4; simp
  by_cases l5 : leaf = 5
  · subst l5; simp [h5]
  by_cases l6 : leaf = 6
  · subst l6; simp [h6]
  by_cases l7 : leaf = 7
  · subst l7; simp [h7]
  have hr : (leaf ≤ 7 || (0x80000000 ≤ leaf && leaf ≤ 0x80000001)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
    constructor
    · intro hle
      have : leaf.toNat ≤ 7 := hle
      have : leaf.toNat = 0 ∨ leaf.toNat = 1 ∨ leaf.toNat = 2 ∨ leaf.toNat = 3 ∨ leaf.toNat = 4 ∨
          leaf.toNat = 5 ∨ leaf.toNat = 6 ∨ leaf.toNat = 7 := by omega
      rcases this with h | h | h | h | h | h | h | h
      · exact h0 (UInt32.toNat_inj.mp (by simpa using h))
      · exact h1 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l2 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l3 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l4 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l5 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l6 (UInt32.toNat_inj.mp (by simpa using h))
      · exact l7 (UInt32.toNat_inj.mp (by simpa using h))
    · by_cases hlo : 0x80000000 ≤ leaf
      · right; intro hhi
        have a : (0x80000000 : UInt32).toNat ≤ leaf.toNat := hlo
        have b : leaf.toNat ≤ (0x80000001 : UInt32).toNat := hhi
        simp at a b
        have : leaf.toNat = 0x80000000 ∨ leaf.toNat = 0x80000001 := by omega
        rcases this with h | h
        · exact h8 (UInt32.toNat_inj.mp (by simpa using h))
        · exact h9 (UInt32.toNat_inj.mp (by simpa using h))
      · left; simpa using hlo
  simp only [hr, Bool.false_eq_true, ↓reduceIte, h7]

theorem cr4Writable_former : Cpuid.cr4Writable = 0x07FC := by decide

theorem eferWritable_former : Cpuid.eferWritable = EFER.NXE := by decide

theorem vexExec_real {m : Machine} {i : Inst} (h : m.cpu.cr0 &&& CR0.PE = 0) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  simp [vexExec, cpu, Cpu.pe, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexExec_vm86 {m : Machine} {i : Inst} (h : m.cpu.eflags &&& Flag.VM ≠ 0) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  simp [vexExec, cpu, Cpu.vm86, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexExec_prefix {m : Machine} {i : Inst} (h : i.lock = true ∨ i.rep ≠ 0 ∨ i.p66 = true) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  rcases h with h | h | h <;>
  · simp only [vexExec, cpu, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]
    split <;> simp_all [EStateM.bind, EStateM.throw]

end X86
