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

/-- The former CPUID (`Exec.cpuidVals` with `addSimd`), for reference, plus the feature bits that
workstreams have implemented since (marked with their owner). -/
def formerCpuid (leaf : UInt32) : Regs :=
  match leaf with
  | 0 => (1, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 0x80000000 => (0x80000001, 0, 0, 0)
  | 0x80000001 => (0, 0, 0xC0, 1 <<< 20)  -- Sse: SSE4A, MisAlignSse
  | _ => (0x00000619, 0, 0x00180201, 0x07808365)  -- Sse: SSE3, SSSE3, SSE4.1, SSE4.2

theorem legacyMax_former : Cpuid.legacyMax = (1, 0x80000001) := by decide

theorem cpuid_former (c : Cpu) (leaf sub : UInt32) : cpuid c leaf sub = formerCpuid leaf := by
  have h12 : Cpuid.featBits 1 0 2 true = 0x00180201 := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x07808365 := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0xC0 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = 1 <<< 20 := by decide
  have hx : implemented .xsave = false := rfl
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, formerCpuid]
  by_cases h0 : leaf = 0
  · subst h0; simp
  by_cases h1 : leaf = 1
  · subst h1; simp [h12, h13, hx]
  by_cases h8 : leaf = 0x80000000
  · subst h8; simp
  by_cases h9 : leaf = 0x80000001
  · subst h9; simp [he2, he3]
  have hr : (leaf ≤ 1 || (0x80000000 ≤ leaf && leaf ≤ 0x80000001)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
    constructor
    · intro hle
      have : leaf.toNat ≤ 1 := hle
      have : leaf.toNat = 0 ∨ leaf.toNat = 1 := by omega
      rcases this with h | h
      · exact h0 (UInt32.toNat_inj.mp (by simpa using h))
      · exact h1 (UInt32.toNat_inj.mp (by simpa using h))
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
  simp only [hr, Bool.false_eq_true, ↓reduceIte, h0, h1, h8, h9]
  simp [h12, h13, hx]

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
