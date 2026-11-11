import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_former`: with the present feature set and the legacy identity, CPUID leaves 0, 1,
  0x80000000 and 0x80000001 return what the model returned before the table-driven CPUID (the
  removed `cpuidVals`) plus the bits of the implemented features (`formerCpuid`); leaf 1 with
  CR4.OSXSAVE = 0 (with it, ECX[27] is set: `Xsave.cpuid_osxsave_legacy`).
* `cr4Writable_former`, `eferWritable_former`: the derived MOV CR4 / WRMSR EFER masks are the former
  constants.
* `vexExec_real`, `vexExec_vm86`, `vexExec_prefix`: a VEX-encoded instruction raises #UD in real and
  virtual-8086 mode and after a 66/F2/F3/LOCK prefix, before any extension hook runs.
-/
namespace X86

/-- CPUID of the legacy identity for leaves 0, 1, 0x80000000 and 0x80000001: the former values
(`Exec.cpuidVals` with `addSimd`) plus the bits of the implemented Gpr features (leaf 1: MONITOR,
MOVBE, POPCNT, RDRAND, CLFSH with its line size in EBX; Crypto: AES, PCLMULQDQ; 8000_0001: ABM, PREFETCHW, MONITORX, RDTSCP)
and the higher maximum leaves (0xD and 8000_0008) they need, of the Sse features (leaf 1: SSE3,
SSSE3, SSE4.1, SSE4.2; 8000_0001: SSE4A, MisAlignSse) and of XSAVE (leaf 1 ECX[26]; ECX[27] is
CR4.OSXSAVE, 0 here). Leaf 7: `cpuid_leaf7_gpr` (Proofs/ExtGpr.lean). -/
def formerCpuid (leaf : UInt32) : Regs :=
  match leaf with
  | 0 => (0xD, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 0x80000000 => (0x80000008, 0, 0, 0)
  | 0x80000001 => (0, 0, 0x200001E0, (1 <<< 20) ||| (1 <<< 27))
  | _ => (0x00000619, 0x800, 0x46D8020B, 0x07888365)

theorem legacyMax_former : Cpuid.legacyMax = (0xD, 0x80000008) := by decide +kernel

theorem cpuid_former (c : Cpu) (leaf sub : UInt32)
    (h : leaf = 0 ∨ leaf = 1 ∨ leaf = 0x80000000 ∨ leaf = 0x80000001)
    (hos : c.cr4 &&& CR4.OSXSAVE = 0) :
    cpuid c leaf sub = formerCpuid leaf := by
  have h12 : Cpuid.featBits 1 0 2 true = 0x46D8020B := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x07888365 := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0x200001E0 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = (1 <<< 20) ||| (1 <<< 27) := by
    decide
  have hc : implemented .clfsh = true := rfl
  have ho : Cpuid.osxsave c = 0 := by simp [Cpuid.osxsave, hos]
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, formerCpuid]
  rcases h with h | h | h | h <;> subst h <;> simp [h12, h13, he2, he3, hc, ho]

theorem cr4Writable_former : Cpuid.cr4Writable = 0x07FC ||| CR4.OSXSAVE := by decide

theorem eferWritable_former : Cpuid.eferWritable = EFER.NXE ||| EFER.MCOMMIT := by decide

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
