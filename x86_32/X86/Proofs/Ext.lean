import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_former`: with the present feature set and the legacy identity, CPUID leaves 0, 1,
  0x80000000 and 0x80000001 return what the model returned before the table-driven CPUID (the
  removed `cpuidVals`) plus the bits of the implemented features (`formerCpuid`).
* `cr4Writable_former`, `eferWritable_former`: the derived MOV CR4 / WRMSR EFER masks are the former
  constants.
* `vexExec_real`, `vexExec_vm86`, `vexExec_prefix`: a VEX-encoded instruction raises #UD in real and
  virtual-8086 mode and after a 66/F2/F3/LOCK prefix, before any extension hook runs.
-/
namespace X86

/-- CPUID of the legacy identity for leaves 0, 1, 0x80000000 and 0x80000001: the former values
(`Exec.cpuidVals` with `addSimd`) plus the bits of the implemented Gpr features (leaf 1: MONITOR,
MOVBE, POPCNT, RDRAND, CLFSH with its line size in EBX; 8000_0001: ABM, PREFETCHW, MONITORX, RDTSCP)
and the higher maximum leaves (7 and 8000_0008) they need, and of the Sse features (leaf 1: SSE3,
SSSE3, SSE4.1, SSE4.2; 8000_0001: SSE4A, MisAlignSse). -/
def formerCpuid (leaf : UInt32) : Regs :=
  match leaf with
  | 0 => (7, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 0x80000000 => (0x80000008, 0, 0, 0)
  | 0x80000001 => (0, 0, 0x20000120 ||| 0xC0, (1 <<< 20) ||| (1 <<< 27))
  | _ => (0x00000619, 0x800, 0x40C00008 ||| 0x00180201, 0x07888365)

theorem legacyMax_former : Cpuid.legacyMax = (7, 0x80000008) := by decide

theorem cpuid_former (c : Cpu) (leaf sub : UInt32)
    (h : leaf = 0 ∨ leaf = 1 ∨ leaf = 0x80000000 ∨ leaf = 0x80000001) :
    cpuid c leaf sub = formerCpuid leaf := by
  have h12 : Cpuid.featBits 1 0 2 true = 0x40C00008 ||| 0x00180201 := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x07888365 := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0x20000120 ||| 0xC0 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = (1 <<< 20) ||| (1 <<< 27) := by
    decide
  have hx : implemented .xsave = false := rfl
  have hc : implemented .clfsh = true := rfl
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, formerCpuid]
  rcases h with h | h | h | h <;> subst h <;> simp [h12, h13, he2, he3, hx, hc]

theorem cr4Writable_former : Cpuid.cr4Writable = 0x07FC := by decide

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
