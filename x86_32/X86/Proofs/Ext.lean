import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_former`: with the present feature set and the legacy identity, CPUID leaves 0, 1,
  0x80000000 and 0x80000001 are what the model returned before the table-driven CPUID
  (`formerCpuid`, the removed `cpuidVals`) plus the XSAVE features (restated by the XSAVE work).
* `cr4Writable_former`, `eferWritable_former`: the derived MOV CR4 / WRMSR EFER masks are the former
  constants.
* `vexExec_real`, `vexExec_vm86`, `vexExec_prefix`: a VEX-encoded instruction raises #UD in real and
  virtual-8086 mode and after a 66/F2/F3/LOCK prefix, before any extension hook runs.
-/
namespace X86

/-- The former CPUID (`Exec.cpuidVals` with `addSimd`), for reference. -/
def formerCpuid (leaf : UInt32) : Regs :=
  match leaf with
  | 0 => (1, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 0x80000000 => (0x80000001, 0, 0, 0)
  | 0x80000001 => (0, 0, 0, 1 <<< 20)
  | _ => (0x00000619, 0, 0, 0x07808365)

theorem legacyMax_former : Cpuid.legacyMax = (0xD, 0x80000008) := by decide

/-- Restated for the XSAVE features (`X86/Ext/Xsave.lean`): leaves 0, 1, 0x80000000 and 0x80000001
are the former ones except for the highest leaves (0xD, 0x80000008: leaf 0xD and XSaveErPtr in
0x80000008:EBX) and CPUID 1:ECX, which reports XSAVE (bit 26) and OSXSAVE = CR4.OSXSAVE (bit 27). -/
theorem cpuid_former (c : Cpu) (sub : UInt32) :
    cpuid c 0 sub = (0xD, 0x756E6547, 0x6C65746E, 0x49656E69) ∧
    cpuid c 1 sub = (0x00000619, 0, (1 <<< 26) ||| Cpuid.osxsave c, 0x07808365) ∧
    cpuid c 0x80000000 sub = (0x80000008, 0, 0, 0) ∧
    cpuid c 0x80000001 sub = formerCpuid 0x80000001 := by
  have h12 : Cpuid.featBits 1 0 2 true = 1 <<< 26 := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x07808365 := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = 1 <<< 20 := by decide
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, formerCpuid]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h12, h13, he2, he3]

theorem cr4Writable_former : Cpuid.cr4Writable = 0x07FC ||| CR4.OSXSAVE := by decide

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
