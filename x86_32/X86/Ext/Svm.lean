import X86.Exec
/-!
# SVM

Owner: the SVM workstream. EFER.SVME (accepted once `svm` is implemented: `Cpuid.eferWritable`),
VMRUN/#VMEXIT, VMCB, intercepts, VMLOAD/VMSAVE, STGI/CLGI, VMMCALL, INVLPGA, SKINIT, nested paging.
State: `SvmState` in `X86/State.lean`.

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns
  D8 (VMRUN), D9 (VMMCALL), DA (VMLOAD), DB (VMSAVE), DC (STGI), DD (CLGI), DE (SKINIT),
  DF (INVLPGA).
* `msr?`: VM_CR (0xC0010114), VM_HSAVE_PA (0xC0010117).
-/
namespace X86
namespace Svm

def op0F? (_i : Inst) : Option (M Unit) := none
def msr? (_n : UInt32) : Option MsrImpl := none

end Svm
end X86
