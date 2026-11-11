import X86.Exec
/-!
# System extensions (system workstream A)

Owner: the system workstream A. SYSENTER/SYSEXIT, legacy-mode SYSCALL/SYSRET (STAR, EFER.SCE),
SMEP/SMAP (CLAC/STAC), UMIP, global pages, PSE-36, #AC, PAT/MTRR/MCA/TSC/TSC_AUX and AMD MSRs,
AltMovCr8, EFER.FFXSR. State: `SysState` in `X86/State.lean`. CR4/EFER bits are accepted once the
feature is implemented (`Cpuid.cr4Writable`, `Cpuid.eferWritable`). Paging changes (SMEP/SMAP,
PSE-36, global pages) are edits of `X86/Machine.lean` owned by this workstream.

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for
  - 0F 05 (SYSCALL), 0F 07 (SYSRET), 0F 34 (SYSENTER), 0F 35 (SYSEXIT) (fallback #UD);
  - LOCK 0F 20 / LOCK 0F 22 (AltMovCr8: MOV from/to CR8; fallback: the core behaviour; `lockOk` in
    `X86/Step.lean` admits LOCK on them once `altMovCr8` is implemented);
  - 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns CA (CLAC) and
    CB (STAC).
* `msr?`: SYSENTER_CS/ESP/EIP (0x174..0x176), STAR (0xC0000081), PAT (0x277), MTRRs, MCA, TSC
  (0x10), ... (looked up after the core MSRs of `Exec.coreMsr?`).

System workstream B (VME/PVI, NMI, exception classes) changes `popf`/`iret` (`X86/Exec.lean`,
`X86/Sys.lean`) and interrupt delivery (`X86/Sys.lean`, `X86/Step.lean`) directly.
-/
namespace X86
namespace Sys

def op0F? (_i : Inst) : Option (M Unit) := none
def msr? (_n : UInt32) : Option MsrImpl := none

end Sys
end X86
