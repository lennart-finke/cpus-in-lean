import X86.Exec
/-!
# Long mode (entry and compatibility mode)

Owner: the long-mode workstream. EFER.LME/LMA, 4-level paging, compatibility mode. Executing 64-bit
code stops with `Fault.unsupported` (the `x86_64` model's job). State: `LongModeState` in
`X86/State.lean`.

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for 0F 01 register forms other than SMSW/LMSW (this module owns F8, SWAPGS,
  #UD outside 64-bit mode) and for the 0F AE forms other than FXSAVE/FXRSTOR/LDMXCSR/STMXCSR and
  the fences (this module owns F3 0F AE register /0../3, RDFSBASE.., #UD outside 64-bit mode);
  fallback #UD.
* `msr?`: FS_BASE, GS_BASE, KERNEL_GS_BASE (0xC0000100..0xC0000102), LSTAR, CSTAR, SFMASK.
-/
namespace X86
namespace LongMode

def op0F? (_i : Inst) : Option (M Unit) := none
def msr? (_n : UInt32) : Option MsrImpl := none

end LongMode
end X86
