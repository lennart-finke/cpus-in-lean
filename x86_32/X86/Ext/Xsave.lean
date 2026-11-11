import X86.Exec
/-!
# XSAVE

Owner: the XSAVE workstream. XCR0 (`Cpu.xcr0`, reset 1), IA32_XSS (`Cpu.xss`), XGETBV/XSETBV,
XSAVE/XRSTOR/XSAVEOPT/XSAVEC/XSAVES/XRSTORS, CPUID leaf 0xD (computed in `X86/Cpuid.lean` from
`xcr0Supported` and `xsaveSize`; adjust it there), CR4.OSXSAVE (accepted by MOV CR4 once `xsave` is
implemented: `Cpuid.cr4Writable`).

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for
  - 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns D0 (XGETBV) and D1
    (XSETBV);
  - 0F AE forms other than FXSAVE/FXRSTOR/LDMXCSR/STMXCSR and the fences (fallback #UD): this
    module owns memory /4 (XSAVE), /5 (XRSTOR), /6 (XSAVEOPT) without prefix;
  - 0F C7 forms other than /1 (fallback #UD): this module owns memory /3 (XRSTORS), /4 (XSAVEC),
    /5 (XSAVES).
* `msr?`: IA32_XSS (0xDA0).
-/
namespace X86
namespace Xsave

def op0F? (_i : Inst) : Option (M Unit) := none
def msr? (_n : UInt32) : Option MsrImpl := none

end Xsave
end X86
