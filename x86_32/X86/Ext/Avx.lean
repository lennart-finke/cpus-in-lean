import X86.Ext.Vex
/-!
# AVX

Owner: the AVX workstream. YMM state (`SseState.ymmh`), VEX forms of the SSE..SSE4.2, AES and
PCLMULQDQ instructions (VEX.128 zeroes bits 255:128 of the destination), the 256-bit AVX
instructions, VZEROUPPER/VZEROALL (VEX.0F 77), VLDMXCSR/VSTMXCSR (VEX.0F AE /2 /3), the 32 compare
predicates, `Vex.vexCheck`.

Hook (called by `X86/Dispatch.lean` after `Gpr.vex?`; `none` = not handled here):

* `vex?`: the VEX instructions of AVX (maps 0F, 0F 38, 0F 3A: `Inst.op`, `pp`, `vvvv`, `vexL`,
  `vexW`). Return `none` for AVX2, FMA and F16C (`Avx2.lean`) and BMI (`Gpr.lean`).
-/
namespace X86
namespace Avx

def vex? (_i : Inst) : Option (M Unit) := none

end Avx
end X86
