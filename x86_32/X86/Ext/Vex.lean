import X86.Exec
/-!
# Shared VEX helpers

Owner: the AVX workstream (`Avx.lean`); `Avx2.lean` and `Gpr.lean` (BMI1/BMI2) use it.

`Dispatch.vexExec` has already raised #UD for every VEX instruction in real or virtual-8086 mode,
with a 66, F2, F3 or LOCK prefix before the VEX prefix, or with an unknown map, before any
`vex?` hook runs.
-/
namespace X86
namespace Vex

/-- The checks of a VEX-encoded SSE/AVX instruction before it touches any state (SDM vol. 1,
13.2 and 14.2; AMD APM vol. 4): #UD unless CR4.OSXSAVE = 1 and XCR0[2:1] = 11b, #NM with CR0.TS.
Not for BMI1/BMI2 (GPR instructions without XSAVE state).

STUB: today every VEX instruction is #UD, so this raises #UD. The AVX workstream implements it
(and proves its key properties in `X86/Proofs/`). -/
def vexCheck (_i : Inst) : M Unit := ud

end Vex
end X86
