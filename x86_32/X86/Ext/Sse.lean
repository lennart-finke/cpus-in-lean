import X86.Exec
/-!
# SSE3, SSSE3, SSE4.1, SSE4.2, SSE4a, MisalignSse

Owner: the SSE workstream (legacy encodings; the VEX forms belong to `Avx.lean`). Reuse the helpers
of `X86/Simd.lean` (`sseCheck`, `rdXE`, `V128.lane`/`map2`, `sseStatus`, `FP.cmp`, ...).

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for the 0F-map forms that the core model leaves #UD: F2/F3 0F 12 and 0F 16
  (MOVDDUP, MOVSLDUP, MOVSHDUP), F2/F3 0F 2B (MOVNTSD/MOVNTSS), 0F 78 and 0F 79 (66: EXTRQ,
  F2: INSERTQ; for 66/F2 0F 78 the decoder puts the two imm8 into `imm` and `imm2`), 0F 7C/7D
  (HADDPx/HSUBPx), 0F D0 (ADDSUBPx), F2 0F F0 (LDDQU). Fallback: the core behaviour (#UD).
* `map2?` (0F 38) and `map3?` (0F 3A, imm8 in `imm`): SSSE3, SSE4.1 and SSE4.2, including
  PCMPxSTRx (F2 0F 38 F0/F1, CRC32, belongs to `Gpr.lean`; AES/SHA to `Crypto.lean`). Fallback
  #UD.

MisalignSse (AMD: MXCSR.MM, bit 17) changes the 16-byte alignment check of `Simd.vecAddr`.
-/
namespace X86
namespace Sse

def op0F? (_i : Inst) : Option (M Unit) := none
def map2? (_i : Inst) : Option (M Unit) := none
def map3? (_i : Inst) : Option (M Unit) := none

end Sse
end X86
