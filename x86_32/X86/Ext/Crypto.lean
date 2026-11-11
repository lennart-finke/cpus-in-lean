import X86.Exec
/-!
# AES, PCLMULQDQ, SHA

Owner: the crypto workstream (legacy encodings; the VEX.128 forms belong to `Avx.lean`).

Hooks (called by `X86/Dispatch.lean` after `Sse.map2?`/`Sse.map3?`; `none` = not handled here):

* `map2?` (0F 38): 66 0F 38 DB..DF (AESIMC, AESENC, AESENCLAST, AESDEC, AESDECLAST), 0F 38 C8..CD
  (SHA1NEXTE, SHA1MSG1, SHA1MSG2, SHA256RNDS2, SHA256MSG1, SHA256MSG2).
* `map3?` (0F 3A, imm8 in `imm`): 66 0F 3A 44 (PCLMULQDQ), 66 0F 3A DF (AESKEYGENASSIST),
  0F 3A CC (SHA1RNDS4).
-/
namespace X86
namespace Crypto

def map2? (_i : Inst) : Option (M Unit) := none
def map3? (_i : Inst) : Option (M Unit) := none

end Crypto
end X86
