import Ssl.Harness
import Ssl.Spec.Sha256
import Ssl.OpensslSha256.Image
/-!
# OpenSSL 3.5.9 `crypto/sha/sha256.c`: the portable SHA-256/SHA-224 low-level API is FIPS 180-4

Image: `targets/openssl_sha256`: `SHA224_Init`, `SHA256_Init`, `SHA224_Update`, `SHA224_Final` and
the C block function from `crypto/sha/sha256.c`; `SHA256_Update`, `SHA256_Transform`, `SHA256_Final`
from the `include/crypto/md32_common.h` template. No `SHA256_ASM`: the C block function is used.

`SHA256_CTX` is 112 bytes: `SHA_LONG h[8]` at 0, `Nl` at 32, `Nh` at 36, `data[16]` (64 bytes) at
40, `num` at 104, `md_len` at 108. The streaming statements treat its contents as opaque: the state
of a computation is the 112 bytes the previous call left in the context, wherever the caller keeps
them. Only the wipe and `SHA256_Transform` refer to the layout.

Statements (`Spec.Sha256` is FIPS 180-4), each call made by an arbitrary caller (`Ssl.Harness`) with
its own placement of the buffers and at most `stackBound` bytes of stack:

* streaming: `SHA256_Init(ctx)`, then `SHA256_Update(ctx, chunk_i, |chunk_i|)` once per chunk of an
  arbitrary chunking of a message of at most `maxLen` bytes, then `SHA256_Final(out, ctx)`; every
  call returns 1; `Init` and `Update` write only the context; `Final` writes the context and the 32
  bytes `Spec.sha256 (chunks.flatten)` at `out`, and leaves the block buffer and `num` (context
  bytes `[40, 108)`) zero. Upstream does not wipe `h`, the bit count or `md_len`;
* the same with `SHA224_Init`/`SHA224_Update`/`SHA224_Final` and the 28-byte `Spec.sha224`;
* per block: `SHA256_Transform(ctx, block)` replaces the eight words `h` by `Spec.compress h block`
  and writes only those 32 bytes.
-/
namespace Ssl.OpensslSha256
open X86 Ssl

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
def maxLen : Nat := 0x100000
def ctxSize : Nat := 112
/-- Offset of `data[16]` (the 64-byte block buffer) in `SHA256_CTX`; `num` follows at 104. -/
def dataOff : UInt32 := 40
/-- Stack any of the calls may use below its entry stack pointer. -/
def stackBound : Nat := 512

/-- A call `ini(ctx)` (`ini` = `SHA256_Init` or `SHA224_Init`). -/
def InitPre (c : Caller) (ctx : UInt32) : Prop :=
  Calls img c stackBound [ctx] ∧ Buffer img c stackBound 1 ctx ctxSize

/-- A call `upd(ctx, msgp, |chunk|)` with the context bytes `st` and `chunk` in memory. -/
def UpdatePre (c : Caller) (ctx msgp : UInt32) (st chunk : List UInt8) : Prop :=
  Calls img c stackBound [ctx, msgp, chunk.length.toUInt32] ∧
  Buffer img c stackBound 3 ctx ctxSize ∧ Buffer img c stackBound 3 msgp chunk.length ∧
  Apart ctx ctxSize msgp chunk.length ∧
  memBytes c.mem ctx ctxSize = st ∧ memBytes c.mem msgp chunk.length = chunk

/-- A call `fin(out, ctx)` writing an `n`-byte digest, with the context bytes `st` in memory (note
the argument order `(md, c)`). -/
def FinalPre (n : Nat) (c : Caller) (out ctx : UInt32) (st : List UInt8) : Prop :=
  Calls img c stackBound [out, ctx] ∧
  Buffer img c stackBound 2 ctx ctxSize ∧ Buffer img c stackBound 2 out n ∧
  Apart ctx ctxSize out n ∧ memBytes c.mem ctx ctxSize = st

/-- A call `SHA256_Transform(ctx, blockp)` with the hash words `H` and the 64-byte `block` in memory. -/
def TransformPre (c : Caller) (ctx blockp : UInt32) (H : Array UInt32) (block : List UInt8) : Prop :=
  Calls img c stackBound [ctx, blockp] ∧
  H.size = 8 ∧ block.length = 64 ∧
  Buffer img c stackBound 2 ctx 32 ∧ Buffer img c stackBound 2 blockp 64 ∧
  Apart ctx 32 blockp 64 ∧
  memWords c.mem ctx 8 = H ∧ memBytes c.mem blockp 64 = block

instance (c : Caller) (ctx : UInt32) : Decidable (InitPre c ctx) := by unfold InitPre; infer_instance
instance (c : Caller) (ctx msgp : UInt32) (st chunk : List UInt8) :
    Decidable (UpdatePre c ctx msgp st chunk) := by unfold UpdatePre; infer_instance
instance (n : Nat) (c : Caller) (out ctx : UInt32) (st : List UInt8) :
    Decidable (FinalPre n c out ctx st) := by unfold FinalPre; infer_instance
instance (c : Caller) (ctx blockp : UInt32) (H : Array UInt32) (block : List UInt8) :
    Decidable (TransformPre c ctx blockp H block) := by unfold TransformPre; infer_instance

/-- One `upd` per chunk, starting from the context bytes `st`; each call returns 1 having written
only the context, and the context bytes after the last one satisfy `P`. -/
def UpdatesThen (upd : UInt32) : List (List UInt8) → List UInt8 → (List UInt8 → Prop) → Prop
  | [], st, P => P st
  | chunk :: rest, st, P =>
    ∀ (c : Caller) (ctx msgp : UInt32), UpdatePre c ctx msgp st chunk →
      Returns img (c.enter upd) stackBound (InRange ctx ctxSize) fun m =>
        m.cpu.eax = 1 ∧ UpdatesThen upd rest (bytesAt m ctx ctxSize) P

/-- `ini`; `upd` per chunk; `fin`: the `n`-byte `digest` at `out`, and the context's
`data` buffer and `num` wiped to zero. -/
def Stream (ini upd fin : UInt32) (n : Nat) (digest : List UInt8) (chunks : List (List UInt8)) : Prop :=
  ∀ (c : Caller) (ctx : UInt32), InitPre c ctx →
    Returns img (c.enter ini) stackBound (InRange ctx ctxSize) fun m1 =>
      m1.cpu.eax = 1 ∧
      UpdatesThen upd chunks (bytesAt m1 ctx ctxSize) fun st =>
        ∀ (c : Caller) (out ctx : UInt32), FinalPre n c out ctx st →
          Returns img (c.enter fin) stackBound
              (fun a => InRange ctx ctxSize a ∨ InRange out n a) fun m3 =>
            m3.cpu.eax = 1 ∧
            bytesAt m3 out n = digest ∧
            bytesAt m3 (ctx + dataOff) 68 = List.replicate 68 0

def sha256_streaming_correct : Prop :=
  ∀ (chunks : List (List UInt8)), chunks.flatten.length ≤ maxLen →
    Stream Image.sym_SHA256_Init Image.sym_SHA256_Update Image.sym_SHA256_Final 32
      (Spec.Sha256.sha256 chunks.flatten) chunks

/-- The same with `SHA224_Init`/`SHA224_Update`/`SHA224_Final` and the 28-byte digest. -/
def sha224_streaming_correct : Prop :=
  ∀ (chunks : List (List UInt8)), chunks.flatten.length ≤ maxLen →
    Stream Image.sym_SHA224_Init Image.sym_SHA224_Update Image.sym_SHA224_Final 28
      (Spec.Sha256.sha224 chunks.flatten) chunks

/-- One block through `SHA256_Transform`: `h := Spec.compress h block`, nothing else written. -/
def SHA256_Transform_correct : Prop :=
  ∀ (c : Caller) (ctx blockp : UInt32) (H : Array UInt32) (block : List UInt8),
    TransformPre c ctx blockp H block →
    Returns img (c.enter Image.sym_SHA256_Transform) stackBound (InRange ctx 32) fun m =>
      wordsAt m ctx 8 = Spec.Sha256.compress H block

end Ssl.OpensslSha256
