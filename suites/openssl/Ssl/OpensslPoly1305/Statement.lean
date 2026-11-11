import Ssl.Harness
import Ssl.Spec.Poly1305
import Ssl.OpensslPoly1305.Image
/-!
# OpenSSL 3.5.9 `crypto/poly1305/poly1305.c`: the portable `Poly1305_Init/Update/Final` is RFC 8439 Poly1305

Image: `targets/openssl_poly1305`: the public API `Poly1305_Init`, `Poly1305_Update`,
`Poly1305_Final`, `Poly1305_ctx_size` over the portable 32-bit-limb core (the branch compiled on
i386, where `INT128_MAX` is not defined and `POLY1305_ASM` is off).

`struct poly1305_context` is 236 bytes on i386 (`Poly1305_ctx_size`). The statements treat its
contents as opaque: the state of a computation is the 236 bytes the previous call left in the
context, wherever the caller keeps them.

Statement: for every 32-byte key and every message of at most `maxLen` bytes, delivered as an
arbitrary sequence of chunks, the calls `Poly1305_Init(ctx, key)`, `Poly1305_Update(ctx, chunk_i,
len_i)`…, `Poly1305_Final(ctx, mac)` each return, having written only the context (and the 16-byte
tag in the last call) and at most `stackBound` bytes of stack; the tag is `Spec.Poly1305.poly1305
key (chunks.flatten)` and `Final` leaves the context zeroed (`OPENSSL_cleanse(ctx, sizeof(*ctx))`).
Every call is made by an arbitrary caller (`Ssl.Harness`) with its own placement of the buffers:
between calls the caller may do anything that keeps the 236 context bytes, and may move them.
`Poly1305_oneshot` is the single-chunk instance, and `Poly1305_ctx_size() = 236`.
-/
namespace Ssl.OpensslPoly1305
open X86 Ssl

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
def maxLen : Nat := 0x100000
def ctxSize : Nat := 236
/-- Stack any of the calls may use below its entry stack pointer. -/
def stackBound : Nat := 256

/-- A call `Poly1305_Init(ctx, keyp)` with the 32-byte `key` in memory. -/
def InitPre (c : Caller) (ctx keyp : UInt32) (key : List UInt8) : Prop :=
  Calls img c stackBound [ctx, keyp] ∧
  Buffer img c stackBound 2 ctx ctxSize ∧ Buffer img c stackBound 2 keyp 32 ∧
  Apart ctx ctxSize keyp 32 ∧ memBytes c.mem keyp 32 = key

/-- A call `Poly1305_Update(ctx, msgp, |chunk|)` with the context bytes `st` and `chunk` in memory. -/
def UpdatePre (c : Caller) (ctx msgp : UInt32) (st chunk : List UInt8) : Prop :=
  Calls img c stackBound [ctx, msgp, chunk.length.toUInt32] ∧
  Buffer img c stackBound 3 ctx ctxSize ∧ Buffer img c stackBound 3 msgp chunk.length ∧
  Apart ctx ctxSize msgp chunk.length ∧
  memBytes c.mem ctx ctxSize = st ∧ memBytes c.mem msgp chunk.length = chunk

/-- A call `Poly1305_Final(ctx, mac)` with the context bytes `st` in memory. -/
def FinalPre (c : Caller) (ctx mac : UInt32) (st : List UInt8) : Prop :=
  Calls img c stackBound [ctx, mac] ∧
  Buffer img c stackBound 2 ctx ctxSize ∧ Buffer img c stackBound 2 mac 16 ∧
  Apart ctx ctxSize mac 16 ∧ memBytes c.mem ctx ctxSize = st

instance (c : Caller) (ctx keyp : UInt32) (key : List UInt8) : Decidable (InitPre c ctx keyp key) := by
  unfold InitPre; infer_instance
instance (c : Caller) (ctx msgp : UInt32) (st chunk : List UInt8) :
    Decidable (UpdatePre c ctx msgp st chunk) := by unfold UpdatePre; infer_instance
instance (c : Caller) (ctx mac : UInt32) (st : List UInt8) : Decidable (FinalPre c ctx mac st) := by
  unfold FinalPre; infer_instance

/-- One `Poly1305_Update` per chunk, starting from the context bytes `st`; each call returns having
written only the context, and the context bytes after the last one satisfy `P`. -/
def UpdatesThen : List (List UInt8) → List UInt8 → (List UInt8 → Prop) → Prop
  | [], st, P => P st
  | chunk :: rest, st, P =>
    ∀ (c : Caller) (ctx msgp : UInt32), UpdatePre c ctx msgp st chunk →
      Returns img (c.enter Image.sym_Poly1305_Update) stackBound (InRange ctx ctxSize) fun m =>
        UpdatesThen rest (bytesAt m ctx ctxSize) P

/-- init; update per chunk; final: the tag is `Spec.Poly1305.poly1305 key (chunks.flatten)` and the
context is wiped. -/
def Stream (key : List UInt8) (chunks : List (List UInt8)) : Prop :=
  ∀ (c : Caller) (ctx keyp : UInt32), InitPre c ctx keyp key →
    Returns img (c.enter Image.sym_Poly1305_Init) stackBound (InRange ctx ctxSize) fun m1 =>
      UpdatesThen chunks (bytesAt m1 ctx ctxSize) fun st =>
        ∀ (c : Caller) (ctx mac : UInt32), FinalPre c ctx mac st →
          Returns img (c.enter Image.sym_Poly1305_Final) stackBound
              (fun a => InRange ctx ctxSize a ∨ InRange mac 16 a) fun m3 =>
            bytesAt m3 mac 16 = Spec.Poly1305.poly1305 key chunks.flatten ∧
            bytesAt m3 ctx ctxSize = List.replicate ctxSize 0

def Poly1305_correct : Prop :=
  ∀ (key : List UInt8) (chunks : List (List UInt8)),
    key.length = 32 → chunks.flatten.length ≤ maxLen → Stream key chunks

/-- The one-shot special case: a single `Poly1305_Update` with the whole message. -/
def Poly1305_oneshot : Prop :=
  ∀ (key msg : List UInt8), key.length = 32 → msg.length ≤ maxLen → Stream key [msg]

/-- `Poly1305_oneshot` is an instance of `Poly1305_correct`, not an independent result. -/
theorem Poly1305_oneshot_of_correct (h : Poly1305_correct) : Poly1305_oneshot :=
  fun key msg hk hm => h key [msg] hk (by simpa using hm)

/-- `Poly1305_ctx_size()` returns `sizeof(struct poly1305_context)` = 236, writing nothing. -/
def Poly1305_ctx_size_correct : Prop :=
  ∀ (c : Caller), Calls img c stackBound [] →
    Returns img (c.enter Image.sym_Poly1305_ctx_size) stackBound NoWrites fun m =>
      m.cpu.eax = ctxSize.toUInt32

end Ssl.OpensslPoly1305
