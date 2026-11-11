import Ssl.Harness
import Ssl.Spec.Chacha
import Ssl.OpensslChacha20.Image
/-!
# OpenSSL 3.5.9 `crypto/chacha/chacha_enc.c`: the portable `ChaCha20_ctr32` is RFC 8439 ChaCha20

Image: `targets/openssl_chacha20`. `ChaCha20_ctr32(out, inp, len, key[8], counter[4])` builds the
16-word state matrix from the constants `expand 32-byte k`, the eight key words and the four
counter/nonce words, then xors `inp` with consecutive keystream blocks, incrementing word 12 modulo
2^32 after each block (the caller is responsible for wider counters).

Statement: for every caller (`Ssl.Harness`), every placement of the four buffers, every key of 8
words, every counter/nonce of 4 words and every input that is a buffer (`Ssl.Buffer`: it fits in
memory and is no larger than a C object; there is no other length bound), the call returns
with the `src.length` bytes at `out` equal to `Spec.Chacha.crypt 20 (sigma ++ key ++ ctr) src`,
having written nothing but those bytes and at most `stackBound` bytes of its own stack. The output
may be the input buffer itself (`out = inp`, in-place encryption) or must not overlap it; it must
not overlap the key or the counter. The key, counter and input are only read and may overlap each
other.
-/
namespace Ssl.OpensslChacha20
open X86 Ssl

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
/-- Stack the call may use below its entry stack pointer. -/
def stackBound : Nat := 512

/-- RFC 8439 §2.3: the constants `expand 32-byte k` as four little-endian words. -/
def sigma : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- The state matrix the function assembles. -/
def state (key ctr : Array UInt32) : Array UInt32 := sigma ++ key ++ ctr

/-- The stack arguments of `ChaCha20_ctr32(out, inp, len, key, counter)`. -/
def args (out inp keyp ctrp : UInt32) (src : List UInt8) : List UInt32 :=
  [out, inp, src.length.toUInt32, keyp, ctrp]

/-- A call `ChaCha20_ctr32(out, inp, |src|, keyp, ctrp)` with `key`, `ctr` and `src` in memory. -/
def Pre (c : Caller) (out inp keyp ctrp : UInt32) (key ctr : Array UInt32) (src : List UInt8) : Prop :=
  Calls img c stackBound (args out inp keyp ctrp src) ∧
  key.size = 8 ∧ ctr.size = 4 ∧
  Buffer img c stackBound 5 out src.length ∧ Buffer img c stackBound 5 inp src.length ∧
  Buffer img c stackBound 5 keyp 32 ∧ Buffer img c stackBound 5 ctrp 16 ∧
  (out = inp ∨ Apart out src.length inp src.length) ∧
  Apart out src.length keyp 32 ∧ Apart out src.length ctrp 16 ∧
  memWords c.mem keyp 8 = key ∧ memWords c.mem ctrp 4 = ctr ∧ memBytes c.mem inp src.length = src

instance (c : Caller) (out inp keyp ctrp : UInt32) (key ctr : Array UInt32) (src : List UInt8) :
    Decidable (Pre c out inp keyp ctrp key ctr src) := by unfold Pre; infer_instance

def ChaCha20_ctr32_correct : Prop :=
  ∀ (c : Caller) (out inp keyp ctrp : UInt32) (key ctr : Array UInt32) (src : List UInt8),
    Pre c out inp keyp ctrp key ctr src →
    Returns img (c.enter Image.sym_ChaCha20_ctr32) stackBound (InRange out src.length) fun m =>
      bytesAt m out src.length = Spec.Chacha.crypt 20 (state key ctr) src

end Ssl.OpensslChacha20
