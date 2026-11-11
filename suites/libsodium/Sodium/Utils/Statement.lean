import Ssl.Harness
import Sodium.Spec.Utils
import Sodium.Utils.Image
/-!
# libsodium 1.0.22 `sodium/codecs.c`, `sodium/utils.c`: encoding, comparing, wiping and padding secrets

Image: `targets/sodium_utils`: `sodium_bin2hex`, `sodium_hex2bin`, `sodium_bin2base64`,
`sodium_base642bin` (`codecs.c`) and `sodium_memcmp`, `sodium_memzero`, `sodium_pad`,
`sodium_unpad` (`utils.c`), compiled unchanged. These are the helpers applications use on keys,
authentication tags and padded plaintexts, which is why libsodium writes them without
data-dependent branches.

Two kinds of statements, for every caller (`Ssl.Harness`) and every placement of the buffers:

* **What a call computes** (`*_correct`, `*_inverts`): the encoders produce the standard encoding
  (`Sodium.Spec`), the decoders give back the bytes of a standard encoding, `sodium_memcmp` is 0
  exactly on equal buffers, `sodium_memzero` leaves zero bytes, `sodium_pad` and `sodium_unpad`
  implement ISO/IEC 7816-4 padding. Together: decoding an encoding, and unpadding a padding, give
  back the input.
* **The same steps whatever the secret** (`*_constant_time`): two calls with the same pointers and
  lengths but different buffer contents execute the same number of instructions at the same
  sequence of addresses (`SameTrace`). This is a property of the compiled code and not of the C
  source: a compiler may turn branch-free C into branches.

Limits. `SameTrace` is about the instruction addresses of the architectural model: it says the
control flow does not depend on the secret, and says nothing about data addresses, caches or
instruction timing. The decoders are called without an `ignore` set and without an end pointer,
and their constant-time statements are about valid encodings (they stop at the first invalid
character by design). The image is built with none of libsodium's `HAVE_*` configuration macros,
so `sodium_memzero` and `sodium_memcmp` are the portable `volatile` loops, not a platform's
`explicit_bzero`. `sodium_pad` is stated for block sizes up to `maxBlock`.
-/
namespace Sodium.Utils
open X86 Ssl Sodium.Spec

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
/-- Stack a call may use below its entry stack pointer. -/
def stackBound : Nat := 128
/-- The `int` result -1. -/
def minusOne : UInt32 := 0xFFFFFFFF

/-! ## Encoders and decoders -/

/-- A call of an encoder with arguments `args`: the `cap`-byte output buffer at `outp`, the input
`x` at `binp`, not overlapping; `cap` exceeds the `encLen` characters of the encoding, leaving
room for the terminating NUL. -/
def EncodePre (c : Caller) (args : List UInt32) (outp binp : UInt32) (cap encLen : Nat)
    (x : List UInt8) : Prop :=
  Calls img c stackBound args ∧
  Buffer img c stackBound args.length outp cap ∧ Buffer img c stackBound args.length binp x.length ∧
  Apart outp cap binp x.length ∧ memBytes c.mem binp x.length = x ∧ encLen < cap

/-- A call of a decoder with arguments `args`: the `cap`-byte output buffer at `binp`, the text at
`textp`, the 4-byte output length at `lenp`, pairwise not overlapping; the output has room for the
`n` decoded bytes. `lenp` is not null (the decoders store no length through a null pointer, and
address 0 is ordinary memory here). -/
def DecodePre (c : Caller) (args : List UInt32) (binp textp lenp : UInt32) (cap n : Nat)
    (text : List UInt8) : Prop :=
  Calls img c stackBound args ∧ lenp ≠ 0 ∧
  Buffer img c stackBound args.length binp cap ∧ Buffer img c stackBound args.length textp text.length ∧
  Buffer img c stackBound args.length lenp 4 ∧
  Apart binp cap textp text.length ∧ Apart binp cap lenp 4 ∧ Apart lenp 4 textp text.length ∧
  memBytes c.mem textp text.length = text ∧ n ≤ cap

instance (c : Caller) (args : List UInt32) (outp binp : UInt32) (cap encLen : Nat) (x : List UInt8) :
    Decidable (EncodePre c args outp binp cap encLen x) := by unfold EncodePre; infer_instance
instance (c : Caller) (args : List UInt32) (binp textp lenp : UInt32) (cap n : Nat) (text : List UInt8) :
    Decidable (DecodePre c args binp textp lenp cap n text) := by unfold DecodePre; infer_instance

/-- The decoder returns 0, stores the length `|x|` and the bytes `x`, and writes nothing else. -/
def Decodes (c : Caller) (fn binp lenp : UInt32) (x : List UInt8) : Prop :=
  Returns img (c.enter fn) stackBound (fun a => InRange binp x.length a ∨ InRange lenp 4 a) fun m =>
    m.cpu.eax = 0 ∧ wordAt m lenp = x.length.toUInt32 ∧ bytesAt m binp x.length = x

/-- `sodium_bin2hex(hex, hex_maxlen, bin, bin_len)`. -/
def bin2hexArgs (hexp binp : UInt32) (cap : Nat) (x : List UInt8) : List UInt32 :=
  [hexp, cap.toUInt32, binp, x.length.toUInt32]

/-- `sodium_hex2bin(bin, bin_maxlen, hex, hex_len, ignore = NULL, bin_len, hex_end = NULL)`. -/
def hex2binArgs (binp textp lenp : UInt32) (cap : Nat) (text : List UInt8) : List UInt32 :=
  [binp, cap.toUInt32, textp, text.length.toUInt32, 0, lenp, 0]

/-- `sodium_bin2hex` writes the lower-case hexadecimal digits of `x` and a NUL, and returns `hex`. -/
def bin2hex_correct : Prop :=
  ∀ (c : Caller) (hexp binp : UInt32) (cap : Nat) (x : List UInt8),
    EncodePre c (bin2hexArgs hexp binp cap x) hexp binp cap (2 * x.length) x →
    Returns img (c.enter Image.sym_sodium_bin2hex) stackBound (InRange hexp (2 * x.length + 1)) fun m =>
      m.cpu.eax = hexp ∧ bytesAt m hexp (2 * x.length + 1) = hex x ++ [0]

/-- `sodium_hex2bin` on the hexadecimal digits of `x` gives back `x`. -/
def hex2bin_inverts : Prop :=
  ∀ (c : Caller) (binp textp lenp : UInt32) (cap : Nat) (x : List UInt8),
    DecodePre c (hex2binArgs binp textp lenp cap (hex x)) binp textp lenp cap x.length (hex x) →
    Decodes c Image.sym_sodium_hex2bin binp lenp x

/-- libsodium's four base64 variants: `sodium_base64_VARIANT_ORIGINAL` (1), `…_ORIGINAL_NO_PADDING`
(3), `…_URLSAFE` (5), `…_URLSAFE_NO_PADDING` (7). -/
def variants : List UInt32 := [1, 3, 5, 7]

/-- The RFC 4648 encoding a variant selects: bit 2 is the URL-safe alphabet, bit 1 omits `=`. -/
def encode (variant : UInt32) (x : List UInt8) : List UInt8 :=
  base64 (variant &&& 4 != 0) (variant &&& 2 == 0) x

/-- `sodium_bin2base64(b64, b64_maxlen, bin, bin_len, variant)`. -/
def bin2base64Args (b64p binp : UInt32) (cap : Nat) (x : List UInt8) (variant : UInt32) : List UInt32 :=
  [b64p, cap.toUInt32, binp, x.length.toUInt32, variant]

/-- `sodium_base642bin(bin, bin_maxlen, b64, b64_len, ignore = NULL, bin_len, b64_end = NULL, variant)`. -/
def base642binArgs (binp textp lenp : UInt32) (cap : Nat) (text : List UInt8) (variant : UInt32) :
    List UInt32 :=
  [binp, cap.toUInt32, textp, text.length.toUInt32, 0, lenp, 0, variant]

/-- `sodium_bin2base64` writes the RFC 4648 encoding of `x`, fills the rest of the buffer with
zero bytes, and returns `b64`. -/
def bin2base64_correct : Prop :=
  ∀ (c : Caller) (b64p binp : UInt32) (cap : Nat) (x : List UInt8) (variant : UInt32),
    variant ∈ variants →
    EncodePre c (bin2base64Args b64p binp cap x variant) b64p binp cap (encode variant x).length x →
    Returns img (c.enter Image.sym_sodium_bin2base64) stackBound (InRange b64p cap) fun m =>
      m.cpu.eax = b64p ∧
      bytesAt m b64p cap = encode variant x ++ List.replicate (cap - (encode variant x).length) 0

/-- `sodium_base642bin` on the RFC 4648 encoding of `x` gives back `x`. -/
def base642bin_inverts : Prop :=
  ∀ (c : Caller) (binp textp lenp : UInt32) (cap : Nat) (x : List UInt8) (variant : UInt32),
    variant ∈ variants →
    DecodePre c (base642binArgs binp textp lenp cap (encode variant x) variant) binp textp lenp cap
      x.length (encode variant x) →
    Decodes c Image.sym_sodium_base642bin binp lenp x

/-! ## Comparing and wiping -/

/-- `sodium_memcmp(ap, bp, |a|)` with `a` at `ap` and `b`, of the same length, at `bp`. The buffers
are only read and may overlap. -/
def MemcmpPre (c : Caller) (ap bp : UInt32) (a b : List UInt8) : Prop :=
  Calls img c stackBound [ap, bp, a.length.toUInt32] ∧
  Buffer img c stackBound 3 ap a.length ∧ Buffer img c stackBound 3 bp b.length ∧
  a.length = b.length ∧ memBytes c.mem ap a.length = a ∧ memBytes c.mem bp b.length = b

instance (c : Caller) (ap bp : UInt32) (a b : List UInt8) : Decidable (MemcmpPre c ap bp a b) := by
  unfold MemcmpPre; infer_instance

/-- `sodium_memcmp` returns 0 if the buffers are equal and -1 otherwise, and writes nothing. -/
def memcmp_correct : Prop :=
  ∀ (c : Caller) (ap bp : UInt32) (a b : List UInt8), MemcmpPre c ap bp a b →
    Returns img (c.enter Image.sym_sodium_memcmp) stackBound NoWrites fun m =>
      m.cpu.eax = if a = b then 0 else minusOne

/-- `sodium_memzero(p, n)`. -/
def MemzeroPre (c : Caller) (p : UInt32) (n : Nat) : Prop :=
  Calls img c stackBound [p, n.toUInt32] ∧ Buffer img c stackBound 2 p n

instance (c : Caller) (p : UInt32) (n : Nat) : Decidable (MemzeroPre c p n) := by
  unfold MemzeroPre; infer_instance

/-- After `sodium_memzero` every byte of the buffer is zero: the stores are in the machine code. -/
def memzero_correct : Prop :=
  ∀ (c : Caller) (p : UInt32) (n : Nat), MemzeroPre c p n →
    Returns img (c.enter Image.sym_sodium_memzero) stackBound (InRange p n) fun m =>
      bytesAt m p n = List.replicate n 0

/-! ## Padding -/

/-- The largest block size `sodium_pad` is stated for, and the largest for which `pad_correct`
holds. The function locates the `0x80` byte with
`((i ^ xpadlen) - 1U) >> ((sizeof(size_t) - 1) * CHAR_BIT)`, which for the 32-bit `size_t` of this
image is 0 for `i ≠ xpadlen` only while `i ^ xpadlen ≤ 2^24`. Up to this bound `i` and `xpadlen`
are both below 2^24, so the test is exact. One above it, padding an empty buffer whose bytes have
their low bit set leaves those bits in the padding. -/
def maxBlock : Nat := 0x1000000

/-- `sodium_pad(lenp, bufp, |x|, block, cap)`: `x` at the start of the `cap`-byte buffer at `bufp`,
the 4-byte output length at `lenp`, not overlapping; the padded length fits the buffer. `lenp` is
not null (the function stores no length through a null pointer). -/
def PadPre (c : Caller) (lenp bufp : UInt32) (x : List UInt8) (block cap : Nat) : Prop :=
  Calls img c stackBound [lenp, bufp, x.length.toUInt32, block.toUInt32, cap.toUInt32] ∧ lenp ≠ 0 ∧
  Buffer img c stackBound 5 bufp cap ∧ Buffer img c stackBound 5 lenp 4 ∧ Apart bufp cap lenp 4 ∧
  memBytes c.mem bufp x.length = x ∧ 0 < block ∧ block ≤ maxBlock ∧ paddedLength x.length block ≤ cap

/-- `sodium_unpad(lenp, bufp, |buf|, block)`: the padded buffer `buf` at `bufp`, at least one block
long, the 4-byte output length at `lenp`, not overlapping. -/
def UnpadPre (c : Caller) (lenp bufp : UInt32) (buf : List UInt8) (block : Nat) : Prop :=
  Calls img c stackBound [lenp, bufp, buf.length.toUInt32, block.toUInt32] ∧
  Buffer img c stackBound 4 bufp buf.length ∧ Buffer img c stackBound 4 lenp 4 ∧
  Apart bufp buf.length lenp 4 ∧ memBytes c.mem bufp buf.length = buf ∧ 0 < block ∧ block ≤ buf.length

instance (c : Caller) (lenp bufp : UInt32) (x : List UInt8) (block cap : Nat) :
    Decidable (PadPre c lenp bufp x block cap) := by unfold PadPre; infer_instance
instance (c : Caller) (lenp bufp : UInt32) (buf : List UInt8) (block : Nat) :
    Decidable (UnpadPre c lenp bufp buf block) := by unfold UnpadPre; infer_instance

/-- `sodium_pad` returns 0, stores the padded length and leaves `x`, a `0x80` byte and zero bytes
up to a multiple of the block size; it writes nothing beyond the padded length. -/
def pad_correct : Prop :=
  ∀ (c : Caller) (lenp bufp : UInt32) (x : List UInt8) (block cap : Nat), PadPre c lenp bufp x block cap →
    Returns img (c.enter Image.sym_sodium_pad) stackBound
      (fun a => InRange bufp (paddedLength x.length block) a ∨ InRange lenp 4 a) fun m =>
      m.cpu.eax = 0 ∧ wordAt m lenp = (paddedLength x.length block).toUInt32 ∧
      bytesAt m bufp (paddedLength x.length block) = pad x block

/-- `sodium_unpad` returns 0 and stores the data length exactly when the buffer's last block ends in
`0x80` followed only by zero bytes, and returns -1 otherwise; it never writes the buffer. -/
def unpad_correct : Prop :=
  ∀ (c : Caller) (lenp bufp : UInt32) (buf : List UInt8) (block : Nat), UnpadPre c lenp bufp buf block →
    Returns img (c.enter Image.sym_sodium_unpad) stackBound (InRange lenp 4) fun m =>
      match unpad buf block with
      | some n => m.cpu.eax = 0 ∧ wordAt m lenp = n.toUInt32
      | none => m.cpu.eax = minusOne

/-! ## The same steps whatever the secret -/

/-- Both calls return after the same number of instructions, executed at the same addresses. -/
def SameTrace (m m' : Machine) : Prop :=
  ∃ k, Trace img k m ∧ returned img (steps k m) = true ∧
       Trace img k m' ∧ returned img (steps k m') = true ∧
       ∀ i, i < k → (steps i m).cpu.eip = (steps i m').cpu.eip

/-- Encoding two byte strings of the same length to hexadecimal takes the same steps. -/
def bin2hex_constant_time : Prop :=
  ∀ (c c' : Caller) (hexp binp : UInt32) (cap : Nat) (x x' : List UInt8), x.length = x'.length →
    EncodePre c (bin2hexArgs hexp binp cap x) hexp binp cap (2 * x.length) x →
    EncodePre c' (bin2hexArgs hexp binp cap x') hexp binp cap (2 * x'.length) x' →
    SameTrace (c.enter Image.sym_sodium_bin2hex) (c'.enter Image.sym_sodium_bin2hex)

/-- Decoding the hexadecimal digits of two byte strings of the same length takes the same steps. -/
def hex2bin_constant_time : Prop :=
  ∀ (c c' : Caller) (binp textp lenp : UInt32) (cap : Nat) (x x' : List UInt8), x.length = x'.length →
    DecodePre c (hex2binArgs binp textp lenp cap (hex x)) binp textp lenp cap x.length (hex x) →
    DecodePre c' (hex2binArgs binp textp lenp cap (hex x')) binp textp lenp cap x'.length (hex x') →
    SameTrace (c.enter Image.sym_sodium_hex2bin) (c'.enter Image.sym_sodium_hex2bin)

/-- Encoding two byte strings of the same length to base64 takes the same steps. -/
def bin2base64_constant_time : Prop :=
  ∀ (c c' : Caller) (b64p binp : UInt32) (cap : Nat) (x x' : List UInt8) (variant : UInt32),
    variant ∈ variants → x.length = x'.length →
    EncodePre c (bin2base64Args b64p binp cap x variant) b64p binp cap (encode variant x).length x →
    EncodePre c' (bin2base64Args b64p binp cap x' variant) b64p binp cap (encode variant x').length x' →
    SameTrace (c.enter Image.sym_sodium_bin2base64) (c'.enter Image.sym_sodium_bin2base64)

/-- Decoding the base64 encodings of two byte strings of the same length takes the same steps. -/
def base642bin_constant_time : Prop :=
  ∀ (c c' : Caller) (binp textp lenp : UInt32) (cap : Nat) (x x' : List UInt8) (variant : UInt32),
    variant ∈ variants → x.length = x'.length →
    DecodePre c (base642binArgs binp textp lenp cap (encode variant x) variant) binp textp lenp cap
      x.length (encode variant x) →
    DecodePre c' (base642binArgs binp textp lenp cap (encode variant x') variant) binp textp lenp cap
      x'.length (encode variant x') →
    SameTrace (c.enter Image.sym_sodium_base642bin) (c'.enter Image.sym_sodium_base642bin)

/-- Comparing takes the same steps whether and where the buffers differ. -/
def memcmp_constant_time : Prop :=
  ∀ (c c' : Caller) (ap bp : UInt32) (a b a' b' : List UInt8), a.length = a'.length →
    MemcmpPre c ap bp a b → MemcmpPre c' ap bp a' b' →
    SameTrace (c.enter Image.sym_sodium_memcmp) (c'.enter Image.sym_sodium_memcmp)

/-- Unpadding takes the same steps whatever the buffer holds: whether the padding is valid, and how
long it is (the information a padding oracle would leak). -/
def unpad_constant_time : Prop :=
  ∀ (c c' : Caller) (lenp bufp : UInt32) (buf buf' : List UInt8) (block : Nat), buf.length = buf'.length →
    UnpadPre c lenp bufp buf block → UnpadPre c' lenp bufp buf' block →
    SameTrace (c.enter Image.sym_sodium_unpad) (c'.enter Image.sym_sodium_unpad)

end Sodium.Utils
