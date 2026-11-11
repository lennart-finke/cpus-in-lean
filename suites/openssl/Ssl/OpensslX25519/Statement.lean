import Ssl.Harness
import Ssl.Spec.X25519
import Ssl.OpensslX25519.Image
/-!
# OpenSSL 3.5.9 `crypto/ec/curve25519.c`: the ref10 X25519 equals RFC 7748

Image: `targets/openssl_x25519`: the reference base-2^25.5 implementation of
`crypto/ec/curve25519.c` (the `fe = int32_t[10]` path, selected on i386 because neither
`X25519_ASM` nor `INT128_MAX` is defined), reachable from the roots `ossl_x25519` and
`ossl_x25519_public_from_private`.

All statements are for an arbitrary caller (`Ssl.Harness`) and an arbitrary placement of the
buffers; each call uses at most `stackBound` bytes of stack.

Statement A (field level, on the internal symbols, which the build keeps out of line): a field
element is ten signed 32-bit limbs `t[0..9]` (`typedef int32_t fe[10]`) representing the integer
`Σ t[i]·2^off(i)` over `ℤ`, `off = [0,26,51,77,102,128,153,179,204,230]`. With the limb bounds
quoted from the function comments in `curve25519.c` — `fe_mul`/`fe_sq`: inputs
`|f| bounded by 1.65*2^26,1.65*2^25,1.65*2^26,1.65*2^25,etc.`, outputs
`|h| bounded by 1.01*2^25,1.01*2^24,1.01*2^25,1.01*2^24,etc.`; `fe_add`/`fe_sub`: inputs
`|f| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.`, outputs
`|h| bounded by 1.1*2^26,1.1*2^25,1.1*2^26,1.1*2^25,etc.` — `fe_mul(h, f, g)` stores limbs within the
output bounds whose value is `≡ f·g (mod p)`, `fe_sq(h, f)` likewise `f²`, `fe_add`/`fe_sub` `f ± g`;
each writes only the 40 bytes of `h`. As in the ladder that calls them, the output may be one of
the inputs (`h = f`, `h = g`) or must not overlap it; the inputs may overlap each other.

These functions are `static`; the compiler passes their first two arguments in `ecx` and `edx` and
the third on the stack (`FieldCall`; see `targets/openssl_x25519/NOTES.md` for the evidence in the
pinned disassembly).

Statement B (curve level): for every 32-byte scalar `k` and u-coordinate `u`,
`ossl_x25519(out, k, u)` returns with the 32 bytes at `out` equal to `Spec.X25519.x25519 k u`
(RFC 7748 §5), `eax = 1` if that result is not all-zero and `eax = 0` if it is, writing only `out`.
`ossl_x25519_public_from_private(out, k)` writes `Spec.X25519.x25519 k (9 ∥ 0^31)`. The output may
be one of the input buffers or must not overlap it.
-/
namespace Ssl.OpensslX25519
open X86 Ssl

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
/-- Stack any of the calls may use below its entry stack pointer. -/
def stackBound : Nat := 2048

/-! ## Statement A: the ref10 field operations -/

/-- The signed integer a ref10 limb vector represents: `Σ toInt32(t[i]) · 2^off(i)` with the
radix-2^25.5 offsets of `Spec.X25519.off` (`t[0]+2^26 t[1]+2^51 t[2]+…+2^230 t[9]`). -/
def feValI (v : Array UInt32) : Int :=
  (List.range 10).foldl (fun acc i => acc + v[i]!.toInt32.toInt * 2 ^ Spec.X25519.off i) 0

/-- `|t[i]| ≤ (num/100)·2^e` for even `i` and `≤ (num/100)·2^(e-1)` for odd `i`: the shape in which
`curve25519.c` writes its limb bounds (`"bounded by 1.65*2^26,1.65*2^25,1.65*2^26,1.65*2^25,etc."` is
`Bounded 165 26`). None of the bounds used is an integer, so `≤` and `<` agree. -/
def Bounded (num e : Nat) (v : Array UInt32) : Prop :=
  v.size = 10 ∧ ∀ i, i < 10 → v[i]!.toInt32.toInt.natAbs * 100 ≤ num * 2 ^ (e - i % 2)

instance (num e : Nat) (v : Array UInt32) : Decidable (Bounded num e v) := by
  unfold Bounded; infer_instance

/-- `fe_mul`/`fe_sq` preconditions: `|f| bounded by 1.65*2^26,1.65*2^25,…`. -/
def MulIn : Array UInt32 → Prop := Bounded 165 26
/-- `fe_mul`/`fe_sq` postconditions: `|h| bounded by 1.01*2^25,1.01*2^24,…`. -/
def MulOut : Array UInt32 → Prop := Bounded 101 25
/-- `fe_add`/`fe_sub` preconditions: `|f| bounded by 1.1*2^25,1.1*2^24,…`. -/
def AddIn : Array UInt32 → Prop := Bounded 110 25
/-- `fe_add`/`fe_sub` postconditions: `|h| bounded by 1.1*2^26,1.1*2^25,…`. -/
def AddOut : Array UInt32 → Prop := Bounded 110 26

def pI : Int := Spec.X25519.p

/-- The output `h` may be the input `f` itself, or must not overlap it. -/
def SameOrApart (h f : UInt32) : Prop := h = f ∨ Apart h 40 f 40

instance (h f : UInt32) : Decidable (SameOrApart h f) := by unfold SameOrApart; infer_instance

/-- A call `fn(h, f, g)` of a static field function: `h` in `ecx`, `f` in `edx`, `g` on the stack,
with the limb vectors `fv`, `gv` in memory. -/
def FieldCall2 (c : Caller) (h f g : UInt32) (fv gv : Array UInt32) : Prop :=
  Calls img c stackBound [g] ∧ c.regs.ecx = h ∧ c.regs.edx = f ∧
  Buffer img c stackBound 1 h 40 ∧ Buffer img c stackBound 1 f 40 ∧ Buffer img c stackBound 1 g 40 ∧
  SameOrApart h f ∧ SameOrApart h g ∧
  memWords c.mem f 10 = fv ∧ memWords c.mem g 10 = gv

/-- A call `fn(h, f)` of a static field function: `h` in `ecx`, `f` in `edx`, no stack arguments. -/
def FieldCall1 (c : Caller) (h f : UInt32) (fv : Array UInt32) : Prop :=
  Calls img c stackBound [] ∧ c.regs.ecx = h ∧ c.regs.edx = f ∧
  Buffer img c stackBound 0 h 40 ∧ Buffer img c stackBound 0 f 40 ∧
  SameOrApart h f ∧ memWords c.mem f 10 = fv

instance (c : Caller) (h f g : UInt32) (fv gv : Array UInt32) : Decidable (FieldCall2 c h f g fv gv) := by
  unfold FieldCall2; infer_instance
instance (c : Caller) (h f : UInt32) (fv : Array UInt32) : Decidable (FieldCall1 c h f fv) := by
  unfold FieldCall1; infer_instance

def fe_mul_correct : Prop :=
  ∀ (c : Caller) (h f g : UInt32) (fv gv : Array UInt32),
    FieldCall2 c h f g fv gv → MulIn fv → MulIn gv →
    Returns img (c.enter Image.sym_fe_mul) stackBound (InRange h 40) fun m =>
      MulOut (wordsAt m h 10) ∧
      feValI (wordsAt m h 10) % pI = feValI fv * feValI gv % pI

def fe_sq_correct : Prop :=
  ∀ (c : Caller) (h f : UInt32) (fv : Array UInt32),
    FieldCall1 c h f fv → MulIn fv →
    Returns img (c.enter Image.sym_fe_sq) stackBound (InRange h 40) fun m =>
      MulOut (wordsAt m h 10) ∧
      feValI (wordsAt m h 10) % pI = feValI fv * feValI fv % pI

def fe_add_correct : Prop :=
  ∀ (c : Caller) (h f g : UInt32) (fv gv : Array UInt32),
    FieldCall2 c h f g fv gv → AddIn fv → AddIn gv →
    Returns img (c.enter Image.sym_fe_add) stackBound (InRange h 40) fun m =>
      AddOut (wordsAt m h 10) ∧
      feValI (wordsAt m h 10) % pI = (feValI fv + feValI gv) % pI

def fe_sub_correct : Prop :=
  ∀ (c : Caller) (h f g : UInt32) (fv gv : Array UInt32),
    FieldCall2 c h f g fv gv → AddIn fv → AddIn gv →
    Returns img (c.enter Image.sym_fe_sub) stackBound (InRange h 40) fun m =>
      AddOut (wordsAt m h 10) ∧
      feValI (wordsAt m h 10) % pI = (feValI fv - feValI gv) % pI

/-! ## Statement B: the scalar multiplication -/

/-- The 32-byte output may be the 32-byte input at `p` itself, or must not overlap it. -/
def SameOrApart32 (out p : UInt32) : Prop := out = p ∨ Apart out 32 p 32

instance (out p : UInt32) : Decidable (SameOrApart32 out p) := by unfold SameOrApart32; infer_instance

/-- A call `ossl_x25519(out, kp, up)` with the scalar `k` and the u-coordinate `u` in memory. -/
def X25519Pre (c : Caller) (out kp up : UInt32) (k u : List UInt8) : Prop :=
  Calls img c stackBound [out, kp, up] ∧
  k.length = 32 ∧ u.length = 32 ∧
  Buffer img c stackBound 3 out 32 ∧ Buffer img c stackBound 3 kp 32 ∧ Buffer img c stackBound 3 up 32 ∧
  SameOrApart32 out kp ∧ SameOrApart32 out up ∧
  memBytes c.mem kp 32 = k ∧ memBytes c.mem up 32 = u

/-- A call `ossl_x25519_public_from_private(out, kp)` with the scalar `k` in memory. -/
def PublicPre (c : Caller) (out kp : UInt32) (k : List UInt8) : Prop :=
  Calls img c stackBound [out, kp] ∧ k.length = 32 ∧
  Buffer img c stackBound 2 out 32 ∧ Buffer img c stackBound 2 kp 32 ∧
  SameOrApart32 out kp ∧ memBytes c.mem kp 32 = k

instance (c : Caller) (out kp up : UInt32) (k u : List UInt8) : Decidable (X25519Pre c out kp up k u) := by
  unfold X25519Pre; infer_instance
instance (c : Caller) (out kp : UInt32) (k : List UInt8) : Decidable (PublicPre c out kp k) := by
  unfold PublicPre; infer_instance

/-- The return value: `CRYPTO_memcmp(kZeros, out, 32) != 0`, i.e. `1` unless the shared secret is
all-zero (the peer value was a point of small order), then `0`. -/
def retVal (r : List UInt8) : UInt32 := if r = List.replicate 32 0 then 0 else 1

def ossl_x25519_correct : Prop :=
  ∀ (c : Caller) (out kp up : UInt32) (k u : List UInt8), X25519Pre c out kp up k u →
    Returns img (c.enter Image.sym_ossl_x25519) stackBound (InRange out 32) fun m =>
      bytesAt m out 32 = Spec.X25519.x25519 k u ∧
      m.cpu.eax = retVal (Spec.X25519.x25519 k u)

/-- The u-coordinate `9` of the Curve25519 base point, encoded (RFC 7748 §4.1). -/
def basePoint : List UInt8 := 9 :: List.replicate 31 0

def ossl_x25519_public_from_private_correct : Prop :=
  ∀ (c : Caller) (out kp : UInt32) (k : List UInt8), PublicPre c out kp k →
    Returns img (c.enter Image.sym_ossl_x25519_public_from_private) stackBound (InRange out 32) fun m =>
      bytesAt m out 32 = Spec.X25519.x25519 k basePoint

end Ssl.OpensslX25519
