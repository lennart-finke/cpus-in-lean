import Sodium.Proofs.HexDigits
/-!
# `sodium_hex2bin`: what the loop computes from a character

The loop's instructions (`HexDecLoop1`, `HexDecLoop2`) composed, as functions of the character `v`
loaded: `nOf` (`(v ^ 0x30) - 10 >> 8`, all ones on a decimal digit), `alOf` (`(v & ~0x20) - 55` as a
byte), `aOf` (all ones on a letter `a … f`), `rOf` (non-zero on a hexadecimal digit), `valOf` (the
value of the digit), `bxOf` (the word stored at `t`), `hivOf` (the value shifted to the high nibble,
stored at `t + 8`), `outOf` (the byte stored, from the high nibble `A`). Checked on all bytes by
kernel evaluation: the two digits of `hex [b]` are valid and give back `b`.
-/
namespace Sodium.Proofs.HexDec
open X86 Solutions.Exec Sodium.Spec

def nOf (v : UInt32) : UInt32 := ((v.xor 48).add 65526).shiftRight 8

def alOf (v : UInt32) : UInt32 :=
  let c9 := (v.land 4294967040).lor (((v.land 255).land 223).land 255)
  let c10 := (c9.land 4294967040).lor ((addF 1 (c9.land 255) 201 0).1.land 255)
  c10.land 255

def aOf (v : UInt32) : UInt32 := (((alOf v).add 65526).xor ((alOf v).add 65520)).shiftRight 8

def rOf (v : UInt32) : UInt32 := ((nOf v).land 255).lor ((aOf v).land 255)

def valOf (v : UInt32) : UInt32 := ((nOf v).land (v.xor 48)).lor ((aOf v).land (alOf v))

def bxOf (v : UInt32) : UInt32 :=
  (((nOf v).land 4294967040).lor ((rOf v).land 255) |>.land 4294967040).lor 1

def hivOf (v : UInt32) : UInt32 :=
  ((valOf v).land 4294967040).lor (((((valOf v).land 255).shiftLeft 4).land 255).land 255)

def outOf (v A : UInt32) : UInt32 := ((valOf v).land 4294967040).lor ((((valOf v).land 255).lor A).land 255)

/-- The byte stored for the two characters `c1 c2`. -/
def pairByte (c1 c2 : UInt8) : UInt8 :=
  ((outOf c2.toUInt32 (hivOf c1.toUInt32).toUInt8.toUInt32).land 255).toUInt8

theorem dig_fin : ∀ k : Fin 256,
    (rOf (hexDigit (k.val.toUInt8 >>> 4)).toUInt32).toNat ≠ 0 ∧
    (rOf (hexDigit (k.val.toUInt8 &&& 15)).toUInt32).toNat ≠ 0 ∧
    pairByte (hexDigit (k.val.toUInt8 >>> 4)) (hexDigit (k.val.toUInt8 &&& 15)) = k.val.toUInt8 ∧
    ((bxOf (hexDigit (k.val.toUInt8 &&& 15)).toUInt32).land 255) = 1 := by
  decide +kernel

theorem dig_spec (b : UInt8) :
    (rOf (hexDigit (b >>> 4)).toUInt32).toNat ≠ 0 ∧ (rOf (hexDigit (b &&& 15)).toUInt32).toNat ≠ 0 ∧
    pairByte (hexDigit (b >>> 4)) (hexDigit (b &&& 15)) = b ∧
    ((bxOf (hexDigit (b &&& 15)).toUInt32).land 255) = 1 := by
  have h := dig_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using h

end Sodium.Proofs.HexDec
