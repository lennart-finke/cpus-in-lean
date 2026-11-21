import Sodium.Spec.Utils
import Solutions.Exec.Alu
/-!
# `sodium_bin2hex`: the two digits the loop computes for a byte

`hiOf v` and `loOf v` are the results of the loop's instructions composed (`HexEncSteps`, from the
byte load at 0x100030 to the stores at 0x100066 and 0x100069). On each of the 256 bytes they are the
digits of `Sodium.Spec.hex` (checked by kernel evaluation). Also: where the digits of a byte are in
`hex x`.
-/
namespace Sodium.Proofs.HexEnc
open X86 Solutions.Exec Sodium.Spec

/-- The first digit the loop stores for the byte `v` (the instruction results composed). -/
def hiOf (v : UInt32) : UInt32 :=
  let b1 := v.shiftRight 4
  let d6 := (((b1.add 65526).shiftRight 8).land 217).add b1
  ((d6.land 4294967040).lor ((addF 1 (d6.land 255) 87 0).1.land 255)).land 255

/-- The second digit. -/
def loOf (v : UInt32) : UInt32 :=
  let c2 := v.land 15
  let c4 := ((c2.shiftLeft 8).add ((c2.add 65526).land 55552)).add 22272
  (c4.shiftRight 8).land 255

theorem hiOf_fin : ∀ k : Fin 256,
    (hiOf k.val.toUInt8.toUInt32).toUInt8 = hexDigit (k.val.toUInt8 >>> 4) := by
  decide +kernel

theorem loOf_fin : ∀ k : Fin 256,
    (loOf k.val.toUInt8.toUInt32).toUInt8 = hexDigit (k.val.toUInt8 &&& 15) := by
  decide +kernel

theorem hiOf_spec (v : UInt8) : (hiOf v.toUInt32).toUInt8 = hexDigit (v >>> 4) := by
  have h := hiOf_fin ⟨v.toNat, v.toNat_lt⟩
  simpa using h

theorem loOf_spec (v : UInt8) : (loOf v.toUInt32).toUInt8 = hexDigit (v &&& 15) := by
  have h := loOf_fin ⟨v.toNat, v.toNat_lt⟩
  simpa using h

/-! ## The digits in `hex x` -/

theorem hex_cons (b : UInt8) (x : List UInt8) :
    hex (b :: x) = hexDigit (b >>> 4) :: hexDigit (b &&& 15) :: hex x := by
  simp only [hex, List.flatMap_cons]; rfl

theorem hex_nil : hex [] = [] := rfl

theorem hex_length (x : List UInt8) : (hex x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [hex_cons]; simp [ih]; omega

theorem hex_getD_hi (x : List UInt8) (k : Nat) (hk : k < x.length) :
    (hex x).getD (2 * k) 0 = hexDigit (x.getD k 0 >>> 4) := by
  induction x generalizing k with
  | nil => simp at hk
  | cons b x ih =>
    rw [hex_cons]
    cases k with
    | zero => simp
    | succ k =>
      have := ih k (by simp at hk; omega)
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
      simpa using this

theorem hex_getD_lo (x : List UInt8) (k : Nat) (hk : k < x.length) :
    (hex x).getD (2 * k + 1) 0 = hexDigit (x.getD k 0 &&& 15) := by
  induction x generalizing k with
  | nil => simp at hk
  | cons b x ih =>
    rw [hex_cons]
    cases k with
    | zero => simp
    | succ k =>
      have := ih k (by simp at hk; omega)
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by omega]
      simpa using this

end Sodium.Proofs.HexEnc
