import Solutions.OpensslSha256.Cbv
import Solutions.OpensslSha256.SpecRounds
/-!
# The word identities the compiled rounds use

The compiled code computes the rotations as left rotations (`rolV x c` is `rotr x (32 - c)`), `Ch` as
`((f ^^^ g) &&& e) ^^^ g` and `Maj` as `((b ^^^ c) &&& a) ^^^ (b &&& c)`. After rewriting with these
the two sides of a round's equations agree up to associativity and commutativity of `+`, `^^^`
and `&&&` (`ac_rfl`).
-/
namespace Solutions.OpensslSha256
open Ssl.Spec.Sha256

theorem rolV_rotr (x c n : UInt32) (h1 : 32 - c = n) (h2 : 32 - n = c) : rolV x c = rotr x n := by
  unfold rolV rotr
  rw [Solutions.Logic.shl32, Solutions.Logic.shr32, h1, UInt32.or_comm, h2]

theorem rolV_26 (x : UInt32) : rolV x 26 = rotr x 6 := rolV_rotr x 26 6 (by decide) (by decide)
theorem rolV_21 (x : UInt32) : rolV x 21 = rotr x 11 := rolV_rotr x 21 11 (by decide) (by decide)
theorem rolV_7 (x : UInt32) : rolV x 7 = rotr x 25 := rolV_rotr x 7 25 (by decide) (by decide)
theorem rolV_30 (x : UInt32) : rolV x 30 = rotr x 2 := rolV_rotr x 30 2 (by decide) (by decide)
theorem rolV_19 (x : UInt32) : rolV x 19 = rotr x 13 := rolV_rotr x 19 13 (by decide) (by decide)
theorem rolV_10 (x : UInt32) : rolV x 10 = rotr x 22 := rolV_rotr x 10 22 (by decide) (by decide)
theorem rolV_25 (x : UInt32) : rolV x 25 = rotr x 7 := rolV_rotr x 25 7 (by decide) (by decide)
theorem rolV_14 (x : UInt32) : rolV x 14 = rotr x 18 := rolV_rotr x 14 18 (by decide) (by decide)
theorem rolV_15 (x : UInt32) : rolV x 15 = rotr x 17 := rolV_rotr x 15 17 (by decide) (by decide)
theorem rolV_13 (x : UInt32) : rolV x 13 = rotr x 19 := rolV_rotr x 13 19 (by decide) (by decide)

theorem shrV_eq (x c : UInt32) : shrV x c = x >>> c := rfl
theorem shl0' (x : UInt32) : ShiftLeft.shiftLeft x (0 : UInt32) = x := UInt32.shiftLeft_zero

theorem bit_ext {x y : UInt32} (h : ∀ i, i < 32 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt32.toBitVec_inj.1 (BitVec.eq_of_getLsbD_eq h)

theorem Ch_m (e f g : UInt32) : Ch e f g = ((f ^^^ g) &&& e) ^^^ g := by
  unfold Ch
  apply bit_ext; intro i hi
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_not, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases e.toBitVec.getLsbD i <;> cases f.toBitVec.getLsbD i <;> cases g.toBitVec.getLsbD i <;> rfl

theorem Maj_m (a b c : UInt32) : Maj a b c = ((b ^^^ c) &&& a) ^^^ (b &&& c) := by
  unfold Maj
  apply bit_ext; intro i hi
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases c.toBitVec.getLsbD i <;> rfl

theorem Ws_rec' (blk : List UInt8) (t : Nat) (ht : t < 48 := by decide) :
    (schedule blk)[t + 16]! = sigma1 (schedule blk)[t + 14]! + (schedule blk)[t + 9]! +
      sigma0 (schedule blk)[t + 1]! + (schedule blk)[t]! := Ws_rec blk t ht

/-- Close a round equation: spell out the spec functions, turn the rotations around, and compare up
to associativity and commutativity. -/
macro "sha_alg" : tactic =>
  `(tactic| ((simp only [rolV_26, rolV_21, rolV_7, rolV_30, rolV_19, rolV_10, rolV_25, rolV_14, rolV_15,
      rolV_13, shrV_eq, shl0', Sigma0, Sigma1, sigma0, sigma1, Ch_m, Maj_m]) <;> ac_rfl))

/-- The rewriting half of `sha_alg`. -/
macro "sha_simp" : tactic =>
  `(tactic| (simp only [rolV_26, rolV_21, rolV_7, rolV_30, rolV_19, rolV_10, rolV_25, rolV_14, rolV_15,
      rolV_13, shrV_eq, shl0', Sigma0, Sigma1, sigma0, sigma1, Ch_m, Maj_m]))

example (a b c d e f g h k w : UInt32) :
    (h + (rolV e 26 ^^^ rolV e 21 ^^^ rolV e 7) + (((f ^^^ g) &&& e) ^^^ g) + k + w) =
      h + Sigma1 e + Ch e f g + k + w := by sha_alg

end Solutions.OpensslSha256
