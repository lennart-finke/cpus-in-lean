import Solutions.OpensslX25519.I.LadSpec
/-!
# The end of the ladder: OpenSSL omits the last conditional swap

`ladder_eq`: for an even scalar (a clamped one, `decodeScalar_even`) the final swap of
`Spec.X25519.ladder` does nothing, so the result is `x₂ · z₂^(p-2)` of `ladFrom x₁ k 255`; `Rep.inv`: the
value `fe_invert` computes represents `inv z`. Prover P.
-/
namespace Solutions.OpensslX25519.I
open Ssl Ssl.Spec.X25519 Ssl.OpensslX25519

theorem ladder_eq (k u : Nat) (hk : k % 2 = 0) :
    ladder k u = mulp (ladFrom (u % p) k 255 (1, 0, u % p, 1, 0)).1
      (inv (ladFrom (u % p) k 255 (1, 0, u % p, 1, 0)).2.1) := by
  have hs := ladFrom_swap (u % p) k 254 (1, 0, u % p, 1, 0)
  have h0 : (k >>> 0) &&& 1 = 0 := by
    rw [Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod k 1]; simpa using hk
  rw [h0] at hs
  unfold ladder
  dsimp only
  rw [ladder_fold]
  generalize ladFrom (u % p) k 255 (1, 0, u % p, 1, 0) = st at hs ⊢
  obtain ⟨a, b, c, d, e⟩ := st
  simp only at hs
  subst hs
  rfl

theorem pow_emod' (a n : Int) : ∀ e : Nat, a ^ e % n = (a % n) ^ e % n
  | 0 => by simp
  | e + 1 => by
    rw [Int.pow_succ, Int.pow_succ, Int.mul_emod, pow_emod' a n e, Int.mul_emod ((a % n) ^ e) (a % n), Int.emod_emod]

/-- `fe_invert`'s value represents the inverse. -/
theorem Rep.inv {f h : Array UInt32} {z : Nat} (hf : Rep f z)
    (hh : feValI h % pI = feValI f ^ (2 ^ 255 - 21) % pI) : Rep h (inv z) := by
  unfold Rep at *
  have hp2 : p - 2 = 2 ^ 255 - 21 := by unfold p; rw [Nat.sub_sub]
  rw [hh, pow_emod', hf, inv_eq, natCast_mod_p, Int.natCast_pow, hp2]

theorem decodeScalar_even (k : List UInt8) : decodeScalar k % 2 = 0 := by
  unfold decodeScalar clamp
  rw [List.range_eq_range', show (32 : Nat) = 31 + 1 from rfl, List.range'_succ, List.map_cons, leNat_cons]
  have hb : (k[0]! &&& 248).toNat % 2 = 0 := by
    rw [UInt8.toNat_and, ← Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.and_assoc,
      show (UInt8.toNat 248 &&& (2 ^ 1 - 1) : Nat) = 0 by decide, Nat.and_zero]
  simp only [ite_true]
  omega

end Solutions.OpensslX25519.I
