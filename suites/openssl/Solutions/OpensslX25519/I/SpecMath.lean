import Ssl.OpensslX25519.Statement
/-!
# The RFC 7748 side of X25519: facts about `Ssl.Spec.X25519`

`powMod` is the power modulo `m` (`powMod_eq`), so `inv x = x^(p-2) mod p`; a limb vector `v`
*represents* the residue `x < p` when `feValI v ≡ x (mod p)` (`Rep`), and the field operations of
the code act on representatives as `addp`, `subp`, `mulp` act on residues (`Rep.add`, `Rep.sub`,
`Rep.mul`); the bit the ladder reads at position `pos` of a little-endian byte string (`leNat_bit`).
-/
namespace Solutions.OpensslX25519.I
open Ssl Ssl.Spec.X25519 Ssl.OpensslX25519

/-! ## Powers -/

theorem powModAux_eq : ∀ (f b e m : Nat), 1 < m → e < 2 ^ f → powModAux f b e m = b ^ e % m
  | 0, b, e, m, hm, he => by
    have : e = 0 := by simp at he; omega
    subst this
    simp [powModAux, Nat.mod_eq_of_lt hm]
  | f + 1, b, e, m, hm, he => by
    unfold powModAux
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have ih := powModAux_eq f (b * b % m) (e / 2) m hm (by rw [Nat.pow_succ] at he; omega)
      simp only
      rw [ih, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1, Nat.mod_mul_mod, ← Nat.pow_succ]
        congr 2; omega
      · rw [if_neg h1]
        congr 2; omega

theorem powMod_eq (b e m : Nat) (hm : 1 < m) (he : e < 2 ^ 300) : powMod b e m = b ^ e % m := by
  unfold powMod
  rw [powModAux_eq 300 _ e m hm he, ← Nat.pow_mod]

theorem p_gt : 1 < p := by unfold p; decide

theorem inv_eq (x : Nat) : inv x = x ^ (p - 2) % p := powMod_eq _ _ _ p_gt (by unfold p; decide)

/-! ## Powers of a residue (`fe_invert`) -/

theorem pow_sq_emod {f h Z P : Int} {a : Nat} (hf : f % P = Z ^ a % P) (hh : h % P = f * f % P) :
    h % P = Z ^ (2 * a) % P := by
  rw [hh, Int.mul_emod, hf, ← Int.mul_emod, ← Int.pow_add]
  congr 2; omega

theorem pow_mul_emod {f g h Z P : Int} {a b : Nat} (hf : f % P = Z ^ a % P) (hg : g % P = Z ^ b % P)
    (hh : h % P = f * g % P) : h % P = Z ^ (a + b) % P := by
  rw [hh, Int.mul_emod, hf, hg, ← Int.mul_emod, ← Int.pow_add]

theorem pow_one_emod (Z P : Int) : Z % P = Z ^ 1 % P := by rw [Int.pow_one]

/-! ## Representatives -/

theorem pI_pos : (0 : Int) < pI := by unfold pI p; decide

theorem pI_nat : pI = ((p : Nat) : Int) := rfl

/-- `v` represents the residue `x`. -/
def Rep (v : Array UInt32) (x : Nat) : Prop := feValI v % pI = (x : Int)

theorem Rep.lt {v : Array UInt32} {x : Nat} (h : Rep v x) : x < p := by
  have h1 := Int.emod_lt_of_pos (feValI v) pI_pos
  unfold Rep at h; rw [h, pI_nat] at h1; omega

theorem Rep.of_mod {v : Array UInt32} {a : Int} {x : Nat} (h : feValI v % pI = a % pI) (hx : (x : Int) = a % pI) :
    Rep v x := by unfold Rep; rw [h, hx]

theorem natCast_mod_p (n : Nat) : ((n % p : Nat) : Int) = (n : Int) % pI := by
  rw [pI_nat]; exact Int.natCast_emod n p

theorem Rep.add {f g h : Array UInt32} {a b : Nat} (hf : Rep f a) (hg : Rep g b)
    (hh : feValI h % pI = (feValI f + feValI g) % pI) : Rep h (addp a b) := by
  unfold Rep at *
  rw [hh, Int.add_emod, hf, hg, addp, natCast_mod_p]; rfl

theorem Rep.mul {f g h : Array UInt32} {a b : Nat} (hf : Rep f a) (hg : Rep g b)
    (hh : feValI h % pI = feValI f * feValI g % pI) : Rep h (mulp a b) := by
  unfold Rep at *
  rw [hh, Int.mul_emod, hf, hg, mulp, natCast_mod_p]; rfl

theorem Rep.sub {f g h : Array UInt32} {a b : Nat} (hf : Rep f a) (hg : Rep g b)
    (hh : feValI h % pI = (feValI f - feValI g) % pI) : Rep h (subp a b) := by
  have hb := hg.lt
  unfold Rep at *
  rw [hh, Int.sub_emod, hf, hg, subp, natCast_mod_p, Nat.mod_eq_of_lt hb]
  have e : ((a + p - b : Nat) : Int) = ((a : Int) - b) + pI := by rw [pI_nat]; omega
  rw [e, Int.add_emod_right]

theorem Rep.m121 {f h : Array UInt32} {a : Nat} (hf : Rep f a) (hh : feValI h % pI = 121666 * feValI f % pI) :
    Rep h (121666 * a % p) := by
  unfold Rep at *
  rw [hh, Int.mul_emod, hf, natCast_mod_p]
  rfl

theorem add_emod_mod (x y : Int) : (x + y % pI) % pI = (x + y) % pI := by
  rw [Int.add_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← Int.add_emod]

/-- `fe_mul121666` gives the ladder's `AA + a24·E` from `BB`: with `E = AA - BB`,
`BB + 121666·E = AA + 121665·E`. -/
theorem a24_identity (AA BB : Nat) (hB : BB < p) :
    addp BB (121666 * subp AA BB % p) = addp AA (mulp a24 (subp AA BB)) := by
  unfold addp mulp a24
  generalize hE : subp AA BB = E
  have hE' : ((E : Nat) : Int) % pI = ((AA : Int) - BB) % pI := by
    rw [← hE]; unfold subp
    rw [natCast_mod_p, Nat.mod_eq_of_lt hB]
    have e : ((AA + p - BB : Nat) : Int) = ((AA : Int) - BB) + pI := by rw [pI_nat]; omega
    rw [e, Int.add_emod_right, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  apply Int.ofNat_inj.mp
  rw [natCast_mod_p, natCast_mod_p, Int.natCast_add, Int.natCast_add, natCast_mod_p, natCast_mod_p,
    add_emod_mod, add_emod_mod, Int.natCast_mul, Int.natCast_mul]
  have hd : pI ∣ ((E : Int) - ((AA : Int) - BB)) :=
    Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hE', Int.sub_self, Int.zero_emod])
  obtain ⟨t, ht⟩ := hd
  have : ((BB : Int) + ((121666 : Nat) : Int) * (E : Int)) = ((AA : Int) + ((121665 : Nat) : Int) * (E : Int)) + pI * t := by
    generalize pI * t = W at *
    omega
  rw [this, Int.add_mul_emod_self_left]

/-! ## Bits of a little-endian byte string -/

theorem leNat_cons (b : UInt8) (bs : List UInt8) : leNat (b :: bs) = b.toNat + 256 * leNat bs := rfl

theorem leNat_bit : ∀ (bs : List UInt8) (pos : Nat), pos < 8 * bs.length →
    (leNat bs >>> pos) % 2 = ((bs[pos / 8]!).toNat >>> (pos % 8)) % 2
  | [], pos, h => by simp at h
  | b :: bs, pos, h => by
    rw [leNat_cons, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have hb := b.toNat_lt
    by_cases hp : pos < 8
    · have e1 : pos / 8 = 0 := by omega
      have e2 : pos % 8 = pos := by omega
      rw [e1, e2]
      simp only [List.getElem!_cons_zero]
      generalize leNat bs = L
      generalize b.toNat = c at hb ⊢
      rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3 ∨ pos = 4 ∨ pos = 5 ∨ pos = 6 ∨ pos = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega
    · have ih := leNat_bit bs (pos - 8) (by simp at h; omega)
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at ih
      have e1 : pos / 8 = (pos - 8) / 8 + 1 := by omega
      have e2 : pos % 8 = (pos - 8) % 8 := by omega
      rw [e1, e2, List.getElem!_cons_succ, ← ih]
      have e3 : 2 ^ pos = 256 * 2 ^ (pos - 8) := by
        rw [show pos = 8 + (pos - 8) by omega, Nat.pow_add]; simp
      rw [e3, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]

end Solutions.OpensslX25519.I
