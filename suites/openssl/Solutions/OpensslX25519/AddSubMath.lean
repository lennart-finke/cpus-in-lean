import Ssl.OpensslX25519.Statement
/-!
# The arithmetic of `fe_add` and `fe_sub`

`fe_add` stores `f[i] + g[i]` (`fe_sub`: `f[i] - g[i]`) as 32-bit words. Under the input bounds
(`AddIn`: every limb below `1.1·2^25` in absolute value) no word overflows a signed 32-bit limb,
so the stored limbs are the exact sums (differences), they satisfy the output bounds (`AddOut`) and
the represented integer is exactly `feValI f ± feValI g`.
-/
namespace Solutions.OpensslX25519
open Ssl.OpensslX25519

theorem toInt_add_small (x y : UInt32) (hx : x.toInt32.toInt.natAbs < 2 ^ 30)
    (hy : y.toInt32.toInt.natAbs < 2 ^ 30) :
    (x + y).toInt32.toInt = x.toInt32.toInt + y.toInt32.toInt := by
  rw [UInt32.toInt32_add, Int32.toInt_add]
  rw [Int.bmod_eq_iff (by decide)]
  refine ⟨by omega, by omega, ?_⟩
  simp

theorem toInt_sub_small (x y : UInt32) (hx : x.toInt32.toInt.natAbs < 2 ^ 30)
    (hy : y.toInt32.toInt.natAbs < 2 ^ 30) :
    (x - y).toInt32.toInt = x.toInt32.toInt - y.toInt32.toInt := by
  rw [UInt32.toInt32_sub, Int32.toInt_sub]
  rw [Int.bmod_eq_iff (by decide)]
  refine ⟨by omega, by omega, ?_⟩
  simp

theorem natAbs_lt_of_addIn {v : Array UInt32} (h : AddIn v) (i : Nat) (hi : i < 10) :
    v[i]!.toInt32.toInt.natAbs < 2 ^ 30 := by
  have := h.2 i hi
  have : 2 ^ (25 - i % 2) ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The ten limbs of a field element, unfolded. -/
theorem feValI_eq (v : Array UInt32) :
    feValI v = v[0]!.toInt32.toInt + v[1]!.toInt32.toInt * 2 ^ 26 + v[2]!.toInt32.toInt * 2 ^ 51 +
      v[3]!.toInt32.toInt * 2 ^ 77 + v[4]!.toInt32.toInt * 2 ^ 102 + v[5]!.toInt32.toInt * 2 ^ 128 +
      v[6]!.toInt32.toInt * 2 ^ 153 + v[7]!.toInt32.toInt * 2 ^ 179 + v[8]!.toInt32.toInt * 2 ^ 204 +
      v[9]!.toInt32.toInt * 2 ^ 230 := by
  simp [feValI, List.range, List.range.loop, Ssl.Spec.X25519.off]

/-- `fe_add`'s result limbs `g[i] + f[i]`. -/
theorem fe_add_math (fv gv w : Array UInt32) (hf : AddIn fv) (hg : AddIn gv)
    (hw : w.size = 10) (hwi : ∀ i, i < 10 → w[i]! = gv[i]! + fv[i]!) :
    AddOut w ∧ feValI w % pI = (feValI fv + feValI gv) % pI := by
  have hs : ∀ i, i < 10 → w[i]!.toInt32.toInt = gv[i]!.toInt32.toInt + fv[i]!.toInt32.toInt := by
    intro i hi
    rw [hwi i hi]
    exact toInt_add_small _ _ (natAbs_lt_of_addIn hg i hi) (natAbs_lt_of_addIn hf i hi)
  refine ⟨⟨hw, fun i hi => ?_⟩, ?_⟩
  · rw [hs i hi]
    have h1 := hf.2 i hi
    have h2 := hg.2 i hi
    have : 2 ^ (26 - i % 2) = 2 * 2 ^ (25 - i % 2) := by
      rw [show 26 - i % 2 = (25 - i % 2) + 1 by omega, Nat.pow_succ]; omega
    omega
  · rw [feValI_eq, feValI_eq fv, feValI_eq gv]
    rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide),
      hs 5 (by decide), hs 6 (by decide), hs 7 (by decide), hs 8 (by decide), hs 9 (by decide)]
    congr 1
    simp only [Int.add_mul]
    omega

/-- `fe_sub`'s result limbs `f[i] - g[i]`. -/
theorem fe_sub_math (fv gv w : Array UInt32) (hf : AddIn fv) (hg : AddIn gv)
    (hw : w.size = 10) (hwi : ∀ i, i < 10 → w[i]! = fv[i]! - gv[i]!) :
    AddOut w ∧ feValI w % pI = (feValI fv - feValI gv) % pI := by
  have hs : ∀ i, i < 10 → w[i]!.toInt32.toInt = fv[i]!.toInt32.toInt - gv[i]!.toInt32.toInt := by
    intro i hi
    rw [hwi i hi]
    exact toInt_sub_small _ _ (natAbs_lt_of_addIn hf i hi) (natAbs_lt_of_addIn hg i hi)
  refine ⟨⟨hw, fun i hi => ?_⟩, ?_⟩
  · rw [hs i hi]
    have h1 := hf.2 i hi
    have h2 := hg.2 i hi
    have : 2 ^ (26 - i % 2) = 2 * 2 ^ (25 - i % 2) := by
      rw [show 26 - i % 2 = (25 - i % 2) + 1 by omega, Nat.pow_succ]; omega
    omega
  · rw [feValI_eq, feValI_eq fv, feValI_eq gv]
    rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide),
      hs 5 (by decide), hs 6 (by decide), hs 7 (by decide), hs 8 (by decide), hs 9 (by decide)]
    congr 1
    simp only [Int.sub_mul]
    omega

end Solutions.OpensslX25519
