import Solutions.OpensslX25519.MulMath
/-!
# The arithmetic of `fe_mul121666`

Over `ℤ`, no machine: the limbs `121666·f[i]` (`m121Raw`), then the carry chain of `fe_mul121666` in
`curve25519.c` (`carry9` with the `19`-fold into `h0`, `carry1, carry3, carry5, carry7`, then
`carry0, carry2, carry4, carry6, carry8`, each `carry = (h + 2^(s-1)) >> s`, `chain121`). The chain
changes the represented value by a multiple of `p` (`chain121_dvd`), and from the `fe_add`/`fe_sub`
output bounds `AddOut` (the ladder's argument `tmp1 = AA - BB`) its limbs satisfy `MulOut`
(`chain121_bound`), hence the `fe_add` input bounds `AddIn` as well.
-/
namespace Solutions.OpensslX25519
open Ssl.OpensslX25519

/-- The limbs times `121666`. -/
def m121Raw (f : L10) : L10 :=
  ⟨121666 * f.a0, 121666 * f.a1, 121666 * f.a2, 121666 * f.a3, 121666 * f.a4, 121666 * f.a5,
    121666 * f.a6, 121666 * f.a7, 121666 * f.a8, 121666 * f.a9⟩

theorem m121Raw_val (f : L10) : (m121Raw f).val = 121666 * f.val := by
  cases f; simp only [m121Raw, L10.val]; omega

/-- The carry chain of `fe_mul121666`. -/
def chain121 (h : L10) : L10 :=
  let c9 := cr h.a9 24
  let h0 := h.a0 + c9 * 19
  let h9 := h.a9 - c9 * 2 ^ 25
  let c1 := cr h.a1 24
  let h2 := h.a2 + c1
  let h1 := h.a1 - c1 * 2 ^ 25
  let c3 := cr h.a3 24
  let h4 := h.a4 + c3
  let h3 := h.a3 - c3 * 2 ^ 25
  let c5 := cr h.a5 24
  let h6 := h.a6 + c5
  let h5 := h.a5 - c5 * 2 ^ 25
  let c7 := cr h.a7 24
  let h8 := h.a8 + c7
  let h7 := h.a7 - c7 * 2 ^ 25
  let c0 := cr h0 25
  let h1 := h1 + c0
  let h0 := h0 - c0 * 2 ^ 26
  let c2 := cr h2 25
  let h3 := h3 + c2
  let h2 := h2 - c2 * 2 ^ 26
  let c4 := cr h4 25
  let h5 := h5 + c4
  let h4 := h4 - c4 * 2 ^ 26
  let c6 := cr h6 25
  let h7 := h7 + c6
  let h6 := h6 - c6 * 2 ^ 26
  let c8 := cr h8 25
  let h9 := h9 + c8
  let h8 := h8 - c8 * 2 ^ 26
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem chain121_dvd (h : L10) : (2 ^ 255 - 19 : Int) ∣ h.val - (chain121 h).val := by
  cases h
  simp only [chain121, L10.val]
  omega

/-- The input bounds `AddOut` as integer bounds (`⌊1.1·2^26⌋`, `⌊1.1·2^25⌋`). -/
def InA (f : L10) : Prop :=
  -73819750 ≤ f.a0 ∧ f.a0 ≤ 73819750 ∧ -36909875 ≤ f.a1 ∧ f.a1 ≤ 36909875 ∧
    -73819750 ≤ f.a2 ∧ f.a2 ≤ 73819750 ∧ -36909875 ≤ f.a3 ∧ f.a3 ≤ 36909875 ∧
    -73819750 ≤ f.a4 ∧ f.a4 ≤ 73819750 ∧ -36909875 ≤ f.a5 ∧ f.a5 ≤ 36909875 ∧
    -73819750 ≤ f.a6 ∧ f.a6 ≤ 73819750 ∧ -36909875 ≤ f.a7 ∧ f.a7 ≤ 36909875 ∧
    -73819750 ≤ f.a8 ∧ f.a8 ≤ 73819750 ∧ -36909875 ≤ f.a9 ∧ f.a9 ≤ 36909875

theorem chain121_bound (f : L10) (hf : InA f) (i : Nat) (hi : i < 10) :
    ((chain121 (m121Raw f)).get i).natAbs * 100 ≤ 101 * 2 ^ (25 - i % 2) := by
  obtain ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ := hf
  cases f
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [chain121, m121Raw, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at *
    omega

theorem inA_of_addOut {v : Array UInt32} (h : AddOut v) : InA (lift v) := by
  have b0 := h.2 0 (by decide)
  have b1 := h.2 1 (by decide)
  have b2 := h.2 2 (by decide)
  have b3 := h.2 3 (by decide)
  have b4 := h.2 4 (by decide)
  have b5 := h.2 5 (by decide)
  have b6 := h.2 6 (by decide)
  have b7 := h.2 7 (by decide)
  have b8 := h.2 8 (by decide)
  have b9 := h.2 9 (by decide)
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reducePow, Nat.reduceMul] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  simp only [InA, lift]
  omega

/-- `w` holds the limbs of the chain over `121666·f`: then it satisfies `MulOut` and represents
`121666·f` modulo `p`. -/
theorem fe_m121_math (fv w : Array UInt32) (hf : AddOut fv) (hw : w.size = 10)
    (hwi : ∀ i, i < 10 → w[i]!.toInt32.toInt = (chain121 (m121Raw (lift fv))).get i) :
    MulOut w ∧ feValI w % pI = 121666 * feValI fv % pI := by
  refine ⟨⟨hw, fun i hi => ?_⟩, ?_⟩
  · rw [hwi i hi]
    exact chain121_bound _ (inA_of_addOut hf) i hi
  · have ev : feValI w = (chain121 (m121Raw (lift fv))).val := by
      rw [feValI_eq, hwi 0 (by decide), hwi 1 (by decide), hwi 2 (by decide), hwi 3 (by decide),
        hwi 4 (by decide), hwi 5 (by decide), hwi 6 (by decide), hwi 7 (by decide), hwi 8 (by decide),
        hwi 9 (by decide)]
      rfl
    rw [ev, ← lift_val fv, ← m121Raw_val, pI_eq]
    have hd := chain121_dvd (m121Raw (lift fv))
    generalize (chain121 (m121Raw (lift fv))).val = a at *
    generalize (m121Raw (lift fv)).val = b at *
    omega

/-- The `fe_mul`/`fe_sq` output bounds are within the `fe_add`/`fe_sub` input bounds. -/
theorem addIn_of_mulOut {v : Array UInt32} (h : MulOut v) : AddIn v :=
  ⟨h.1, fun i hi => Nat.le_trans (h.2 i hi) (Nat.mul_le_mul_right _ (by decide))⟩

/-- The `fe_add`/`fe_sub` output bounds are within the `fe_mul`/`fe_sq` input bounds. -/
theorem mulIn_of_addOut {v : Array UInt32} (h : AddOut v) : MulIn v :=
  ⟨h.1, fun i hi => Nat.le_trans (h.2 i hi) (Nat.mul_le_mul_right _ (by decide))⟩

/-- The `fe_mul`/`fe_sq` output bounds are within their input bounds. -/
theorem mulIn_of_mulOut {v : Array UInt32} (h : MulOut v) : MulIn v := by
  refine ⟨h.1, fun i hi => Nat.le_trans (h.2 i hi) ?_⟩
  have : 2 ^ (25 - i % 2) * 2 = 2 ^ (26 - i % 2) := by
    rw [← Nat.pow_succ]; congr 1; omega
  omega

end Solutions.OpensslX25519
