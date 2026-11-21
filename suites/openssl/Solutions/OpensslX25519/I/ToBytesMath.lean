import Solutions.OpensslX25519.MulMath
/-!
# The arithmetic of `fe_tobytes`: the quotient by `p`

`fe_tobytes` first computes `q` by a chain of arithmetic shifts over the limbs (`qChain`), adds
`19·q` to `h0` and carries; the result represents `h - q·p`. For limbs within the `fe_mul` output
bounds (`InM`), `q = ⌊h / p⌋` (`qChain_spec`), so the result is the canonical residue.
-/
namespace Solutions.OpensslX25519.I
open Solutions.OpensslX25519

/-- The `fe_mul`/`fe_sq` output bounds `MulOut` as integer bounds (`⌊1.01·2^25⌋`, `⌊1.01·2^24⌋`). -/
def InM (f : L10) : Prop :=
  -33890058 ≤ f.a0 ∧ f.a0 ≤ 33890058 ∧ -16945029 ≤ f.a1 ∧ f.a1 ≤ 16945029 ∧
    -33890058 ≤ f.a2 ∧ f.a2 ≤ 33890058 ∧ -16945029 ≤ f.a3 ∧ f.a3 ≤ 16945029 ∧
    -33890058 ≤ f.a4 ∧ f.a4 ≤ 33890058 ∧ -16945029 ≤ f.a5 ∧ f.a5 ≤ 16945029 ∧
    -33890058 ≤ f.a6 ∧ f.a6 ≤ 33890058 ∧ -16945029 ≤ f.a7 ∧ f.a7 ≤ 16945029 ∧
    -33890058 ≤ f.a8 ∧ f.a8 ≤ 33890058 ∧ -16945029 ≤ f.a9 ∧ f.a9 ≤ 16945029

/-- `q` as `fe_tobytes` computes it. -/
def qChain (h : L10) : Int :=
  let q := (19 * h.a9 + 2 ^ 24) / 2 ^ 25
  let q := (h.a0 + q) / 2 ^ 26
  let q := (h.a1 + q) / 2 ^ 25
  let q := (h.a2 + q) / 2 ^ 26
  let q := (h.a3 + q) / 2 ^ 25
  let q := (h.a4 + q) / 2 ^ 26
  let q := (h.a5 + q) / 2 ^ 25
  let q := (h.a6 + q) / 2 ^ 26
  let q := (h.a7 + q) / 2 ^ 25
  let q := (h.a8 + q) / 2 ^ 26
  (h.a9 + q) / 2 ^ 25

/-- `⌊(a + ⌊b / 2^i⌋) / 2^j⌋ = ⌊(a·2^i + b) / 2^(i+j)⌋`. -/
theorem ediv_add_ediv (a b : Int) (i j : Nat) :
    (a + b / 2 ^ i) / 2 ^ j = (a * 2 ^ i + b) / 2 ^ (i + j) := by
  have hm : (0 : Int) < 2 ^ i := Int.pow_pos (by decide)
  rw [Int.pow_add, ← Int.ediv_ediv_of_nonneg (Int.le_of_lt hm), Int.add_comm (a * 2 ^ i) b,
    Int.add_mul_ediv_right _ _ (Int.ne_of_gt hm), Int.add_comm (b / 2 ^ i) a]

theorem qChain_eq (h : L10) :
    qChain h = (2 ^ 25 * h.val + 19 * h.a9 + 2 ^ 24) / 2 ^ 280 := by
  cases h
  simp only [qChain, L10.val]
  simp only [ediv_add_ediv, Nat.reduceAdd]
  congr 1
  simp only [Int.reducePow]
  omega

theorem qChain_key (L a9 : Int) (h1 : -2 ^ 230 < L) (h2 : L < 2 ^ 230) (h3 : -16945029 ≤ a9)
    (h4 : a9 ≤ 16945029) :
    (2 ^ 25 * (L + a9 * 2 ^ 230) + 19 * a9 + 2 ^ 24) / 2 ^ 280 * (2 ^ 255 - 19) ≤ L + a9 * 2 ^ 230 ∧
      L + a9 * 2 ^ 230 < ((2 ^ 25 * (L + a9 * 2 ^ 230) + 19 * a9 + 2 ^ 24) / 2 ^ 280 + 1) * (2 ^ 255 - 19) := by
  have : (2 ^ 25 * (L + a9 * 2 ^ 230) + 19 * a9 + 2 ^ 24) / 2 ^ 280 = -1 ∨
      (2 ^ 25 * (L + a9 * 2 ^ 230) + 19 * a9 + 2 ^ 24) / 2 ^ 280 = 0 := by omega
  rcases this with h | h <;> rw [h] <;> omega

theorem qChain_spec (h : L10) (hb : InM h) :
    qChain h * (2 ^ 255 - 19) ≤ h.val ∧ h.val < (qChain h + 1) * (2 ^ 255 - 19) := by
  rw [qChain_eq]
  obtain ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ := hb
  cases h
  simp only [L10.val] at *
  exact qChain_key _ _ (by omega) (by omega) b9 b9'

end Solutions.OpensslX25519.I
