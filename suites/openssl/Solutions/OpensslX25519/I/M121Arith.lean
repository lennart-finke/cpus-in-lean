import Solutions.OpensslX25519.I.M121Math
import Solutions.OpensslX25519.Pair
/-!
# The arithmetic of the run of `fe_mul121666`

Generated (`gen/genm121main.py`): the low word of `shld $7` (the carry `t >> 25` of a pair), the
values `fe_mul121666` shifts are within the signed 64-bit range (`m121_b*`), the carry it multiplies
by `19` is within the signed 32-bit range (`m121_s*`), and the words it stores are the limbs of
`chain121 (m121Raw f)` (`m121_f*`), all by `omega` from the input bounds `InA`.
-/
namespace Solutions.OpensslX25519.I
open X86 Solutions.Exec Solutions.Exec.Mul Solutions.OpensslX25519

theorem shld_toNat7 (c a : UInt32) :
    (sdR true c a 7).toNat = (c.toNat * 2 ^ 32 + a.toNat) * 128 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
  have e : sdR true c a 7 = (((((c.toUInt64 <<< 32) ||| a.toUInt64) <<< (7 : UInt64)) >>> 32).toUInt32) := rfl
  rw [e, UInt64.toNat_toUInt32, u64_shr, u64_shl, or_lo,
    show (7 : UInt64).toNat % 64 = 7 from rfl, show (32 : UInt64).toNat % 64 = 32 from rfl]

theorem shld25 {a c x : UInt32} {T : Int} (h : M64 a c T) (e : x = sdR true c a 7) :
    ∃ C : Int, C = T / 33554432 ∧ M32 x C := by
  refine ⟨_, rfl, ?_⟩
  subst e
  unfold M64 pv at h; unfold M32
  rw [shld_toNat7]
  have := a.toNat_lt; have := c.toNat_lt
  omega

/-- The limbs of `chain121 (m121Raw X)` in terms of its ten carries. -/
def M121V (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) : L10 :=
  ⟨121666 * X0 + C1 * 19 - C6 * 2 ^ 26, 121666 * X1 - C2 * 2 ^ 25 + C6, 121666 * X2 + C2 - C7 * 2 ^ 26,
    121666 * X3 - C3 * 2 ^ 25 + C7, 121666 * X4 + C3 - C8 * 2 ^ 26, 121666 * X5 - C4 * 2 ^ 25 + C8,
    121666 * X6 + C4 - C9 * 2 ^ 26, 121666 * X7 - C5 * 2 ^ 25 + C9, 121666 * X8 + C5 - C10 * 2 ^ 26,
    121666 * X9 - C1 * 2 ^ 25 + C10⟩

theorem m121_chain (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int)
    (k1 : C1 = cr (121666 * X9) 24) (k2 : C2 = cr (121666 * X1) 24) (k3 : C3 = cr (121666 * X3) 24)
    (k4 : C4 = cr (121666 * X5) 24) (k5 : C5 = cr (121666 * X7) 24) (k6 : C6 = cr (121666 * X0 + C1 * 19) 25)
    (k7 : C7 = cr (121666 * X2 + C2) 25) (k8 : C8 = cr (121666 * X4 + C3) 25)
    (k9 : C9 = cr (121666 * X6 + C4) 25) (k10 : C10 = cr (121666 * X8 + C5) 25) :
    chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩) =
      M121V X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 := by
  subst k6 k7 k8 k9 k10
  subst k1 k2 k3 k4 k5
  rfl

theorem m121_b1 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (121666 * X1) + 16777216 ∧ (121666 * X1) + 16777216 < 2 ^ 63 := by
  simp only [InA] at hA
  omega

theorem m121_b2 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (121666 * X3) + 16777216 ∧ (121666 * X3) + 16777216 < 2 ^ 63 := by
  simp only [InA] at hA
  omega

theorem m121_b3 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (121666 * X5) + 16777216 ∧ (121666 * X5) + 16777216 < 2 ^ 63 := by
  simp only [InA] at hA
  omega

theorem m121_b4 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (121666 * X7) + 16777216 ∧ (121666 * X7) + 16777216 < 2 ^ 63 := by
  simp only [InA] at hA
  omega

theorem m121_s0 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432) :
    -2 ^ 31 ≤ C1 ∧ C1 < 2 ^ 31 := by
  simp only [InA] at hA
  omega

theorem m121_chainM (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)) = M121V X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 := by
  have k1 : C1 = cr (121666 * X9) 24 := by
    rw [hC1]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k2 : C2 = cr (121666 * X1) 24 := by
    rw [hC2]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k3 : C3 = cr (121666 * X3) 24 := by
    rw [hC3]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k4 : C4 = cr (121666 * X5) 24 := by
    rw [hC4]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k5 : C5 = cr (121666 * X7) 24 := by
    rw [hC5]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k6 : C6 = cr (121666 * X0 + C1 * 19) 25 := by
    rw [hC6]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k7 : C7 = cr (121666 * X2 + C2) 25 := by
    rw [hC7]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k8 : C8 = cr (121666 * X4 + C3) 25 := by
    rw [hC8]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k9 : C9 = cr (121666 * X6 + C4) 25 := by
    rw [hC9]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  have k10 : C10 = cr (121666 * X8 + C5) 25 := by
    rw [hC10]; simp only [cr, Int.reducePow, Nat.reduceAdd] <;> omega
  exact m121_chain X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10

theorem m121_f0 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 0 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 0 < 2 ^ 31) ∧
      ((C1 * 19) + (121666 * X0)) - (C6 * 67108864) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 0 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f1 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 1 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 1 < 2 ^ 31) ∧
      C6 + ((121666 * X1) - (C2 * 33554432)) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 1 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f2 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 2 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 2 < 2 ^ 31) ∧
      (C2 + (121666 * X2)) - (C7 * 67108864) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 2 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f3 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 3 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 3 < 2 ^ 31) ∧
      C7 + ((121666 * X3) - (C3 * 33554432)) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 3 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f4 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 4 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 4 < 2 ^ 31) ∧
      (C3 + (121666 * X4)) - (C8 * 67108864) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 4 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f5 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 5 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 5 < 2 ^ 31) ∧
      C8 + ((121666 * X5) - (C4 * 33554432)) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 5 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f6 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 6 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 6 < 2 ^ 31) ∧
      (C4 + (121666 * X6)) - (C9 * 67108864) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 6 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f7 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 7 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 7 < 2 ^ 31) ∧
      C9 + ((121666 * X7) - (C5 * 33554432)) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 7 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f8 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 8 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 8 < 2 ^ 31) ∧
      (C5 + (121666 * X8)) - (C10 * 67108864) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 8 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

theorem m121_f9 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hA : InA ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hC1 : C1 = ((121666 * X9) + 16777216) / 33554432)
    (hC2 : C2 = ((121666 * X1) + 16777216) / 33554432)
    (hC3 : C3 = ((121666 * X3) + 16777216) / 33554432)
    (hC4 : C4 = ((121666 * X5) + 16777216) / 33554432)
    (hC5 : C5 = ((121666 * X7) + 16777216) / 33554432)
    (hC6 : C6 = (((C1 * 19) + (121666 * X0)) + 33554432) / 67108864)
    (hC7 : C7 = ((C2 + (121666 * X2)) + 33554432) / 67108864)
    (hC8 : C8 = ((C3 + (121666 * X4)) + 33554432) / 67108864)
    (hC9 : C9 = ((C4 + (121666 * X6)) + 33554432) / 67108864)
    (hC10 : C10 = ((C5 + (121666 * X8)) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 9 ∧ (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 9 < 2 ^ 31) ∧
      C10 + ((121666 * X9) - (C1 * 33554432)) = (chain121 (m121Raw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)).get 9 := by
  rw [m121_chainM X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10]
  simp only [M121V, L10.get]
  simp only [InA] at hA
  omega

end Solutions.OpensslX25519.I
