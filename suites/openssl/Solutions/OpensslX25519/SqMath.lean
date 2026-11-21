import Solutions.OpensslX25519.MulMath
/-!
# The arithmetic of the run of `fe_sq`

Generated (`.lake/scratch/i/genmain.py`): the sums of products that `fe_sq` accumulates are the
limbs of `mulRaw f f` (`sq_h*`, ring identities by `grind`), the values it shifts are within the
signed 64-bit range (`sq_b*`), and the words it stores are the limbs of `carryChain` within the
signed 32-bit range (`sq_f*`), all by `omega` from the bounds `RawB` of the limbs.
-/
namespace Solutions.OpensslX25519

theorem sq_h0 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    ((((((38 * X5) * X5) + (X0 * X0)) + ((19 * X6) * (2 * X4))) + ((38 * X7) * (2 * X3))) + ((19 * X8) * (2 * X2))) + ((38 * X9) * (2 * X1)) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a0 := by
  simp only [mulRaw]
  grind

theorem sq_h4 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((X2 * X2) + ((2 * X3) * (2 * X1))) + (X4 * (2 * X0))) + ((38 * X7) * X7)) + ((19 * X8) * (2 * X6))) + ((38 * X9) * (2 * X5)) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a4 := by
  simp only [mulRaw]
  grind

theorem sq_h1 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((19 * X6) * (2 * X5)) + ((2 * X0) * X1)) + ((38 * X7) * X4)) + ((19 * X8) * (2 * X3))) + ((38 * X9) * X2) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a1 := by
  simp only [mulRaw]
  grind

theorem sq_h5 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((2 * X2) * X3) + (X4 * (2 * X1))) + (X5 * (2 * X0))) + ((19 * X8) * (2 * X7))) + ((38 * X9) * X6) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a5 := by
  simp only [mulRaw]
  grind

theorem sq_h2 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    ((((((2 * X1) * X1) + (X2 * (2 * X0))) + ((19 * X6) * X6)) + ((38 * X7) * (2 * X5))) + ((19 * X8) * (2 * X4))) + ((38 * X9) * (2 * X3)) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a2 := by
  simp only [mulRaw]
  grind

theorem sq_h6 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    ((((((2 * X3) * X3) + (X4 * (2 * X2))) + ((2 * X5) * (2 * X1))) + (X6 * (2 * X0))) + ((19 * X8) * X8)) + ((38 * X9) * (2 * X7)) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a6 := by
  simp only [mulRaw]
  grind

theorem sq_h3 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((2 * X1) * X2) + (X3 * (2 * X0))) + ((38 * X7) * X6)) + ((19 * X8) * (2 * X5))) + ((38 * X9) * X4) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a3 := by
  simp only [mulRaw]
  grind

theorem sq_h7 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((2 * X3) * X4) + (X5 * (2 * X2))) + (X6 * (2 * X1))) + (X7 * (2 * X0))) + ((38 * X9) * X8) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a7 := by
  simp only [mulRaw]
  grind

theorem sq_h8 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((X4 * X4) + (X6 * (2 * X2))) + ((2 * X5) * (2 * X3))) + ((2 * X7) * (2 * X1))) + (X8 * (2 * X0))) + ((38 * X9) * X9) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a8 := by
  simp only [mulRaw]
  grind

theorem sq_h9 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : Int) :
    (((((2 * X4) * X5) + (X6 * (2 * X3))) + (X7 * (2 * X2))) + (X8 * (2 * X1))) + (X9 * (2 * X0)) = (mulRaw ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩).a9 := by
  simp only [mulRaw]
  grind

theorem sq_b0 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩) :
    -2 ^ 63 ≤ R0 + 33554432 ∧ R0 + 33554432 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b1 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864) :
    -2 ^ 63 ≤ R4 + 33554432 ∧ R4 + 33554432 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b2 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864) :
    -2 ^ 63 ≤ (R1 + C1) + 16777216 ∧ (R1 + C1) + 16777216 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b3 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (R5 + C2) + 16777216 ∧ (R5 + C2) + 16777216 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b4 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (R2 + C3) + 33554432 ∧ (R2 + C3) + 33554432 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b5 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864) :
    -2 ^ 63 ≤ (R6 + C4) + 33554432 ∧ (R6 + C4) + 33554432 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b6 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864) :
    -2 ^ 63 ≤ (R3 + C5) + 16777216 ∧ (R3 + C5) + 16777216 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b7 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432) :
    -2 ^ 63 ≤ (R7 + C6) + 16777216 ∧ (R7 + C6) + 16777216 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b9 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864) :
    -2 ^ 63 ≤ (R8 + C8) + 33554432 ∧ (R8 + C8) + 33554432 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_b10 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864) :
    -2 ^ 63 ≤ (R9 + C10) + 16777216 ∧ (R9 + C10) + 16777216 < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega

theorem sq_f0 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 0 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 0 < 2 ^ 31) ∧
      ((19 * C11) + (R0 - (C1 * 67108864))) - (C12 * 67108864) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 0 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 0 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f1 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 1 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 1 < 2 ^ 31) ∧
      C12 + ((R1 + C1) - (C3 * 33554432)) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 1 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 1 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f2 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 2 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 2 < 2 ^ 31) ∧
      (R2 + C3) - (C5 * 67108864) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 2 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 2 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f3 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 3 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 3 < 2 ^ 31) ∧
      (R3 + C5) - (C7 * 33554432) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 3 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 3 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f4 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 4 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 4 < 2 ^ 31) ∧
      (C7 + (R4 - (C2 * 67108864))) - (C9 * 67108864) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 4 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 4 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f5 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 5 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 5 < 2 ^ 31) ∧
      C9 + ((R5 + C2) - (C4 * 33554432)) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 5 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 5 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f6 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 6 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 6 < 2 ^ 31) ∧
      (R6 + C4) - (C6 * 67108864) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 6 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 6 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f7 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 7 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 7 < 2 ^ 31) ∧
      (R7 + C6) - (C8 * 33554432) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 7 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 7 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f8 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 8 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 8 < 2 ^ 31) ∧
      (R8 + C8) - (C10 * 67108864) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 8 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 8 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

theorem sq_f9 (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 : Int) (hRB : RawB ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩)
    (hC1 : C1 = (R0 + 33554432) / 67108864)
    (hC2 : C2 = (R4 + 33554432) / 67108864)
    (hC3 : C3 = ((R1 + C1) + 16777216) / 33554432)
    (hC4 : C4 = ((R5 + C2) + 16777216) / 33554432)
    (hC5 : C5 = ((R2 + C3) + 33554432) / 67108864)
    (hC6 : C6 = ((R6 + C4) + 33554432) / 67108864)
    (hC7 : C7 = ((R3 + C5) + 16777216) / 33554432)
    (hC8 : C8 = ((R7 + C6) + 16777216) / 33554432)
    (hC9 : C9 = ((C7 + (R4 - (C2 * 67108864))) + 33554432) / 67108864)
    (hC10 : C10 = ((R8 + C8) + 33554432) / 67108864)
    (hC11 : C11 = ((R9 + C10) + 16777216) / 33554432)
    (hC12 : C12 = (((19 * C11) + (R0 - (C1 * 67108864))) + 33554432) / 67108864) :
    (-2 ^ 31 ≤ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 9 ∧ (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 9 < 2 ^ 31) ∧
      (R9 + C10) - (C11 * 33554432) = (carryChain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩).get 9 := by
  have hb := carryChain_bound ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩ hRB 9 (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega

end Solutions.OpensslX25519
