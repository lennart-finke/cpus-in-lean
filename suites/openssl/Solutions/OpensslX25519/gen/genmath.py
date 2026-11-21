# The arithmetic lemmas of the semantic facts: sq_h{k} (complete product sums are the limbs of
# mulRaw), sq_b{j} (the carried values are within the signed 64-bit range), sq_f{i} (the final words).
XS = "X0 X1 X2 X3 X4 X5 X6 X7 X8 X9"
RS = "R0 R1 R2 R3 R4 R5 R6 R7 R8 R9"
LX = "⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩"
LR = "⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9⟩"


def hlemma(pre, k, es):
    return f"""
theorem {pre}_h{k} ({XS} : Int) :
    {es} = (mulRaw {LX} {LX}).a{k} := by
  simp only [mulRaw]
  grind
"""


def chyps(carries):
    cs = ' '.join(c for (c, _, _) in carries)
    hs = ''.join(f"\n    (h{c} : {c} = ({t}) / {2 ** s})" for (c, t, s) in carries)
    return cs, hs


def blemma(pre, j, tes, carries):
    cs, hs = chyps(carries)
    binder = f"({RS} {cs} : Int)" if cs else f"({RS} : Int)"
    return f"""
theorem {pre}_b{j} {binder} (hRB : RawB {LR}){hs} :
    -2 ^ 63 ≤ {tes} ∧ {tes} < 2 ^ 63 := by
  simp only [RawB] at hRB
  omega
"""


def flemma(pre, i, es, carries):
    cs, hs = chyps(carries)
    return f"""
theorem {pre}_f{i} ({RS} {cs} : Int) (hRB : RawB {LR}){hs} :
    (-2 ^ 31 ≤ (carryChain {LR}).get {i} ∧ (carryChain {LR}).get {i} < 2 ^ 31) ∧
      {es} = (carryChain {LR}).get {i} := by
  have hb := carryChain_bound {LR} hRB {i} (by decide)
  simp only [RawB] at hRB
  simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at hb ⊢
  omega
"""
