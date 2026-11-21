import Solutions.Exec.Step
import Solutions.Exec.Mul
/-!
# Conditional jumps on symbolic flags

A conditional jump tests a bit of `efl F` (`UInt32.land (efl F) k`, `k` = `1` (CF), `64` (ZF) or
`65` (CF or ZF)). When `F` are the flags of a comparison, subtraction, decrement or addition of
symbolic words, `cbv` cannot evaluate the test. The `cbv_simproc` `cbvFlagBit` (scoped in
`Solutions.Exec.Branch`) rewrites such a test to its value when `exec_omega` decides it from the
hypotheses in context, by one of the lemmas below (each states the bit under an arithmetic
condition on the operands). Prover L, additions only.
-/
namespace Solutions.Exec.Branch
open X86 Solutions.Logic Solutions.Exec Lean Meta

theorem pack_bits (f : AFlags) :
    f.pack &&& 1 = (if f.cf then 1 else 0) ∧ f.pack &&& 64 = (if f.zf then 64 else 0) ∧
      f.pack &&& 65 = (if f.cf then 1 else 0) ||| (if f.zf then 64 else 0) := by
  obtain ⟨cf, pf, af, zf, sf, of⟩ := f
  revert cf pf af zf sf of
  decide

theorem efl_land_k (f k : UInt32) (hk : (2 : UInt32) &&& k = 0) (hc : (0x8D5 : UInt32) &&& k = k) :
    UInt32.land (efl f) k = f &&& k := by
  show (2 ||| (f &&& 0x8D5)) &&& k = f &&& k
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 := congrArg (fun x : UInt32 => x.toBitVec.getLsbD i) hk
  have e2 := congrArg (fun x : UInt32 => x.toBitVec.getLsbD i) hc
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  simp only [UInt32.toBitVec_zero, BitVec.getLsbD_zero] at e1
  revert e1 e2
  generalize (UInt32.toBitVec 2).getLsbD i = x1
  generalize (UInt32.toBitVec 2261).getLsbD i = x2
  generalize f.toBitVec.getLsbD i = x3
  generalize k.toBitVec.getLsbD i = x4
  revert x1 x2 x3 x4
  decide

theorem mixF_land (a b m k : UInt32) (h : m &&& k = k) : mixF a b m &&& k = b &&& k := by
  show ((a &&& ~~~m) ||| (b &&& m)) &&& k = b &&& k
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e2 := congrArg (fun x : UInt32 => x.toBitVec.getLsbD i) h
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and] at *
  revert e2
  generalize m.toBitVec.getLsbD i = x1
  generalize a.toBitVec.getLsbD i = x2
  generalize b.toBitVec.getLsbD i = x3
  generalize k.toBitVec.getLsbD i = x4
  revert x1 x2 x3 x4
  decide

theorem mask4 (x : UInt32) : x &&& Sz.mask 4 = x := by
  show x &&& 0xFFFFFFFF = x
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, BitVec.getLsbD_and]
  have : (UInt32.toBitVec 0xFFFFFFFF).getLsbD i = true := by
    have : ∀ j, j < 32 → (UInt32.toBitVec 0xFFFFFFFF).getLsbD j = true := by decide
    exact this i hi
  rw [this, Bool.and_true]

theorem zf_true (a b : UInt32) (h : a.toNat = b.toNat) : ((a - b - 0) &&& Sz.mask 4 == 0) = true := by
  rw [mask4, UInt32.sub_zero, UInt32.toNat_inj.1 h, UInt32.sub_self]; rfl

theorem zf_false (a b : UInt32) (h : a.toNat ≠ b.toNat) : ((a - b - 0) &&& Sz.mask 4 == 0) = false := by
  rw [mask4, UInt32.sub_zero]
  cases hc : (a - b == 0)
  · rfl
  · exfalso; apply h
    have h1 := congrArg UInt32.toNat (beq_iff_eq.1 hc)
    rw [UInt32.toNat_sub] at h1
    have := a.toNat_lt; have := b.toNat_lt
    simp at h1
    omega

theorem cf_true (a b : UInt32) (h : a.toNat < b.toNat) : (decide (a.toUInt64 < b.toUInt64 + (0 : UInt32).toUInt64)) = true := by
  simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64]
  simp; omega

theorem cf_false (a b : UInt32) (h : b.toNat ≤ a.toNat) : (decide (a.toUInt64 < b.toUInt64 + (0 : UInt32).toUInt64)) = false := by
  simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64]
  simp; omega

theorem acf (a b : UInt32) : (decide (a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64 > (Sz.mask 4).toUInt64)) =
    decide (2 ^ 32 ≤ a.toNat + b.toNat) := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  show decide ((4294967295 : UInt32).toUInt64 < _) = _
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64]
  simp
  omega

theorem sub_flags (a b : UInt32) :
    (subF 4 a b 0).2 = AFlags.pack ⟨a.toUInt64 < b.toUInt64 + (0 : UInt32).toUInt64, parity ((a - b - 0) &&& Sz.mask 4),
      (a ^^^ b ^^^ ((a - b - 0) &&& Sz.mask 4)) &&& 0x10 != 0, (a - b - 0) &&& Sz.mask 4 == 0,
      (a - b - 0) &&& Sz.mask 4 &&& Sz.msb 4 != 0,
      (a ^^^ b) &&& (a ^^^ ((a - b - 0) &&& Sz.mask 4)) &&& Sz.msb 4 != 0⟩ := rfl

theorem add_flags (a b : UInt32) :
    (addF 4 a b 0).2 = AFlags.pack ⟨a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64 > (Sz.mask 4).toUInt64,
      parity ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4),
      (a ^^^ b ^^^ ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4)) &&& 0x10 != 0,
      (a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4 == 0,
      (a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4 &&& Sz.msb 4 != 0,
      (a ^^^ ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4)) &&&
        (b ^^^ ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64).toUInt32 &&& Sz.mask 4)) &&& Sz.msb 4 != 0⟩ := rfl

/-! ### The bit lemmas used by `cbvFlagBit` -/

theorem cf_sub_lt (a b : UInt32) (h : a.toNat < b.toNat) : UInt32.land (efl (subF 4 a b 0).2) 1 = 1 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).1, cf_true a b h]; rfl
theorem cf_sub_ge (a b : UInt32) (h : b.toNat ≤ a.toNat) : UInt32.land (efl (subF 4 a b 0).2) 1 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).1, cf_false a b h]; rfl
theorem zf_sub_eq (a b : UInt32) (h : a.toNat = b.toNat) : UInt32.land (efl (subF 4 a b 0).2) 64 = 64 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).2.1, zf_true a b h]; rfl
theorem zf_sub_ne (a b : UInt32) (h : a.toNat ≠ b.toNat) : UInt32.land (efl (subF 4 a b 0).2) 64 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).2.1, zf_false a b h]; rfl
theorem cz_sub_lt (a b : UInt32) (h : a.toNat < b.toNat) : UInt32.land (efl (subF 4 a b 0).2) 65 = 1 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).2.2, cf_true a b h,
    zf_false a b (by omega)]; simp
theorem cz_sub_eq (a b : UInt32) (h : a.toNat = b.toNat) : UInt32.land (efl (subF 4 a b 0).2) 65 = 64 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).2.2, cf_false a b (by omega),
    zf_true a b h]; simp
theorem cz_sub_gt (a b : UInt32) (h : b.toNat < a.toNat) : UInt32.land (efl (subF 4 a b 0).2) 65 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), sub_flags, (pack_bits _).2.2, cf_false a b (by omega),
    zf_false a b (by omega)]; simp

/-- `decl x`: ZF (the flags merged under `0x8D4`). -/
theorem zf_dec_one (A x : UInt32) (h : x.toNat = 1) :
    UInt32.land (efl (mixF A (subF 4 x 1 0).2 2260)) 64 = 64 := by
  rw [efl_land_k _ _ (by decide) (by decide), mixF_land _ _ _ _ (by decide), sub_flags, (pack_bits _).2.1,
    zf_true x 1 h]; rfl
theorem zf_dec_ne (A x : UInt32) (h : x.toNat ≠ 1) :
    UInt32.land (efl (mixF A (subF 4 x 1 0).2 2260)) 64 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), mixF_land _ _ _ _ (by decide), sub_flags, (pack_bits _).2.1,
    zf_false x 1 h]; rfl

theorem logic_flags (r : UInt32) :
    (logicF 4 r).2 = AFlags.pack ⟨false, parity r, false, r == 0, r &&& Sz.msb 4 != 0, false⟩ := rfl

/-- `testl x, x`: ZF. -/
theorem zf_test_ne (x : UInt32) (h : x.toNat ≠ 0) : UInt32.land (efl (logicF 4 (UInt32.land x x)).2) 64 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), logic_flags, (pack_bits _).2.1]
  have e : UInt32.land x x = x := UInt32.and_self
  have : (UInt32.land x x == 0) = false := by
    rw [e]
    cases hc : (x == 0)
    · rfl
    · exfalso; apply h; rw [beq_iff_eq.1 hc]; rfl
  rw [this]; rfl
theorem zf_test_zero (x : UInt32) (h : x.toNat = 0) : UInt32.land (efl (logicF 4 (UInt32.land x x)).2) 64 = 64 := by
  rw [efl_land_k _ _ (by decide) (by decide), logic_flags, (pack_bits _).2.1]
  have e : UInt32.land x x = x := UInt32.and_self
  have : (UInt32.land x x == 0) = true := by
    rw [e, show x = 0 from UInt32.toNat_inj.1 (by rw [h]; rfl)]; rfl
  rw [this]; rfl

/-- `addl $-1, x`: CF. -/
theorem cf_addm1_ne (x : UInt32) (h : x.toNat ≠ 0) : UInt32.land (efl (addF 4 x 4294967295 0).2) 1 = 1 := by
  rw [efl_land_k _ _ (by decide) (by decide), add_flags, (pack_bits _).1, acf,
    decide_eq_true (by simp only [UInt32.reduceToNat]; omega)]; rfl
theorem cf_addm1_zero (x : UInt32) (h : x.toNat = 0) : UInt32.land (efl (addF 4 x 4294967295 0).2) 1 = 0 := by
  rw [efl_land_k _ _ (by decide) (by decide), add_flags, (pack_bits _).1, acf,
    decide_eq_false (by simp only [UInt32.reduceToNat]; omega)]; rfl

/-! ### Two-byte conditional jumps and `setcc`

`execOp0F` reaches `0F 80`–`0F 9F` through its catch-all case, which `cbv` cannot use. -/

theorem execOp0F_range (op : Nat) (h : 0x180 ≤ op ∧ op < 0x1A0) : execOp0F op = execRange op := by
  unfold execOp0F
  split <;> first | omega | (rw [if_neg (by simp only [isSimdOp]; simp; omega)])

theorem execOp0F_x182 : execOp0F 386 = execRange 386 := execOp0F_range 386 (by decide)
theorem execOp0F_x192 : execOp0F 402 = execRange 402 := execOp0F_range 402 (by decide)
theorem execOp0F_x195 : execOp0F 405 = execRange 405 := execOp0F_range 405 (by decide)

attribute [scoped cbv_eval] execOp0F_x182 execOp0F_x192 execOp0F_x195

theorem cfB_addm1_ne (x : UInt32) (h : x.toNat ≠ 0) : Mul.cfB (addF 4 x 4294967295 0).2 = true := by
  unfold Mul.cfB
  rw [show Flag.CF = (1 : UInt32) from rfl, add_flags, (pack_bits _).1, acf,
    decide_eq_true (by simp only [UInt32.reduceToNat]; omega)]; rfl
theorem cfB_addm1_zero (x : UInt32) (h : x.toNat = 0) : Mul.cfB (addF 4 x 4294967295 0).2 = false := by
  unfold Mul.cfB
  rw [show Flag.CF = (1 : UInt32) from rfl, add_flags, (pack_bits _).1, acf,
    decide_eq_false (by simp only [UInt32.reduceToNat]; omega)]; rfl
theorem cfB_sub_lt (a b : UInt32) (h : a.toNat < b.toNat) : Mul.cfB (subF 4 a b 0).2 = true := by
  unfold Mul.cfB
  rw [show Flag.CF = (1 : UInt32) from rfl, sub_flags, (pack_bits _).1, cf_true a b h]; rfl
theorem cfB_sub_ge (a b : UInt32) (h : b.toNat ≤ a.toNat) : Mul.cfB (subF 4 a b 0).2 = false := by
  unfold Mul.cfB
  rw [show Flag.CF = (1 : UInt32) from rfl, sub_flags, (pack_bits _).1, cf_false a b h]; rfl

initialize registerTraceClass `exec.branch

/-- A flag test stated by a hypothesis (for flags kept as a variable). -/
theorem land_hyp (f k v : UInt32) (h : UInt32.land (efl f) k = v) : UInt32.land (efl f) k = v := h
theorem cfB_hyp (f : UInt32) (b : Bool) (h : Mul.cfB f = b) : Mul.cfB f = b := h

open Discharge in
/-- Rewrite `e` by the first lemma of `lems` whose left side matches and whose last hypothesis
`exec_omega` proves. -/
def tryLemmas (lems : List Name) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  trace[exec.branch] "try {e}"
  for lem in lems do
    let c ← mkConstWithFreshMVarLevels lem
    let (xs, _, ty) ← forallMetaTelescope (← inferType c)
    let some (_, lhs, rhs) := ty.eq? | continue
    unless ← withReducible (isDefEq lhs e) do continue
    let hyp := xs[xs.size - 1]!
    trace[exec.branch] "match {lem}"
    let hty ← instantiateMVars (← inferType hyp)
    -- a hypothesis in context, else `exec_omega`
    let mut found := false
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if ← withReducible (isDefEq d.type hty) then
        hyp.mvarId!.assign d.toExpr
        found := true
        break
    unless found do
      if hty.hasExprMVar then continue
      let some hp ← omega? hty | continue
      hyp.mvarId!.assign hp
    let pf ← instantiateMVars (mkAppN c xs)
    if pf.hasExprMVar then continue
    let rhs ← Sym.share (← instantiateMVars rhs)
    return .step rhs pf
  return .rfl

/-- The value of a flag test `UInt32.land (efl F) k` that `exec_omega` decides from the context. -/
scoped cbv_simproc cbv_eval cbvFlagBit (UInt32.land (efl _) _) := fun e =>
  tryLemmas [``land_hyp, ``zf_test_ne, ``zf_test_zero, ``zf_dec_ne, ``zf_dec_one, ``cf_addm1_ne, ``cf_addm1_zero, ``zf_sub_ne, ``zf_sub_eq,
      ``cf_sub_lt, ``cf_sub_ge, ``cz_sub_lt, ``cz_sub_eq, ``cz_sub_gt] e

/-- The carry `cfB F` (`Solutions.Exec.Mul`) that `exec_omega` decides from the context. -/
scoped cbv_simproc cbv_eval cbvCfB (Mul.cfB _) := fun e =>
  tryLemmas [``cfB_hyp, ``cfB_addm1_ne, ``cfB_addm1_zero, ``cfB_sub_lt, ``cfB_sub_ge] e

end Solutions.Exec.Branch
