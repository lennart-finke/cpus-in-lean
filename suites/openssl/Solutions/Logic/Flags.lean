import Solutions.Logic.Cbx
import Solutions.Exec.Alu
import Lean
/-!
# Branches on the zero flag, for `cbv`

With `open Solutions.Logic`, `cbv` (set up by `Solutions.Cbx`) evaluates a conditional jump on the
zero flag left by `test`, `and`, `or`, `xor` (`logicF`) or `cmp`, `sub` (`subF`): the zero flag of
`efl f` is that of `f` (`efl_zf`), the zero flag of `logicF 4 r` is `r = 0` and that of
`subF 4 a b 0` is `a = b`, as the opaque comparison `eqU`. The simproc `cbvEqU` decides `eqU a b`
from the hypotheses in context (by `omega` on `toNat`, as the data accesses are).

Also the 32-bit results of `inc` (`addF`), `xor r, r` and `test r, r`.
-/
namespace Solutions.Logic
open X86 Solutions.Exec Solutions.Cbx Lean Meta

/-- Equality of words, as a function `cbv` does not unfold. -/
def eqU (a b : UInt32) : Bool := decide (a = b)

theorem eqU_true {a b : UInt32} (h : a.toNat = b.toNat) : eqU a b = true := by
  simp [eqU, UInt32.toNat_inj.mp h]

theorem eqU_false {a b : UInt32} (h : a.toNat ≠ b.toNat) : eqU a b = false := by
  simp only [eqU, decide_eq_false_iff_not]
  intro e; exact h (congrArg UInt32.toNat e)

theorem efl_zf (f : UInt32) : UInt32.land (efl f) 64 = UInt32.land f 64 := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((2 ||| (f &&& 0x8D5)) &&& 64 : UInt32).toBitVec.getLsbD i = (f &&& 64 : UInt32).toBitVec.getLsbD i
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  have e1 : ∀ j, (UInt32.toBitVec 2).getLsbD j = decide (j = 1) := by
    intro j; rcases Nat.lt_or_ge j 32 with h | h
    · revert j; decide
    · simp [BitVec.getLsbD_of_ge _ _ h]; omega
  have e2 : ∀ j, (UInt32.toBitVec 64).getLsbD j = decide (j = 6) := by
    intro j; rcases Nat.lt_or_ge j 32 with h | h
    · revert j; decide
    · simp [BitVec.getLsbD_of_ge _ _ h]; omega
  have e3 : (UInt32.toBitVec 0x8D5).getLsbD 6 = true := by decide
  rw [e1, e2]
  by_cases h6 : i = 6
  · subst h6; simp [e3]
  · simp [h6]

theorem pack_zf (f : AFlags) : UInt32.land f.pack 64 = cond f.zf 64 0 := by
  cases f with
  | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem logicF_zf (r : UInt32) : UInt32.land (logicF 4 r).2 64 = cond (eqU r 0) 64 0 := by
  simp only [logicF, logicCore, pack_zf, eqU]
  cases h : r == 0 <;> simp_all

theorem mask4 : Sz.mask 4 = 0xFFFFFFFF := by decide

theorem and_ones (x : UInt32) : x &&& 0xFFFFFFFF = x := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]

theorem subF_zf (a b : UInt32) : UInt32.land (subF 4 a b 0).2 64 = cond (eqU a b) 64 0 := by
  simp only [subF, subCore, pack_zf, eqU, mask4, and_ones]
  congr 1
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0 := by
      intro e; apply h
      have := congrArg (· + b) e
      simpa using this
    simp [h, this]

theorem logicF_fst (sz : Sz) (r : UInt32) : (logicF sz r).1 = r := rfl

theorem subF_fst' (a b : UInt32) : (subF 4 a b 0).1 = UInt32.sub a b := Solutions.Exec.subF_fst a b

theorem addF_fst' (a b : UInt32) : (addF 4 a b 0).1 = UInt32.add a b := Solutions.Exec.addF_fst a b

theorem land_self (x : UInt32) : UInt32.land x x = x := UInt32.and_self (a := x)

theorem xor_self (x : UInt32) : UInt32.xor x x = 0 := UInt32.xor_self (a := x)

/-- A proof of `P` by `sym_omega` from the hypotheses in context, or `none`. The tactic runs without
error recovery, so a failed attempt is a failure (and not an error-recovery placeholder), and a proof
that still contains a placeholder or a metavariable is rejected. -/
def omegaSound? (P : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar P
  let msgs := (← getThe Core.State).messages
  let ok ← try
      let gs ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry <|
        Elab.Tactic.run g.mvarId! (Elab.Tactic.withoutRecover (Elab.Tactic.evalTactic (← `(tactic| sym_omega))))
      pure gs.isEmpty
    catch _ => pure false
  modifyThe Core.State fun st => { st with messages := msgs }
  if !ok then return none
  let pf ← instantiateMVars g
  if pf.hasSorry || pf.hasSyntheticSorry || pf.hasExprMVar then return none
  return some pf

/-- `eqU a b` decided by `omega` from the hypotheses in context. -/
scoped cbv_simproc cbv_eval cbvEqU (eqU _ _) := fun e => do
  let_expr eqU a b := e | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let P ← mkEq (toNat a) (toNat b)
  if let some h ← omegaSound? P then
    let pf := mkApp3 (mkConst ``eqU_true) a b h
    return .step (mkConst ``Bool.true) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.true)))
  if let some h ← omegaSound? (mkNot P) then
    let pf := mkApp3 (mkConst ``eqU_false) a b h
    return .step (mkConst ``Bool.false) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.false)))
  return .rfl

/-- The second component of a pair, whether as `Prod.snd` or as a projection. -/
def sndOf? (x : Expr) : Option Expr :=
  if x.isAppOfArity ``Prod.snd 3 then some x.appArg!
  else match x with
    | .proj ``Prod 1 p => some p
    | _ => none

open Solutions.Cbx.Discharge in
/-- The zero flag of `logicF 4 r` or `subF 4 a b 0`, with the second component written either way. -/
scoped cbv_simproc cbv_eval cbvZF (UInt32.land _ 64) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless kv == 64 do return .rfl
  let some p := sndOf? x | return .rfl
  if p.isAppOfArity ``logicF 2 then
    let r := p.appArg!
    let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``eqU) r (toExpr (0 : UInt32)), toExpr (64 : UInt32), toExpr (0 : UInt32)]
    let pf := mkApp (mkConst ``logicF_zf) r
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  if p.isAppOfArity ``subF 4 then
    let a := p.getArg! 1
    let b := p.getArg! 2
    let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``eqU) a b, toExpr (64 : UInt32), toExpr (0 : UInt32)]
    let pf := mkApp2 (mkConst ``subF_zf) a b
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  return .rfl

theorem shl_zero_of (x k : UInt32) (h : k = 0) : UInt32.shiftLeft x k = x := by
  subst h; exact UInt32.shiftLeft_zero

/-- `x <<< 0` (an address with scale 1), whatever form the literal `0` has. -/
scoped cbv_simproc cbv_eval cbvShl0 (UInt32.shiftLeft _ _) := fun e => do
  let_expr UInt32.shiftLeft x k := e | return .rfl
  let kn ← whnfD (mkApp (mkConst ``UInt32.toNat) k)
  let v : Option Nat := match kn.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? kn).run
  unless v == some 0 do return .rfl
  let zero := toExpr (0 : UInt32)
  let hk ← mkExpectedTypeHint (← mkEqRefl zero) (← mkEq k zero)
  let pf := mkApp3 (mkConst ``shl_zero_of) x k hk
  return .step x (← mkExpectedTypeHint pf (← mkEq e x))

/-! ### The carry flag (`bt`, `adc`, `sbb`) -/

theorem land_bits (x k : UInt32) (h : ∀ i, i < 32 → (k.toBitVec.getLsbD i = true → (0x8D5 : UInt32).toBitVec.getLsbD i = true)) :
    UInt32.land (efl x) k = UInt32.land x k := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((2 ||| (x &&& 0x8D5)) &&& k : UInt32).toBitVec.getLsbD i = (x &&& k : UInt32).toBitVec.getLsbD i
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  have hk := h i hi
  have e1 : ∀ j, (UInt32.toBitVec 2).getLsbD j = decide (j = 1) := by
    intro j; rcases Nat.lt_or_ge j 32 with h | h
    · revert j; decide
    · simp [BitVec.getLsbD_of_ge _ _ h]; omega
  have e2 : (UInt32.toBitVec 0x8D5).getLsbD 1 = false := by decide
  rw [e1]
  by_cases h1 : i = 1
  · subst h1
    cases hb : k.toBitVec.getLsbD 1
    · simp
    · exact absurd (hk hb) (by rw [e2]; decide)
  · cases hb : k.toBitVec.getLsbD i
    · simp
    · have h2 := hk hb
      simp only [h1, decide_false, Bool.false_or, Bool.and_true]
      cases x.toBitVec.getLsbD i
      · rfl
      · exact h2

theorem efl_cf (f : UInt32) : UInt32.land (efl f) 1 = UInt32.land f 1 :=
  land_bits f 1 (by decide)

theorem efl_setCF (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294967294) (UInt32.land v 1) = efl (mixF f v 1) :=
  efl_set f v 1 (by decide)

theorem mixF_cf (f v : UInt32) : UInt32.land (mixF f v 1) 1 = UInt32.land v 1 := by
  unfold mixF
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (((f &&& ~~~1) ||| (v &&& 1)) &&& 1 : UInt32).toBitVec.getLsbD i = (v &&& 1 : UInt32).toBitVec.getLsbD i
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not]
  cases (UInt32.toBitVec 1).getLsbD i <;> simp

attribute [scoped cbv_opaque] eqU
attribute [scoped cbv_eval] efl_cf efl_setCF mixF_cf
attribute [scoped cbv_eval] efl_zf logicF_zf subF_zf logicF_fst addF_fst' subF_fst' land_self xor_self

end Solutions.Logic
