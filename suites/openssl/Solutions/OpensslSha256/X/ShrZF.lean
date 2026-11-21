import Solutions.OpensslSha256.X.UpdRun1
/-!
# The zero flag of `shr` by a literal count

`cbvShrZF`: the zero flag (`&&& 64`) of `shrF a c` (also under `efl`) is `cond (eqU (a >>> c) 0) 64 0`,
which `cbvEqU` decides from the hypotheses.
-/
namespace Solutions.ShaX
open X86 Solutions.Logic Lean Meta

theorem shrF_zf (a c : UInt32) (hc : c.toNat < 32) (hc0 : c.toNat ≠ 0) :
    UInt32.land (shrF a c) 64 = cond (eqU (UInt32.shiftRight a c) 0) 64 0 := by
  have h1 : c &&& 0x1F = c := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  have h2 : (c == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hc0; rw [h]; rfl
  have hr : (a.toUInt64 >>> c.toUInt64).toUInt32 &&& 0xFFFFFFFF = UInt32.shiftRight a c := by
    rw [and_mask4, shr_eq' a c hc]; rfl
  unfold shrF shiftOp
  simp only [h1, h2, Bool.false_eq_true, ite_false, Option.elim, Sz.mask,
    show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide]
  rw [hr]
  unfold eqU szp
  by_cases hz : UInt32.shiftRight a c = 0
  · simp only [hz, decide_true, Bool.cond_true]
    split <;> split <;> split <;> split <;> first | decide | simp_all
  · simp only [hz, decide_false, Bool.cond_false, beq_iff_eq, ite_false]
    split <;> split <;> split <;> split <;> first | decide | simp_all

cbv_simproc cbv_eval cbvShrZF (UInt32.land _ _) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  unless (← smallV? ``UInt32.toNat k) == some 64 do return .rfl
  let (y, isEfl) := if x.isAppOfArity ``Solutions.Cbx.efl 1 then (x.appArg!, true) else (x, false)
  unless y.isAppOfArity ``shrF 2 do return .rfl
  let a := y.getArg! 0
  let c := y.getArg! 1
  let some cv ← smallV? ``UInt32.toNat c | return .rfl
  unless 0 < cv && cv < 32 do return .rfl
  let hc ← mkDecideProof (← mkLT (mkApp (mkConst ``UInt32.toNat) c) (mkNatLit 32))
  let hc0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) c) (mkNatLit 0)))
  let pf1 := mkAppN (mkConst ``shrF_zf) #[a, c, hc, hc0]
  let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``eqU) (mkApp2 (mkConst ``UInt32.shiftRight) a c) (toExpr (0 : UInt32)),
    toExpr (64 : UInt32), toExpr (0 : UInt32)]
  if isEfl then
    let hk ← mkDecideProof (← mkEq (← mkAppM ``HAnd.hAnd #[toExpr (64 : UInt32), toExpr (0x8D5 : UInt32)])
      (toExpr (64 : UInt32)))
    let pf0 := mkAppN (mkConst ``efl_and) #[y, k, hk]
    let pf ← mkEqTrans pf0 pf1
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  return .step rhs (← mkExpectedTypeHint pf1 (← mkEq e rhs))

end Solutions.ShaX
