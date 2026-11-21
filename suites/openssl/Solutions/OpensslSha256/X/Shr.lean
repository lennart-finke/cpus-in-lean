import Solutions.OpensslSha256.X.Hyp
/-!
# `shr` by a literal count

`shiftOp` is opaque to `cbv` in the execution layer, and it takes the incoming carry flag, which is a
variable in the states of `exN` pieces. `cbvShr` evaluates `shr` (operation 5, 32 bits) by a literal
count `0 < c < 32` to `a >>> c` with flags `shrF a c` (opaque), whatever the incoming flag.
(The lemmas are those of `Solutions.OpensslSha256.Cbv`.)
-/
namespace Solutions.ShaX
open X86 Solutions.Logic Lean Meta

/-- The flags `shr` sets. -/
def shrF (a c : UInt32) : UInt32 :=
  (shiftOp 5 4 a c false).elim 0 (fun x => x.2.2)

theorem and_mask4 (x : UInt32) : x &&& 0xFFFFFFFF = x := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]

theorem shr64' (a b : UInt64) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl

theorem shr_eq' (a cnt : UInt32) (hc : cnt.toNat < 32) :
    (a.toUInt64 >>> cnt.toUInt64).toUInt32 = a >>> cnt := by
  apply UInt32.toNat_inj.1
  have := a.toNat_lt
  rw [shr64', shr32]
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]
  rw [Nat.mod_eq_of_lt (a := cnt.toNat) (by omega), Nat.mod_eq_of_lt (a := cnt.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega))

theorem shiftOp_shr_some' (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    ∃ fl, shiftOp 5 4 a cnt cf = some (a >>> cnt, Flag.arith, fl) := by
  have h1 : cnt &&& 0x1F = cnt := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  have h2 : (cnt == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hc0; rw [h]; rfl
  unfold shiftOp
  simp only [h1, h2, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq, and_true]
  refine ⟨_, ?_, trivial, rfl⟩
  simp only [Sz.mask, show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, and_mask4]
  exact shr_eq' a cnt hc

theorem shiftOp_shr' (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    shiftOp 5 4 a cnt cf = some (a >>> cnt, Flag.arith, shrF a cnt) := by
  obtain ⟨fl', h'⟩ := shiftOp_shr_some' a cnt false hc hc0
  have hcf : shiftOp 5 4 a cnt cf = shiftOp 5 4 a cnt false := by
    unfold shiftOp; rfl
  rw [hcf, h']
  unfold shrF
  rw [h']
  rfl

/-- The value of a small closed number-like term. -/
def smallV? (toNat : Name) (x : Expr) : MetaM (Option Nat) := do
  let n ← whnfD (mkApp (mkConst toNat) x)
  return match n.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? n).run

cbv_simproc cbv_eval cbvShr (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  unless (← smallV? ``UInt8.toNat op) == some 5 do return .rfl
  unless (← smallV? ``UInt8.toNat sz) == some 4 do return .rfl
  let some c ← smallV? ``UInt32.toNat cnt | return .rfl
  unless 0 < c && c < 32 do return .rfl
  let hop ← mkExpectedTypeHint (← mkEqRefl op) (← mkEq op (toExpr (5 : UInt8)))
  let hsz ← mkExpectedTypeHint (← mkEqRefl sz) (← mkEq sz (toExpr (4 : UInt8)))
  let hc ← mkDecideProof (← mkLT (mkApp (mkConst ``UInt32.toNat) cnt) (mkNatLit 32))
  let hc0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) cnt) (mkNatLit 0)))
  let pf0 := mkAppN (mkConst ``shiftOp_shr') #[a, cnt, cf, hc, hc0]
  let rhs ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[← mkAppM ``HShiftRight.hShiftRight #[a, cnt],
    ← mkAppM ``Prod.mk #[mkConst ``Flag.arith, mkApp2 (mkConst ``shrF) a cnt]]]
  let _ := (hop, hsz)
  return .step rhs (← mkExpectedTypeHint pf0 (← mkEq e rhs))

attribute [cbv_opaque] shrF

end Solutions.ShaX
