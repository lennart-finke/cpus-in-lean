import Solutions.Exec.Mul
import Solutions.Exec.Branch
/-!
# `shr`/`shl` by a literal count under `cbv`

The counterpart of `Solutions.Exec.Mul.cbvSar` for logical shifts: a 32-bit `shr`/`shl` by a nonzero
literal count of a symbolic word is `shrR`/`shlR` with flags `shrF`/`shlF` (opaque). Scoped in
`Solutions.Exec.Shift`. Prover L, additions only.
-/
namespace Solutions.Exec.Shift
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Mul

/-- The result of a 32-bit `shr` by `cnt`. -/
def shrR (a cnt : UInt32) : UInt32 := ((shiftOp 5 4 a cnt false).getD (a, 0, 0)).1
/-- The flags of a 32-bit `shr` by `cnt`. -/
def shrF (a cnt : UInt32) : UInt32 := ((shiftOp 5 4 a cnt false).getD (a, 0, 0)).2.2
/-- The result of a 32-bit `shl` by `cnt`. -/
def shlR (a cnt : UInt32) : UInt32 := ((shiftOp 4 4 a cnt false).getD (a, 0, 0)).1
/-- The flags of a 32-bit `shl` by `cnt`. -/
def shlF (a cnt : UInt32) : UInt32 := ((shiftOp 4 4 a cnt false).getD (a, 0, 0)).2.2

theorem shiftOp_shr (op : UInt8) (sz : Sz) (a cnt : UInt32) (cf : Bool) (hop : op = 5) (hsz : sz = 4)
    (h : (cnt &&& 0x1F == 0) = false) :
    shiftOp op sz a cnt cf = some (shrR a cnt, Flag.arith, shrF a cnt) := by
  subst hop hsz
  unfold shrR shrF shiftOp
  simp only [h]
  rfl

theorem shiftOp_shl (op : UInt8) (sz : Sz) (a cnt : UInt32) (cf : Bool) (hop : op = 4) (hsz : sz = 4)
    (h : (cnt &&& 0x1F == 0) = false) :
    shiftOp op sz a cnt cf = some (shlR a cnt, Flag.arith, shlF a cnt) := by
  subst hop hsz
  unfold shlR shlF shiftOp
  simp only [h]
  rfl

attribute [scoped cbv_opaque] shrR shrF shlR shlF

open Lean Meta Sym in
scoped cbv_simproc cbv_eval cbvShrShl (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  let some o ← smallVal? ``UInt8.toNat op | return .rfl
  unless o == 5 || o == 4 do return .rfl
  unless (← smallVal? ``UInt8.toNat sz) == some 4 do return .rfl
  let some c ← smallVal? ``UInt32.toNat cnt | return .rfl
  unless c % 32 != 0 do return .rfl
  let (R, F, L) := if o == 5 then (``shrR, ``shrF, ``shiftOp_shr) else (``shlR, ``shlF, ``shiftOp_shl)
  let rhs ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkApp2 (mkConst R) a cnt,
    ← mkAppM ``Prod.mk #[mkConst ``Flag.arith, mkApp2 (mkConst F) a cnt]]]
  let hop ← mkExpectedTypeHint (← Meta.mkEqRefl op) (← mkEq op (toExpr (o.toUInt8 : UInt8)))
  let hsz ← mkExpectedTypeHint (← Meta.mkEqRefl sz) (← mkEq sz (toExpr (4 : UInt8)))
  let hc ← mkDecideProof (← mkEq (← mkAppM ``BEq.beq #[← mkAppM ``HAnd.hAnd #[cnt, toExpr (0x1F : UInt32)],
    toExpr (0 : UInt32)]) (mkConst ``Bool.false))
  let pf := mkAppN (mkConst L) #[op, sz, a, cnt, cf, hop, hsz, hc]
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- The flags after `bt` (CF replaced): back in the `efl` form. -/
theorem efl_bt (f X : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294967294) (UInt32.land X 1) = efl (mixF f X 1) := by
  show ((2 ||| (f &&& 0x8D5)) &&& 4294967294) ||| (X &&& 1) = 2 ||| (((f &&& ~~~1) ||| (X &&& 1)) &&& 0x8D5)
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    have a1 : (UInt32.toBitVec 4294967294).getLsbD 0 = false := by decide
    have a2 : (UInt32.toBitVec 1).getLsbD 0 = true := by decide
    have a3 : (UInt32.toBitVec 2).getLsbD 0 = false := by decide
    have a4 : (UInt32.toBitVec 2261).getLsbD 0 = true := by decide
    rw [a1, a2, a3, a4]; simp
  · have h1 : ∀ j, j < 32 → j ≠ 0 → (UInt32.toBitVec 4294967294).getLsbD j = true := by decide
    have h2 : ∀ j, j < 32 → j ≠ 0 → (UInt32.toBitVec 1).getLsbD j = false := by decide
    rw [h1 i hi h0, h2 i hi h0]; simp

attribute [scoped cbv_eval] efl_bt

theorem shrR_toNat (a : UInt32) (k : Nat) (hk : 0 < k) (hk' : k < 32) :
    (shrR a k.toUInt32).toNat = a.toNat / 2 ^ k := by
  have e : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have e1 : k.toUInt32 &&& 0x1F = k.toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, e, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hne : k.toUInt32 ≠ 0 := fun h => by
    have := congrArg UInt32.toNat h; rw [e] at this; simp at this; omega
  have hc : (k.toUInt32 &&& 0x1F == 0) = false := by rw [e1]; simpa using hne
  unfold shrR shiftOp
  simp only [hc]
  show ((((a.toUInt64 >>> (k.toUInt32 &&& 0x1F).toUInt64).toUInt32 &&& Sz.mask 4))).toNat = _
  rw [e1, Branch.mask4, UInt64.toNat_toUInt32]
  have u : (ShiftRight.shiftRight a.toUInt64 k.toUInt32.toUInt64).toNat =
      a.toUInt64.toNat / 2 ^ (k.toUInt32.toUInt64.toNat % 64) :=
    (UInt64.toNat_shiftRight _ _).trans (Nat.shiftRight_eq_div_pow _ _)
  rw [u, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, e, Nat.mod_eq_of_lt (a := k) (by omega)]
  have := a.toNat_lt
  exact Nat.mod_eq_of_lt (by have := Nat.div_le_self a.toNat (2 ^ k); omega)

end Solutions.Exec.Shift
