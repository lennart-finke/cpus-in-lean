import Solutions.Logic.Cmp
import Lean
/-!
# Byte shifts by a literal count, and `0F` conditional jumps and moves, for `cbv` (opt-in)

`open Solutions.Logic.Shb` adds the evaluation of `shiftOp` for SHL on 8 bits (`shlb $k, %r8`) by a
literal count in `1 … 31`: the result is `(a <<< k) &&& 255`, the flags `shFl1 4 a k` (opaque to
`cbv`); and the dispatch of the `0F` opcodes `jae`/`je`/`jne` (rel32) and `cmove` to `execRange`
(the catch-all case of `execOp0F`, which `cbv` cannot take); and `cbvZFs`, the zero flag of
`logicF sz r` at any size (`logicF_zfs`) and of `subF 4 a b 0`, to be used in place of
`Solutions.Logic.cbvZF` (which applies the 32-bit `logicF_zf` to every size): files using it remove
that one (`attribute [-cbvSimprocAttr] Solutions.Logic.cbvZF`). The scope is separate so that what
`cbv` gives without it does not change.
-/
namespace Solutions.Logic.Shb
open X86 Solutions.Exec Solutions.Cbx Solutions.Logic Solutions.Logic.Cmp Lean Meta

/-- The flags of an 8-bit shift, opaque to `cbv`. -/
def shFl1 (op : UInt8) (a k : UInt32) : UInt32 :=
  match shiftOp op 1 a k false with
  | some (_, _, f) => f
  | none => 0

theorem shiftOp_shl1 (a k : UInt32) (c : Bool) (hk : k.toNat < 32) (hk0 : k.toNat ≠ 0) :
    shiftOp 4 1 a k c = some (UInt32.land (UInt32.shiftLeft a k) 255, Flag.arith, shFl1 4 a k) := by
  have hm : k &&& 0x1F = k := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hk]
  have h0 : (k == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hk0 (by rw [e]; rfl)
  have hv : (a.toUInt64 <<< k.toUInt64).toUInt32 = UInt32.shiftLeft a k :=
    (and_ones _).symm.trans (shl_res a k hk)
  unfold shFl1 shiftOp
  simp (config := { decide := true }) only [hm, h0, Bool.false_eq_true, _root_.ite_false, hv]
  rfl

private def lit? (e : Expr) : Option Nat := (Sym.getNatValue? e).run

/-- `shiftOp` of SHL on 8 bits by a literal count in `1 … 31`. -/
scoped cbv_simproc cbv_eval cbvShiftOp1 (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a k c := e | return .rfl
  let some opv ← u8Val? op | return .rfl
  unless opv == 4 do return .rfl
  unless (← u8Val? sz) == some 1 do return .rfl
  let some kv := lit? k | return .rfl
  unless 0 < kv && kv < 32 do return .rfl
  let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkApp (mkConst ``UInt32.toNat) k, mkNatLit 32])
  let hk0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) k) (mkNatLit 0)))
  let pf := mkAppN (mkConst ``shiftOp_shl1) #[a, k, c, hk, hk0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

attribute [scoped cbv_opaque] shFl1

theorem execOp0F_x183 : execOp0F 0x183 = execRange 0x183 := by unfold execOp0F; rfl
theorem execOp0F_x184 : execOp0F 0x184 = execRange 0x184 := by unfold execOp0F; rfl
theorem execOp0F_x185 : execOp0F 0x185 = execRange 0x185 := by unfold execOp0F; rfl
theorem execOp0F_x144 : execOp0F 0x144 = execRange 0x144 := by unfold execOp0F; rfl
attribute [scoped cbv_eval] execOp0F_x183 execOp0F_x184 execOp0F_x185 execOp0F_x144

theorem logicF_zfs (sz : Sz) (r : UInt32) : UInt32.land (logicF sz r).2 64 = cond (eqU r 0) 64 0 := by
  simp only [logicF, logicCore, pack_zf, eqU]
  cases h : r == 0 <;> simp_all

open Solutions.Cbx.Discharge in
/-- The zero flag of `logicF sz r` (any size) or `subF 4 a b 0`. -/
scoped cbv_simproc cbv_eval cbvZFs (UInt32.land _ 64) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless kv == 64 do return .rfl
  let some p := sndOf? x | return .rfl
  if p.isAppOfArity ``logicF 2 then
    let sz := p.getArg! 0
    let r := p.appArg!
    let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``eqU) r (toExpr (0 : UInt32)), toExpr (64 : UInt32), toExpr (0 : UInt32)]
    let pf := mkApp2 (mkConst ``logicF_zfs) sz r
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  if p.isAppOfArity ``subF 4 then
    unless (← u8Val? (p.getArg! 0)) == some 4 do return .rfl
    unless lit? (p.getArg! 3) == some 0 do return .rfl
    let a := p.getArg! 1
    let b := p.getArg! 2
    let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``eqU) a b, toExpr (64 : UInt32), toExpr (0 : UInt32)]
    let pf := mkApp2 (mkConst ``subF_zf) a b
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  return .rfl

end Solutions.Logic.Shb
