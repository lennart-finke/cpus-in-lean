import Solutions.OpensslPoly1305.Base
import Solutions.Logic.Cmp
/-!
# `cbv` additions for the Poly1305 runs

`open Solutions.OpensslPoly1305.Cbv` (next to `Solutions.Exec.Mul`, `Solutions.Exec.Fast`):

* `shr` by a literal count `k` (`0 < k < 32`): the result is `UInt32.shiftRight a k`, the flags the
  opaque `shFl 5 a k` (`Solutions.Logic.Cmp.shiftOp_shr`);
* the `0F` jumps `ja`/`jb` rel32 (`execOp0F` to `execRange`; with `open Solutions.Logic.Cmp`, whose
  `ltU`/`eqU` rules decide the condition by `omega`);
* `esp_subF`/`esp_addF`: the stack pointer after `subl`/`addl $k, %esp` back in the form `U + c`.
-/
namespace Solutions.OpensslPoly1305.Cbv
open X86 Solutions.Logic Solutions.Exec Lean Meta Sym

attribute [scoped cbv_opaque] Solutions.Logic.Cmp.shFl

open Lean Meta Sym in
scoped cbv_simproc cbv_eval cbvShr (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  unless (← Solutions.Exec.Mul.smallVal? ``UInt8.toNat op) == some 5 do return .rfl
  unless (← Solutions.Exec.Mul.smallVal? ``UInt8.toNat sz) == some 4 do return .rfl
  let some c ← Solutions.Exec.Mul.smallVal? ``UInt32.toNat cnt | return .rfl
  unless 0 < c && c < 32 do return .rfl
  let five := toExpr (5 : UInt8)
  let rhs ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkApp2 (mkConst ``UInt32.shiftRight) a cnt,
    ← mkAppM ``Prod.mk #[mkConst ``Flag.arith, mkApp3 (mkConst ``Solutions.Logic.Cmp.shFl) five a cnt]]]
  let hk ← mkDecideProof (← mkLT (mkApp (mkConst ``UInt32.toNat) cnt) (mkNatLit 32))
  let hk0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) cnt) (mkNatLit 0)))
  let pf := mkAppN (mkConst ``Solutions.Logic.Cmp.shiftOp_shr) #[a, cnt, cf, hk, hk0]
  -- `op`, `sz` are the literals 5, 4 up to defeq
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

theorem eflX_land (x k : UInt32) (h : ∀ i, i < 32 → (k.toBitVec.getLsbD i = true → (0x8D5 : UInt32).toBitVec.getLsbD i = true)) :
    UInt32.land (Solutions.Exec.efl x) k = UInt32.land x k :=
  Solutions.Logic.land_bits x k h

theorem eflX_cz (a b : UInt32) : UInt32.land (Solutions.Exec.efl (subF 4 a b 0).2) 65 =
    UInt32.lor (cond (Solutions.Logic.Cmp.ltU a b) 1 0) (cond (Solutions.Logic.eqU a b) 64 0) :=
  (eflX_land _ 65 (by decide)).trans (Solutions.Logic.Cmp.subF_cz a b)

theorem eflX_cf (a b : UInt32) : UInt32.land (Solutions.Exec.efl (subF 4 a b 0).2) 1 =
    cond (Solutions.Logic.Cmp.ltU a b) 1 0 :=
  (eflX_land _ 1 (by decide)).trans (Solutions.Logic.Cmp.subF_cf 4 a b)

theorem mixF_zf (f v : UInt32) : UInt32.land (Solutions.Exec.mixF f v 2260) 64 = UInt32.land v 64 := by
  unfold Solutions.Exec.mixF
  show ((f &&& ~~~2260) ||| (v &&& 2260)) &&& 64 = v &&& 64
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not]
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_assoc]
  rw [show (~~~(2260 : UInt32).toBitVec &&& (64 : UInt32).toBitVec) = 0#32 by decide,
    show ((2260 : UInt32).toBitVec &&& (64 : UInt32).toBitVec) = (64 : UInt32).toBitVec by decide]
  simp

theorem eflX_zl (r : UInt32) : UInt32.land (Solutions.Exec.efl (logicF 4 r).2) 64 =
    cond (Solutions.Logic.eqU r 0) 64 0 :=
  (eflX_land _ 64 (by decide)).trans (Solutions.Logic.logicF_zf r)

theorem eflX_zs (a b : UInt32) : UInt32.land (Solutions.Exec.efl (subF 4 a b 0).2) 64 =
    cond (Solutions.Logic.eqU a b) 64 0 :=
  (eflX_land _ 64 (by decide)).trans (Solutions.Logic.subF_zf a b)

theorem eflX_zd (g a : UInt32) : UInt32.land (Solutions.Exec.efl (Solutions.Exec.mixF g (subF 4 a 1 0).2 2260)) 64 =
    cond (Solutions.Logic.eqU a 1) 64 0 :=
  ((eflX_land _ 64 (by decide)).trans (mixF_zf _ _)).trans (Solutions.Logic.subF_zf a 1)

/-- The zero flag (`je`/`jne`) of `efl` of a `logicF` (`test`), a `subF` (`cmp`) or a `dec`. -/
scoped cbv_simproc cbv_eval cbvEflZ (UInt32.land (Solutions.Exec.efl _) 64) := fun e => do
  let_expr UInt32.land x _ := e | return .rfl
  let_expr Solutions.Exec.efl f := x | return .rfl
  let pf? : Option Expr ← do
    if let some p := Solutions.Logic.sndOf? f then
      if p.isAppOfArity ``logicF 2 then
        pure (some (mkApp (mkConst ``eflX_zl) p.appArg!))
      else if p.isAppOfArity ``subF 4 then
        pure (some (mkApp2 (mkConst ``eflX_zs) (p.getArg! 1) (p.getArg! 2)))
      else pure none
    else if f.isAppOfArity ``Solutions.Exec.mixF 3 then
      match Solutions.Logic.sndOf? (f.getArg! 1) with
      | some p =>
        if p.isAppOfArity ``subF 4 then pure (some (mkApp2 (mkConst ``eflX_zd) (f.getArg! 0) (p.getArg! 1)))
        else pure none
      | none => pure none
    else pure none
  let some pf := pf? | return .rfl
  let some (_, _, rhs) := (← Meta.inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- The carry-or-zero bits (`ja`/`jbe`) and the carry bit (`jae`/`jb`) of `efl` of a `subF`. -/
scoped cbv_simproc cbv_eval cbvEflSub (UInt32.land (Solutions.Exec.efl _) _) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  let some kv := ((Sym.getNatValue? k).run : Option Nat) | return .rfl
  unless kv == 1 || kv == 65 do return .rfl
  let_expr Solutions.Exec.efl f := x | return .rfl
  let some p := Solutions.Logic.sndOf? f | return .rfl
  unless p.isAppOfArity ``subF 4 do return .rfl
  let c0 : Option Nat := (Sym.getNatValue? (p.getArg! 3)).run
  unless c0 == some 0 do return .rfl
  unless (← Solutions.Exec.Mul.smallVal? ``UInt8.toNat (p.getArg! 0)) == some 4 do return .rfl
  let (a, b) := (p.getArg! 1, p.getArg! 2)
  let pf := mkApp2 (mkConst (if kv == 1 then ``eflX_cf else ``eflX_cz)) a b
  let some (_, _, rhs) := (← Meta.inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- A byte load `rdBytes mem a 1` by a hypothesis `rdBytes mem a 1 = v` of the local context. -/
scoped cbv_simproc cbv_eval cbvHypByte1 (rdBytes _ _ 1) := fun e => do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, l, r) := d.type.eq? | continue
    if l == e then
      return .step r (mkFVar d.fvarId)
  return .rfl

theorem execOp0F_x187 : execOp0F 0x187 = execRange 0x187 := by unfold execOp0F; rfl
theorem execOp0F_x182 : execOp0F 0x182 = execRange 0x182 := by unfold execOp0F; rfl
attribute [scoped cbv_eval] execOp0F_x187 execOp0F_x182

end Solutions.OpensslPoly1305.Cbv

namespace Solutions.OpensslPoly1305
open X86 Solutions.Logic Solutions.Exec

theorem esp_subF (U a b c : UInt32) (h : b + c = a) : (subF 4 (UInt32.add U a) b 0).1 = UInt32.add U c := by
  rw [subF_fst]; subst h
  show U + (b + c) - b = U + c
  rw [UInt32.add_comm b c, ← UInt32.add_assoc, UInt32.add_sub_cancel]

theorem esp_addF (U a b c : UInt32) (h : a + b = c) : (addF 4 (UInt32.add U a) b 0).1 = UInt32.add U c := by
  rw [addF_fst]; subst h
  show U + a + b = U + (a + b)
  rw [UInt32.add_assoc]

end Solutions.OpensslPoly1305
