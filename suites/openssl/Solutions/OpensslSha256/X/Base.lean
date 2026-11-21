import Solutions.OpensslSha256.X.Exec
/-!
# Common definitions of the ChaCha20 proof

The image in memory (`CMem`), the address facts every step needs, and `cbv` setup shared by the step
files.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

abbrev CMem := CodeMem Image.base Image.size Image.byte

/-- `UInt64` additions of literals folded: `(x + a) + b = x + (a + b)`. -/
theorem u64_add_assoc (x a b : UInt64) : UInt64.add (UInt64.add x a) b = UInt64.add x (a + b) :=
  UInt64.add_assoc x a b

open Lean Meta in
cbv_simproc cbv_eval cbvU64Add (UInt64.add _ _) := fun e => do
  let_expr UInt64.add x b := e | return .rfl
  let some bv := (Sym.getNatValue? b).run | return .rfl
  let_expr UInt64.add y a := x | return .rfl
  let some av := (Sym.getNatValue? a).run | return .rfl
  let c := (av + bv) % 2 ^ 64
  let r ← Sym.share (mkApp2 (mkConst ``UInt64.add) y (toExpr c.toUInt64))
  let pf := mkApp3 (mkConst ``u64_add_assoc) y a b
  return .step r (← mkExpectedTypeHint pf (← mkEq e r))

open Lean Meta in
/-- A binary operation of `UInt32` on two literals, evaluated (checked by the kernel). -/
def foldU32 (f : Nat → Nat → Nat) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let some a := (Sym.getNatValue? e.appFn!.appArg!).run | return .rfl
  let some b := (Sym.getNatValue? e.appArg!).run | return .rfl
  let r := toExpr (f a b % 2 ^ 32).toUInt32
  return .step r (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r))

cbv_simproc cbv_eval cbvLor32 (UInt32.lor _ _) := foldU32 (· ||| ·)
cbv_simproc cbv_eval cbvLand32 (UInt32.land _ _) := foldU32 (· &&& ·)
cbv_simproc cbv_eval cbvXor32 (UInt32.xor _ _) := foldU32 (· ^^^ ·)
cbv_simproc cbv_eval cbvShl32 (UInt32.shiftLeft _ _) := foldU32 (fun a b => a <<< (b % 32))
cbv_simproc cbv_eval cbvShr32 (UInt32.shiftRight _ _) := foldU32 (fun a b => a >>> (b % 32))
cbv_simproc cbv_eval cbvAdd32 (UInt32.add _ _) := foldU32 (· + ·)

theorem exN_zero (halt : UInt32) (s : St) : exN halt 0 s = some s := by simp [exN]

theorem exN_succ_bind (halt : UInt32) (k : Nat) (s : St) :
    exN halt (k + 1) s = (exN halt 1 s).bind (exN halt k) := by
  rw [Nat.add_comm, exN_add]

/-- The conditional instructions of the image (`je`, `jne`, `ja`, `cmovb`): before them the flags
are kept as they are, so that the condition can be evaluated. -/
def condAddrs : List Nat := [0x1000ea, 0x100107, 0x10010f, 0x10011d, 0x100170, 0x10018b, 0x1001c8, 0x10023f,
  0x100248, 0x10024d, 0x10030e, 0x100318, 0x100331, 0x1011fc, 0x10121a, 0x10122b, 0x101244, 0x101190]

open Lean Meta Elab Tactic in
/-- One instruction of an `exN` run in the goal: split it off (`exN_succ_bind`) and evaluate it by
`cbv` as an auxiliary theorem in which the arithmetic flags of the state are a variable (unless the
instruction is conditional and needs them). The kernel thus never checks the evaluation of an
instruction against the ALU terms that earlier instructions left in the flags. -/
elab "ex_step" : tactic => do
  evalTactic (← `(tactic| rw [exN_succ_bind]))
  withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => e.isAppOfArity ``exN 3 && (e.getArg! 1).nat? == some 1)
    | throwError "ex_step: no `exN _ 1 _`"
  let halt := e.getArg! 0
  let st := e.getArg! 2
  unless st.isAppOfArity ``St.mk 12 do throwError "ex_step: state is not a literal"
  let eip := (Sym.getNatValue? (st.getArg! 9)).run
  let fl := st.getArg! 10
  let cond := match eip with | some a => condAddrs.contains a | none => false
  let gen := !cond && fl.isAppOfArity ``efl 1
  let X := if gen then fl.appArg! else toExpr (0 : UInt32)
  let pf ← withLocalDeclD `F (mkConst ``UInt32) fun F => do
    let args := st.getAppArgs
    let st' := if gen then mkAppN (mkConst ``St.mk) (args.set! 10 (mkApp (mkConst ``efl) F)) else st
    let lhs := mkAppN (mkConst ``exN) #[halt, mkNatLit 1, st']
    let r ← Lean.Meta.Tactic.Cbv.cbvEntry lhs
    let (rhs, p) ← match r with
      | .step e' p .. => pure (e', p)
      | .rfl .. => throwError "ex_step: cbv made no progress"
    unless rhs.isAppOfArity ``Option.some 2 do
      throwError "ex_step: the instruction at {eip} did not evaluate:{indentExpr rhs}"
    -- proofs inside the new state (the store side conditions) become auxiliary theorems, so that
    -- the states of later steps stay small
    let rhs ← abstractNestedProofs rhs
    let ty ← mkEq lhs rhs
    let lctx ← getLCtx
    let fvars := lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.toExpr
    let ty' ← mkForallFVars fvars ty
    let val' ← mkLambdaFVars fvars (← instantiateMVars p)
    let base ← match (← Lean.Elab.Term.getDeclName?) with | some n => pure n | none => pure `ex_step
    let name := base ++ (← mkFreshUserName `step)
    addDecl (Declaration.thmDecl { name, levelParams := [], type := ty', value := val' })
    let pfF := mkAppN (mkConst name) fvars
    -- `F` is the last local; instantiate it with the flags of the state
    return (← mkLambdaFVars #[F] pfF).beta #[X]
  let pfTy ← inferType pf
  let some (_, lhs, rhs) := pfTy.eq? | throwError "ex_step: bad proof"
  let r ← g.rewrite t pf
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)
  let _ := (lhs, rhs)
  -- `(some s').bind f` to `f s'` by an explicit equation (a definitional step here would let the
  -- kernel unfold `exN`)
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some e := t.find? (fun e => e.isAppOfArity ``Option.bind 4) | throwError "ex_step: no bind"
    let pfb ← mkAppM ``Option.bind_some #[(e.getArg! 2).appArg!, e.getArg! 3]
    let r ← g.rewrite t pfb
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)

/-- All instructions of the `exN` run in the goal, one by one. -/
macro "ex_run" : tactic => `(tactic| ((repeat ex_step); rw [exN_zero]))

set_option maxHeartbeats 4000000 in
theorem execOp0F_x182 : execOp0F 0x182 = execRange 0x182 := by
  unfold execOp0F; rfl

set_option maxHeartbeats 4000000 in
theorem execOp0F_x183 : execOp0F 0x183 = execRange 0x183 := by
  unfold execOp0F; rfl

set_option maxHeartbeats 4000000 in
theorem execOp0F_x184 : execOp0F 0x184 = execRange 0x184 := by
  unfold execOp0F; rfl

set_option maxHeartbeats 4000000 in
theorem execOp0F_x185 : execOp0F 0x185 = execRange 0x185 := by
  unfold execOp0F; rfl

set_option maxHeartbeats 4000000 in
theorem execOp0F_x187 : execOp0F 0x187 = execRange 0x187 := by
  unfold execOp0F; rfl

attribute [cbv_eval] execOp0F_x182 execOp0F_x183 execOp0F_x184 execOp0F_x185 execOp0F_x187

end Solutions.ShaX
