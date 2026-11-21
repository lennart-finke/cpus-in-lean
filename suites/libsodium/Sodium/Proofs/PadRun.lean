import Sodium.Proofs.PadLib
import Sodium.Proofs.Code
import Solutions.Logic.Path
import Solutions.Logic.MemRules
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
/-!
# Straight-line runs at any instruction count, by `cbv` one instruction at a time

`run_chain h : k from s0` evaluates `k` instructions from the state `St.m s0` of the libsodium image,
each with `cbv` on `okState (execInstr (St.m s))` (so the instruction count stays symbolic: it only
enters through `Solutions.Logic.prun_step`), and adds the hypothesis

    h : PRun img [eip₀, …, eip_{k-1}] (St.m s0) (St.m s_k)

with the final state `s_k` read off the evaluation, its instruction count `ic + k.toUInt64` for the
count `ic` of `s0`. The side conditions of a step: the address is not the sentinel (`rfl`), the trap
flag is clear (EFLAGS must be `efl f`), and the count is below its maximum (`omega` from the context,
or `decide`).

Keeping the kernel's work small (each step is checked in a few seconds and well under 4 GB):

* every step is a theorem of its own (`auxThm`), over the hypotheses of the context;
* a step is first proved for fresh variables in place of the compound register values (and of the
  argument of `efl`), then, if it needs facts about them (an address, a branch), for fresh variables
  in place of the compound arguments of the flag computations with their `toNat` known to `omega`,
  and only then on the values themselves (`chainStep`);
* the proofs that stores are outside the code, which the memory term carries, are theorems of their
  own (`abbrevProofs`);
* the state after a step is evaluated by `cbv` as well, so that the kernel compares equal normal forms.

Files using it should set `Elab.async false`, so that the step theorems are checked one at a time.
-/
namespace Sodium.Proofs.PadRun
open Lean Meta Elab Tactic X86 Lean.Meta.Tactic.Cbv Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Utils

theorem running_of_eip (s : St) (h : (s.eip == Image.sym_halt) = false) : Running img s.m := by
  unfold Running returned
  simp [St.m, img, h]

theorem ic_lt (ic0 : UInt64) (i : Nat) (h : ic0.toNat + i + 1 < 2 ^ 64) :
    ic0 + i.toUInt64 < 0xFFFFFFFFFFFFFFFF := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ic_succ (ic0 : UInt64) (i : Nat) : ic0 + i.toUInt64 + 1 = ic0 + (i + 1).toUInt64 := by
  rw [UInt64.add_assoc]
  congr 1
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem ic_zero (ic0 : UInt64) : ic0 = ic0 + (0 : Nat).toUInt64 := by
  simp

theorem prun_cast {l : List UInt32} {m a b : Machine} (h : PRun img l m a) (e : a = b) : PRun img l m b :=
  e ▸ h

/-- Field `f` of the structure literal `e` of structure `S`. -/
def fld (e : Expr) (S f : Name) : MetaM Expr := do
  let some idx := (getStructureFields (← getEnv) S).idxOf? f | throwError "no field {f} in {S}"
  whnfCore (Expr.proj S idx e)

/-- The fields of the `St` literal `s`. -/
def stFields (s : Expr) : MetaM (Array Expr) := do
  let s ← whnfR s
  unless s.isAppOfArity ``St.mk 12 do throwError "not an St literal: {s}"
  return s.getAppArgs

/-- `value : type` as a theorem of its own, over every hypothesis of the local context (so that the
kernel checks each instruction separately). -/
def auxThm (type value : Expr) (kind : Name := `run_step) : TacticM Expr := do
  let fvars := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || d.isLet then acc else acc.push d.toExpr
  let ty ← mkForallFVars fvars type
  let val ← mkLambdaFVars fvars value
  let name ← Term.mkAuxName kind
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := val })
  return mkAppN (mkConst name) fvars

/-- The proof arguments of the code-keeping stores in `mem`, replaced by auxiliary theorems. -/
partial def abbrevProofs (mem : Expr) : TacticM Expr := do
  if (mem.isAppOfArity ``CodeMem.wr4 7 || mem.isAppOfArity ``CodeMem.wr1 7) then
    let args := mem.getAppArgs
    let g ← abbrevProofs args[3]!
    let ok := args[6]!
    let ok ← if ok.getAppFn.constName?.any (fun n => (toString n).endsWith "run_ok" ||
        ((toString n).splitOn "run_ok").length > 1) then pure ok
      else auxThm (← inferType ok) (← instantiateMVars ok) `run_ok
    return mkAppN mem.getAppFn (args.set! 3 g |>.set! 6 ok)
  else if mem.isAppOfArity ``CodeMem.get 4 then
    let args := mem.getAppArgs
    return mkAppN mem.getAppFn (args.set! 3 (← abbrevProofs args[3]!))
  else return mem

/-- One instruction: the proof of `PRun img [eip] (St.m s) (St.m s')` and `s'` (count `ic0 + (i+1)`). -/
def chainStep0 (s ic0 : Expr) (i : Nat) : TacticM (Expr × Expr × Expr) := do
  let fs ← stFields s
  let eip := fs[9]!
  let fl := fs[10]!
  let ic := fs[11]!
  let sm := mkApp (mkConst ``St.m) s
  let e ← mkAppM ``okState #[← mkAppM ``execInstr #[sm]]
  let r ← cbvEntry e
  let (rhs, pf) ← match r with
    | .step rhs pf _ _ => pure (rhs, pf)
    | .rfl _ _ => throwError "cbv made no progress at {eip}"
  unless rhs.isAppOfArity ``Option.some 2 do
    throwError "instruction at {eip} did not complete:{indentExpr rhs}"
  let m' := rhs.appArg!
  let cpu ← fld m' ``Machine `cpu
  let mem ← fld m' ``Machine `mem
  let get (f : Name) := fld cpu ``Cpu f
  -- the proofs that the stores are outside the code, as theorems of their own (small terms)
  let mem ← abbrevProofs mem
  let s' := mkAppN (mkConst ``St.mk) #[mem, ← get `eax, ← get `ecx, ← get `edx, ← get `ebx, ← get `esp,
    ← get `ebp, ← get `esi, ← get `edi, ← get `eip, ← get `eflags, ic]
  let rhsS ← mkAppM ``Option.some #[mkApp (mkConst ``St.m) s']
  let hxTy ← mkEq e rhsS
  -- `some (St.m s')` evaluated by `cbv` as well, so that the kernel compares equal normal forms
  -- (up to the proofs in the memory)
  let pf2 ← match ← cbvEntry rhsS with
    | .step _ pf2 _ _ => mkEqSymm pf2
    | .rfl _ _ => mkEqRefl rhsS
  let hx ← mkExpectedTypeHint (← mkEqTrans pf pf2) hxTy
  -- side conditions
  let hicTy ← mkAppM ``LT.lt #[ic, toExpr (0xFFFFFFFFFFFFFFFF : UInt64)]
  let hic ← (do
    let goalTy ← mkAppM ``LT.lt #[← mkAdd (← mkAdd (mkApp (mkConst ``UInt64.toNat) ic0) (mkNatLit i)) (mkNatLit 1),
      ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]]
    let g ← mkFreshExprMVar goalTy
    let gs ← Tactic.run g.mvarId! (evalTactic (← `(tactic| first | decide | omega | (simp; omega))))
    unless gs.isEmpty do throwError "icount bound"
    let h ← instantiateMVars g
    mkExpectedTypeHint (mkApp3 (mkConst ``ic_lt) ic0 (mkNatLit i) h) hicTy)
  unless fl.isAppOfArity ``efl 1 do throwError "EFLAGS not of the form efl f at {eip}: {fl}"
  let hTF := mkApp (mkConst ``efl_TF) fl.appArg!
  let hTF ← mkExpectedTypeHint hTF (← mkEq (← mkAppM ``HAnd.hAnd #[fl, mkConst ``Flag.TF]) (toExpr (0 : UInt32)))
  let hr := mkApp2 (mkConst ``running_of_eip) s (← mkEqRefl (mkConst ``Bool.false))
  let hic' ← mkEqRefl ic
  let step := mkAppN (mkConst ``prun_step) #[mkConst ``img, s, s', hic, hTF, hx, hic', hr]
  -- the next state, with count `ic0 + (i + 1)`
  let icN ← mkAppM ``HAdd.hAdd #[ic0, mkApp (mkConst ``Nat.toUInt64) (mkNatLit (i + 1))]
  let fs' := (← stFields s')
  let sN := mkAppN (mkConst ``St.mk) (fs'.set! 11 icN)
  let icS ← mkAppM ``HAdd.hAdd #[ic, toExpr (1 : UInt64)]
  let sS := mkAppN (mkConst ``St.mk) (fs'.set! 11 icS)
  let x ← mkFreshUserName `x
  let fn := Expr.lam x (mkConst ``UInt64) (mkApp (mkConst ``St.m) (mkAppN (mkConst ``St.mk) (fs'.set! 11 (.bvar 0)))) .default
  let heq ← mkCongrArg fn (mkApp2 (mkConst ``ic_succ) ic0 (mkNatLit i))
  let heq ← mkExpectedTypeHint heq (← mkEq (mkApp (mkConst ``St.m) sS) (mkApp (mkConst ``St.m) sN))
  let lTy ← mkListLit (mkConst ``UInt32) [eip]
  let stepTy := mkAppN (mkConst ``PRun) #[mkConst ``img, lTy, sm, mkApp (mkConst ``St.m) sS]
  let step ← mkExpectedTypeHint step stepTy
  let step := mkAppN (mkConst ``prun_cast) #[lTy, sm, mkApp (mkConst ``St.m) sS, mkApp (mkConst ``St.m) sN, step, heq]
  -- checked by the kernel on its own, as an auxiliary theorem
  let ty := mkAppN (mkConst ``PRun) #[mkConst ``img, lTy, sm, mkApp (mkConst ``St.m) sN]
  let step ← auxThm ty (← instantiateMVars step)
  return (step, sN, eip)

/-- A register value kept as it is in a step: a variable, a literal, a load, or `x + literal`. -/
def keepVal (e : Expr) : Bool :=
  e.isFVar || (Sym.getNatValue? e).run.isSome || e.isAppOfArity ``rdRaw 3 ||
    (e.isAppOfArity ``UInt32.add 2 && e.appFn!.appArg!.isFVar && (Sym.getNatValue? e.appArg!).run.isSome)

/-- The compound arguments of the flag computations in `f`. -/
partial def flagArgs (f : Expr) (acc : Array Expr) : Array Expr :=
  let add (acc : Array Expr) (x : Expr) := if keepVal x || acc.contains x then acc else acc.push x
  if f.isAppOfArity ``Prod.snd 3 then flagArgs f.appArg! acc
  else match f with
  | .proj _ _ p => flagArgs p acc
  | _ =>
    if f.isAppOfArity ``subF 4 || f.isAppOfArity ``addF 4 then add (add acc (f.getArg! 1)) (f.getArg! 2)
    else if f.isAppOfArity ``logicF 2 then add acc f.appArg!
    else if f.isAppOfArity ``mixF 3 then flagArgs (f.getArg! 1) (flagArgs (f.getArg! 0) acc)
    else acc

/-- One instruction, proved for fresh variables `x` in place of the values `cands` in the register
fields of `s` (and, with `withEqs`, hypotheses `x.toNat = v.toNat` for `omega`), so that the kernel
checks it on small terms; then instantiated. -/
def chainStepGen (s ic0 : Expr) (i : Nat) (cands : Array Expr) (withEqs : Bool) :
    TacticM (Expr × Expr × Expr) := do
  let fs ← stFields s
  withLocalDeclsD (cands.map fun _ => (`g, fun _ => pure (mkConst ``UInt32))) fun xs => do
    let eqTys ← if withEqs then
        (cands.zip xs).mapM (fun (v, x) => mkEq (mkApp (mkConst ``UInt32.toNat) x) (mkApp (mkConst ``UInt32.toNat) v))
      else pure #[]
    withLocalDeclsD (eqTys.map fun ty => (`hg, fun _ => pure ty)) fun hs => do
      let rep (e : Expr) : Expr := e.replace fun x =>
        match cands.idxOf? x with
        | some k => some xs[k]!
        | none => none
      let fs2 := fs.mapIdx fun j f => if j == 0 || j == 9 || j == 11 then f else rep f
      let (pf, sN, eip) ← chainStep0 (mkAppN (mkConst ``St.mk) fs2) ic0 i
      let refls ← if withEqs then cands.mapM (fun v => mkEqRefl (mkApp (mkConst ``UInt32.toNat) v))
        else pure #[]
      let back (e : Expr) : Expr := (e.replaceFVars hs refls).replaceFVars xs cands
      return (back pf, back sN, eip)

/-- One instruction: first with the compound register values and flag argument generalized, then with
the compound arguments of the flag computations generalized and their values known to `omega`, then
on the values themselves. -/
def chainStep (s ic0 : Expr) (i : Nat) : TacticM (Expr × Expr × Expr) := do
  let fs ← stFields s
  let mut regs : Array Expr := #[]
  for j in [1:9] do
    unless keepVal fs[j]! || regs.contains fs[j]! do regs := regs.push fs[j]!
  let mut c1 := regs
  if fs[10]!.isAppOfArity ``efl 1 && !keepVal fs[10]!.appArg! then c1 := c1.push fs[10]!.appArg!
  let c2 := if fs[10]!.isAppOfArity ``efl 1 then flagArgs fs[10]!.appArg! regs else regs
  let saved ← saveState
  if !c1.isEmpty then
    try return ← chainStepGen s ic0 i c1 false
    catch _ => saved.restore
  if !c2.isEmpty then
    try return ← chainStepGen s ic0 i c2 true
    catch _ => saved.restore
  chainStep0 s ic0 i

syntax (name := runChain) "run_chain " ident " : " num " from " term : tactic

@[tactic runChain] def evalRunChain : Tactic := fun stx => withMainContext do
  let name := stx[1].getId
  let k := stx[3].isNatLit?.getD 0
  let s0 ← elabTerm stx[5] (some (mkConst ``St))
  let s0 ← instantiateMVars s0
  let fs ← stFields s0
  let ic0 := fs[11]!
  -- start from count `ic0 + 0`
  let s ← pure (mkAppN (mkConst ``St.mk) (fs.set! 11 (← mkAppM ``HAdd.hAdd #[ic0, mkApp (mkConst ``Nat.toUInt64) (mkNatLit 0)])))
  let mut cur := s
  let mut steps : Array Expr := #[]
  let mut eips : Array Expr := #[]
  let mut starts : Array Expr := #[]
  for i in [0:k] do
    let (pf, sN, eip) ← chainStep cur ic0 i
    starts := starts.push (mkApp (mkConst ``St.m) cur)
    steps := steps.push pf
    eips := eips.push eip
    cur := sN
  -- compose right-nested
  let fin := mkApp (mkConst ``St.m) cur
  let mut acc := mkAppN (mkConst ``PRun.nil) #[mkConst ``img, fin]
  let mut accL ← mkListLit (mkConst ``UInt32) []
  for j in [0:k] do
    let i := k - 1 - j
    let l1 ← mkListLit (mkConst ``UInt32) [eips[i]!]
    let a := starts[i]!
    let b := if i + 1 < k then starts[i + 1]! else fin
    acc := mkAppN (mkConst ``PRun.append) #[mkConst ``img, l1, accL, a, b, fin, steps[i]!, acc]
    accL ← mkAppM ``List.cons #[eips[i]!, accL]
  -- the start with count `ic0`
  let e0 ← mkCongrArg (Expr.lam `x (mkConst ``UInt64)
    (mkApp (mkConst ``St.m) (mkAppN (mkConst ``St.mk) (fs.set! 11 (.bvar 0)))) .default) (mkApp (mkConst ``ic_zero) ic0)
  let finTy := mkAppN (mkConst ``PRun) #[mkConst ``img, accL, mkApp (mkConst ``St.m) s0, mkApp (mkConst ``St.m) cur]
  let pf ← mkEqMPR (← mkCongrArg (Expr.lam `y (mkConst ``Machine)
    (mkAppN (mkConst ``PRun) #[mkConst ``img, accL, .bvar 0, mkApp (mkConst ``St.m) cur]) .default) e0) acc
  let pf ← mkExpectedTypeHint pf finTy
  liftMetaTactic fun g => do
    let g ← g.assert name finTy pf
    let (_, g) ← g.intro1P
    return [g]

end Sodium.Proofs.PadRun
