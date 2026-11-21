import Curl.Proofs.Sym
/-!
# `xrun`: symbolic execution of the curl image in a proof

For a goal `Reaches img (St.m s) Q` with `s` a structure literal at a literal address, `xrun stops`
executes instructions one at a time (`reaches_step`, each instruction evaluated by `cbv` with the
`Curl.Proofs.Sym` set-up) until the address is one of `stops` (or the return sentinel). When an
instruction's effect depends on an undecided fact `P` (an undecided `pdec P` in the result), the
goal is split on `P` and both cases are executed further. The goals left are the states at the stop
addresses, each with its path condition in context.

The instruction count of a state is kept as `x + c` with a literal `c`; each step needs
`x.toNat + c + 1 < 2 ^ 64`, which `omega` proves from the hypotheses (`xomega`).

Status (work in progress): checked on the entry of `memchr` (push, loads, `test`/`je` with a case
split, `pop`/`ret`, the `nop` run up to the loop head). The kernel check of the resulting proof is
expensive: about 250 MB and 2 s per instruction, so a single declaration should stay below about a
dozen instructions (split longer runs into lemmas at block boundaries).
-/
namespace Curl.Proofs.Sym
open X86 Ssl Solutions.Logic Solutions.Exec Curl.Proofs Curl.Hostcheck Lean Meta Elab Tactic

register_option xrunDebug : Bool := { defValue := false, descr := "xrun: timing messages" }

theorem running_of_eip (s : St) (h : s.eip ≠ Image.sym_halt) : Running img s.m := by
  unfold Running returned
  have : (s.eip == Image.sym_halt) = false := by simpa using h
  simp [St.m, img, this]

theorem reaches_step {Q : Machine → Prop} (s s' : St) (x c c' : UInt64) (hx : s.ic = x + c)
    (hc : c' = c + 1) (hb : x.toNat + c.toNat + 1 < 2 ^ 64) (hTF : s.fl &&& Flag.TF = 0)
    (he : s.eip ≠ Image.sym_halt) (h : okState (execInstr s.m) = some s'.m) (hic : s'.ic = s.ic)
    (hn : Reaches img ({ s' with ic := x + c' }).m Q) : Reaches img s.m Q := by
  have hlt : s.ic < 0xFFFFFFFFFFFFFFFF := by
    rw [hx, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    have := c.toNat_lt
    simp
    omega
  have hs := step_of_okState s hlt hTF s' h hic
  have e : s.ic + 1 = x + c' := by rw [hx, hc, UInt64.add_assoc]
  rw [e] at hs
  exact Reaches.run (Run.single (running_of_eip s he) hs) hn

theorem ic_add_zero (x : UInt64) : x = x + 0 := (UInt64.add_zero x).symm

theorem tf_efl (f : UInt32) : efl f &&& Flag.TF = 0 := efl_TF f

theorem ne_halt_of (a : UInt32) (h : (a == Image.sym_halt) = false) : a ≠ Image.sym_halt := by
  simpa using h

/-- The fields of an `St` literal. -/
def stFields (s : Expr) : MetaM (Array Expr) := do
  let s ← whnfR s
  unless s.isAppOfArity ``St.mk 12 do throwError "xrun: not a state literal {s}"
  return s.getAppArgs

def mkSt (fs : Array Expr) : Expr := mkAppN (mkConst ``St.mk) fs

/-- The literal value of a `UInt32` or `UInt64` expression, if it is one. -/
def litVal? (e : Expr) : MetaM (Option Nat) := do
  if let some v := (Sym.getNatValue? e).run then return some v
  for t in [``UInt32, ``UInt64] do
    if let some (n, _) ← getOfNatValue? e t then return some n
  return none

/-- `x + c` with a literal `c`. -/
def icSplit (e : Expr) : MetaM (Expr × Nat) := do
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some c ← litVal? e.appArg! then return (e.appFn!.appArg!, c)
  if e.isAppOfArity ``UInt64.add 2 then
    if let some c ← litVal? e.appArg! then return (e.appFn!.appArg!, c)
  return (e, 0)

/-- The first undecided `pdec P` in `e`. -/
def findPdec (e : Expr) : Option Expr :=
  (e.find? fun t => t.isAppOfArity ``pdec 2 && !t.hasLooseBVars).map (·.getArg! 0)

structure XState where
  steps : Nat := 0
  splits : Nat := 0

/-- One step at the goal `g`: `.inl goals` after a split or a step, `.inr ()` if `g` is at a stop. -/
def xstep1 (g : MVarId) (stops : Array Nat) : MetaM (Option (List MVarId)) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let_expr Reaches _ m Q := ty | throwError "xrun: goal is not `Reaches`: {ty}"
  unless m.isAppOfArity ``St.m 1 do throwError "xrun: machine is not `St.m _`"
  let s := m.appArg!
  let fs ← stFields s
  let some eip ← litVal? fs[9]! | return none
  if stops.contains eip || eip == 0x100808 then return none
  Sym.Discharge.resetOmegaCache
  let e ← mkAppM ``okState #[mkApp (mkConst ``execInstr) m]
  let t0 ← IO.monoMsNow
  let r ← Lean.Meta.Tactic.Cbv.cbvEntry e
  let t1 ← IO.monoMsNow
  if xrunDebug.get (← getOptions) then IO.eprintln s!"step {eip}: cbv {t1 - t0} ms"
  let (e', pf) ← match r with
    | .step e' pf .. => pure (e', pf)
    | .rfl .. => throwError "xrun: no progress at {eip}"
  if let some P := findPdec e' then
    -- split on `P` and retry both cases
    let (g1, g2) ← g.byCases P `hpath
    return some [g1.mvarId, g2.mvarId]
  unless e'.isAppOfArity ``Option.some 2 do
    let stuck := e'.find? fun t => (t.isAppOf ``rdMem || t.isAppOf ``wrMem || t.isAppOf ``wrBytes ||
      t.isAppOf ``rdBytes) && !t.hasLooseBVars
    let ifs := e'.find? fun t => (t.isAppOf ``ite || t.isAppOf ``dite || t.isAppOf ``cond) && !t.hasLooseBVars
    throwError "xrun: at {eip}: stuck at {stuck}; first if: {ifs}\nTERM {e'}"
  let m' := e'.appArg!
  let cpu ← Sym.Discharge.field m' ``Machine `cpu
  let get (n : Name) := Sym.Discharge.field cpu ``Cpu n
  let fs' : Array Expr := #[← Sym.Discharge.field m' ``Machine `mem, ← get `eax, ← get `ecx, ← get `edx,
    ← get `ebx, ← get `esp, ← get `ebp, ← get `esi, ← get `edi, ← get `eip, ← get `eflags,
    ← Sym.Discharge.field m' ``Machine `icount]
  let s' := mkSt fs'
  unless fs'[10]!.isAppOfArity ``efl 1 do throwError "xrun: flags after {eip} not `efl _`: {fs'[10]!}"
  let target ← mkEq e (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Machine) (mkApp (mkConst ``St.m) s'))
  let hstep ← mkExpectedTypeHint pf target
  let (x, c) ← icSplit fs[11]!
  let cE := toExpr c.toUInt64
  let c'E := toExpr (c + 1).toUInt64
  let hxT ← mkEq fs[11]! (← mkAppM ``HAdd.hAdd #[x, cE])
  let hx ← if c == 0 && !(fs[11]!.isAppOfArity ``HAdd.hAdd 6 || fs[11]!.isAppOfArity ``UInt64.add 2) then
      mkExpectedTypeHint (mkApp (mkConst ``ic_add_zero) x) hxT
    else mkExpectedTypeHint (← mkEqRefl fs[11]!) hxT
  let hc ← mkExpectedTypeHint (← mkEqRefl c'E) (← mkEq c'E (← mkAppM ``HAdd.hAdd #[cE, toExpr (1 : UInt64)]))
  let hbP ← mkLT (← mkAdd (← mkAdd (mkApp (mkConst ``UInt64.toNat) x) (mkApp (mkConst ``UInt64.toNat) cE))
    (mkNatLit 1)) (mkNatLit (2 ^ 64))
  let some hb ← Sym.Discharge.omegaP? hbP | throwError "xrun: no bound for the instruction count {x} + {c + 1}"
  let hTF := mkApp (mkConst ``tf_efl) fs[10]!.appArg!
  let he := mkApp2 (mkConst ``ne_halt_of) fs[9]! (← mkEqRefl (mkConst ``Bool.false))
  let hic ← mkEqRefl fs[11]!
  let fs2 := fs'.set! 11 (← mkAppM ``HAdd.hAdd #[x, c'E])
  let s2 := mkSt fs2
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Reaches #[mkConst ``img, mkApp (mkConst ``St.m) s2, Q])
    (← g.getTag)
  let pfAll := mkAppN (mkConst ``reaches_step) #[Q, s, s', x, cE, c'E, hx, hc, hb, hTF, he, hstep, hic, g']
  g.assign pfAll
  if xrunDebug.get (← getOptions) then IO.eprintln s!"step {eip}: total {(← IO.monoMsNow) - t0} ms"
  return some [g'.mvarId!]

/-- Execute from every goal until a stop; returns the goals left. -/
partial def xrunCore (stops : Array Nat) (fuel : Nat) (gs : List MVarId) : MetaM (List MVarId) := do
  let mut out := []
  let mut work := gs
  let mut fuel := fuel
  while !work.isEmpty do
    let g :: rest := work | break
    work := rest
    if fuel == 0 then out := out ++ [g]; continue
    fuel := fuel - 1
    match ← xstep1 g stops with
    | none => out := out ++ [g]
    | some gs' => work := gs' ++ work
  return out

syntax "xrun" "[" num,* "]" (num)? : tactic

elab_rules : tactic
  | `(tactic| xrun [$stops,*] $[$fuel]?) => do
    let stops := stops.getElems.map (·.getNat)
    let fuel := match fuel with | some f => f.getNat | none => 100000
    let gs ← getGoals
    let g :: rest := gs | throwError "no goals"
    let out ← xrunCore stops fuel [g]
    setGoals (out ++ rest)

/-- The address and registers of the state of a `Reaches` goal (for writing invariants). -/
elab "xshow" : tactic => withMainContext do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  let_expr Reaches _ m _ := ty | throwError "not Reaches"
  let fs ← stFields m.appArg!
  logInfo m!"eip {fs[9]!}\neax {fs[1]!}\necx {fs[2]!}\nedx {fs[3]!}\nebx {fs[4]!}\nesp {fs[5]!}\nebp {fs[6]!}\nesi {fs[7]!}\nedi {fs[8]!}\nfl {fs[10]!}\nic {fs[11]!}\nmem {fs[0]!}"

/-- The path conditions of the goal. -/
elab "xpath" : tactic => withMainContext do
  let mut out : Array MessageData := #[]
  for d in (← getLCtx) do
    if d.userName.toString.startsWith "hpath" then out := out.push m!"{d.type}"
  logInfo m!"path {out}"

end Curl.Proofs.Sym
