import Solutions.Exec.Mem
import Solutions.Exec.CodeWr
import Solutions.Exec.Cbv
import Solutions.Exec.Alu
import Solutions.Logic.Decode
import Solutions.Logic.CodeWr1
import Lean
/-!
# Executing instructions with `cbv` (a fixed copy)

This is `Solutions/Exec/Step.lean` as of commit 2a24e43 (prover A's execution layer), copied into the
namespace `Solutions.Cbx` so that the libsodium and curl proofs do not change with the original,
which is still being developed. Two changes:

* the discharger `omega?` runs `omega` without error recovery and with the whole context, and
  rejects a proof that contains a placeholder or a metavariable (with error recovery, a failed `omega`
  can leave an error-recovery placeholder behind, which the original took for a proof);
* the tactic is named `sym_omega`;
* `x - k` is normalized to `x + (-k)` by default (`logic.addrSub`).

Everything else (the `efl` form of EFLAGS, the opaque integer operations, the data-access rules,
the code-keeping stores, the address normal form) is the original's; see its documentation.
-/
namespace Solutions.Cbx
open X86 Solutions.Logic Solutions.Exec Lean Meta

/-! ## EFLAGS -/

/-- EFLAGS with arithmetic flags from `f` and everything else as `Ssl.entry` sets it. -/
def efl (f : UInt32) : UInt32 := 2 ||| (f &&& 0x8D5)

theorem efl_and_zero (f k : UInt32) (h2 : (2 : UInt32) &&& k = 0) (h3 : (0x8D5 : UInt32) &&& k = 0) :
    efl f &&& k = 0 := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  have h2' := congrArg UInt32.toBitVec h2
  have h3' := congrArg UInt32.toBitVec h3
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or] at *
  rw [BitVec.and_or_distrib_right, h2',
    show f.toBitVec &&& (0x8D5 : UInt32).toBitVec &&& k.toBitVec =
      f.toBitVec &&& ((0x8D5 : UInt32).toBitVec &&& k.toBitVec) by ac_rfl, h3']
  simp

/-- The arithmetic flags of `f` replaced by those of `v` under `mask`. -/
def mixF (f v mask : UInt32) : UInt32 := (f &&& ~~~mask) ||| (v &&& mask)

theorem efl_set (f v mask : UInt32) (hm : mask &&& ~~~0x8D5 = 0) :
    (efl f &&& ~~~mask) ||| (v &&& mask) = efl (mixF f v mask) := by
  unfold efl mixF
  apply UInt32.toBitVec_inj.1
  have hm' := congrArg UInt32.toBitVec hm
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not] at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun x => BitVec.getLsbD x i) hm'
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi,
    decide_true, Bool.true_and] at hb ⊢
  have h2 := congrArg (fun x => BitVec.getLsbD x i)
    (show (2 : UInt32).toBitVec &&& (0x8D5 : UInt32).toBitVec = 0 by decide)
  have hz : ∀ j, (UInt32.toBitVec 0).getLsbD j = false := fun j => by simp
  have hz' : ∀ j, (0 : BitVec 32).getLsbD j = false := fun j => by simp
  rw [BitVec.getLsbD_and, hz'] at h2
  rw [hz] at hb
  cases ha : (2 : UInt32).toBitVec.getLsbD i <;> cases hb2 : (0x8D5 : UInt32).toBitVec.getLsbD i <;>
    cases hmi : mask.toBitVec.getLsbD i <;> cases f.toBitVec.getLsbD i <;> cases v.toBitVec.getLsbD i <;>
    simp_all

theorem efl_set_arith (f v : UInt32) : (efl f &&& ~~~0x8D5) ||| (v &&& 0x8D5) = efl v := by
  rw [efl_set f v 0x8D5 (by decide)]
  unfold efl mixF
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (0x8D5 : UInt32).toBitVec.getLsbD i <;> simp

/-! The rules `cbv` uses on EFLAGS (stated on the opaque operations `cbv` leaves behind). -/
section rules
set_option linter.unusedVariables false
theorem efl_TF (f : UInt32) : UInt32.land (efl f) 256 = 0 := efl_and_zero f 256 (by decide) (by decide)
theorem efl_IF (f : UInt32) : UInt32.land (efl f) 512 = 0 := efl_and_zero f 512 (by decide) (by decide)
theorem efl_DF (f : UInt32) : UInt32.land (efl f) 1024 = 0 := efl_and_zero f 1024 (by decide) (by decide)
theorem efl_NT (f : UInt32) : UInt32.land (efl f) 16384 = 0 := efl_and_zero f 16384 (by decide) (by decide)
theorem efl_RF (f : UInt32) : UInt32.land (efl f) 65536 = 0 := efl_and_zero f 65536 (by decide) (by decide)
theorem efl_VM (f : UInt32) : UInt32.land (efl f) 131072 = 0 := efl_and_zero f 131072 (by decide) (by decide)
theorem efl_AC (f : UInt32) : UInt32.land (efl f) 262144 = 0 := efl_and_zero f 262144 (by decide) (by decide)
theorem efl_setArith (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965034) (UInt32.land v 2261) = efl v := efl_set_arith f v
theorem efl_setNoCF (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965035) (UInt32.land v 2260) = efl (mixF f v 2260) :=
  efl_set f v 2260 (by decide)
theorem efl_setCFOF (f v : UInt32) :
    UInt32.lor (UInt32.land (efl f) 4294965246) (UInt32.land v 2049) = efl (mixF f v 2049) :=
  efl_set f v 2049 (by decide)
/-- A 32-bit target is never above the flat code segment's limit (`jumpTo`). -/
theorem max_lt_false (t : UInt32) : ((4294967295 : UInt32) < t) = False := by
  apply propext; constructor
  · intro h; rw [UInt32.lt_iff_toNat_lt] at h; have := t.toNat_lt; simp at h; omega
  · intro h; exact h.elim
end rules

register_option logic.addrSub : Bool := {
  defValue := false
  descr := "Solutions.Logic: rewrite `x - literal` to `x + literal`"
}

register_option logic.addrNorm : Bool := {
  defValue := true
  descr := "Solutions.Logic: normalize addresses to `x + literal`"
}

register_option logic.codeWr : Bool := {
  defValue := true
  descr := "Solutions.Logic: keep stores outside the code as `CodeMem.wr4` (code fetches stay direct)"
}

/-! ## Side conditions of data accesses -/

theorem cpl_zero (c : Cpu) (f : UInt32) (h1 : c.cr0 = 17) (h2 : c.eflags = efl f) (h3 : c.cs.sel = 8) :
    c.cpl = 0 := by
  have hv := efl_VM f
  simp only [Cpu.cpl, Cpu.pe, Cpu.vm86, h1, h2, h3, Flag.VM, CR0.PE]
  rw [show efl f &&& 131072 = UInt32.land (efl f) 131072 from rfl, hv]
  decide

theorem flatM_intro (m : Machine) (h1 : m.cpu.cr0 &&& CR0.PG = 0) (h2 : m.cpu.npOn = false)
    (h3 : m.cpu.bpOn = false) (h4 : m.tso = none) (h5 : m.apic.mmio = 0xFEE00000) (h6 : m.watch = #[]) :
    FlatM m := ⟨h1, h2, h3, h4, h5, h6⟩

theorem flatSeg_intro (sr : SegReg) (h1 : sr.base = 0) (h2 : sr.limit = 0xFFFFFFFF) (h3 : sr.attr = 0xC093) :
    FlatSeg sr := ⟨h1, h2, h3⟩

theorem toNat_uadd (a b : UInt32) : (UInt32.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 :=
  UInt32.toNat_add a b
theorem toNat_usub (a b : UInt32) : (UInt32.sub a b).toNat = (2 ^ 32 - b.toNat + a.toNat) % 2 ^ 32 :=
  UInt32.toNat_sub a b

/-- The side conditions of the data-access rules: arithmetic on addresses and memory sizes, from the
hypotheses in context. -/
macro "sym_omega" : tactic =>
  `(tactic| ((try simp only [size_wrBytes, wr4_get_size, Solutions.Logic.wr1_get_size, toNat_uadd, toNat_usub, ramTop, UInt32.toNat_add,
      UInt32.toNat_sub, UInt32.reduceToNat] at *) <;> omega))

attribute [scoped cbv_opaque] efl mixF UInt32.add UInt32.sub UInt32.mul UInt32.land UInt32.lor UInt32.xor
  UInt32.shiftLeft UInt32.shiftRight UInt32.complement UInt64.add UInt64.sub UInt64.land UInt64.lor
  CodeMem.wr4 StoreOk Array.replicate X86.cmosInit X86.rdMem X86.wrMem X86.addF X86.subF X86.logicF X86.shiftOp X86.imulCore

attribute [scoped cbv_eval] efl_TF efl_IF efl_DF efl_NT efl_RF efl_VM efl_AC efl_setArith efl_setNoCF
  efl_setCFOF max_lt_false

/-! ## The data-access simprocs -/

theorem rdBytes4_wrBytes4_same {mem : ByteArray} {a b v : UInt32} (h : a.toNat + 4 ≤ mem.size)
    (hab : a.toNat = b.toNat) : rdBytes (wrBytes mem a 4 v) b 4 = v := by
  rw [← UInt32.toNat_inj.mp hab]
  exact Solutions.Logic.rdBytes4_wrBytes4_self h

namespace Discharge
open Lean Meta Elab

/-- Field `fieldName` of the structure literal `e`, reduced. -/
def field (e : Expr) (structName fieldName : Name) : MetaM Expr := do
  let some idx := (getStructureFields (← getEnv) structName).idxOf? fieldName
    | throwError "no field {fieldName}"
  whnfCore (Expr.proj structName idx e)

/-- Prove `P` by `sym_omega` in the current context: without error recovery, so that a failed
attempt is a failure, and only a proof without placeholders or metavariables counts. -/
def omega? (P : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar P
  let msgs := (← getThe Core.State).messages
  let ok ← try
      let gs ← Term.TermElabM.run' <| Term.withoutErrToSorry <|
        Tactic.run g.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| sym_omega))))
      pure gs.isEmpty
    catch e => do
      trace[Meta.Tactic.cbv.rewrite] "omega failed on {P}: {e.toMessageData}"
      pure false
  modifyThe Core.State fun st => { st with messages := msgs }
  if !ok then return none
  let pf ← instantiateMVars g
  if pf.hasSorry || pf.hasSyntheticSorry || pf.hasExprMVar then
    trace[Meta.Tactic.cbv.rewrite] "omega proof incomplete for {P}"
    return none
  return some pf

/-- Elaborate a closed proof term. -/
def elabPf (stx : Term) : MetaM (Option Expr) := do
  try
    let e ← Term.TermElabM.run' do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasExprMVar then return none
    return some e
  catch _ => return none

/-- `Eq.refl` at the elaborated equation `stx`, left to the kernel to check. -/
def reflOf (stx : Term) : MetaM (Option Expr) := do
  try
    let ty ← Term.TermElabM.run' do
      let e ← Term.elabTerm stx (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let some (_, a, _) := ty.eq? | return none
    return some (← mkExpectedTypeHint (← mkEqRefl a) ty)
  catch _ => return none

/-- A size operand: a literal, or the conversion of a literal (`Sz` is `UInt8`). -/
def sizeLit? (n : Expr) : Option Nat :=
  match (Sym.getNatValue? n).run with
  | some v => some v
  | none => if n.isAppOfArity ``UInt8.toUInt32 1 then (Sym.getNatValue? n.appArg!).run else none

/-- The proofs that the machine literal `m` is flat at CPL 0 with segment `s` flat, and that the
access of `n` bytes at `off` is inside memory below `ramTop`. -/
def accessProofs (m s off n : Expr) : MetaM (Option (Array Expr)) := do
  let some nv := sizeLit? n | do trace[Meta.Tactic.cbv.rewrite] "n not literal {n}"; return none
  let n := toExpr nv.toUInt32
  unless nv == 1 || nv == 2 || nv == 4 do return none
  let cpu ← field m ``Machine `cpu
  let ef ← field cpu ``Cpu `eflags
  unless ef.isAppOfArity ``efl 1 do trace[Meta.Tactic.cbv.rewrite] "eflags {ef}"; return none
  let f := ef.appArg!
  let mS ← Term.TermElabM.run' (Term.exprToSyntax m)
  let sS ← Term.TermElabM.run' (Term.exprToSyntax s)
  let fS ← Term.TermElabM.run' (Term.exprToSyntax f)
  let nS ← Term.TermElabM.run' (Term.exprToSyntax n)
  let some f1 ← reflOf (← `(($mS).cpu.cr0 &&& CR0.PG = 0)) | return none
  let some f2 ← reflOf (← `(($mS).cpu.npOn = false)) | return none
  let some f3 ← reflOf (← `(($mS).cpu.bpOn = false)) | return none
  let some f4 ← reflOf (← `(($mS).tso = none)) | return none
  let some f5 ← reflOf (← `(($mS).apic.mmio = 0xFEE00000)) | return none
  let some f6 ← reflOf (← `(($mS).watch = #[])) | return none
  let hflat := mkAppN (mkConst ``flatM_intro) #[m, f1, f2, f3, f4, f5, f6]
  let some c1 ← reflOf (← `(($mS).cpu.cr0 = 17)) | return none
  let some c2 ← reflOf (← `(($mS).cpu.eflags = efl $fS)) | return none
  let some c3 ← reflOf (← `(($mS).cpu.cs.sel = 8)) | return none
  let hcpl := mkAppN (mkConst ``cpl_zero) #[cpu, f, c1, c2, c3]
  let some s1 ← reflOf (← `((($mS).cpu.getSeg $sS).base = 0)) | return none
  let some s2 ← reflOf (← `((($mS).cpu.getSeg $sS).limit = 0xFFFFFFFF)) | return none
  let some s3 ← reflOf (← `((($mS).cpu.getSeg $sS).attr = 0xC093)) | return none
  let hs := mkAppN (mkConst ``flatSeg_intro) #[mkApp2 (mkConst ``Cpu.getSeg) (mkApp (mkConst ``Machine.cpu) m) s, s1, s2, s3]
  let some hn ← elabPf (← `((by decide : $nS = 1 ∨ $nS = 2 ∨ $nS = 4))) | do trace[Meta.Tactic.cbv.rewrite] "n"; return none
  let mem ← field m ``Machine `mem
  let size := mkApp (mkConst ``ByteArray.size) mem
  let lhs ← mkAdd (mkApp (mkConst ``UInt32.toNat) off) (mkApp (mkConst ``UInt32.toNat) n)
  let some hr ← omega? (← mkLE lhs size) | do trace[Meta.Tactic.cbv.rewrite] "range {lhs} {size}"; return none
  let some hm ← omega? (← mkLE size (mkConst ``ramTop)) | do trace[Meta.Tactic.cbv.rewrite] "top {size}"; return none
  return some #[hflat, hcpl, hs, hn, hr, hm]

end Discharge

open Discharge in
/-- `rdMem` of a flat machine inside memory: `rdBytes`. -/
scoped cbv_simproc cbv_eval cbvRdMem (rdMem _ _ _ _ _ _) := fun e => do
  let_expr rdMem s off n w al m := e | return .rfl
  trace[Meta.Tactic.cbv.rewrite] "cbvRdMem at {e}"
  let some hs ← accessProofs m s off n | return .rfl
  let pf ← mkAppM ``rdMem_flat (hs ++ #[w, al])
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

open Discharge in
/-- `wrMem` of a flat machine inside memory: `wrBytes`. -/
scoped cbv_simproc cbv_eval cbvWrMem (wrMem _ _ _ _ _ _) := fun e => do
  let_expr wrMem s off n v al m := e | return .rfl
  let some hs ← accessProofs m s off n | return .rfl
  let pf ← mkAppM ``wrMem_flat (hs ++ #[v, al])
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  -- a word store outside the code keeps the code memory a `CodeMem`
  let rhs ← (do
    let mem ← field m ``Machine `mem
    unless (← getBoolOption `logic.codeWr true) do return rhs
    unless mem.isAppOfArity ``CodeMem.get 4 && sizeLit? n == some 4 do return rhs
    let base := mem.getArg! 0
    let size := mem.getArg! 1
    let code := mem.getArg! 2
    let G := mem.getArg! 3
    let litOf (x : Expr) : MetaM Expr := do
      match x with
      | .const .. => return (← unfoldDefinition? x).getD x
      | _ => return x
    let baseL ← litOf base
    let sizeL ← litOf size
    let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
    let four := mkNatLit 4
    let P := mkAnd (← mkLE (← mkAdd (toNat off) four) (mkApp (mkConst ``ByteArray.size) mem))
      (mkOr (← mkLE (← mkAdd (toNat off) four) (toNat baseL)) (← mkLE (← mkAdd (toNat baseL) sizeL) (toNat off)))
    let some hP ← omega? P | return rhs
    let ok ← mkExpectedTypeHint hP
      (mkAppN (mkConst ``StoreOk) #[base, size, mkApp4 (mkConst ``CodeMem.mem) base size code G, off])
    let newMem := mkApp4 (mkConst ``CodeMem.get) base size code
      (mkAppN (mkConst ``CodeMem.wr4) #[base, size, code, G, off, v, ok])
    return rhs.replace fun x =>
      if x.isAppOfArity ``wrBytes 4 && x.getArg! 1 == off && x.getArg! 3 == v then some newMem else none)
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

open Discharge in
/-- A load through a code-keeping store (`CodeMem.wr4`): the stored word when it is the same word,
the older memory when the two are disjoint. -/
scoped cbv_simproc cbv_eval cbvRdWr4 (rdRaw (CodeMem.get (CodeMem.wr4 _ _ _ _)) _ _) := fun e => do
  let_expr rdRaw mem b k := e | return .rfl
  let_expr CodeMem.get base size code G' := mem | return .rfl
  let_expr CodeMem.wr4 _ _ _ G a v _ := G' | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless kv == 4 || kv == 1 do return .rfl
  let M := mkApp4 (mkConst ``CodeMem.get) base size code G
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let sizeE := mkApp (mkConst ``ByteArray.size) M
  let four := mkNatLit 4
  let some ha ← omega? (← mkLE (← mkAdd (toNat a) four) sizeE) | return .rfl
  if kv == 4 then
    if a == b then
      let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes4_wrBytes4_self) #[M, a, v, ha]
      return .step v (← mkExpectedTypeHint pf (← mkEq e v))
    if let some hab ← omega? (← mkEq (toNat a) (toNat b)) then
      let pf := mkAppN (mkConst ``rdBytes4_wrBytes4_same) #[M, a, b, v, ha, hab]
      return .step v (← mkExpectedTypeHint pf (← mkEq e v))
    let some hb ← omega? (← mkLE (← mkAdd (toNat b) four) sizeE) | return .rfl
    let some hd ← omega? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b))
        (← mkLE (← mkAdd (toNat b) four) (toNat a))) | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes4_wrBytes4_other) #[M, a, b, v, ha, hb, hd]
    let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) M b k)
    return .step r (← mkExpectedTypeHint pf (← mkEq e r))
  else
    let some hb ← omega? (← mkLT (toNat b) sizeE) | return .rfl
    let some hd ← omega? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b)) (← mkLT (toNat b) (toNat a)))
      | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes1_wrBytes4_other) #[M, a, b, v, ha, hb, hd]
    let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) M b k)
    return .step r (← mkExpectedTypeHint pf (← mkEq e r))

open Discharge in
/-- A load after a word store: the stored word when it is the same word, the older memory when the
two are disjoint (as `sym_omega` shows from the context). -/
scoped cbv_simproc cbv_eval cbvRdWr (rdBytes (wrBytes _ _ _ _) _ _) := fun e => do
  let_expr rdBytes mem b k := e | return .rfl
  let_expr wrBytes M a n v := mem | return .rfl
  let some nv := sizeLit? n | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless nv == 4 && (kv == 4 || kv == 1) do return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let size := mkApp (mkConst ``ByteArray.size) M
  let four := mkNatLit 4
  let some ha ← omega? (← mkLE (← mkAdd (toNat a) four) size) | return .rfl
  if kv == 4 && a == b then
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes4_wrBytes4_self) #[M, a, v, ha]
    let pf ← mkExpectedTypeHint pf (← mkEq e v)
    return .step v pf
  if kv == 4 then
    if let some hab ← omega? (← mkEq (toNat a) (toNat b)) then
      let pf := mkAppN (mkConst ``rdBytes4_wrBytes4_same) #[M, a, b, v, ha, hab]
      return .step v (← mkExpectedTypeHint pf (← mkEq e v))
  if kv == 4 then
    let some hb ← omega? (← mkLE (← mkAdd (toNat b) four) size) | return .rfl
    let some hd ← omega? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b))
        (← mkLE (← mkAdd (toNat b) four) (toNat a))) | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes4_wrBytes4_other) #[M, a, b, v, ha, hb, hd]
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step (← Sym.share rhs) pf
  else
    let some hb ← omega? (← mkLT (toNat b) size) | return .rfl
    let some hd ← omega? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b)) (← mkLT (toNat b) (toNat a)))
      | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes1_wrBytes4_other) #[M, a, b, v, ha, hb, hd]
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step (← Sym.share rhs) pf

/-! ## Address normal form

Addresses are kept as `UInt32.add x k` with a literal `k` (or `x`): `(x + a) + b` with literals
`a`, `b` becomes `x + (a + b)`, `x - k` becomes `x + (-k)`, and `x + 0` becomes `x`. -/

theorem uadd_zero (x : UInt32) : UInt32.add x 0 = x := UInt32.add_zero x
theorem uadd_assoc (x a b : UInt32) : UInt32.add (UInt32.add x a) b = UInt32.add x (a + b) :=
  UInt32.add_assoc x a b
theorem usub_of (x k c : UInt32) (h : (c + k).toNat = 0) : UInt32.sub x k = UInt32.add x c := by
  show x - k = x + c
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_add] at h
  rw [UInt32.toNat_sub, UInt32.toNat_add]
  have := c.toNat_lt; have := k.toNat_lt; have := x.toNat_lt
  omega

/-- Normalize `x + k`, `(x + a) + b` and `x - k` with literal `k`, `a`, `b`. -/
scoped cbv_simproc cbv_eval cbvUAdd (UInt32.add _ _) := fun e => do
  unless (← getBoolOption `logic.addrNorm true) do return .rfl
  let_expr UInt32.add x b := e | return .rfl
  let some bv := (Sym.getNatValue? b).run | return .rfl
  if bv % 2 ^ 32 == 0 then
    return .step x (← mkExpectedTypeHint (mkApp (mkConst ``uadd_zero) x) (← mkEq e x))
  let_expr UInt32.add y a := x | return .rfl
  let some av := (Sym.getNatValue? a).run | return .rfl
  let c := (av + bv) % 2 ^ 32
  let r ← if c == 0 then pure y else Sym.share (mkApp2 (mkConst ``UInt32.add) y (toExpr c.toUInt32))
  let pf := mkApp3 (mkConst ``uadd_assoc) y a b
  let pf := if c == 0 then
      mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``UInt32) e (mkApp2 (mkConst ``UInt32.add) y (toExpr (0 : UInt32))) y
        pf (mkApp (mkConst ``uadd_zero) y)
    else pf
  return .step r (← mkExpectedTypeHint pf (← mkEq e r))

scoped cbv_simproc cbv_eval cbvUSub (UInt32.sub _ _) := fun e => do
  unless (← getBoolOption `logic.addrSub true) do return .rfl
  let_expr UInt32.sub x k := e | return .rfl
  let some kv := (Sym.getNatValue? k).run | return .rfl
  let c := (2 ^ 32 - kv % 2 ^ 32) % 2 ^ 32
  let cE := toExpr c.toUInt32
  let r ← Sym.share (mkApp2 (mkConst ``UInt32.add) x cE)
  -- `(c + k).toNat = 0` by evaluation in the kernel
  let pf := mkApp4 (mkConst ``usub_of) x k cE (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0))
  return .step r pf

end Solutions.Cbx
