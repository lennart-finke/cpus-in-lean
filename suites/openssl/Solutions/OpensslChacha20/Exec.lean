import Solutions.Logic.Cbx
import Solutions.Exec.Dispatch
import Solutions.Exec.Call
import Solutions.Logic.MemRules
import Solutions.Logic.Step
import Solutions.Logic.Run
import Ssl.OpensslChacha20.Statement
/-!
# Running several instructions at any instruction count

`exN halt k s` executes `k` instructions from the flat state `s` (`Solutions.Logic.St`), one
`execInstr` at a time, re-reading the machine after each instruction as a state `St` (`stOf?`) and
advancing the instruction count by one. `cbv` evaluates it in one call (`cbvStOf` reads the state
back from the machine literal), and `exN_run` turns the result into a `Run`, whatever the
instruction count is (it only has to stay below 2^64 - 1).

Also the `cbv` rules for the rotations (`shiftOp` of `rol` by a literal count is `Spec.Chacha.rotl`)
and for the carry flag of `cmp` (`cmovb`, `ja`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Lean Meta

/-! ## Reading a machine back as a state -/

/-- The fields of `m` that a `St` keeps, with the instruction count `ic`. -/
def repack (m : Machine) (ic : UInt64) : St :=
  ⟨m.mem, m.cpu.eax, m.cpu.ecx, m.cpu.edx, m.cpu.ebx, m.cpu.esp, m.cpu.ebp, m.cpu.esi, m.cpu.edi,
    m.cpu.eip, m.cpu.eflags, ic⟩

open Classical in
/-- `m` as a state with instruction count `ic`, when it is one. -/
noncomputable def stOf? (m : Machine) (ic : UInt64) : Option St :=
  if m = St.m (repack m ic) then some (repack m ic) else none

theorem repack_m (s : St) : repack s.m s.ic = s := rfl

theorem stOf?_of (m : Machine) (s : St) (h : m = St.m s) : stOf? m s.ic = some s := by
  subst h
  unfold stOf?
  rw [repack_m, if_pos rfl]

theorem stOf?_spec {m : Machine} {ic : UInt64} {s : St} (h : stOf? m ic = some s) :
    m = St.m s ∧ s.ic = ic := by
  unfold stOf? at h
  split at h
  · rename_i hm
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hm, rfl⟩
  · simp at h

/-! ## Several instructions -/

/-- `k` instructions from `s`, each from a running state (EIP not the sentinel `halt`, trap flag
clear), or `none`. -/
noncomputable def exN (halt : UInt32) : Nat → St → Option St
  | 0, s => some s
  | k + 1, s =>
    if s.eip = halt then none
    else if s.fl &&& 256 = 0 then
      match okState (execInstr s.m) with
      | some m =>
        match stOf? m s.ic with
        | some s' => exN halt k { s' with ic := s.ic + 1 }
        | none => none
      | none => none
    else none

theorem running_of_eip {img : Img} (s : St) (h : s.eip ≠ img.halt) : Running img s.m := by
  unfold Running returned
  have : (s.eip == img.halt) = false := by simpa using h
  simp [St.m, this]

theorem u64_succ {ic : UInt64} (h : ic.toNat + 1 < 2 ^ 64) : (ic + 1).toNat = ic.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem exN_run {img : Img} : ∀ (k : Nat) (s s' : St), exN img.halt k s = some s' →
    s.ic.toNat + k < 2 ^ 64 → Run img s.m s'.m
  | 0, s, s', h, _ => by
    simp only [exN, Option.some.injEq] at h; subst h; exact Run.refl img _
  | k + 1, s, s', h, hb => by
    simp only [exN] at h
    split at h
    · simp at h
    · rename_i he
      split at h
      · rename_i hTF
        split at h
        · rename_i m hm
          split at h
          · rename_i s1 hs1
            obtain ⟨rfl, hic⟩ := stOf?_spec hs1
            have hlt : s.ic < 0xFFFFFFFFFFFFFFFF := by
              rw [UInt64.lt_iff_toNat_lt]; simp; omega
            have hstep := step_of_okState s hlt hTF s1 hm hic
            refine Run.step (running_of_eip s he) hstep (exN_run k _ s' h ?_)
            show (s.ic + 1).toNat + k < 2 ^ 64
            rw [u64_succ (by omega)]; omega
          · simp at h
        · simp at h
      · simp at h

theorem exN_add (halt : UInt32) : ∀ (a b : Nat) (s : St),
    exN halt (a + b) s = (exN halt a s).bind (exN halt b)
  | 0, b, s => by simp [exN]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [exN]
    split
    · rfl
    · split
      · split
        · split
          · exact exN_add halt a b _
          · rfl
        · rfl
      · rfl

theorem exN_trans {halt : UInt32} {a b : Nat} {s s1 s2 : St} (h1 : exN halt a s = some s1)
    (h2 : exN halt b s1 = some s2) : exN halt (a + b) s = some s2 := by
  rw [exN_add, h1]; exact h2

/-- The fields of a structure literal. -/
def litField (e : Expr) (structName fieldName : Name) : MetaM Expr := do
  let some idx := (getStructureFields (← getEnv) structName).idxOf? fieldName
    | throwError "no field {fieldName}"
  whnfCore (Expr.proj structName idx e)

/-- `stOf? m ic` of a machine literal `m` that is a flat state: the state, read off the literal. -/
cbv_simproc cbv_eval cbvStOf (stOf? _ _) := fun e => do
  let_expr stOf? m ic := e | return .rfl
  let cpu ← litField m ``Machine `cpu
  let g (n : Name) := litField cpu ``Cpu n
  let s := mkAppN (mkConst ``St.mk) #[← litField m ``Machine `mem, ← g `eax, ← g `ecx, ← g `edx, ← g `ebx,
    ← g `esp, ← g `ebp, ← g `esi, ← g `edi, ← g `eip, ← g `eflags, ic]
  let ty ← mkEq m (mkApp (mkConst ``St.m) s)
  unless ← withDefault (isDefEq m (mkApp (mkConst ``St.m) s)) do
    trace[Meta.Tactic.cbv.rewrite] "stOf?: not a flat state {m}"
    return .rfl
  let h ← mkExpectedTypeHint (← mkEqRefl m) ty
  let pf := mkApp3 (mkConst ``stOf?_of) m s h
  let rhs ← mkAppM ``Option.some #[s]
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

attribute [cbv_opaque] stOf?

/-! ## Rotations -/

/-- The flags `rol` leaves (CF, OF), of its result `r`. -/
def rolFl (r : UInt32) : UInt32 :=
  (if r &&& 1 != 0 then Flag.CF else 0) ||| (if (r &&& 0x80000000 != 0) != (r &&& 1 != 0) then Flag.OF else 0)

theorem and_mask4 (x : UInt32) : x &&& 0xFFFFFFFF = x := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]

theorem shiftOp_rol (op sz : UInt8) (a cnt : UInt32) (cf : Bool) (hop : op = 0) (hsz : sz = 4)
    (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    shiftOp op sz a cnt cf = some (Ssl.Spec.Chacha.rotl a cnt, 2049, rolFl (Ssl.Spec.Chacha.rotl a cnt)) := by
  subst hop hsz
  have h1 : cnt &&& 0x1F = cnt := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  have h2 : (cnt == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hc0; rw [h]; rfl
  have h3 : cnt % Sz.bits 4 = cnt := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_mod, show (Sz.bits 4).toNat = 32 by decide, Nat.mod_eq_of_lt hc]
  have h4 : Sz.bits 4 = 32 := by decide
  unfold shiftOp
  simp only [h1, h2, h3, Bool.false_eq_true, ite_false]
  rw [h4]
  simp only [Sz.mask, show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, and_mask4, Sz.msb]
  rfl

/-- The value of a literal of a fixed-width type, through `toNat` and evaluation. -/
def natOf? (e : Expr) (toNatFn : Name) : MetaM (Option Nat) := do
  let kn ← whnfD (mkApp (mkConst toNatFn) e)
  match kn.rawNatLit? with
  | some v => return some v
  | none => return (Sym.getNatValue? kn).run

/-- `rol` by a literal count: `Spec.Chacha.rotl`. -/
cbv_simproc cbv_eval cbvRol (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  let some opv ← natOf? op ``UInt8.toNat | return .rfl
  let some szv ← natOf? sz ``UInt8.toNat | return .rfl
  let some cv ← natOf? cnt ``UInt32.toNat | return .rfl
  unless opv == 0 && szv == 4 && 0 < cv && cv < 32 do return .rfl
  let hop ← mkExpectedTypeHint (← mkEqRefl op) (← mkEq op (toExpr (0 : UInt8)))
  let hsz ← mkExpectedTypeHint (← mkEqRefl sz) (← mkEq sz (toExpr (4 : UInt8)))
  let cN := mkApp (mkConst ``UInt32.toNat) cnt
  let hc ← mkDecideProof (← mkLT cN (mkNatLit 32))
  let hc0 ← mkDecideProof (mkNot (← mkEq cN (mkNatLit 0)))
  let pf := mkAppN (mkConst ``shiftOp_rol) #[op, sz, a, cnt, cf, hop, hsz, hc, hc0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs pf

attribute [cbv_opaque] Ssl.Spec.Chacha.rotl rolFl

/-! ## The carry flag of `cmp` -/

/-- Unsigned `a < b`, as a function `cbv` does not unfold. -/
def ltU (a b : UInt32) : Bool := decide (a.toNat < b.toNat)

theorem ltU_true {a b : UInt32} (h : a.toNat < b.toNat) : ltU a b = true := by simp [ltU, h]
theorem ltU_false {a b : UInt32} (h : ¬ a.toNat < b.toNat) : ltU a b = false := by simp [ltU, h]

theorem efl_and (f k : UInt32) (hk : k &&& 0x8D5 = k) : UInt32.land (efl f) k = UInt32.land f k := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk' := congrArg (fun x : UInt32 => x.toBitVec.getLsbD i) hk
  show ((2 ||| (f &&& 0x8D5)) &&& k : UInt32).toBitVec.getLsbD i = (f &&& k : UInt32).toBitVec.getLsbD i
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or] at hk' ⊢
  have e2 : (UInt32.toBitVec 2).getLsbD i = decide (i = 1) := by
    have : ∀ j, j < 32 → (UInt32.toBitVec 2).getLsbD j = decide (j = 1) := by decide
    exact this i hi
  have e3 : (UInt32.toBitVec 0x8D5).getLsbD 1 = false := by decide
  rw [e2]
  by_cases h1 : i = 1
  · subst h1; rw [e3] at hk'; simp only [Bool.and_false] at hk'; rw [← hk']; simp [e3]
  · simp only [h1, decide_false, Bool.false_or]
    cases hf : f.toBitVec.getLsbD i <;> cases hkk : k.toBitVec.getLsbD i <;> simp_all

theorem efl_and1 (f : UInt32) : UInt32.land (efl f) 1 = UInt32.land f 1 := efl_and f 1 (by decide)
theorem efl_and65 (f : UInt32) : UInt32.land (efl f) 65 = UInt32.land f 65 := efl_and f 65 (by decide)

theorem pack_and1 (f : AFlags) : UInt32.land f.pack 1 = cond f.cf 1 0 := by
  cases f with
  | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem pack_and65 (f : AFlags) : UInt32.land f.pack 65 = UInt32.lor (cond f.cf 1 0) (cond f.zf 64 0) := by
  cases f with
  | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem subCore_cf (a b : UInt32) : (subCore 4 a b 0).2.cf = ltU a b := by
  simp only [subCore, ltU]
  have : (0 : UInt32).toUInt64 = 0 := rfl
  rw [this, UInt64.add_zero]
  simp only [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64]

theorem subCore_zf (a b : UInt32) : (subCore 4 a b 0).2.zf = eqU a b := by
  have := Solutions.Logic.subF_zf a b
  simp only [subF, pack_zf] at this
  cases h1 : (subCore 4 a b 0).2.zf <;> cases h2 : eqU a b <;> simp_all <;> revert this <;> decide

theorem subF_and1 (a b : UInt32) : UInt32.land (subF 4 a b 0).2 1 = cond (ltU a b) 1 0 := by
  simp only [subF, pack_and1, subCore_cf]

theorem subF_and65 (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 65 = UInt32.lor (cond (ltU a b) 1 0) (cond (eqU a b) 64 0) := by
  simp only [subF, pack_and65, subCore_cf, subCore_zf]

/-- `ltU a b` decided by `omega` from the hypotheses in context. -/
cbv_simproc cbv_eval cbvLtU (ltU _ _) := fun e => do
  let_expr ltU a b := e | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let P ← mkLT (toNat a) (toNat b)
  if let some h ← omegaSound? P then
    let pf := mkApp3 (mkConst ``ltU_true) a b h
    return .step (mkConst ``Bool.true) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.true)))
  if let some h ← omegaSound? (mkNot P) then
    let pf := mkApp3 (mkConst ``ltU_false) a b h
    return .step (mkConst ``Bool.false) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.false)))
  return .rfl

/-- The carry flag (`&&& 1`) and carry-or-zero (`&&& 65`) of `efl` and of `cmp`. -/
cbv_simproc cbv_eval cbvCF (UInt32.land _ _) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  let some kv := Solutions.Cbx.Discharge.sizeLit? k | return .rfl
  unless kv == 1 || kv == 65 do return .rfl
  if x.isAppOfArity ``efl 1 then
    let f := x.appArg!
    let pf := if kv == 1 then mkApp (mkConst ``efl_and1) f else mkApp (mkConst ``efl_and65) f
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  let some p := sndOf? x | return .rfl
  unless p.isAppOfArity ``subF 4 do return .rfl
  let some szv := Solutions.Cbx.Discharge.sizeLit? (p.getArg! 0) | return .rfl
  let some binv := (Sym.getNatValue? (p.getArg! 3)).run | return .rfl
  unless szv == 4 && binv == 0 do return .rfl
  let a := p.getArg! 1
  let b := p.getArg! 2
  let pf := if kv == 1 then mkApp2 (mkConst ``subF_and1) a b else mkApp2 (mkConst ``subF_and65) a b
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

attribute [cbv_opaque] ltU

/-! ## Comparisons of addresses

A one-byte load from a `CodeMem` asks whether the address is in the code (`rdBytes_codeMem`). For a
symbolic address the comparisons `Nat.decLe`/`Nat.decLt` are decided by `omega` from the context. -/

theorem decLe_isTrue (a b : Nat) (h : a ≤ b) : Nat.decLe a b = isTrue h := Subsingleton.elim _ _
theorem decLe_isFalse (a b : Nat) (h : ¬ a ≤ b) : Nat.decLe a b = isFalse h := Subsingleton.elim _ _
theorem decLt_isTrue (a b : Nat) (h : a < b) : Nat.decLt a b = isTrue h := Subsingleton.elim _ _
theorem decLt_isFalse (a b : Nat) (h : ¬ a < b) : Nat.decLt a b = isFalse h := Subsingleton.elim _ _

/-- Constants whose values are numerals (like `Image.base`) replaced by the numerals. -/
def unfoldNumConsts (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .const .. := x then
      if let some v ← unfoldDefinition? x then
        if (Sym.getNatValue? v).run.isSome || v.isRawNatLit then return .done v
    return .continue)

def decideNat (e : Expr) (lt : Bool) : Sym.Simp.SimpM Sym.Simp.Result := do
  let a := e.appFn!.appArg!
  let b := e.appArg!
  if (Sym.getNatValue? a).run.isSome && (Sym.getNatValue? b).run.isSome then return .rfl
  let P ← if lt then mkLT a b else mkLE a b
  let P ← unfoldNumConsts P
  let (tN, fN) := if lt then (``decLt_isTrue, ``decLt_isFalse) else (``decLe_isTrue, ``decLe_isFalse)
  if let some h ← omegaSound? P then
    let pf := mkApp3 (mkConst tN) a b h
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs pf
  if let some h ← omegaSound? (mkNot P) then
    let pf := mkApp3 (mkConst fN) a b h
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs pf
  return .rfl

cbv_simproc cbv_eval cbvDecLe (Nat.decLe _ _) := fun e => decideNat e false
cbv_simproc cbv_eval cbvDecLt (Nat.decLt _ _) := fun e => decideNat e true

theorem decAnd_false_right {p q : Prop} (dp : Decidable p) (dq : Decidable q) (h : ¬ q) :
    @instDecidableAnd p q dp dq = isFalse (fun hpq => h hpq.2) := Subsingleton.elim _ _

/-- `p ∧ (lo ≤ a ∧ a < hi)` (an address in the code range) decided false by `omega` as a whole. -/
cbv_simproc cbv_eval cbvDecAnd (@instDecidableAnd _ _ _ _) := fun e => do
  let_expr instDecidableAnd p q dp dq := e | return .rfl
  unless q.isAppOfArity ``And 2 do return .rfl
  unless (q.getArg! 0).isAppOfArity ``LE.le 4 && (q.getArg! 1).isAppOfArity ``LT.lt 4 do return .rfl
  let some h ← omegaSound? (mkNot (← unfoldNumConsts q)) | return .rfl
  let h ← mkExpectedTypeHint h (mkNot q)
  let pf := mkAppN (mkConst ``decAnd_false_right) #[p, q, dp, dq, h]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs pf

end Solutions.OpensslChacha20
