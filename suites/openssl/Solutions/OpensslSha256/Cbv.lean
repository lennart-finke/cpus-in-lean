import Solutions.Exec.Mem
import Solutions.Exec.Cbv
import Solutions.Exec.Alu
import Solutions.Exec.Dispatch
import Solutions.Logic.Decode
import Solutions.Logic.Step
import Lean
/-!
# `cbv` set-up for instructions at a symbolic address

The execution layers of `Solutions/Exec` and `Solutions/Logic` run `cbv` on a machine at a
concrete instruction address. Here the address `p` of the instruction is a variable: the code is a
*window* `CodeMem p n code` (the `n` bytes `code i` at `p + i`), so that one lemma covers every
occurrence of an instruction encoding. A displacement byte may be a variable too.

* `fetch8` of a flat machine below `ramTop` is the byte of memory (`fetch8_flat`, simproc
  `cbvFetch8`); a byte of the window at `p + k` is `code k` (`rdBytes_win`, simproc `cbvRdWin`),
  every other read of a `CodeMem` stays the opaque `rdRaw`;
* data accesses (`rdMem`, `wrMem`) become `rdBytes`/`wrBytes` (`Solutions.Exec.Mem`), with their
  side conditions proved by `omega` from the hypotheses in context;
* EFLAGS is `efl f` (only the arithmetic flags vary), the integer operations are opaque, `rol` and
  `shr` by a literal count are the opaque `rolV`/`shrV` with opaque flags, `sext 1` of a value
  below 128 is the value.

This copies the parts of `Solutions/Logic/Cbx.lean` it needs (the EFLAGS rules, the omega
discharger, the data-access simprocs, the address normal form) into this namespace, so that it is
independent of changes there.
-/
namespace Solutions.OpensslSha256
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
theorem max_lt_false (t : UInt32) : ((4294967295 : UInt32) < t) = False := by
  apply propext; constructor
  · intro h; rw [UInt32.lt_iff_toNat_lt] at h; have := t.toNat_lt; simp at h; omega
  · intro h; exact h.elim
theorem zero_uadd (x : UInt32) : UInt32.add 0 x = x := UInt32.zero_add x
theorem shr64 (a b : UInt64) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
theorem u64_shr32 (x : UInt32) : UInt64.shiftRight (UInt32.toUInt64 x) 32 = 0 := by
  apply UInt64.toBitVec_inj.1
  have := x.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.shiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (UInt64.mod 32 64).toNat = 32 from rfl]
  first | omega | exact Nat.div_eq_of_lt (by omega)
theorem u64_u32 (x : UInt32) : UInt64.toUInt32 (UInt32.toUInt64 x) = x := by
  apply UInt32.toNat_inj.1
  simp
theorem subF_fst' (a b : UInt32) : (subF 4 a b 0).1 = UInt32.sub a b := subF_fst a b
theorem shl_zero (x : UInt32) : UInt32.shiftLeft x 0 = x := UInt32.shiftLeft_zero
theorem logicF_fst (v : UInt32) : (logicF 4 v).1 = v := rfl
theorem addF_fst' (a b : UInt32) : (addF 4 a b 0).1 = UInt32.add a b := addF_fst a b
end rules

/-! ## Rotations and shifts by a literal count -/

/-- `rol a c` (for `0 < c < 32`). -/
def rolV (a c : UInt32) : UInt32 := (a <<< c) ||| (a >>> (32 - c))
/-- The flags `rol` sets (CF, OF). -/
def rolF (r : UInt32) : UInt32 :=
  (if r &&& 1 != 0 then Flag.CF else 0) ||| (if (r &&& 0x80000000 != 0) != (r &&& 1 != 0) then Flag.OF else 0)
/-- `shr a c`. -/
def shrV (a c : UInt32) : UInt32 := a >>> c
/-- The flags `shr` sets. -/
def shrF (a c : UInt32) : UInt32 :=
  (shiftOp 5 4 a c false).elim 0 (fun x => x.2.2)

theorem and_mask4 (x : UInt32) : x &&& 0xFFFFFFFF = x := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]

theorem shiftOp_rol (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    shiftOp 0 4 a cnt cf = some (rolV a cnt, 2049, rolF (rolV a cnt)) := by
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

theorem shr_eq (a cnt : UInt32) (hc : cnt.toNat < 32) :
    (a.toUInt64 >>> cnt.toUInt64).toUInt32 = a >>> cnt := by
  apply UInt32.toNat_inj.1
  have := a.toNat_lt
  rw [shr64, shr32]
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]
  rw [Nat.mod_eq_of_lt (a := cnt.toNat) (by omega), Nat.mod_eq_of_lt (a := cnt.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega))

theorem shiftOp_shr_some (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
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
  exact shr_eq a cnt hc

theorem shiftOp_shr (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    shiftOp 5 4 a cnt cf = some (shrV a cnt, Flag.arith, shrF a cnt) := by
  obtain ⟨fl, h⟩ := shiftOp_shr_some a cnt cf hc hc0
  obtain ⟨fl', h'⟩ := shiftOp_shr_some a cnt false hc hc0
  have hcf : shiftOp 5 4 a cnt cf = shiftOp 5 4 a cnt false := by
    unfold shiftOp; rfl
  rw [hcf, h']
  unfold shrF shrV
  rw [h']
  rfl

theorem sext1_lt (x : UInt32) (h : x.toNat < 128) : sext 1 x = x := by
  have key : ∀ k : Fin 128, sext 1 (k.val.toUInt32) = k.val.toUInt32 := by decide
  have := key ⟨x.toNat, h⟩
  simpa using this

/-! ## Instruction fetch and the code window -/

theorem fetch8_flat {m : Machine} (h : FlatM m) (hcpl : m.cpu.cpl = 0) (hb : m.cpu.cs.base = 0)
    (hl : m.cpu.cs.limit = 0xFFFFFFFF) {a : UInt32} (ha : a.toNat < ramTop) :
    fetch8 a m = .ok (rdBytes m.mem a 1) m := by
  have h1 : ¬ (a > m.cpu.cs.limit) := by
    rw [hl]; intro h'; rw [GT.gt, UInt32.lt_iff_toNat_lt] at h'; have := a.toNat_lt; simp at h'; omega
  unfold fetch8
  simp only [h1, if_false, hb, UInt32.zero_add, bind, EStateM.bind, isUser]
  rw [translate_flat h]
  exact physRd_flat h ha 1

/-- The bytes `l` (`0` past its end): the code of a window. -/
def codeOf (l : List UInt8) (i : Nat) : UInt8 := l.getD i 0

theorem rdBytes_win {p : UInt32} {n : Nat} {code : Nat → UInt8} (G : CodeMem p n code) (k : Nat)
    (hk : k < n) (hp : p.toNat + n ≤ 2 ^ 32) :
    rdBytes G.get (UInt32.add p k.toUInt32) 1 = (code k).toUInt32 := by
  have hkk : (UInt32.add p k.toUInt32).toNat = p.toNat + k := by
    show (p + k.toUInt32).toNat = _
    rw [UInt32.toNat_add]; simp; omega
  rw [rdBytes_codeMem]
  rw [if_pos ⟨rfl, by omega, by omega⟩]
  rw [hkk, Nat.add_sub_cancel_left]

theorem rdBytes_win0 {p : UInt32} {n : Nat} {code : Nat → UInt8} (G : CodeMem p n code)
    (hk : 0 < n) (hp : p.toNat + n ≤ 2 ^ 32) :
    rdBytes G.get p 1 = (code 0).toUInt32 := by
  have := rdBytes_win G 0 hk hp
  rw [show UInt32.add p (0 : Nat).toUInt32 = p from UInt32.add_zero p] at this
  exact this

theorem rdBytes_raw (mem : ByteArray) (a n : UInt32) : rdBytes mem a n = rdRaw mem a n := rfl

/-! ## The `omega` discharger -/

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

macro "sha_omega" : tactic =>
  `(tactic| ((try simp only [size_wrBytes, toNat_uadd, toNat_usub, ramTop, UInt32.toNat_add,
      UInt32.toNat_sub, UInt32.reduceToNat, UInt8.toNat_toUInt32, Nat.toUInt32_eq, UInt32.toNat_ofNat',
      CodeMem.get] at *) <;> omega))

attribute [scoped cbv_opaque] efl mixF UInt32.add UInt32.sub UInt32.mul UInt32.land UInt32.lor UInt32.xor
  UInt32.shiftLeft UInt32.shiftRight UInt32.complement UInt64.add UInt64.sub UInt64.land UInt64.lor
  UInt64.shiftRight Array.replicate X86.cmosInit X86.rdMem X86.wrMem X86.addF X86.subF X86.logicF
  X86.shiftOp X86.imulCore X86.fetch8 X86.sext rolV rolF shrV shrF
  X86.rdBytes X86.wrBytes X86.opInfoTable X86.execTable rdRaw CodeMem.get UInt8.toUInt32

attribute [scoped cbv_eval] efl_TF efl_IF efl_DF efl_NT efl_RF efl_VM efl_AC efl_setArith efl_setNoCF
  efl_setCFOF max_lt_false zero_uadd u64_shr32 u64_u32 opInfoTable_get execTable_get logicF_fst addF_fst' shl_zero subF_fst'

namespace Discharge
open Lean Meta Elab

def field (e : Expr) (structName fieldName : Name) : MetaM Expr := do
  let some idx := (getStructureFields (← getEnv) structName).idxOf? fieldName
    | throwError "no field {fieldName}"
  whnfCore (Expr.proj structName idx e)

/-- Prove `P` by `sha_omega` in the current context, without error recovery; only a complete
proof using the standard postulates counts. -/
def omega? (P : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar P
  let msgs := (← getThe Core.State).messages
  let ok ← try
      let gs ← Term.TermElabM.run' <| Term.withoutErrToSorry <|
        Tactic.run g.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| sha_omega))))
      pure gs.isEmpty
    catch _ => pure false
  modifyThe Core.State fun st => { st with messages := msgs }
  if !ok then return none
  let pf ← instantiateMVars g
  -- the kernel checks the proof; the postulates the final theorems use are listed by `#print`
  if pf.hasExprMVar then return none
  return some pf

def reflOf (stx : Term) : MetaM (Option Expr) := do
  try
    let ty ← Term.TermElabM.run' do
      let e ← Term.elabTerm stx (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let some (_, a, _) := ty.eq? | return none
    return some (← mkExpectedTypeHint (← mkEqRefl a) ty)
  catch _ => return none

def elabPf (stx : Term) : MetaM (Option Expr) := do
  try
    let e ← Term.TermElabM.run' do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasExprMVar then return none
    return some e
  catch _ => return none

def sizeLit? (n : Expr) : Option Nat :=
  match (Sym.getNatValue? n).run with
  | some v => some v
  | none => if n.isAppOfArity ``UInt8.toUInt32 1 then (Sym.getNatValue? n.appArg!).run else none

/-- `FlatM m` and `m.cpu.cpl = 0` for a machine literal `m` with EFLAGS `efl f`. -/
def flatProofs (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let cpu ← field m ``Machine `cpu
  let ef ← field cpu ``Cpu `eflags
  unless ef.isAppOfArity ``efl 1 do return none
  let f := ef.appArg!
  let mS ← Term.TermElabM.run' (Term.exprToSyntax m)
  let fS ← Term.TermElabM.run' (Term.exprToSyntax f)
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
  return some (hflat, hcpl)

def accessProofs (m s off n : Expr) : MetaM (Option (Array Expr)) := do
  let some nv := sizeLit? n | return none
  let n := toExpr nv.toUInt32
  unless nv == 1 || nv == 2 || nv == 4 do return none
  let some (hflat, hcpl) ← flatProofs m | return none
  let mS ← Term.TermElabM.run' (Term.exprToSyntax m)
  let sS ← Term.TermElabM.run' (Term.exprToSyntax s)
  let nS ← Term.TermElabM.run' (Term.exprToSyntax n)
  let some s1 ← reflOf (← `((($mS).cpu.getSeg $sS).base = 0)) | return none
  let some s2 ← reflOf (← `((($mS).cpu.getSeg $sS).limit = 0xFFFFFFFF)) | return none
  let some s3 ← reflOf (← `((($mS).cpu.getSeg $sS).attr = 0xC093)) | return none
  let hs := mkAppN (mkConst ``flatSeg_intro) #[mkApp2 (mkConst ``Cpu.getSeg) (mkApp (mkConst ``Machine.cpu) m) s, s1, s2, s3]
  let some hn ← elabPf (← `((by decide : $nS = 1 ∨ $nS = 2 ∨ $nS = 4))) | return none
  let mem ← field m ``Machine `mem
  let size := mkApp (mkConst ``ByteArray.size) mem
  let lhs ← mkAdd (mkApp (mkConst ``UInt32.toNat) off) (mkApp (mkConst ``UInt32.toNat) n)
  let some hr ← omega? (← mkLE lhs size) | do
    trace[Meta.Tactic.cbv.rewrite] "sha: range {lhs} ≤ {size}"; return none
  let some hm ← omega? (← mkLE size (mkConst ``ramTop)) | return none
  return some #[hflat, hcpl, hs, hn, hr, hm]

/-- The proofs `fetch8_flat` needs for the machine literal `m` and the address `a`. -/
def fetchProofs (m a : Expr) : MetaM (Option (Array Expr)) := do
  let some (hflat, hcpl) ← flatProofs m | return none
  let mS ← Term.TermElabM.run' (Term.exprToSyntax m)
  let some hb ← reflOf (← `(($mS).cpu.cs.base = 0)) | return none
  let some hl ← reflOf (← `(($mS).cpu.cs.limit = 0xFFFFFFFF)) | return none
  let some ha ← omega? (← mkLT (mkApp (mkConst ``UInt32.toNat) a) (mkConst ``ramTop)) | do
    trace[Meta.Tactic.cbv.rewrite] "sha: fetch {a}"; return none
  return some #[hflat, hcpl, hb, hl, ha]

end Discharge

open Discharge in
/-- `rdMem` of a flat machine inside memory: `rdBytes`. -/
scoped cbv_simproc cbv_eval cbvRdMem (rdMem _ _ _ _ _ _) := fun e => do
  let_expr rdMem s off n w al m := e | return .rfl
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
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

open Discharge in
/-- `fetch8` of a flat machine below `ramTop`: the byte of memory. -/
scoped cbv_simproc cbv_eval cbvFetch8 (fetch8 _ _) := fun e => do
  let_expr fetch8 a m := e | return .rfl
  let some hs ← fetchProofs m a | return .rfl
  let pf ← mkAppM ``fetch8_flat hs
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- The value of a literal of a fixed-width type, through `toNat` and evaluation. -/
def natOf? (e : Expr) (toNatFn : Name) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  let kn ← whnfD (mkApp (mkConst toNatFn) e)
  match kn.rawNatLit? with
  | some v => return some v
  | none => return (Sym.getNatValue? kn).run

open Discharge in
/-- A read of a `CodeMem`: a byte of the window at `p + k` is `code k`; anything else is `rdRaw`. -/
scoped cbv_simproc cbv_eval cbvRdWin (rdBytes _ _ _) := fun e => do
  let_expr rdBytes mem a n := e | return .rfl
  let raw : Sym.Simp.SimpM Sym.Simp.Result := do
    let r ← Sym.share (mkApp3 (mkConst ``rdRaw) mem a n)
    return .step r (← mkExpectedTypeHint (mkApp3 (mkConst ``rdBytes_raw) mem a n) (← mkEq e r))
  let some nv := sizeLit? n | raw
  unless nv == 1 && mem.isAppOfArity ``CodeMem.get 4 do return (← raw)
  let p := mem.getArg! 0
  let sz := mem.getArg! 1
  let code := mem.getArg! 2
  let G := mem.getArg! 3
  let some szv := (Sym.getNatValue? sz).run | raw
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  -- `a` is `p` or `p + k`
  let k? : Option Nat ← (do
    if a == p then return some 0
    if a.isAppOfArity ``UInt32.add 2 && a.getArg! 0 == p then
      return (Sym.getNatValue? (a.getArg! 1)).run
    -- a window at a literal address
    if a.hasFVar || p.hasFVar || a.hasMVar || p.hasMVar then return none
    let some av ← natOf? a ``UInt32.toNat | return none
    let some pv ← natOf? p ``UInt32.toNat | return none
    if pv ≤ av then return some (av - pv) else return none)
  let some k := k? | raw
  if k ≥ szv then return (← raw)
  let some hp ← omega? (← mkLE (← mkAdd (toNat p) sz) (mkNatLit (2 ^ 32))) | raw
  let hk ← mkDecideProof (← mkLT (mkNatLit k) sz)
  if k == 0 then
    let pf := mkAppN (mkConst ``rdBytes_win0) #[p, sz, code, G, hk, hp]
    let some (_, _, rhs) := (← inferType pf).eq? | return (← raw)
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  let pf := mkAppN (mkConst ``rdBytes_win) #[p, sz, code, G, mkNatLit k, hk, hp]
  let some (_, _, rhs) := (← inferType pf).eq? | raw
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

open Discharge in
/-- `sext 1 x` of a value below 128 (as `omega` shows from the context). -/
scoped cbv_simproc cbv_eval cbvSext (sext _ _) := fun e => do
  let_expr sext s x := e | return .rfl
  let some sv := (Sym.getNatValue? s).run | return .rfl
  unless sv == 1 do return .rfl
  let some h ← omega? (← mkLT (mkApp (mkConst ``UInt32.toNat) x) (mkNatLit 128)) | return .rfl
  let pf := mkApp2 (mkConst ``sext1_lt) x h
  return .step x (← mkExpectedTypeHint pf (← mkEq e x))

/-- `rol`/`shr` of a 32-bit value by a literal count in `[1, 32)`. -/
scoped cbv_simproc cbv_eval cbvShift (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  let some opv ← natOf? op ``UInt8.toNat | return .rfl
  let some szv ← natOf? sz ``UInt8.toNat | return .rfl
  let some cv ← natOf? cnt ``UInt32.toNat | return .rfl
  unless szv == 4 && 0 < cv && cv < 32 && (opv == 0 || opv == 5) do return .rfl
  let cnt' := toExpr cv.toUInt32
  let hc ← mkDecideProof (← mkLT (mkApp (mkConst ``UInt32.toNat) cnt') (mkNatLit 32))
  let hc0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) cnt') (mkNatLit 0)))
  let pf := if opv == 0 then mkAppN (mkConst ``shiftOp_rol) #[a, cnt', cf, hc, hc0]
    else mkAppN (mkConst ``shiftOp_shr) #[a, cnt', cf, hc, hc0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))


/-! ## Ground evaluation of the opaque integer operations on closed literals -/

def closedU32? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  match (Sym.getNatValue? e).run with
  | some v => return some v
  | none =>
    unless (← inferType e).isConstOf ``UInt32 do return none
    natOf? e ``UInt32.toNat

def ground2 (f : Nat → Nat → Nat) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let a := e.appFn!.appArg!
  let b := e.appArg!
  let some av ← closedU32? a | return .rfl
  let some bv ← closedU32? b | return .rfl
  let r := toExpr ((f av bv) % 2 ^ 32).toUInt32
  return .step r (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r))

scoped cbv_simproc cbv_eval cbvGLor (UInt32.lor _ _) := ground2 (· ||| ·)
scoped cbv_simproc cbv_eval cbvGLand (UInt32.land _ _) := ground2 (· &&& ·)
scoped cbv_simproc cbv_eval cbvGXor (UInt32.xor _ _) := ground2 (· ^^^ ·)
scoped cbv_simproc cbv_eval cbvGShl (UInt32.shiftLeft _ _) := ground2 (fun a b => a <<< (b % 32))
scoped cbv_simproc cbv_eval cbvGShr (UInt32.shiftRight _ _) := ground2 (fun a b => a >>> (b % 32))
scoped cbv_simproc cbv_eval cbvGSub (UInt32.sub _ _) := ground2 (fun a b => a + (2 ^ 32 - b))
scoped cbv_simproc cbv_eval cbvGMul (UInt32.mul _ _) := ground2 (· * ·)
scoped cbv_simproc cbv_eval cbvGU8 (UInt8.toUInt32 _) := fun e => do
  let x := e.appArg!
  if x.hasFVar || x.hasMVar then return .rfl
  let some v ← natOf? x ``UInt8.toNat | return .rfl
  let r := toExpr (v % 256).toUInt32
  return .step r (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r))

/-! ## Address normal form: `x + literal` -/

theorem uadd_zero (x : UInt32) : UInt32.add x 0 = x := UInt32.add_zero x
theorem uadd_assoc (x a b : UInt32) : UInt32.add (UInt32.add x a) b = UInt32.add x (a + b) :=
  UInt32.add_assoc x a b

scoped cbv_simproc cbv_eval cbvUAdd (UInt32.add _ _) := fun e => do
  let_expr UInt32.add x b := e | return .rfl
  if let some av ← closedU32? x then
    if let some bv ← closedU32? b then
      let r := toExpr ((av + bv) % 2 ^ 32).toUInt32
      return .step r (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r))
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

end Solutions.OpensslSha256
