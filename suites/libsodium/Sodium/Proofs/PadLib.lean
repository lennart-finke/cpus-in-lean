import Solutions.Logic.Flags
import Solutions.Logic.MemRules
/-!
# Branches on the carry flag, for `cbv`

`Solutions.Logic.Flags` evaluates branches on the zero flag. This file adds the carry flag
(`jb`/`jae`), with `open Sodium.Proofs.PadLib`: the carry flag of `efl f` is that of `f`
(`efl_cf`), the carry of `subF 4 a b 0` is `a < b` as the opaque comparison `ltU` (decided by
`omega` from the hypotheses in context, `cbvLtU`), and a logical operation clears it.
-/
namespace Sodium.Proofs.PadLib
open X86 Solutions.Exec Solutions.Cbx Solutions.Logic Lean Meta

/-- Unsigned `<` of words, as a function `cbv` does not unfold. -/
def ltU (a b : UInt32) : Bool := decide (a.toNat < b.toNat)

theorem ltU_true {a b : UInt32} (h : a.toNat < b.toNat) : ltU a b = true := by
  simp [ltU, h]

theorem ltU_false {a b : UInt32} (h : ¬ a.toNat < b.toNat) : ltU a b = false := by
  simp [ltU, h]

theorem bit_of_or (f : UInt32) (k : Nat) (hk : k < 32) :
    ((2 ||| (f &&& 0x8D5)) &&& 1 : UInt32).toBitVec.getLsbD k = (f &&& 1 : UInt32).toBitVec.getLsbD k := by
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  have e1 : ∀ j, j < 32 → (UInt32.toBitVec 2).getLsbD j = decide (j = 1) := by decide
  have e2 : ∀ j, j < 32 → (UInt32.toBitVec 1).getLsbD j = decide (j = 0) := by decide
  have e3 : (UInt32.toBitVec 0x8D5).getLsbD 0 = true := by decide
  rw [e1 k hk, e2 k hk]
  by_cases h0 : k = 0
  · subst h0; simp [e3]
  · simp [h0]

theorem efl_cf (f : UInt32) : UInt32.land (efl f) 1 = UInt32.land f 1 := by
  unfold efl
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bit_of_or f i hi

theorem pack_cf (f : AFlags) : UInt32.land f.pack 1 = cond f.cf 1 0 := by
  cases f with
  | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem subF_cf (a b : UInt32) : UInt32.land (subF 4 a b 0).2 1 = cond (ltU a b) 1 0 := by
  simp only [subF, subCore, pack_cf, ltU]
  congr 1
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64]
  simp only [UInt32.reduceToNat, Nat.add_zero, Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]

theorem logicF_cf (r : UInt32) : UInt32.land (logicF 4 r).2 1 = 0 := by
  simp only [logicF, logicCore, pack_cf]
  rfl

/-- `ltU a b` decided by `omega` from the hypotheses in context. -/
scoped cbv_simproc cbv_eval cbvLtU (ltU _ _) := fun e => do
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

open Solutions.Cbx.Discharge in
/-- The carry flag of `logicF 4 r` or `subF 4 a b 0`, with the second component written either way. -/
scoped cbv_simproc cbv_eval cbvCF (UInt32.land _ 1) := fun e => do
  let_expr UInt32.land x k := e | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless kv == 1 do return .rfl
  let some p := sndOf? x | return .rfl
  if p.isAppOfArity ``logicF 2 then
    let r := p.appArg!
    let rhs := toExpr (0 : UInt32)
    let pf := mkApp (mkConst ``logicF_cf) r
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  if p.isAppOfArity ``subF 4 && sizeLit? (p.getArg! 0) == some 4 && sizeLit? (p.getArg! 3) == some 0 then
    let a := p.getArg! 1
    let b := p.getArg! 2
    let rhs ← mkAppM ``cond #[mkApp2 (mkConst ``ltU) a b, toExpr (1 : UInt32), toExpr (0 : UInt32)]
    let pf := mkApp2 (mkConst ``subF_cf) a b
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  return .rfl

/-- A word store over a word store at the same address. -/
theorem wrBytes4_wrBytes4 {mem : ByteArray} {t a b : UInt32} (h : t.toNat + 4 ≤ mem.size) :
    wrBytes (wrBytes mem t 4 a) t 4 b = wrBytes mem t 4 b := by
  have s1 := size_wrBytes4 (v := a) h
  apply bytes_ext
  · rw [size_wrBytes4 (by rw [s1]; exact h), s1, size_wrBytes4 h]
  · intro j _
    rw [get!_wrBytes4 (by rw [s1]; exact h), get!_wrBytes4 h, get!_wrBytes4 h]
    by_cases h0 : j = t.toNat
    · simp [h0]
    by_cases h1 : j = t.toNat + 1
    · simp [h1]
    by_cases h2 : j = t.toNat + 2
    · simp [h2]
    by_cases h3 : j = t.toNat + 3
    · simp [h3]
    simp [h0, h1, h2, h3]

theorem wr4_wr4 {base : UInt32} {size : Nat} {code : Nat → UInt8} (H : CodeMem base size code)
    (t a b : UInt32) (ok : StoreOk base size H.mem t) (ok' : StoreOk base size (CodeMem.wr4 H t a ok).mem t) :
    (CodeMem.wr4 (CodeMem.wr4 H t a ok) t b ok').get = (CodeMem.wr4 H t b ok).get :=
  wrBytes4_wrBytes4 ok.1

/-! ## Shifts by a literal count (as in `Solutions/OpensslSha256/Cbv.lean`) -/

/-- The flags `shr` sets. -/
def shrF (a c : UInt32) : UInt32 := (shiftOp 5 4 a c false).elim 0 (fun x => x.2.2)

theorem shr64 (a b : UInt64) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl

theorem and_mask4 (x : UInt32) : x &&& 0xFFFFFFFF = x := by
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]

theorem shiftOp_shr_some (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    ∃ fl, shiftOp 5 4 a cnt cf = some (a >>> cnt, Flag.arith, fl) := by
  have h1 : cnt &&& 0x1F = cnt := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  have h2 : (cnt == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hc0; rw [h]; rfl
  unfold shiftOp
  simp only [h1, h2, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq, true_and]
  refine ⟨_, ?_, rfl⟩
  simp only [Sz.mask, show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, and_mask4]
  apply UInt32.toNat_inj.1
  have := a.toNat_lt
  simp only [shr32, shr64, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]
  rw [Nat.mod_eq_of_lt (b := 2 ^ 32), Nat.mod_eq_of_lt (a := cnt.toNat) (by omega),
    Nat.mod_eq_of_lt (a := cnt.toNat) (by omega)]
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega)

theorem shiftOp_shr (a cnt : UInt32) (cf : Bool) (hc : cnt.toNat < 32) (hc0 : cnt.toNat ≠ 0) :
    shiftOp 5 4 a cnt cf = some (UInt32.shiftRight a cnt, Flag.arith, shrF a cnt) := by
  obtain ⟨fl', h'⟩ := shiftOp_shr_some a cnt false hc hc0
  have hcf : shiftOp 5 4 a cnt cf = shiftOp 5 4 a cnt false := by
    unfold shiftOp; rfl
  rw [hcf, h']
  unfold shrF
  rw [h']
  rfl

/-- A small literal: a numeral, a conversion of one, or a `UInt8` built from `BitVec.ofNat`. -/
def lit8? (e : Expr) : Option Nat :=
  match Solutions.Cbx.Discharge.sizeLit? e with
  | some v => some v
  | none =>
    if e.isAppOfArity ``UInt8.ofBitVec 1 then
      let b := e.appArg!
      if b.isAppOfArity ``BitVec.ofNat 2 then (Sym.getNatValue? b.appArg!).run else none
    else none

/-- `shr` by a count in `1 … 31` that `omega` bounds. -/
scoped cbv_simproc cbv_eval cbvShr (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  unless lit8? op == some 5 && lit8? sz == some 4 do
    return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let some hc ← omegaSound? (← mkLT (toNat cnt) (mkNatLit 32)) | return .rfl
  let some hc0 ← omegaSound? (mkNot (← mkEq (toNat cnt) (mkNatLit 0))) | return .rfl
  let pf := mkAppN (mkConst ``shiftOp_shr) #[a, cnt, cf, hc, hc0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs pf

/-! ## Memories that agree outside a range -/

/-- `M` has the size of `G` and the same bytes outside `[lo, hi)`. -/
def Agree (M G : ByteArray) (lo hi : Nat) : Prop :=
  M.size = G.size ∧ ∀ a, a < G.size → (a < lo ∨ hi ≤ a) → M.get! a = G.get! a

theorem Agree.refl (G : ByteArray) (lo hi : Nat) : Agree G G lo hi := ⟨rfl, fun _ _ _ => rfl⟩

theorem Agree.wr4 {M G : ByteArray} {lo hi : Nat} (h : Agree M G lo hi) (t v : UInt32)
    (h1 : lo ≤ t.toNat) (h2 : t.toNat + 4 ≤ hi) (h3 : t.toNat + 4 ≤ M.size) :
    Agree (wrBytes M t 4 v) G lo hi := by
  refine ⟨by rw [size_wrBytes4 h3]; exact h.1, fun a ha hout => ?_⟩
  rw [get!_wrBytes4 h3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact h.2 a ha hout

theorem Agree.wr1 {M G : ByteArray} {lo hi : Nat} (h : Agree M G lo hi) (t v : UInt32)
    (h1 : lo ≤ t.toNat) (h2 : t.toNat + 1 ≤ hi) (h3 : t.toNat < M.size) :
    Agree (wrBytes M t 1 v) G lo hi := by
  refine ⟨by rw [size_wrBytes1 h3]; exact h.1, fun a ha hout => ?_⟩
  rw [get!_wrBytes1 h3, if_neg (by omega)]
  exact h.2 a ha hout

theorem Agree.mono {M G : ByteArray} {lo hi lo' hi' : Nat} (h : Agree M G lo hi) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : Agree M G lo' hi' :=
  ⟨h.1, fun a ha hout => h.2 a ha (by omega)⟩

theorem Agree.trans {M N G : ByteArray} {lo hi : Nat} (h : Agree M N lo hi) (h' : Agree N G lo hi) :
    Agree M G lo hi :=
  ⟨h.1.trans h'.1, fun a ha hout => by rw [h.2 a (by rw [h'.1]; exact ha) hout, h'.2 a ha hout]⟩

theorem Agree.rd1 {M G : ByteArray} {lo hi : Nat} (h : Agree M G lo hi) (a : UInt32)
    (ha : a.toNat < G.size) (hout : a.toNat < lo ∨ hi ≤ a.toNat) : rdBytes M a 1 = rdBytes G a 1 := by
  rw [rdBytes1_eq (by rw [h.1]; exact ha), rdBytes1_eq ha, memByte_def (by rw [h.1]; exact ha),
    memByte_def ha, h.2 _ ha hout]

theorem Agree.rd4 {M G : ByteArray} {lo hi : Nat} (h : Agree M G lo hi) (a : UInt32)
    (ha : a.toNat + 4 ≤ G.size) (hout : a.toNat + 4 ≤ lo ∨ hi ≤ a.toNat) : rdBytes M a 4 = rdBytes G a 4 :=
  rdBytes4_congr (by rw [h.1]; exact ha) ha (fun k hk => h.2 _ (by omega) (by omega))

theorem Agree.byte {M G : ByteArray} {lo hi : Nat} (h : Agree M G lo hi) (a : UInt32)
    (ha : a.toNat < G.size) (hout : a.toNat < lo ∨ hi ≤ a.toNat) : Ssl.memByte M a = Ssl.memByte G a := by
  rw [memByte_def (by rw [h.1]; exact ha), memByte_def ha, h.2 _ ha hout]

/-! ## Two-byte opcodes, evaluated directly (`cbv` exceeds the recursion depth on `execOp0F`'s match) -/

theorem execOp0F_1B6 : execOp0F 0x1B6 = fun (i : Inst) => (do wrReg i.opsz i.reg (← rdE i 1) : M Unit) := rfl

theorem execOp0F_x180 : execOp0F 0x180 = execRange 0x180 := by
  unfold execOp0F; rfl
theorem execOp0F_x181 : execOp0F 0x181 = execRange 0x181 := by
  unfold execOp0F; rfl
theorem execOp0F_x182 : execOp0F 0x182 = execRange 0x182 := by
  unfold execOp0F; rfl
theorem execOp0F_x183 : execOp0F 0x183 = execRange 0x183 := by
  unfold execOp0F; rfl
theorem execOp0F_x184 : execOp0F 0x184 = execRange 0x184 := by
  unfold execOp0F; rfl
theorem execOp0F_x185 : execOp0F 0x185 = execRange 0x185 := by
  unfold execOp0F; rfl
theorem execOp0F_x186 : execOp0F 0x186 = execRange 0x186 := by
  unfold execOp0F; rfl
theorem execOp0F_x187 : execOp0F 0x187 = execRange 0x187 := by
  unfold execOp0F; rfl
theorem execOp0F_x188 : execOp0F 0x188 = execRange 0x188 := by
  unfold execOp0F; rfl
theorem execOp0F_x189 : execOp0F 0x189 = execRange 0x189 := by
  unfold execOp0F; rfl
theorem execOp0F_x18A : execOp0F 0x18A = execRange 0x18A := by
  unfold execOp0F; rfl
theorem execOp0F_x18B : execOp0F 0x18B = execRange 0x18B := by
  unfold execOp0F; rfl
theorem execOp0F_x18C : execOp0F 0x18C = execRange 0x18C := by
  unfold execOp0F; rfl
theorem execOp0F_x18D : execOp0F 0x18D = execRange 0x18D := by
  unfold execOp0F; rfl
theorem execOp0F_x18E : execOp0F 0x18E = execRange 0x18E := by
  unfold execOp0F; rfl
theorem execOp0F_x18F : execOp0F 0x18F = execRange 0x18F := by
  unfold execOp0F; rfl

attribute [scoped cbv_eval] execOp0F_1B6 execOp0F_x180 execOp0F_x181 execOp0F_x182 execOp0F_x183 execOp0F_x184 execOp0F_x185 execOp0F_x186 execOp0F_x187 execOp0F_x188 execOp0F_x189 execOp0F_x18A execOp0F_x18B execOp0F_x18C execOp0F_x18D execOp0F_x18E execOp0F_x18F

/-! ## Byte loads outside the code -/

theorem rdBytes_codeMem_out {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a n : UInt32) (h : a.toNat < base.toNat ∨ base.toNat + size ≤ a.toNat) :
    rdBytes g.get a n = rdRaw g.get a n := by
  rw [rdBytes_codeMem, if_neg]
  intro ⟨_, h1, h2⟩
  omega

/-- A byte load from a `CodeMem` outside the code range (`omega` from the context) is `rdRaw`. -/
scoped cbv_simproc cbv_eval cbvRdOut (rdBytes (CodeMem.get _) _ _) := fun e => do
  let_expr rdBytes mem a n := e | return .rfl
  let_expr CodeMem.get base size code G := mem | return .rfl
  unless (Solutions.Cbx.Discharge.sizeLit? n) == some 1 do return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let baseL ← litOf base
  let sizeL ← litOf size
  let P := mkOr (← mkLT (toNat a) (toNat baseL)) (← mkLE (← mkAdd (toNat baseL) sizeL) (toNat a))
  let some h ← omegaSound? P | return .rfl
  let pf := mkAppN (mkConst ``rdBytes_codeMem_out) #[base, size, code, G, a, n, h]
  let rhs := mkApp3 (mkConst ``rdRaw) mem a n
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-! ## Folding the opaque word operations on literals -/

def lit32? (e : Expr) : Option Nat := (Sym.getNatValue? e).run

/-- `op a b` with literal `a`, `b`, replaced by its value (checked by the kernel by evaluation). -/
def fold2 (f : UInt32 → UInt32 → UInt32) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let some a := lit32? (e.getArg! 0) | return .rfl
  let some b := lit32? (e.getArg! 1) | return .rfl
  let r := toExpr (f a.toUInt32 b.toUInt32)
  let pf ← mkEqRefl r
  return .step r (← mkExpectedTypeHint pf (← mkEq e r))

scoped cbv_simproc cbv_eval cbvFoldShl (UInt32.shiftLeft _ _) := fun e => fold2 (· <<< ·) e
scoped cbv_simproc cbv_eval cbvFoldShr (UInt32.shiftRight _ _) := fun e => fold2 (· >>> ·) e
scoped cbv_simproc cbv_eval cbvFoldOr (UInt32.lor _ _) := fun e => fold2 (· ||| ·) e
scoped cbv_simproc cbv_eval cbvFoldAnd (UInt32.land _ _) := fun e => fold2 (· &&& ·) e
scoped cbv_simproc cbv_eval cbvFoldXor (UInt32.xor _ _) := fun e => fold2 (· ^^^ ·) e

/-! ## Conditions on the carry flag after `cmp` -/

theorem evalCC_cf (a b : UInt32) (f : UInt32) (hf : f = (subF 4 a b 0).2) :
    (f &&& Flag.CF != 0) = ltU a b := by
  subst hf
  have := subF_cf a b
  show (UInt32.land (subF 4 a b 0).2 1 != 0) = ltU a b
  rw [this]
  cases ltU a b <;> decide

/-- `jb` (condition 2) and `jae` (condition 3) after `cmp a, b`. -/
theorem evalCC_2 (a b : UInt32) : evalCC (efl (subF 4 a b 0).2) 2 = ltU a b := by
  unfold evalCC
  simp only
  have h := efl_cf (subF 4 a b 0).2
  show (UInt32.land (efl (subF 4 a b 0).2) 1 != 0) = ltU a b
  rw [h, subF_cf]
  cases ltU a b <;> decide

theorem evalCC_3 (a b : UInt32) : evalCC (efl (subF 4 a b 0).2) 3 = !ltU a b := by
  unfold evalCC
  simp only
  have h := efl_cf (subF 4 a b 0).2
  show (!(UInt32.land (efl (subF 4 a b 0).2) 1 != 0)) = !ltU a b
  rw [h, subF_cf]
  cases ltU a b <;> decide

attribute [scoped cbv_eval] evalCC_2 evalCC_3

attribute [scoped cbv_opaque] ltU shrF
attribute [scoped cbv_eval] efl_cf

end Sodium.Proofs.PadLib
