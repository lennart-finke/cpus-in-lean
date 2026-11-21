import Solutions.Logic.Flags
import Lean
/-!
# Unsigned comparisons and 32-bit immediates for `cbv` (opt-in)

`open Solutions.Logic.Cmp` adds, on top of the default rules of `Solutions.Logic`:

* the carry flag and the carry-or-zero bits (mask 65, used by `ja`/`jbe`) of `subF`, as
  `cond (ltU a b) 1 0` and `cond (ltU a b) 1 0 ||| cond (eqU a b) 64 0`; `ltU a b` (unsigned
  `a < b`) is opaque to `cbv` and decided by `omega` from the hypotheses in context, as `eqU` is;
* the folding of `UInt32.lor`, `land`, `xor`, `shiftLeft`, `shiftRight` on two literals (the
  32-bit immediates of the decoder come out as `lor`s of shifted bytes).

The rules on `UInt32.land` are one simproc (not `cbv_eval` equations next to `land_self`). The scope
is separate so that what `cbv` gives without it does not change.
-/
namespace Solutions.Logic.Cmp
open X86 Solutions.Exec Solutions.Cbx Solutions.Logic Lean Meta

/-- Unsigned `a < b`, as a function `cbv` does not unfold. -/
def ltU (a b : UInt32) : Bool := decide (a.toNat < b.toNat)

theorem ltU_true {a b : UInt32} (h : a.toNat < b.toNat) : ltU a b = true := by simp [ltU, h]
theorem ltU_false {a b : UInt32} (h : ¬ a.toNat < b.toNat) : ltU a b = false := by simp [ltU, h]

theorem pack_cf (f : AFlags) : f.pack &&& 1 = cond f.cf 1 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem pack_cz (f : AFlags) : f.pack &&& 65 = cond f.cf 1 0 ||| cond f.zf 64 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem subCore_cf (sz : Sz) (a b : UInt32) : (subCore sz a b 0).2.cf = ltU a b := by
  simp only [subCore, ltU]
  rw [decide_eq_decide]
  simp [UInt64.lt_iff_toNat_lt]

theorem subCore4_zf (a b : UInt32) : (subCore 4 a b 0).2.zf = eqU a b := by
  simp only [subCore, eqU, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, _root_.ite_false, UInt32.sub_zero]
  have e : (a - b &&& 0xFFFFFFFF) = a - b := and_ones (a - b)
  rw [e]
  by_cases h : a = b
  · subst h; simp
  · have h1 : a - b ≠ 0 := by
      intro e; apply h
      have := congrArg (· + b) e
      simpa using this
    simp [h1, h]

theorem subF_cf (sz : Sz) (a b : UInt32) : UInt32.land (subF sz a b 0).2 1 = cond (ltU a b) 1 0 := by
  show (subCore sz a b 0).2.pack &&& 1 = _
  rw [pack_cf, subCore_cf]

theorem subF_cz (a b : UInt32) :
    UInt32.land (subF 4 a b 0).2 65 = UInt32.lor (cond (ltU a b) 1 0) (cond (eqU a b) 64 0) := by
  show (subCore 4 a b 0).2.pack &&& 65 = _
  rw [pack_cz, subCore_cf, subCore4_zf]
  rfl

theorem efl_cz (f : UInt32) : UInt32.land (efl f) 65 = UInt32.land f 65 :=
  land_bits f 65 (by decide)

/-- `ltU a b` decided by `omega` from the hypotheses in context. -/
scoped cbv_simproc cbv_eval cbvLtU (ltU _ _) := fun e => do
  let_expr ltU a b := e | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let P ← mkAppM ``LT.lt #[toNat a, toNat b]
  if let some h ← omegaSound? P then
    let pf := mkApp3 (mkConst ``ltU_true) a b h
    return .step (mkConst ``Bool.true) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.true)))
  if let some h ← omegaSound? (mkNot P) then
    let pf := mkApp3 (mkConst ``ltU_false) a b h
    return .step (mkConst ``Bool.false) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.false)))
  return .rfl

private def lit? (e : Expr) : Option Nat := (Sym.getNatValue? e).run

/-- A binary operation on two literals, folded (the step is definitional). -/
private def fold2 (f : UInt32 → UInt32 → UInt32) (e : Expr) : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
  let some a := lit? (e.getArg! 0) | return none
  let some b := lit? (e.getArg! 1) | return none
  let r ← Sym.share (toExpr (f a.toUInt32 b.toUInt32))
  return some (.step r (← Sym.mkEqRefl r))

scoped cbv_simproc cbv_eval cbvLorLit (UInt32.lor _ _) := fun e => do
  return (← fold2 UInt32.lor e).getD .rfl
scoped cbv_simproc cbv_eval cbvXorLit (UInt32.xor _ _) := fun e => do
  return (← fold2 UInt32.xor e).getD .rfl
scoped cbv_simproc cbv_eval cbvShrLit (UInt32.shiftRight _ _) := fun e => do
  return (← fold2 UInt32.shiftRight e).getD .rfl

/-- `x &&& k`: literals folded; the carry and carry-or-zero bits of `efl` and of `subF`. -/
scoped cbv_simproc cbv_eval cbvLand (UInt32.land _ _) := fun e => do
  if let some r ← fold2 UInt32.land e then return r
  let_expr UInt32.land x k := e | return .rfl
  let some kv := lit? k | return .rfl
  unless kv == 1 || kv == 65 do return .rfl
  if x.isAppOfArity ``efl 1 && kv == 65 then
    let f := x.appArg!
    let pf := mkApp (mkConst ``efl_cz) f
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  let some p := sndOf? x | return .rfl
  unless p.isAppOfArity ``subF 4 do return .rfl
  let lit0? := lit? (p.getArg! 3)
  unless lit0? == some 0 do return .rfl
  let (sz, a, b) := (p.getArg! 0, p.getArg! 1, p.getArg! 2)
  if kv == 1 then
    let pf := mkApp3 (mkConst ``subF_cf) sz a b
    let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
    return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
  unless lit? sz == some 4 do return .rfl
  let pf := mkApp2 (mkConst ``subF_cz) a b
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))


/-! ### Shifts by a literal count, and scaled addresses -/

/-- The flags of a 32-bit shift, opaque to `cbv`. -/
def shFl (op : UInt8) (a k : UInt32) : UInt32 :=
  match shiftOp op 4 a k false with
  | some (_, _, f) => f
  | none => 0

theorem shr_res (a k : UInt32) (hk : k.toNat < 32) :
    (a.toUInt64 >>> k.toUInt64).toUInt32 &&& 0xFFFFFFFF = UInt32.shiftRight a k := by
  rw [and_ones]
  apply UInt32.toNat_inj.1
  have h1 : (UInt32.shiftRight a k).toNat = (a >>> k).toNat := rfl
  have e1 : ∀ x y : UInt64, ShiftRight.shiftRight x y = HShiftRight.hShiftRight x y := fun _ _ => rfl
  have e2 : ∀ x y : UInt32, ShiftRight.shiftRight x y = HShiftRight.hShiftRight x y := fun _ _ => rfl
  simp only [e1, e2] at h1 ⊢
  rw [h1, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_shiftRight, UInt32.toNat_toUInt64,
    UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (show k.toNat < 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt)

theorem shl_res (a k : UInt32) (hk : k.toNat < 32) :
    (a.toUInt64 <<< k.toUInt64).toUInt32 &&& 0xFFFFFFFF = UInt32.shiftLeft a k := by
  rw [and_ones]
  apply UInt32.toNat_inj.1
  have h1 : (UInt32.shiftLeft a k).toNat = (a <<< k).toNat := rfl
  have e1 : ∀ x y : UInt64, ShiftLeft.shiftLeft x y = HShiftLeft.hShiftLeft x y := fun _ _ => rfl
  have e2 : ∀ x y : UInt32, ShiftLeft.shiftLeft x y = HShiftLeft.hShiftLeft x y := fun _ _ => rfl
  simp only [e1, e2] at h1 ⊢
  rw [h1, UInt64.toNat_toUInt32, UInt64.toNat_shiftLeft, UInt32.toNat_shiftLeft, UInt32.toNat_toUInt64,
    UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (show k.toNat < 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.mod_mod_of_dvd _ (by decide)]

theorem shiftOp_shr (a k : UInt32) (c : Bool) (hk : k.toNat < 32) (hk0 : k.toNat ≠ 0) :
    shiftOp 5 4 a k c = some (UInt32.shiftRight a k, Flag.arith, shFl 5 a k) := by
  have hm : k &&& 0x1F = k := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hk]
  have h0 : (k == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hk0 (by rw [e]; rfl)
  unfold shFl shiftOp
  simp only [hm, h0, Bool.false_eq_true, _root_.ite_false, mask4, shr_res a k hk]

theorem shiftOp_shl (a k : UInt32) (c : Bool) (hk : k.toNat < 32) (hk0 : k.toNat ≠ 0) :
    shiftOp 4 4 a k c = some (UInt32.shiftLeft a k, Flag.arith, shFl 4 a k) := by
  have hm : k &&& 0x1F = k := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hk]
  have h0 : (k == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hk0 (by rw [e]; rfl)
  unfold shFl shiftOp
  simp (config := { decide := true }) only [hm, h0, Bool.false_eq_true, _root_.ite_false, mask4, shl_res a k hk]

theorem shl_one (x : UInt32) : UInt32.shiftLeft x 1 = UInt32.add x x := by
  apply UInt32.toNat_inj.1
  have h1 : (UInt32.shiftLeft x 1).toNat = (x <<< 1).toNat := rfl
  have h2 : (UInt32.add x x).toNat = (x + x).toNat := rfl
  have e2 : ∀ x y : UInt32, ShiftLeft.shiftLeft x y = HShiftLeft.hShiftLeft x y := fun _ _ => rfl
  simp only [e2] at h1 ⊢
  rw [h1, h2, UInt32.toNat_shiftLeft, UInt32.toNat_add, Nat.shiftLeft_eq]
  simp only [show (1 : UInt32).toNat % 32 = 1 by decide]
  congr 1; omega

/-- The value of a byte literal, also in the structure form `{ toBitVec := n#8 }`. -/
def u8Val? (x : Expr) : MetaM (Option Nat) := do
  if let some v := lit? x then return some v
  unless x.isAppOfArity ``UInt8.ofBitVec 1 do return none
  let n ← whnfD (mkApp (mkConst ``UInt8.toNat) x)
  return match n.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? n).run

/-- `shiftOp` of SHR/SHL on 32 bits by a literal count in `1 … 31`. -/
scoped cbv_simproc cbv_eval cbvShiftOp (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a k c := e | return .rfl
  let some opv ← u8Val? op | return .rfl
  unless (← u8Val? sz) == some 4 do return .rfl
  let some kv := lit? k | return .rfl
  unless 0 < kv && kv < 32 do return .rfl
  let lem := if opv == 5 then ``shiftOp_shr else if opv == 4 then ``shiftOp_shl else Name.anonymous
  if lem.isAnonymous then return .rfl
  let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkApp (mkConst ``UInt32.toNat) k, mkNatLit 32])
  let hk0 ← mkDecideProof (mkNot (← mkEq (mkApp (mkConst ``UInt32.toNat) k) (mkNatLit 0)))
  let pf := mkAppN (mkConst lem) #[a, k, c, hk, hk0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- `UInt8.toUInt32` of a byte literal in any form (such as the scale of an address). -/
scoped cbv_simproc cbv_eval cbvU8Lit (UInt8.toUInt32 _) := fun e => do
  let x := e.appArg!
  if (lit? x).isSome then return .rfl
  unless x.isAppOfArity ``UInt8.ofBitVec 1 do return .rfl
  let n ← whnfD (mkApp (mkConst ``UInt8.toNat) x)
  let v? : Option Nat := match n.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? n).run
  let some v := v? | return .rfl
  let r ← Sym.share (toExpr (v % 256).toUInt32)
  return .step r (← Sym.mkEqRefl r)

scoped cbv_simproc cbv_eval cbvShlLit (UInt32.shiftLeft _ _) := fun e => do
  if let some r ← fold2 UInt32.shiftLeft e then return r
  let_expr UInt32.shiftLeft x k := e | return .rfl
  unless lit? k == some 1 do return .rfl
  let pf := mkApp (mkConst ``shl_one) x
  let some (_, _, rhs) := (← inferType pf).eq? | return .rfl
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))
attribute [scoped cbv_opaque] shFl

attribute [scoped cbv_opaque] ltU

end Solutions.Logic.Cmp
