import Solutions.Exec.Step
/-!
# 64-bit arithmetic on register pairs under `cbv`

`open Solutions.Exec.Mul` (in addition to `Solutions.Exec`) lets `cbv` run the instructions of
32-bit code doing 64-bit arithmetic (ref10 `fe_mul`/`fe_sq`), keeping symbolic values small:

* one-operand `mul`/`imul` (`edx:eax ← eax · r/m`): the product stays the opaque
  `(imulCore 4 a b).1` (resp. `UInt64.mul`), its halves `UInt64.toUInt32 p` and
  `UInt64.toUInt32 (p >>> 32)`; the flags of `setMulFlags` fold to `efl (mixF f (ovfBits ovf) 2049)`;
  `UInt64` shifts and products of literals are still computed;
* `adc`/`sbb`: the carry-in read from `efl f` is `cfBit f` (`cfB f` as a `Bool`);
* `sar`, `shrd`, `shld` by a literal count: `sarR a k`, `sdR left a src k` with flags `sarF`, `sdF`;
* `x <<< 0` of a scaled-index address with scale 1, whatever form the `0` has.

Tested on pieces of `fe_sq` (`lea`/`imul` chains, `add`/`adc` chains over stack loads, the carry
step `add $2^25`/`adc $0`/`sar`/`shrd`).
-/
namespace Solutions.Exec.Mul
open X86 Solutions.Exec

/-- The CF and OF bits that `setMulFlags` sets. -/
def ovfBits (ovf : Bool) : UInt32 := if ovf then Flag.CF ||| Flag.OF else 0

theorem setMulFlags_eq (sz : Sz) (ovf : Bool) (lo : UInt32) :
    setMulFlags sz ovf lo = setFlags (Flag.CF ||| Flag.OF) (ovfBits ovf) := by
  unfold setMulFlags ovfBits
  cases ovf <;> rfl

attribute [scoped cbv_opaque] UInt64.toUInt32 UInt64.shiftRight UInt64.mul UInt32.toUInt64 ovfBits
attribute [scoped cbv_eval] setMulFlags_eq

open Lean Meta Sym in
/-- Fold a binary `UInt64` operation on two literals (they are opaque here). -/
def bin64 (f : UInt64 → UInt64 → UInt64) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let some a := (Sym.getNatValue? e.appFn!.appArg!).run | return .rfl
  let some b := (Sym.getNatValue? e.appArg!).run | return .rfl
  let r ← share (toExpr (f a.toUInt64 b.toUInt64))
  return .step r (← Sym.mkEqRefl r)

scoped cbv_simproc cbv_eval cbvShr64 (UInt64.shiftRight _ _) := bin64 (· >>> ·)
scoped cbv_simproc cbv_eval cbvMul64 (UInt64.mul _ _) := bin64 (· * ·)

theorem shl_zero_of (x k : UInt32) (h : k = 0) : UInt32.shiftLeft x k = x := by
  subst h; exact UInt32.shiftLeft_zero

open Lean Meta Sym in
/-- `x <<< 0` (an address with scale 1), whatever form the `0` has. -/
scoped cbv_simproc cbv_eval cbvShl0 (UInt32.shiftLeft _ _) := fun e => do
  let_expr UInt32.shiftLeft x k := e | return .rfl
  if let some a := (Sym.getNatValue? x).run then
    if let some b := (Sym.getNatValue? k).run then
      let r ← share (toExpr (a.toUInt32 <<< b.toUInt32))
      return .step r (← Sym.mkEqRefl r)
  let kn ← whnfD (mkApp (mkConst ``UInt32.toNat) k)
  let v : Option Nat := match kn.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? kn).run
  unless v == some 0 do return .rfl
  let zero := toExpr (0 : UInt32)
  let hk ← mkExpectedTypeHint (← Meta.mkEqRefl zero) (← mkEq k zero)
  let pf := mkApp3 (mkConst ``shl_zero_of) x k hk
  return .step x (← mkExpectedTypeHint pf (← mkEq e x))

/-! ### The carry flag (`adc`, `sbb`) -/

/-- The carry `0`/`1` that `adc`/`sbb` add, read from the flags `f` of the previous operation. -/
def cfBit (f : UInt32) : UInt32 := b2u (f &&& Flag.CF != 0)

theorem efl_cfBit (f : UInt32) : b2u (bne (UInt32.land (efl f) 1) 0) = cfBit f := by
  unfold cfBit efl b2u
  have : ∀ x : UInt32, (2 ||| (x &&& 0x8D5)) &&& 1 = x &&& 1 := by
    intro x
    apply UInt32.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
    rcases (by omega : i = 0 ∨ 0 < i) with rfl | h
    · cases x.toBitVec.getLsbD 0 <;> rfl
    · simp [show i ≠ 0 by omega]
  show (if (2 ||| (f &&& 0x8D5)) &&& 1 != 0 then 1 else 0) = (if f &&& 1 != 0 then 1 else 0)
  rw [this]

/-- The carry flag of `f`, as the `Bool` that `doAlu` passes on. -/
def cfB (f : UInt32) : Bool := f &&& Flag.CF != 0

theorem efl_cfB (f : UInt32) : bne (UInt32.land (efl f) 1) 0 = cfB f := by
  have h := efl_cfBit f
  unfold cfBit b2u at h
  unfold cfB
  cases h1 : bne (UInt32.land (efl f) 1) 0 <;> cases h2 : (f &&& Flag.CF != 0) <;> simp_all <;> rfl

theorem b2u_cfB (f : UInt32) : b2u (cfB f) = cfBit f := rfl

attribute [scoped cbv_opaque] cfBit cfB
attribute [scoped cbv_eval] efl_cfB b2u_cfB

/-! ### Shifts by a literal count (`sar`, `shrd`, `shld`) -/

/-- The result of a 32-bit `sar` by `cnt`. -/
def sarR (a cnt : UInt32) : UInt32 := ((shiftOp 7 4 a cnt false).getD (a, 0, 0)).1
/-- The flags of a 32-bit `sar` by `cnt`. -/
def sarF (a cnt : UInt32) : UInt32 := ((shiftOp 7 4 a cnt false).getD (a, 0, 0)).2.2

theorem shiftOp_sar (op : UInt8) (sz : Sz) (a cnt : UInt32) (cf : Bool) (hop : op = 7) (hsz : sz = 4)
    (h : (cnt &&& 0x1F == 0) = false) :
    shiftOp op sz a cnt cf = some (sarR a cnt, Flag.arith, sarF a cnt) := by
  subst hop hsz
  unfold sarR sarF shiftOp
  simp only [h]
  rfl

/-- The result of a 32-bit `shld` (`left`) or `shrd` by `cnt`. -/
def sdR (left : Bool) (a src cnt : UInt32) : UInt32 := ((shiftDouble left 4 a src cnt).getD (a, 0)).1
/-- The flags of a 32-bit `shld` (`left`) or `shrd` by `cnt`. -/
def sdF (left : Bool) (a src cnt : UInt32) : UInt32 := ((shiftDouble left 4 a src cnt).getD (a, 0)).2

theorem shiftDouble_lit (left : Bool) (sz : Sz) (a src cnt : UInt32) (hsz : sz = 4)
    (h : ((cnt &&& 0x1F).toUInt64 == 0) = false) :
    shiftDouble left sz a src cnt = some (sdR left a src cnt, sdF left a src cnt) := by
  subst hsz
  unfold sdR sdF shiftDouble
  simp only [h]
  rfl

attribute [scoped cbv_opaque] sarR sarF sdR sdF

open Lean Meta Sym in
/-- The value of a small closed natural-number-like term (a `UInt8`/`UInt32` in any form). -/
def smallVal? (toNat : Name) (x : Expr) : MetaM (Option Nat) := do
  let n ← whnfD (mkApp (mkConst toNat) x)
  return match n.rawNatLit? with
    | some v => some v
    | none => (Sym.getNatValue? n).run

open Lean Meta Sym in
scoped cbv_simproc cbv_eval cbvSar (shiftOp _ _ _ _ _) := fun e => do
  let_expr shiftOp op sz a cnt cf := e | return .rfl
  unless (← smallVal? ``UInt8.toNat op) == some 7 do return .rfl
  unless (← smallVal? ``UInt8.toNat sz) == some 4 do return .rfl
  let some c ← smallVal? ``UInt32.toNat cnt | return .rfl
  unless c % 32 != 0 do return .rfl
  let rhs ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkApp2 (mkConst ``sarR) a cnt,
    ← mkAppM ``Prod.mk #[mkConst ``Flag.arith, mkApp2 (mkConst ``sarF) a cnt]]]
  let hop ← mkExpectedTypeHint (← Meta.mkEqRefl op) (← mkEq op (toExpr (7 : UInt8)))
  let hsz ← mkExpectedTypeHint (← Meta.mkEqRefl sz) (← mkEq sz (toExpr (4 : UInt8)))
  let hc ← mkDecideProof (← mkEq (← mkAppM ``BEq.beq #[← mkAppM ``HAnd.hAnd #[cnt, toExpr (0x1F : UInt32)],
    toExpr (0 : UInt32)]) (mkConst ``Bool.false))
  let pf := mkAppN (mkConst ``shiftOp_sar) #[op, sz, a, cnt, cf, hop, hsz, hc]
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

open Lean Meta Sym in
scoped cbv_simproc cbv_eval cbvShiftDouble (shiftDouble _ _ _ _ _) := fun e => do
  let_expr shiftDouble left sz a src cnt := e | return .rfl
  unless (← smallVal? ``UInt8.toNat sz) == some 4 do return .rfl
  let some c ← smallVal? ``UInt32.toNat cnt | return .rfl
  unless c % 32 != 0 do return .rfl
  let rhs ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkApp4 (mkConst ``sdR) left a src cnt,
    mkApp4 (mkConst ``sdF) left a src cnt]]
  let hsz ← mkExpectedTypeHint (← Meta.mkEqRefl sz) (← mkEq sz (toExpr (4 : UInt8)))
  let hc ← mkDecideProof (← mkEq (← mkAppM ``BEq.beq #[← mkAppM ``UInt32.toUInt64
    #[← mkAppM ``HAnd.hAnd #[cnt, toExpr (0x1F : UInt32)]], toExpr (0 : UInt64)]) (mkConst ``Bool.false))
  let pf := mkAppN (mkConst ``shiftDouble_lit) #[left, sz, a, src, cnt, hsz, hc]
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

end Solutions.Exec.Mul
