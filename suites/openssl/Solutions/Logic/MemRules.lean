import Solutions.Logic.Cbx
import Solutions.Logic.CodeWr1
import Solutions.Exec.CodeWr
import Solutions.Logic.Flags
/-!
# Loads through stores, for `cbv`

A store outside the code range keeps the memory a `CodeMem` (`Solutions.Exec.CodeMem.wr4` for
words, `CodeMem.wr1` here for bytes), so that instruction fetches still read the code. A load from
such a memory (`rdRaw`, what `Solutions.Logic.rdBytes_codeMem` leaves for data) is resolved by
`cbvLoad`: the stored value when the load is the store's word or byte, the older memory when the two
are disjoint. Both are decided by `omega` from the hypotheses in context, and a decision is taken
only from a complete proof (`omegaSound?`); otherwise the load is left as it is.

They replace `Solutions.Cbx.cbvRdWr4` and `Solutions.Cbx.cbvRdWr`, which files using these rules
remove (`attribute [-cbvSimprocAttr] …` after `open Solutions.Cbx`).
-/
namespace Solutions.Logic
open X86 Solutions.Exec Solutions.Cbx Lean Meta

theorem rdRaw_wr4_same {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk base size g.mem a) (hab : a.toNat = b.toNat) :
    rdRaw (CodeMem.wr4 g a v h).get b 4 = v := by
  have := UInt32.toNat_inj.mp hab; subst this
  exact rdBytes4_wrBytes4_self h.1

theorem rdRaw_wr4_other4 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk base size g.mem a) (hb : b.toNat + 4 ≤ g.get.size)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdRaw (CodeMem.wr4 g a v h).get b 4 = rdRaw g.get b 4 :=
  rdBytes4_wrBytes4_other h.1 hb hd

theorem rdRaw_wr4_other1 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk base size g.mem a) (hb : b.toNat < g.get.size)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat < a.toNat) :
    rdRaw (CodeMem.wr4 g a v h).get b 1 = rdRaw g.get b 1 :=
  rdBytes1_wrBytes4_other h.1 hb hd

theorem rdRaw_wr1_same {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk1 base size g.mem a) (hab : a.toNat = b.toNat) :
    rdRaw (CodeMem.wr1 g a v h).get b 1 = v.toUInt8.toUInt32 := by
  have := UInt32.toNat_inj.mp hab; subst this
  exact rdBytes1_wrBytes1_self h.1

theorem rdRaw_wr1_other1 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk1 base size g.mem a) (hb : b.toNat < g.get.size) (hd : a.toNat ≠ b.toNat) :
    rdRaw (CodeMem.wr1 g a v h).get b 1 = rdRaw g.get b 1 :=
  rdBytes1_wrBytes1_other h.1 hb hd

theorem rdRaw_wr1_other4 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a b v : UInt32) (h : StoreOk1 base size g.mem a) (hb : b.toNat + 4 ≤ g.get.size)
    (hd : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdRaw (CodeMem.wr1 g a v h).get b 4 = rdRaw g.get b 4 :=
  rdBytes4_wrBytes1_other h.1 hb hd

theorem mem_eq_get {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code) :
    g.mem = g.get := rfl

/-- The literal value of a constant like `Image.base`. -/
def litOf (x : Expr) : MetaM Expr := do
  match x with
  | .const .. => return (← unfoldDefinition? x).getD x
  | _ => return x

/-- A byte store outside the code keeps the memory a `CodeMem` (`CodeMem.wr1`). -/
scoped cbv_simproc cbv_eval cbvWr1 (wrBytes (CodeMem.get _) _ _ _) := fun e => do
  let_expr wrBytes mem a n v := e | return .rfl
  unless (Solutions.Cbx.Discharge.sizeLit? n) == some 1 do return .rfl
  let_expr CodeMem.get base size code G := mem | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let baseL ← litOf base
  let sizeL ← litOf size
  let P := mkAnd (← mkLT (toNat a) (mkApp (mkConst ``ByteArray.size) mem))
    (mkOr (← mkLT (toNat a) (toNat baseL)) (← mkLE (← mkAdd (toNat baseL) sizeL) (toNat a)))
  let some hP ← omegaSound? P | return .rfl
  let ok ← mkExpectedTypeHint hP (mkAppN (mkConst ``StoreOk1) #[base, size, mkApp4 (mkConst ``CodeMem.mem) base size code G, a])
  let rhs := mkApp4 (mkConst ``CodeMem.get) base size code (mkAppN (mkConst ``CodeMem.wr1) #[base, size, code, G, a, v, ok])
  let pf ← mkEqRefl rhs
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

/-- A load through a code-keeping store: the stored value when the same word or byte, the older
memory when disjoint, decided by `omega` from the context. -/
scoped cbv_simproc cbv_eval cbvLoad (rdRaw (CodeMem.get _) _ _) := fun e => do
  let_expr rdRaw mem b k := e | return .rfl
  let_expr CodeMem.get base size code G' := mem | return .rfl
  let some kv := Solutions.Cbx.Discharge.sizeLit? k | return .rfl
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let four := mkNatLit 4
  let older (G : Expr) : Expr := mkApp3 (mkConst ``rdRaw) (mkApp4 (mkConst ``CodeMem.get) base size code G) b k
  let sizeOf (G : Expr) : Expr := mkApp (mkConst ``ByteArray.size) (mkApp4 (mkConst ``CodeMem.get) base size code G)
  if G'.isAppOfArity ``CodeMem.wr4 7 then
    let G := G'.getArg! 3; let a := G'.getArg! 4; let v := G'.getArg! 5; let ok := G'.getArg! 6
    if kv == 4 then
      if let some hab ← omegaSound? (← mkEq (toNat a) (toNat b)) then
        let pf := mkAppN (mkConst ``rdRaw_wr4_same) #[base, size, code, G, a, b, v, ok, hab]
        return .step v (← mkExpectedTypeHint pf (← mkEq e v))
      let some hb ← omegaSound? (← mkLE (← mkAdd (toNat b) four) (sizeOf G)) | return .rfl
      let some hd ← omegaSound? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b))
          (← mkLE (← mkAdd (toNat b) four) (toNat a))) | return .rfl
      let pf := mkAppN (mkConst ``rdRaw_wr4_other4) #[base, size, code, G, a, b, v, ok, hb, hd]
      let r := older G
      return .step r (← mkExpectedTypeHint pf (← mkEq e r))
    if kv == 1 then
      let some hb ← omegaSound? (← mkLT (toNat b) (sizeOf G)) | return .rfl
      let some hd ← omegaSound? (mkOr (← mkLE (← mkAdd (toNat a) four) (toNat b)) (← mkLT (toNat b) (toNat a)))
        | return .rfl
      let pf := mkAppN (mkConst ``rdRaw_wr4_other1) #[base, size, code, G, a, b, v, ok, hb, hd]
      let r := older G
      return .step r (← mkExpectedTypeHint pf (← mkEq e r))
    return .rfl
  if G'.isAppOfArity ``CodeMem.wr1 7 then
    let G := G'.getArg! 3; let a := G'.getArg! 4; let v := G'.getArg! 5; let ok := G'.getArg! 6
    if kv == 1 then
      if let some hab ← omegaSound? (← mkEq (toNat a) (toNat b)) then
        let pf := mkAppN (mkConst ``rdRaw_wr1_same) #[base, size, code, G, a, b, v, ok, hab]
        let r ← mkAppM ``UInt8.toUInt32 #[← mkAppM ``UInt32.toUInt8 #[v]]
        return .step r (← mkExpectedTypeHint pf (← mkEq e r))
      let some hb ← omegaSound? (← mkLT (toNat b) (sizeOf G)) | return .rfl
      let some hd ← omegaSound? (mkNot (← mkEq (toNat a) (toNat b))) | return .rfl
      let pf := mkAppN (mkConst ``rdRaw_wr1_other1) #[base, size, code, G, a, b, v, ok, hb, hd]
      let r := older G
      return .step r (← mkExpectedTypeHint pf (← mkEq e r))
    if kv == 4 then
      let some hb ← omegaSound? (← mkLE (← mkAdd (toNat b) four) (sizeOf G)) | return .rfl
      let some hd ← omegaSound? (mkOr (← mkLT (toNat a) (toNat b)) (← mkLE (← mkAdd (toNat b) four) (toNat a)))
        | return .rfl
      let pf := mkAppN (mkConst ``rdRaw_wr1_other4) #[base, size, code, G, a, b, v, ok, hb, hd]
      let r := older G
      return .step r (← mkExpectedTypeHint pf (← mkEq e r))
    return .rfl
  return .rfl

attribute [scoped cbv_opaque] CodeMem.wr1 CodeMem.wr4

end Solutions.Logic

namespace Solutions.Logic.Bytes
/-! ## Byte loads from data

`open Solutions.Logic.Bytes` sets `cbv` up for code that loads single bytes from data: the byte
conversions of symbolic values stay unevaluated (their literals are still folded by
`Solutions.Exec`'s conversion rules), and whether a 1-byte load is in the code range is decided by
`cbvInCode` (on a literal address by evaluation, otherwise by `omega` from the context) instead of
by unfolding the comparison. A file that opens this namespace should also remove
`Solutions.Logic.rdBytes_codeMem` (`attribute [-cbv_eval] …`), which `rdBytes_codeMem2` replaces. -/
open X86 Solutions.Exec Lean Meta

/-- Whether `a` is in the code range `[base, base + size)`, as a function `cbv` does not unfold. -/
def inCodeB (base : UInt32) (size : Nat) (a : UInt32) : Bool :=
  decide (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size)

theorem rdBytes_codeMem2 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a n : UInt32) :
    rdBytes g.get a n =
      if n = 1 ∧ inCodeB base size a = true then (code (a.toNat - base.toNat)).toUInt32
      else rdRaw g.get a n := by
  rw [rdBytes_codeMem]
  simp only [inCodeB, decide_eq_true_eq]

theorem inCodeB_false {base : UInt32} {size : Nat} {a : UInt32}
    (h : ¬(base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size)) : inCodeB base size a = false := by
  simp only [inCodeB, decide_eq_false_iff_not]; exact h

theorem inCodeB_true {base : UInt32} {size : Nat} {a : UInt32}
    (h : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size) : inCodeB base size a = true := by
  simp only [inCodeB, decide_eq_true_eq]; exact h

/-- `inCodeB` by evaluation on literals, otherwise by `omega` from the context. -/
scoped cbv_simproc cbv_eval cbvInCode (inCodeB _ _ _) := fun e => do
  let_expr inCodeB base size a := e | return .rfl
  let baseL ← litOf base
  let sizeL ← litOf size
  -- a literal address: by evaluation (checked by the kernel)
  if let (some av, some bv, some sv) :=
      ((Sym.getNatValue? a).run, (Sym.getNatValue? baseL).run, (Sym.getNatValue? sizeL).run) then
    let r := decide (bv % 2 ^ 32 ≤ av % 2 ^ 32 ∧ av % 2 ^ 32 < bv % 2 ^ 32 + sv)
    let rE := toExpr r
    let pf ← mkExpectedTypeHint (← mkEqRefl rE) (← mkEq e rE)
    return .step rE pf
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let P := mkAnd (← mkLE (toNat baseL) (toNat a)) (← mkLT (toNat a) (← mkAdd (toNat baseL) sizeL))
  if let some h ← omegaSound? (mkNot P) then
    let pf := mkApp4 (mkConst ``inCodeB_false) base size a h
    return .step (mkConst ``Bool.false) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.false)))
  if let some h ← omegaSound? P then
    let pf := mkApp4 (mkConst ``inCodeB_true) base size a h
    return .step (mkConst ``Bool.true) (← mkExpectedTypeHint pf (← mkEq e (mkConst ``Bool.true)))
  return .rfl

attribute [scoped cbv_opaque] UInt32.toUInt8 UInt8.toUInt32 inCodeB
attribute [scoped cbv_eval] rdBytes_codeMem2
end Solutions.Logic.Bytes
