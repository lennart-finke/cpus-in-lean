import Solutions.Exec.Step
import Solutions.Logic.CodeWr1
import Solutions.Exec.Alu
/-!
# Byte stores under `cbv`

`cbvWrMem` (`Solutions.Exec.Step`) keeps a word store outside the code as a `CodeMem` (`CodeMem.wr4`), so
that later instructions are still decoded from the code bytes; a byte store stays a plain `wrBytes`.
The `cbv_simproc`s here (scoped in `Solutions.Exec.Byte`) do the same for byte stores
(`CodeMem.wr1`, with `StoreOk1` shown by `exec_omega`) and resolve loads through them (the old
memory when disjoint, the stored byte when the same byte). Prover L, additions only.
-/
namespace Solutions.Exec.Byte
open X86 Solutions.Logic Solutions.Exec Lean Meta

attribute [scoped cbv_opaque] CodeMem.wr1

theorem xor_self' (x : UInt32) : UInt32.xor x x = 0 := UInt32.xor_self

/-- The result of a 32-bit `add` as `UInt32.add` (the address normal form), the result of `xor x, x`. -/
theorem addF_fst' (a b : UInt32) : (addF 4 a b 0).1 = UInt32.add a b := addF_fst a b

attribute [scoped cbv_eval] xor_self' addF_fst'

open Discharge in
/-- A byte store outside the code into a code memory: `CodeMem.wr1`. -/
scoped cbv_simproc cbv_eval cbvWr1 (wrBytes (CodeMem.get _) _ _ _) := fun e => do
  let_expr wrBytes mem a n v := e | return .rfl
  unless sizeLit? n == some 1 do return .rfl
  unless mem.isAppOfArity ``CodeMem.get 4 do return .rfl
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
  let P := mkAnd (← mkLT (toNat a) (mkApp (mkConst ``ByteArray.size) mem))
    (mkOr (← mkLT (toNat a) (toNat baseL)) (← mkLE (← mkAdd (toNat baseL) sizeL) (toNat a)))
  let some hP ← omega? P | return .rfl
  let ok ← mkExpectedTypeHint hP
    (mkAppN (mkConst ``StoreOk1) #[base, size, mkApp4 (mkConst ``CodeMem.mem) base size code G, a])
  let newMem ← Sym.share (mkApp4 (mkConst ``CodeMem.get) base size code
    (mkAppN (mkConst ``CodeMem.wr1) #[base, size, code, G, a, v, ok]))
  return .step newMem (← mkExpectedTypeHint (← mkEqRefl newMem) (← mkEq e newMem))

open Discharge in
/-- A load through a byte store into a code memory. -/
scoped cbv_simproc cbv_eval cbvRdWr1 (rdRaw (CodeMem.get (CodeMem.wr1 _ _ _ _)) _ _) := fun e => do
  let_expr rdRaw mem b k := e | return .rfl
  let_expr CodeMem.get base size code G' := mem | return .rfl
  let_expr CodeMem.wr1 _ _ _ G a v _ := G' | return .rfl
  let some kv := sizeLit? k | return .rfl
  unless kv == 4 || kv == 1 do return .rfl
  let M := mkApp4 (mkConst ``CodeMem.get) base size code G
  let toNat (x : Expr) := mkApp (mkConst ``UInt32.toNat) x
  let sizeE := mkApp (mkConst ``ByteArray.size) M
  let some ha ← omega? (← mkLT (toNat a) sizeE) | return .rfl
  if kv == 4 then
    let some hb ← omega? (← mkLE (← mkAdd (toNat b) (mkNatLit 4)) sizeE) | return .rfl
    let some hd ← omega? (mkOr (← mkLT (toNat a) (toNat b)) (← mkLE (← mkAdd (toNat b) (mkNatLit 4)) (toNat a)))
      | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes4_wrBytes1_other) #[M, a, b, v, ha, hb, hd]
    let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) M b k)
    return .step r (← mkExpectedTypeHint pf (← mkEq e r))
  else
    if a == b then
      let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes1_wrBytes1_self) #[M, a, v, ha]
      let r ← Sym.share (mkApp (mkConst ``UInt8.toUInt32) (mkApp (mkConst ``UInt32.toUInt8) v))
      return .step r (← mkExpectedTypeHint pf (← mkEq e r))
    let some hb ← omega? (← mkLT (toNat b) sizeE) | return .rfl
    let some hd ← omega? (mkNot (← mkEq (toNat a) (toNat b))) | return .rfl
    let pf := mkAppN (mkConst ``Solutions.Logic.rdBytes1_wrBytes1_other) #[M, a, b, v, ha, hb, hd]
    let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) M b k)
    return .step r (← mkExpectedTypeHint pf (← mkEq e r))

theorem rdBytes_codeMem_out {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a n : UInt32) (h : a.toNat < base.toNat ∨ base.toNat + size ≤ a.toNat) : rdBytes g.get a n = rdRaw g.get a n := by
  rw [rdBytes_codeMem, if_neg (by omega)]

open Discharge in
/-- A data read outside the code range of a code memory (`rdBytes_codeMem` cannot decide its test for
a symbolic address): `rdRaw`. -/
scoped cbv_simproc cbv_eval cbvRdOut (rdBytes (CodeMem.get _) _ _) := fun e => do
  let_expr rdBytes mem a n := e | return .rfl
  unless mem.isAppOfArity ``CodeMem.get 4 do return .rfl
  if (Sym.getNatValue? a).run.isSome then return .rfl
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
  let P := mkOr (← mkLT (toNat a) (toNat baseL)) (← mkLE (← mkAdd (toNat baseL) sizeL) (toNat a))
  let some hP ← omega? P | return .rfl
  let hT := mkOr (← mkLT (toNat a) (toNat base)) (← mkLE (← mkAdd (toNat base) size) (toNat a))
  let pf := mkAppN (mkConst ``rdBytes_codeMem_out) #[base, size, code, G, a, n, ← mkExpectedTypeHint hP hT]
  let r ← Sym.share (mkApp3 (mkConst ``Solutions.Logic.rdRaw) mem a n)
  return .step r (← mkExpectedTypeHint pf (← mkEq e r))

end Solutions.Exec.Byte
