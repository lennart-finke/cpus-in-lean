import Solutions.Exec.Step
import Solutions.Exec.Mul
/-!
# `if c then 1 else 0` on a symbolic `Bool` under `cbv`

`bt` sets CF to `if (v >>> b) &&& 1 != 0 then CF else 0` and `setcc` writes
`if evalCC f cc then 1 else 0`. When the condition is a symbolic `Bool`, `cbv` keeps the `ite`, and
after it rewrites the condition (e.g. `evalCC` to `Mul.cfB`) the instance of the `ite` is a cast
(`decidable_of_decidable_of_eq …`) that no hand-written statement has. The `cbv_simproc` `cbvBitU`
(scoped in `Solutions.Exec.Bit`) turns every `@ite UInt32 (c = true) _ 1 0` (also with `Flag.CF` for
`1`) into `bitU c` (opaque) before the instance matters. Prover P, additions only.
-/
namespace Solutions.Exec.Bit
open X86 Lean Meta

/-- `1` if `c`, else `0`. -/
def bitU (c : Bool) : UInt32 := if c then 1 else 0

theorem ite_bitU (c : Bool) (inst : Decidable (c = true)) : @ite UInt32 (c = true) inst 1 0 = bitU c := by
  cases c
  · exact if_neg (by simp)
  · exact if_pos rfl

theorem ite_bitU_cf (c : Bool) (inst : Decidable (c = true)) :
    @ite UInt32 (c = true) inst Flag.CF 0 = bitU c := ite_bitU c inst

attribute [scoped cbv_opaque] bitU

/-- `@ite UInt32 (c = true) inst 1 0` (or with `Flag.CF`) to `bitU c`. -/
scoped cbv_simproc cbv_eval cbvBitU (@ite UInt32 _ _ _ _) := fun e => do
  let_expr ite α cond inst t f := e | return .rfl
  unless α.isConstOf ``UInt32 do return .rfl
  let_expr Eq β c tr := cond | return .rfl
  unless β.isConstOf ``Bool && tr.isConstOf ``Bool.true do return .rfl
  let some fv ← Mul.smallVal? ``UInt32.toNat f | return .rfl
  unless fv == 0 do return .rfl
  let lem ←
    if t.isConstOf ``Flag.CF then pure ``ite_bitU_cf
    else
      let some tv ← Mul.smallVal? ``UInt32.toNat t | return .rfl
      unless tv == 1 do return .rfl
      pure ``ite_bitU
  let rhs := mkApp (mkConst ``bitU) c
  let pf := mkApp2 (mkConst lem) c inst
  return .step rhs (← mkExpectedTypeHint pf (← mkEq e rhs))

theorem bitU_lt (c : Bool) : (bitU c).toNat < 2 := by cases c <;> decide

theorem bitU_01 (c : Bool) : bitU c = 0 ∨ bitU c = 1 := by cases c <;> simp [bitU]

end Solutions.Exec.Bit
