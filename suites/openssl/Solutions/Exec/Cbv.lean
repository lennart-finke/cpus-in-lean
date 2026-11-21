import Lean
/-!
# `cbv` support for fixed-width integer conversions

The `cbv` evaluator folds `+ - * &&& ||| ^^^ <<< >>> ~~~` on literals of the fixed-width types, but
not the conversions between them (`UInt64.toUInt32`, `UInt8.toUInt32`, `UInt32.toNat`, …), which it
then unfolds into raw structures such as `{ toBitVec := 1048576#32 }` that no longer look like
literals. These `cbv_eval` simprocs fold the conversions of literals. Each only replaces a closed
term by its value, so the step is definitional and checked by the kernel.
-/
namespace Solutions.Exec
open Lean Meta Sym

private def lit? (e : Expr) : Option Nat := (Sym.getNatValue? e).run

private def conv (f : Nat → Expr) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  let some n := lit? e.appArg! | return .rfl
  let r ← share (f n)
  return .step r (← Sym.mkEqRefl r)

cbv_simproc cbv_eval cbvU64toU32 (UInt64.toUInt32 _) := conv fun n => toExpr n.toUInt32
cbv_simproc cbv_eval cbvU64toU8 (UInt64.toUInt8 _) := conv fun n => toExpr n.toUInt8
cbv_simproc cbv_eval cbvU64toU16 (UInt64.toUInt16 _) := conv fun n => toExpr n.toUInt16
cbv_simproc cbv_eval cbvU64toNat (UInt64.toNat _) := conv fun n => toExpr (n % 2 ^ 64)
cbv_simproc cbv_eval cbvU32toU64 (UInt32.toUInt64 _) := conv fun n => toExpr (n % 2 ^ 32).toUInt64
cbv_simproc cbv_eval cbvU32toU8 (UInt32.toUInt8 _) := conv fun n => toExpr n.toUInt8
cbv_simproc cbv_eval cbvU32toU16 (UInt32.toUInt16 _) := conv fun n => toExpr n.toUInt16
cbv_simproc cbv_eval cbvU32toNat (UInt32.toNat _) := conv fun n => toExpr (n % 2 ^ 32)
cbv_simproc cbv_eval cbvU16toU32 (UInt16.toUInt32 _) := conv fun n => toExpr (n % 2 ^ 16).toUInt32
cbv_simproc cbv_eval cbvU16toU8 (UInt16.toUInt8 _) := conv fun n => toExpr n.toUInt8
cbv_simproc cbv_eval cbvU16toU64 (UInt16.toUInt64 _) := conv fun n => toExpr (n % 2 ^ 16).toUInt64
cbv_simproc cbv_eval cbvU16toNat (UInt16.toNat _) := conv fun n => toExpr (n % 2 ^ 16)
cbv_simproc cbv_eval cbvU8toU32 (UInt8.toUInt32 _) := conv fun n => toExpr (n % 2 ^ 8).toUInt32
cbv_simproc cbv_eval cbvU8toU16 (UInt8.toUInt16 _) := conv fun n => toExpr (n % 2 ^ 8).toUInt16
cbv_simproc cbv_eval cbvU8toU64 (UInt8.toUInt64 _) := conv fun n => toExpr (n % 2 ^ 8).toUInt64
cbv_simproc cbv_eval cbvU8toNat (UInt8.toNat _) := conv fun n => toExpr (n % 2 ^ 8)
cbv_simproc cbv_eval cbvNattoU32 (Nat.toUInt32 _) := conv fun n => toExpr n.toUInt32
cbv_simproc cbv_eval cbvNattoU8 (Nat.toUInt8 _) := conv fun n => toExpr n.toUInt8
cbv_simproc cbv_eval cbvNattoU64 (Nat.toUInt64 _) := conv fun n => toExpr n.toUInt64
cbv_simproc cbv_eval cbvNattoU16 (Nat.toUInt16 _) := conv fun n => toExpr n.toUInt16

end Solutions.Exec
