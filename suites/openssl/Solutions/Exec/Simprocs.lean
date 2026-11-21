import Lean
/-!
# Ground evaluation of fixed-width bitwise operations

Core Lean has simprocs for `+ - * / %` and comparisons on literals of `UInt8/16/32/64`, but not
for the bitwise operations and conversions the model uses everywhere (`&&&`, `|||`, `^^^`, `~~~`,
`<<<`, `>>>`, `toUInt32`, …). These `dsimproc`s fold such operations on literals. They only replace
a closed term by its value, so every use is checked by the kernel as a definitional unfolding.
-/
namespace Solutions.Exec
open Lean Meta Simp

/-- A literal of one of the fixed-width types, as (type name, value). -/
def litU? (e : Expr) : MetaM (Option (Name × Nat)) := do
  for t in [``UInt8, ``UInt16, ``UInt32, ``UInt64] do
    if let some (n, _) ← getOfNatValue? e t then return some (t, n)
  return none

def widthOf : Name → Nat
  | ``UInt8 => 8 | ``UInt16 => 16 | ``UInt32 => 32 | _ => 64

def mkLitU (t : Name) (n : Nat) : Expr :=
  let n := n % 2 ^ widthOf t
  match t with
  | ``UInt8 => toExpr n.toUInt8
  | ``UInt16 => toExpr n.toUInt16
  | ``UInt32 => toExpr n.toUInt32
  | _ => toExpr n.toUInt64

def binU (op : Nat → Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  let some (t, a) ← litU? e.appFn!.appArg! | return .continue
  let some (t', b) ← litU? e.appArg! | return .continue
  unless t == t' do return .continue
  return .done <| mkLitU t (op (widthOf t) a b)

dsimproc [simp] reduceAndU (@HAnd.hAnd _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  binU (fun _ a b => a &&& b) e
dsimproc [simp] reduceOrU (@HOr.hOr _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HOr.hOr 6 do return .continue
  binU (fun _ a b => a ||| b) e
dsimproc [simp] reduceXorU (@HXor.hXor _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HXor.hXor 6 do return .continue
  binU (fun _ a b => a ^^^ b) e
dsimproc [simp] reduceShlU (@HShiftLeft.hShiftLeft _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HShiftLeft.hShiftLeft 6 do return .continue
  binU (fun w a b => a <<< (b % w)) e
dsimproc [simp] reduceShrU (@HShiftRight.hShiftRight _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HShiftRight.hShiftRight 6 do return .continue
  binU (fun w a b => a >>> (b % w)) e
dsimproc [simp] reduceNotU (@Complement.complement _ _ _) := fun e => do
  unless e.isAppOfArity ``Complement.complement 3 do return .continue
  let some (t, a) ← litU? e.appArg! | return .continue
  return .done <| mkLitU t (2 ^ widthOf t - 1 - a)

/-- `x.toUInt8`, `x.toUInt16`, `x.toUInt32`, `x.toUInt64` on a literal of a fixed-width type. -/
def convU (dst : Name) (e : Expr) : SimpM DStep := do
  let some (_, a) ← litU? e.appArg! | return .continue
  return .done <| mkLitU dst a

dsimproc [simp] reduceU8toU32 (UInt8.toUInt32 _) := convU ``UInt32
dsimproc [simp] reduceU8toU64 (UInt8.toUInt64 _) := convU ``UInt64
dsimproc [simp] reduceU8toU16 (UInt8.toUInt16 _) := convU ``UInt16
dsimproc [simp] reduceU16toU32 (UInt16.toUInt32 _) := convU ``UInt32
dsimproc [simp] reduceU16toU8 (UInt16.toUInt8 _) := convU ``UInt8
dsimproc [simp] reduceU16toU64 (UInt16.toUInt64 _) := convU ``UInt64
dsimproc [simp] reduceU32toU8 (UInt32.toUInt8 _) := convU ``UInt8
dsimproc [simp] reduceU32toU16 (UInt32.toUInt16 _) := convU ``UInt16
dsimproc [simp] reduceU32toU64 (UInt32.toUInt64 _) := convU ``UInt64
dsimproc [simp] reduceU64toU32 (UInt64.toUInt32 _) := convU ``UInt32
dsimproc [simp] reduceU64toU8 (UInt64.toUInt8 _) := convU ``UInt8
dsimproc [simp] reduceU64toU16 (UInt64.toUInt16 _) := convU ``UInt16

end Solutions.Exec
