import Std.Tactic.BVDecide
import X86.Exec
import X86.Proofs.Basic
/-!
# Shifts, rotates and multiplication

32-bit shift/rotate results equal the `BitVec` operations for every count; the carry is
the last bit shifted out. One-operand IMUL's overflow flag is set exactly when the signed
product does not fit in 32 bits.
-/
namespace X86

section
variable (a c : UInt32) (cf : Bool)


theorem shl_res (h : c &&& 31 ≠ 0) :
    (shiftOp 4 4 a c cf).map (·.1) = some (a <<< (c &&& 31)) := by
  simp only [shiftOp, Sz.bits, Sz.mask, Sz.msb, shl64, shr64, shl32, shr32, bne]
  simp [h]; bv_decide

theorem shl_cf (h : c &&& 31 ≠ 0) :
    (shiftOp 4 4 a c cf).map (fun r => r.2.2 &&& Flag.CF != 0) =
      some ((a >>> (32 - (c &&& 31))) &&& 1 != 0) := by
  simp only [shiftOp, Sz.bits, Sz.mask, Sz.msb, shl64, shr64, shl32, shr32, bne]
  simp [h, Flag.CF, Flag.OF, Flag.PF, Flag.SF, Flag.ZF, Flag.AF, szp, Sz.msb, parity]; bv_decide

theorem shr_res (h : c &&& 31 ≠ 0) :
    (shiftOp 5 4 a c cf).map (·.1) = some (a >>> (c &&& 31)) := by
  simp only [shiftOp, Sz.bits, Sz.mask, Sz.msb, shl64, shr64, shl32, shr32, bne]
  simp [h]; bv_decide

theorem shr_cf (h : c &&& 31 ≠ 0) :
    (shiftOp 5 4 a c cf).map (fun r => r.2.2 &&& Flag.CF != 0) =
      some ((a >>> ((c &&& 31) - 1)) &&& 1 != 0) := by
  simp only [shiftOp, Sz.bits, Sz.mask, Sz.msb, shl64, shr64, shl32, shr32, bne]
  simp [h, Flag.CF, Flag.OF, Flag.PF, Flag.SF, Flag.ZF, Flag.AF, szp, Sz.msb, parity]; bv_decide

theorem sar_res (h : c &&& 31 ≠ 0) :
    (shiftOp 7 4 a c cf).map (·.1) = some (UInt32.ofBitVec (a.toBitVec.sshiftRight' (c &&& 31).toBitVec)) := by
  have h' : (c &&& 31 == 0) = false := by simpa using h
  simp only [shiftOp, Sz.bits, Sz.mask, Sz.msb, shl64, shr64, shl32, shr32, bne, h', Option.map]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq]
  bv_decide

/-- A masked count of zero leaves the operand and the flags alone. -/
theorem shift_zero (op : UInt8) (sz : Sz) (h : c &&& 31 = 0) : shiftOp op sz a c cf = none := by
  simp only [shiftOp] at *; simp [h]

end

theorem sext64_4 (a : UInt32) : sext64 4 a = a.toInt32.toInt64.toUInt64 := by
  simp only [sext64, sext, bne]; bv_decide

/-- IMUL r/m32: the 64-bit result is the signed product, and CF = OF is set exactly when it
does not fit in 32 bits. -/
theorem imul32 (a b : UInt32) :
    (imulCore 4 a b).1 = (a.toInt32.toInt64 * b.toInt32.toInt64).toUInt64 ∧
    (imulCore 4 a b).2 = decide ((a.toInt32.toInt64 * b.toInt32.toInt64) ≠
                                  (a.toInt32.toInt64 * b.toInt32.toInt64).toInt32.toInt64) := by
  simp only [imulCore, sext64_4, ← Int64.toUInt64_mul]
  generalize a.toInt32.toInt64 * b.toInt32.toInt64 = p
  simp only [sext64, sext, Sz.mask, bne]
  constructor
  · first | rfl | trivial
  · bv_decide

end X86
