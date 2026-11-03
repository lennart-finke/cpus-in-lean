import Std.Tactic.BVDecide
import X64.Alu
import X64.Proofs.Basic
namespace X64
section
variable (a c : UInt64) (cf : Bool)

theorem shl64_res (h : c &&& 63 ≠ 0) :
    (shiftOp 4 8 a c cf).map (·.1) = some (a <<< (c &&& 63)) := by
  simp [shiftOp, Sz.bits, Sz.mask, Sz.msb, h]
  bv_decide

theorem shr64_res (h : c &&& 63 ≠ 0) :
    (shiftOp 5 8 a c cf).map (·.1) = some (a >>> (c &&& 63)) := by
  simp [shiftOp, Sz.bits, Sz.msb, h]
  bv_decide

theorem sar64_res (h : c &&& 63 ≠ 0) :
    (shiftOp 7 8 a c cf).map (·.1) = some (UInt64.ofBitVec (a.toBitVec.sshiftRight' (c &&& 63).toBitVec)) := by
  conv => lhs; simp [shiftOp, Sz.bits, Sz.mask, Sz.msb, h]
  simp only [Option.some.injEq]
  bv_decide

theorem shl64_cf (h : c &&& 63 ≠ 0) :
    (shiftOp 4 8 a c cf).map (fun r => r.2.2 &&& Flag.CF != 0) =
      some ((a >>> (64 - (c &&& 63))) &&& 1 != 0) := by
  simp [shiftOp, Sz.bits, Sz.mask, Sz.msb, h, AFlags.pack, logicCore,
    Flag.arith, Flag.CF, Flag.PF, Flag.ZF, Flag.SF, Flag.OF, parity, bne]
  bv_decide

theorem shr64_cf (h : c &&& 63 ≠ 0) :
    (shiftOp 5 8 a c cf).map (fun r => r.2.2 &&& Flag.CF != 0) =
      some ((a >>> ((c &&& 63) - 1)) &&& 1 != 0) := by
  simp [shiftOp, Sz.bits, Sz.msb, h, AFlags.pack, logicCore,
    Flag.arith, Flag.CF, Flag.PF, Flag.ZF, Flag.SF, Flag.OF, parity, bne]
  bv_decide

theorem shift_zero64 (op : UInt8) (h : c &&& 63 = 0) : shiftOp op 8 a c cf = none := by
  simp [shiftOp, h]

theorem shl32_res (h : c &&& 31 ≠ 0) :
    (shiftOp 4 4 (a &&& 0xFFFFFFFF) c cf).map (·.1) = some ((a <<< (c &&& 31)) &&& 0xFFFFFFFF) := by
  simp [shiftOp, Sz.bits, Sz.mask, Sz.msb, h]
  bv_decide
end
end X64
