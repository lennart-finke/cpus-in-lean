import X86.Word
/-!
# Proof infrastructure

The model elaborates `<<<`/`>>>` through the homogeneous `ShiftLeft`/`ShiftRight`
classes (see `X86.Word`); these lemmas bridge back to the standard heterogeneous form
that the `simp`/`bv_decide` libraries know about.
-/
namespace X86

@[simp] theorem shr8 (a b : UInt8) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
@[simp] theorem shl8 (a b : UInt8) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl
@[simp] theorem shr16 (a b : UInt16) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
@[simp] theorem shl16 (a b : UInt16) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl
@[simp] theorem shr32 (a b : UInt32) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
@[simp] theorem shl32 (a b : UInt32) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl
@[simp] theorem shr64 (a b : UInt64) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
@[simp] theorem shl64 (a b : UInt64) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl

end X86
