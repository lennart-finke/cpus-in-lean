import Std.Tactic.BVDecide
import X86.Step
import X86.Proofs.Basic
/-!
# x87 transcendental instructions: out-of-range operands and exact cases
-/
namespace X86

/-- FSIN, FCOS, FPTAN and FSINCOS with a finite operand |x| ≥ 2^63 (outside the SDM's −2^63 < x <
2^63) leave the register stack untouched: the registers, the tags and TOP are unchanged, and C2 is
set. (FPTAN/FSINCOS: when ST(7) is free, so that there is no stack overflow.) -/
theorem fpTrig_out_of_range {m : Machine} {a : F80} (which : Nat) (h0 : m.cpu.stOpt 0 = some a)
    (h7 : (decide (which ≥ 2) && !m.cpu.stEmpty 7) = false)
    (hs : Trans.trigSpecial a = none) (hr : Trans.trigOutOfRange a = true) :
    ∃ m', fpTrig which m = .ok () m' ∧ m'.cpu.fpr = m.cpu.fpr ∧ m'.cpu.fempty = m.cpu.fempty ∧
      (m'.cpu.fsw >>> 11) &&& 7 = (m.cpu.fsw >>> 11) &&& 7 ∧ m'.cpu.fsw &&& 0x400 = 0x400 := by
  simp only [fpTrig, cpu, bind, EStateM.bind, h0, h7, hs, hr, fpStatus, fpSetC2, modCpu,
    Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩ <;> (simp only [shr16, FPF.C1]; bv_decide)

/-- The operand ranges of FSIN etc.: out of range means a biased exponent of at least 16383 + 63. -/
theorem trigOutOfRange_exp {a : F80} (h : Trans.trigOutOfRange a = true) : a.exp ≥ 16446 := by
  simp [Trans.trigOutOfRange] at h
  omega

/-- sin ±0 = ±0, tan ±0 = ±0 and cos ±0 = 1 exactly, without status flags. -/
theorem trigFinite_zero (which : Nat) {a : F80} (cw : UInt32) (h : a.isZero = true) :
    Trans.trigFinite which a cw = (if which == 1 then F80.one else a, 0) := by
  simp [Trans.trigFinite, h]

/-- F2XM1 at the ends of its domain is exact: 2^1 - 1 = 1 and 2^-1 - 1 = -1/2. -/
theorem f2xm1_one (cw : UInt32) : Trans.f2xm1 F80.one cw = (F80.one, 0) := rfl
theorem f2xm1_neg_one (cw : UInt32) :
    Trans.f2xm1 (F80.one.withNeg true) cw = ({ sig := 0x8000000000000000, se := 0xBFFE }, 0) := rfl

/-- F2XM1 outside its domain (|x| ≥ 2, including ±∞; the SDM leaves it undefined) is an invalid
operation with the QNaN indefinite as the masked result. -/
theorem f2xm1_out_of_domain {a : F80} (cw : UInt32) (hu : a.unsupported = false) (hn : a.isNaN = false)
    (he : a.exp > 16383) : Trans.f2xm1 a cw = (F80.indefinite, FPF.IE) := by
  have hz : a.isZero = false := by simp [F80.isZero]; omega
  simp [Trans.f2xm1, hu, hn, hz, he]

end X86
