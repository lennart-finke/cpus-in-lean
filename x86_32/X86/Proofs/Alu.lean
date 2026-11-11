import Std.Tactic.BVDecide
import X86.Alu
import X86.Proofs.Basic
/-!
# Correctness of the integer ALU

The flag computations of the model are proven equal to mathematical specifications
stated with `BitVec`/fixed-width integer comparisons. Most proofs are by `bv_decide`
(bit-blasting to SAT with a checked LRAT certificate).
-/
namespace X86

/-! ## ADD -/

theorem add_res (a b : UInt32) : (addCore 4 a b 0).1 = a + b := by
  simp only [addCore, Sz.mask]; bv_decide

theorem adc_res (a b : UInt32) (c : Bool) : (addCore 4 a b (b2u c)).1 = a + b + b2u c := by
  simp only [addCore, Sz.mask, b2u]; bv_decide

/-- CF after ADD is the unsigned carry out: the 32-bit sum wrapped around. -/
theorem add_cf (a b : UInt32) : (addCore 4 a b 0).2.cf = decide (a + b < a) := by
  simp only [addCore, Sz.mask]; bv_decide

/-- OF after ADD is signed overflow. -/
theorem add_of (a b : UInt32) :
    (addCore 4 a b 0).2.of = BitVec.saddOverflow a.toBitVec b.toBitVec := by
  simp only [addCore, Sz.mask, Sz.msb, bne]; bv_decide

theorem add_zf (a b : UInt32) : (addCore 4 a b 0).2.zf = decide (a + b = 0) := by
  simp only [addCore, Sz.mask]; bv_decide

theorem add_sf (a b : UInt32) : (addCore 4 a b 0).2.sf = (a + b).toBitVec.msb := by
  simp only [addCore, Sz.mask, Sz.msb, bne]; bv_decide

/-- 8-bit ADD on zero-extended operands: result and carry. -/
theorem add8 (a b : UInt32) (ha : a < 256) (hb : b < 256) :
    (addCore 1 a b 0).1 = (a.toUInt8 + b.toUInt8).toUInt32 ∧
    (addCore 1 a b 0).2.cf = decide (a.toUInt8 + b.toUInt8 < a.toUInt8) := by
  simp only [addCore, Sz.mask]; constructor <;> bv_decide

/-- 16-bit ADD on zero-extended operands: result, carry, overflow. -/
theorem add16 (a b : UInt32) (ha : a < 65536) (hb : b < 65536) :
    (addCore 2 a b 0).1 = (a.toUInt16 + b.toUInt16).toUInt32 ∧
    (addCore 2 a b 0).2.cf = decide (a.toUInt16 + b.toUInt16 < a.toUInt16) ∧
    (addCore 2 a b 0).2.of = BitVec.saddOverflow a.toUInt16.toBitVec b.toUInt16.toBitVec := by
  simp only [addCore, Sz.mask, Sz.msb, bne]; refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-! ## SUB / CMP -/

theorem sub_res (a b : UInt32) : (subCore 4 a b 0).1 = a - b := by
  simp only [subCore, Sz.mask]; bv_decide

theorem sbb_res (a b : UInt32) (c : Bool) : (subCore 4 a b (b2u c)).1 = a - b - b2u c := by
  simp only [subCore, Sz.mask, b2u]; bv_decide

/-- CF after CMP/SUB is unsigned borrow. -/
theorem sub_cf (a b : UInt32) : (subCore 4 a b 0).2.cf = decide (a < b) := by
  simp only [subCore, Sz.mask]; bv_decide

theorem sub_zf (a b : UInt32) : (subCore 4 a b 0).2.zf = decide (a = b) := by
  simp only [subCore, Sz.mask]; bv_decide

theorem sub_of (a b : UInt32) :
    (subCore 4 a b 0).2.of = BitVec.ssubOverflow a.toBitVec b.toBitVec := by
  simp only [subCore, Sz.mask, Sz.msb, bne]; bv_decide

/-- After CMP, SF ≠ OF exactly when `a < b` as signed integers. -/
theorem sub_slt (a b : UInt32) :
    ((subCore 4 a b 0).2.sf != (subCore 4 a b 0).2.of) = decide (a.toInt32 < b.toInt32) := by
  simp only [subCore, Sz.mask, Sz.msb, bne]; bv_decide

theorem sub_slt16 (a b : UInt32) (ha : a < 65536) (hb : b < 65536) :
    ((subCore 2 a b 0).2.sf != (subCore 2 a b 0).2.of) = decide (a.toUInt16.toInt16 < b.toUInt16.toInt16) := by
  simp only [subCore, Sz.mask, Sz.msb, bne]; bv_decide

theorem sub_slt8 (a b : UInt32) (ha : a < 256) (hb : b < 256) :
    ((subCore 1 a b 0).2.sf != (subCore 1 a b 0).2.of) = decide (a.toUInt8.toInt8 < b.toUInt8.toInt8) := by
  simp only [subCore, Sz.mask, Sz.msb, bne]; bv_decide

theorem sub_cf8 (a b : UInt32) (ha : a < 256) (hb : b < 256) :
    (subCore 1 a b 0).2.cf = decide (a < b) := by
  simp only [subCore, Sz.mask]; bv_decide

theorem sub_cf16 (a b : UInt32) (ha : a < 65536) (hb : b < 65536) :
    (subCore 2 a b 0).2.cf = decide (a < b) := by
  simp only [subCore, Sz.mask]; bv_decide

/-! ## Condition codes after CMP

`CMP a, b` followed by `Jcc`/`SETcc`/`CMOVcc` decides exactly the intended relation. -/

section cmp
variable (a b : UInt32)

theorem cc_o  : condB (subCore 4 a b 0).2 0x0 = BitVec.ssubOverflow a.toBitVec b.toBitVec := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_b  : condB (subCore 4 a b 0).2 0x2 = decide (a < b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_ae : condB (subCore 4 a b 0).2 0x3 = decide (a ≥ b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_e  : condB (subCore 4 a b 0).2 0x4 = decide (a = b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_ne : condB (subCore 4 a b 0).2 0x5 = decide (a ≠ b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_be : condB (subCore 4 a b 0).2 0x6 = decide (a ≤ b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_a  : condB (subCore 4 a b 0).2 0x7 = decide (a > b) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_s  : condB (subCore 4 a b 0).2 0x8 = (a - b).toBitVec.msb := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_l  : condB (subCore 4 a b 0).2 0xC = decide (a.toInt32 < b.toInt32) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_ge : condB (subCore 4 a b 0).2 0xD = decide (a.toInt32 ≥ b.toInt32) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_le : condB (subCore 4 a b 0).2 0xE = decide (a.toInt32 ≤ b.toInt32) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
theorem cc_g  : condB (subCore 4 a b 0).2 0xF = decide (a.toInt32 > b.toInt32) := by
  simp only [condB, subCore, Sz.mask, Sz.msb, bne]; bv_decide
end cmp

/-! ## Packing: the EFLAGS-level condition evaluation agrees with the unpacked one -/

theorem pack_cf (f : AFlags) : (f.pack &&& Flag.CF != 0) = f.cf := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_pf (f : AFlags) : (f.pack &&& Flag.PF != 0) = f.pf := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_zf (f : AFlags) : (f.pack &&& Flag.ZF != 0) = f.zf := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_sf (f : AFlags) : (f.pack &&& Flag.SF != 0) = f.sf := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_of (f : AFlags) : (f.pack &&& Flag.OF != 0) = f.of := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_cfzf (f : AFlags) : (f.pack &&& (Flag.CF ||| Flag.ZF) != 0) = (f.cf || f.zf) := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

/-- Flags are only ever placed in the six arithmetic positions. -/
theorem pack_arith (f : AFlags) : f.pack &&& ~~~Flag.arith = 0 := by
  rcases f with ⟨cf, pf, af, zf, sf, of⟩
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem evalCC_pack (f : AFlags) (cc : UInt8) : evalCC f.pack cc = condB f cc := by
  simp only [evalCC, condB, pack_cf, pack_zf, pack_sf, pack_of, pack_pf, pack_cfzf]

/-! ## Logic -/

theorem logic_flags (sz : Sz) (r : UInt32) :
    (logicCore sz r).2.cf = false ∧ (logicCore sz r).2.of = false ∧ (logicCore sz r).2.zf = (r == 0) := by
  simp [logicCore]

/-! ## Parity -/

/-- `parity` is the x86 PF: set iff the low byte has an even number of one bits. -/
theorem parity_spec (x : UInt32) :
    parity x = !(x.toBitVec.getLsbD 0 ^^ x.toBitVec.getLsbD 1 ^^ x.toBitVec.getLsbD 2 ^^
      x.toBitVec.getLsbD 3 ^^ x.toBitVec.getLsbD 4 ^^ x.toBitVec.getLsbD 5 ^^
      x.toBitVec.getLsbD 6 ^^ x.toBitVec.getLsbD 7) := by
  simp only [parity, shr32]; bv_decide

/-! ## Sign extension -/

theorem sext8 (x : UInt32) : sext 1 x = x.toUInt8.toInt8.toInt32.toUInt32 := by
  simp only [sext, bne]; bv_decide
theorem sext16 (x : UInt32) : sext 2 x = x.toUInt16.toInt16.toInt32.toUInt32 := by
  simp only [sext, bne]; bv_decide

end X86
