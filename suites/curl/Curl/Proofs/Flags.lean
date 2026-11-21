import X86
import Solutions.Exec.Alu
/-!
# The arithmetic flags as propositions about `toNat`

`pdec P` is `decide P` under a name the `cbv` set-up of `Curl.Proofs.Sym` does not unfold. The flag
bits of `subF`, `logicF` and `addF` are stated here as `cond (pdec P) bit 0` with `P` a linear fact
about the operands' `toNat` (so that `omega` can decide it from the path condition), and the bits of
the EFLAGS forms `efl` and `mixF` are reduced to the bits of their parts.
-/
namespace Curl.Proofs
open X86

/-- `decide`, opaque to `cbv`. -/
def pdec (P : Prop) [Decidable P] : Bool := decide P

theorem pdec_true {P : Prop} [Decidable P] (h : P) : pdec P = true := by simp [pdec, h]
theorem pdec_false {P : Prop} [Decidable P] (h : ¬P) : pdec P = false := by simp [pdec, h]

theorem pdec_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : pdec P = pdec Q := by
  simp only [pdec]; exact decide_eq_decide.mpr h

/-- EFLAGS with arithmetic flags from `f` and everything else as `Ssl.entry` sets it. -/
def efl (f : UInt32) : UInt32 := 2 ||| (f &&& 0x8D5)

/-- The arithmetic flags of `f` replaced by those of `v` under `mask`. -/
def mixF (f v mask : UInt32) : UInt32 := (f &&& ~~~mask) ||| (v &&& mask)

/-! ## Bits -/

theorem nat_and_pow_eq_zero (n i : Nat) : (n &&& 2 ^ i = 0) ↔ n.testBit i = false := by
  constructor
  · intro h
    have := congrArg (Nat.testBit · i) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hij : i = j
    · subst hij; simp [h]
    · simp [hij]

theorem bit_ne_zero (x : UInt32) (i : Nat) (hi : i < 32) :
    (x &&& (2 ^ i : Nat).toUInt32 != 0) = decide (x.toNat / 2 ^ i % 2 = 1) := by
  have h2 : ((2 ^ i : Nat).toUInt32).toNat = 2 ^ i := by
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hi)
  have e : (x &&& (2 ^ i : Nat).toUInt32 = 0) ↔ x.toNat.testBit i = false := by
    have hx : (x &&& (2 ^ i : Nat).toUInt32).toNat = x.toNat &&& 2 ^ i := by rw [UInt32.toNat_and, h2]
    constructor
    · intro h; rw [← nat_and_pow_eq_zero, ← hx, h]; rfl
    · intro h; apply UInt32.toNat_inj.mp; rw [hx]; exact (nat_and_pow_eq_zero _ _).mpr h
  rw [Nat.testBit_eq_decide_div_mod_eq] at e
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  rw [e]
  simp

theorem testBit_toNat (x : UInt32) (i : Nat) : x.toNat.testBit i = decide (x.toNat / 2 ^ i % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

theorem bit_xor (x y : UInt32) (i : Nat) :
    decide ((x ^^^ y).toNat / 2 ^ i % 2 = 1) = (decide (x.toNat / 2 ^ i % 2 = 1) != decide (y.toNat / 2 ^ i % 2 = 1)) := by
  rw [← testBit_toNat, ← testBit_toNat, ← testBit_toNat, UInt32.toNat_xor, Nat.testBit_xor]

theorem bit_and (x y : UInt32) (i : Nat) :
    decide ((x &&& y).toNat / 2 ^ i % 2 = 1) = (decide (x.toNat / 2 ^ i % 2 = 1) && decide (y.toNat / 2 ^ i % 2 = 1)) := by
  rw [← testBit_toNat, ← testBit_toNat, ← testBit_toNat, UInt32.toNat_and, Nat.testBit_and]

/-! ## Packed flags -/

theorem pack_cf (f : AFlags) : f.pack &&& 1 = cond f.cf 1 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_zf (f : AFlags) : f.pack &&& 64 = cond f.zf 64 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_sf (f : AFlags) : f.pack &&& 128 = cond f.sf 128 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_of (f : AFlags) : f.pack &&& 2048 = cond f.of 2048 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide
theorem pack_cz (f : AFlags) : f.pack &&& 65 = cond f.cf 1 0 ||| cond f.zf 64 0 := by
  cases f with | mk cf pf af zf sf of =>
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

/-! ## `sub`/`cmp` -/

theorem sub_toNat (a b : UInt32) : (a - b).toNat = (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32 := by
  rw [UInt32.toNat_sub]; omega

theorem subCore_cf (sz : Sz) (a b : UInt32) : (subCore sz a b 0).2.cf = pdec (a.toNat < b.toNat) := by
  simp only [subCore, pdec]
  rw [decide_eq_decide]
  simp [UInt64.lt_iff_toNat_lt]

theorem subCore4_zf (a b : UInt32) : (subCore 4 a b 0).2.zf = pdec (a.toNat = b.toNat) := by
  simp only [subCore, pdec, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, UInt32.sub_zero]
  have : (a - b &&& 0xFFFFFFFF) = a - b := UInt32.toNat_inj.mp (by
    rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt32.toNat_lt _)])
  rw [this]
  by_cases h : a = b
  · subst h; simp
  · have h1 : a - b ≠ 0 := by intro e; apply h; have := congrArg (· + b) e; simpa using this
    have h2 : a.toNat ≠ b.toNat := fun e => h (UInt32.toNat_inj.mp e)
    simp [h1, h2]

theorem subCore1_zf (a b : UInt32) :
    (subCore 1 a b 0).2.zf = pdec ((a.toNat + (2 ^ 32 - b.toNat)) % 256 = 0) := by
  simp only [subCore, pdec, Sz.mask]
  simp only [show ((1 : UInt8) == 1) = true by decide, ite_true, UInt32.sub_zero]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e
    have := congrArg UInt32.toNat e
    rw [UInt32.toNat_and, show (0xFF : UInt32).toNat = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      sub_toNat] at this
    simp at this; omega
  · intro e
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and, show (0xFF : UInt32).toNat = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      sub_toNat]
    simp; omega

theorem subCore4_sf (a b : UInt32) :
    (subCore 4 a b 0).2.sf = pdec (2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32) := by
  simp only [subCore, pdec, Sz.mask, Sz.msb]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, UInt32.sub_zero]
  have e1 : (a - b &&& 0xFFFFFFFF) = a - b := UInt32.toNat_inj.mp (by
    rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt32.toNat_lt _)])
  rw [e1, show (0x80000000 : UInt32) = (2 ^ 31 : Nat).toUInt32 by decide, bit_ne_zero _ 31 (by decide),
    sub_toNat]
  rw [decide_eq_decide]
  have := (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32 |> fun x => Nat.mod_lt (a.toNat + (2 ^ 32 - b.toNat)) (show 2 ^ 32 > 0 by decide)
  omega

theorem subCore4_of (a b : UInt32) :
    (subCore 4 a b 0).2.of = pdec ((2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ b.toNat) ∧
      (2 ^ 31 ≤ a.toNat ↔ ¬ 2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32)) := by
  simp only [subCore, pdec, Sz.mask, Sz.msb]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, UInt32.sub_zero]
  have e1 : (a - b &&& 0xFFFFFFFF) = a - b := UInt32.toNat_inj.mp (by
    rw [UInt32.toNat_and, show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt32.toNat_lt _)])
  rw [e1, show (0x80000000 : UInt32) = (2 ^ 31 : Nat).toUInt32 by decide, bit_ne_zero _ 31 (by decide),
    bit_and, bit_xor, bit_xor, sub_toNat]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hr := Nat.mod_lt (a.toNat + (2 ^ 32 - b.toNat)) (show 2 ^ 32 > 0 by decide)
  have k1 : decide (a.toNat / 2 ^ 31 % 2 = 1) = decide (2 ^ 31 ≤ a.toNat) := by rw [decide_eq_decide]; omega
  have k2 : decide (b.toNat / 2 ^ 31 % 2 = 1) = decide (2 ^ 31 ≤ b.toNat) := by rw [decide_eq_decide]; omega
  have k3 : decide ((a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32 / 2 ^ 31 % 2 = 1) =
      decide (2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32) := by rw [decide_eq_decide]; omega
  rw [k1, k2, k3]
  by_cases p : 2 ^ 31 ≤ a.toNat <;> by_cases q : 2 ^ 31 ≤ b.toNat <;>
    by_cases r : 2 ^ 31 ≤ (a.toNat + (2 ^ 32 - b.toNat)) % 2 ^ 32 <;> simp [p, q, r]

/-! ## `test`/`and`/`or`/`xor` -/

theorem logicCore_cf (sz : Sz) (r : UInt32) : (logicCore sz r).2.cf = false := rfl
theorem logicCore_of (sz : Sz) (r : UInt32) : (logicCore sz r).2.of = false := rfl
theorem logicCore_zf (sz : Sz) (r : UInt32) : (logicCore sz r).2.zf = pdec (r.toNat = 0) := by
  simp only [logicCore, pdec]
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => by rw [h]; rfl, fun h => UInt32.toNat_inj.mp h⟩
theorem logicCore4_sf (r : UInt32) : (logicCore 4 r).2.sf = pdec (2 ^ 31 ≤ r.toNat) := by
  simp only [logicCore, pdec, Sz.msb]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false]
  rw [show (0x80000000 : UInt32) = (2 ^ 31 : Nat).toUInt32 by decide, bit_ne_zero _ 31 (by decide),
    decide_eq_decide]
  have := r.toNat_lt; omega
theorem logicCore1_sf (r : UInt32) : (logicCore 1 r).2.sf = pdec (r.toNat / 128 % 2 = 1) := by
  simp only [logicCore, pdec, Sz.msb]
  simp only [show ((1 : UInt8) == 1) = true by decide, ite_true]
  rw [show (0x80 : UInt32) = (2 ^ 7 : Nat).toUInt32 by decide, bit_ne_zero _ 7 (by decide)]

/-! ## `add`/`inc` -/

theorem addCore_cf4 (a b : UInt32) : (addCore 4 a b 0).2.cf = pdec (2 ^ 32 ≤ a.toNat + b.toNat) := by
  simp only [addCore, pdec, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false]
  rw [decide_eq_decide]
  simp [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have := a.toNat_lt; have := b.toNat_lt
  omega

theorem addCore_zf4 (a b : UInt32) : (addCore 4 a b 0).2.zf = pdec ((a.toNat + b.toNat) % 2 ^ 32 = 0) := by
  have h := Solutions.Exec.addF_fst a b
  simp only [addF] at h
  simp only [addCore, pdec] at h ⊢
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  rw [h]
  constructor
  · intro e; have := congrArg UInt32.toNat e; rw [UInt32.toNat_add] at this; simpa using this
  · intro e; apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simpa using e

end Curl.Proofs
