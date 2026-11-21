import Solutions.OpensslX25519.Pair
import Solutions.Logic.Cmp
/-!
# The values of the `cbv` normal forms as natural numbers

Each lemma states one normal form that the runs produce (`add`/`adc` with the carry, the 64-bit
product of `mul`, the low word of `imul`, shifts and masks, and the two carry tricks of
`poly1305_blocks`) as an equation over `toNat`.
-/
namespace Solutions.OpensslPoly1305
open X86 Solutions.Exec Solutions.Exec.Mul Solutions.OpensslX25519

theorem cfBit_le (g : UInt32) : (cfBit g).toNat ≤ 1 := by
  unfold cfBit b2u; split <;> decide

theorem add_sem (a b c : UInt32) (hc : c.toNat ≤ 1) :
    (addF 4 a b c).1.toNat + 2 ^ 32 * (cfBit (addF 4 a b c).2).toNat = a.toNat + b.toNat + c.toNat := by
  rw [addF_fst_toNat, addF_cf]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt
  split
  · show _ + 2 ^ 32 * 1 = _; omega
  · show _ + 2 ^ 32 * 0 = _; omega

theorem add_lo (a b c : UInt32) : (addF 4 a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 :=
  addF_fst_toNat a b c

theorem mul_sem (a b : UInt32) :
    (UInt64.toUInt32 (UInt64.mul (UInt32.toUInt64 a) (UInt32.toUInt64 b))).toNat +
      2 ^ 32 * (UInt64.toUInt32 (UInt64.shiftRight (UInt64.mul (UInt32.toUInt64 a) (UInt32.toUInt64 b)) 32)).toNat =
      a.toNat * b.toNat := by
  have h := pv_halves (UInt64.mul (UInt32.toUInt64 a) (UInt32.toUInt64 b))
  unfold pv at h
  have e : (UInt64.mul (UInt32.toUInt64 a) (UInt32.toUInt64 b)).toNat = a.toNat * b.toNat := by
    show (a.toUInt64 * b.toUInt64).toNat = _
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    have ha := a.toNat_lt; have hb := b.toNat_lt
    exact Nat.mod_eq_of_lt (by
      calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
        _ = 2 ^ 64 := by decide)
  rw [e] at h
  omega

theorem imul_sem (a b : UInt32) :
    (UInt32.land (UInt64.toUInt32 (imulCore 4 a b).1) 4294967295).toNat = a.toNat * b.toNat % 2 ^ 32 := by
  rw [land_ones]
  have h : ((imulCore 4 a b).1.toNat : Int) = sv a * sv b % 2 ^ 64 := by
    show (((sext64 4 a) * (sext64 4 b)).toNat : Int) = _
    rw [UInt64.toNat_mul, Int.natCast_emod, Int.natCast_mul, sext64_toNat, sext64_toNat,
      show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 from rfl]
    exact (Int.mul_emod _ _ _).symm
  rw [UInt64.toNat_toUInt32]
  have ha := sv_eq a; have hb := sv_eq b
  have := a.toNat_lt; have := b.toNat_lt
  show _ % 4294967296 = _ % 4294967296
  have h1 : (((imulCore 4 a b).1.toNat % 4294967296 : Nat) : Int) = (sv a * sv b) % 4294967296 := by
    rw [Int.natCast_emod, h]; exact Int.emod_emod_of_dvd _ ⟨4294967296, by decide⟩
  have h2 : (((a.toNat * b.toNat) % 4294967296 : Nat) : Int) = (sv a * sv b) % 4294967296 := by
    rw [Int.natCast_emod, Int.natCast_mul, Int.mul_emod, Int.mul_emod (sv a)]
    congr 2
    · rw [ha]; split <;> omega
    · rw [hb]; split <;> omega
  exact Int.ofNat_inj.mp (h1.trans h2.symm)

theorem shr_sem (a k : UInt32) (hk : k.toNat < 32) : (UInt32.shiftRight a k).toNat = a.toNat / 2 ^ k.toNat := by
  show (HShiftRight.hShiftRight a k : UInt32).toNat = _
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem uadd_sem (a b : UInt32) : (UInt32.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 := UInt32.toNat_add a b

theorem land3_sem (a : UInt32) : (UInt32.land a 3).toNat = a.toNat % 4 := by
  show (a &&& 3).toNat = _
  rw [UInt32.toNat_and, show (3 : UInt32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem nat_and_m4 (x : Nat) (hx : x < 2 ^ 32) : x &&& 4294967292 = 4 * (x / 4) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ex : x = 2 ^ 2 * (x / 4) + x % 4 := by omega
  rw [Nat.testBit_and, show 4 * (x / 4) = 2 ^ 2 * (x / 4) + 0 by omega, Nat.testBit_two_pow_mul_add _ (by decide),
    show (4294967292 : Nat) = 2 ^ 2 * (2 ^ 30 - 1) + 0 by decide, Nat.testBit_two_pow_mul_add _ (by decide)]
  rw [ex, Nat.testBit_two_pow_mul_add _ (by omega)]
  have hq : x / 4 < 2 ^ 30 := by omega
  rw [show (2 ^ 2 * (x / 4) + x % 4) / 4 = x / 4 by omega]
  split
  · simp [Nat.zero_testBit]
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases h : i - 2 < 30
    · simp [h]
    · have := Nat.testBit_lt_two_pow (i := i - 2) (Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h, this]

theorem landm4_sem (a : UInt32) : (UInt32.land a 4294967292).toNat = 4 * (a.toNat / 4) := by
  show (a &&& 4294967292).toNat = _
  rw [UInt32.toNat_and, show (4294967292 : UInt32).toNat = 4294967292 from rfl, nat_and_m4 _ a.toNat_lt]

/-! ## The carry tricks of `poly1305_blocks` -/

theorem bit_cases (x : Nat) (h : x < 2 ^ 32) : x / 2 ^ 31 = 0 ∨ x / 2 ^ 31 = 1 := by omega

/-- `CONSTANT_TIME_CARRY(s, c)` for `s = a + c`, as compiled: the carry of `a + c`. -/
theorem carry_xor (a c : UInt32) :
    (UInt32.shiftRight (logicF 4 (UInt32.xor (logicF 4 (UInt32.lor (logicF 4 (UInt32.xor c a)).1
      (logicF 4 (UInt32.xor (UInt32.add a c) c)).1)).1 (UInt32.add a c))).1 31).toNat =
      if 2 ^ 32 ≤ a.toNat + c.toNat then 1 else 0 := by
  simp only [Solutions.Logic.logicF_fst]
  rw [shr_sem _ _ (by decide)]
  show (((c ^^^ a) ||| ((UInt32.add a c) ^^^ c)) ^^^ (UInt32.add a c)).toNat / 2 ^ 31 = _
  rw [UInt32.toNat_xor, UInt32.toNat_or, UInt32.toNat_xor, UInt32.toNat_xor, uadd_sem,
    Nat.xor_div_two_pow, Nat.or_div_two_pow, Nat.xor_div_two_pow, Nat.xor_div_two_pow]
  have ha := a.toNat_lt; have hc := c.toNat_lt
  rcases bit_cases a.toNat ha with h1 | h1 <;> rcases bit_cases c.toNat hc with h2 | h2 <;>
    rcases bit_cases ((a.toNat + c.toNat) % 2 ^ 32) (Nat.mod_lt _ (by decide)) with h3 | h3 <;>
    rw [h1, h2, h3] <;> simp only [Nat.reduceXor, Nat.reduceOr] <;> split <;> omega

/-- The carry of `a + b` (`b ≤ 1`) as `(~(a + b) & a) >> 31`. -/
theorem carry_not (a b : UInt32) (hb : b.toNat ≤ 1) :
    (UInt32.shiftRight (UInt32.land (UInt32.land (UInt32.complement (addF 4 b a 0).1) 4294967295) a) 31).toNat =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  rw [shr_sem _ _ (by decide), land_ones]
  show ((~~~(addF 4 b a 0).1) &&& a).toNat / 2 ^ 31 = _
  rw [UInt32.toNat_and, UInt32.toNat_not, add_lo, Nat.and_div_two_pow]
  have ha := a.toNat_lt
  have hs : UInt32.size = 2 ^ 32 := rfl
  rw [hs]
  rcases bit_cases a.toNat ha with h1 | h1 <;>
    rcases bit_cases (2 ^ 32 - 1 - (b.toNat + a.toNat + (0 : UInt32).toNat) % 2 ^ 32) (by omega) with h3 | h3 <;>
    rw [h1, h3] <;> simp only [Nat.reduceAnd] <;> split <;> simp only [UInt32.toNat_zero] at * <;> omega

theorem carry_not' (a b : UInt32) (hb : b.toNat ≤ 1) :
    (UInt32.shiftRight (UInt32.land (UInt32.land (UInt32.complement (UInt32.add b a)) 4294967295) a) 31).toNat =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  have e : UInt32.add b a = (addF 4 b a 0).1 := (Solutions.Exec.addF_fst b a).symm
  rw [e]; exact carry_not a b hb

end Solutions.OpensslPoly1305
