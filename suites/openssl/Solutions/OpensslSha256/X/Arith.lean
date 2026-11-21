import Solutions.OpensslSha256.X.Shr
/-!
# The bit count update of `SHA256_Update` (`add`/`adc`), in `toNat` form

`lea (,%ebp,8),%eax; mov %ebp,%ecx; shr $29,%ecx; add %eax,Nl; adc %ecx,Nh`, as `cbv` leaves it.
-/
namespace Solutions.ShaX
open X86

theorem addF_toNat (a b c : UInt32) (hc : c.toNat ≤ 1) :
    (addF 4 a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  simp only [addF, addCore, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false]
  rw [UInt32.toNat_and, show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt32.toNat_toUInt64]
  have := a.toNat_lt; have := b.toNat_lt
  omega

theorem addF_cf (a b : UInt32) :
    ((addF 4 a b 0).2.land 1 = 0) ↔ a.toNat + b.toNat < 2 ^ 32 := by
  have h : (addF 4 a b 0).2.land 1 = cond (addCore 4 a b 0).2.cf 1 0 := by
    simp only [addF]; exact pack_and1 _
  rw [h]
  simp only [addCore, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false]
  have := a.toNat_lt; have := b.toNat_lt
  by_cases hlt : a.toNat + b.toNat < 2 ^ 32
  · have : (decide ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64) > (4294967295 : UInt32).toUInt64)) = false := by
      simp only [decide_eq_false_iff_not, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
        UInt32.toNat_toUInt64]
      simp; omega
    simp only [this, cond_false, hlt, iff_true]
  · have : (decide ((a.toUInt64 + b.toUInt64 + (0 : UInt32).toUInt64) > (4294967295 : UInt32).toUInt64)) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
        UInt32.toNat_toUInt64]
      simp; omega
    simp only [this, cond_true, hlt, iff_false]
    decide

theorem shl3_toNat (len : UInt32) : (UInt32.add 0 (len.shiftLeft 3)).toNat = 8 * len.toNat % 2 ^ 32 := by
  have e : UInt32.add 0 (len.shiftLeft 3) = len <<< (3 : UInt32) := UInt32.zero_add _
  have e2 : ∀ x y : UInt32, ShiftLeft.shiftLeft x y = HShiftLeft.hShiftLeft x y := fun _ _ => rfl
  rw [e]; simp only [e2]; rw [UInt32.toNat_shiftLeft]
  simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  omega

/-- The new `Nl`. -/
theorem nl_toNat (Nl len : UInt32) :
    (Nl.add (UInt32.add 0 (len.shiftLeft 3))).toNat = (Nl.toNat + 8 * len.toNat) % 2 ^ 32 := by
  have e : Nl.add (UInt32.add 0 (len.shiftLeft 3)) = Nl + UInt32.add 0 (len.shiftLeft 3) := rfl
  rw [e, UInt32.toNat_add, shl3_toNat]; omega

/-- The new `Nh`. -/
theorem nh_toNat (Nl Nh len : UInt32) :
    (addF 4 Nh (len.shiftRight 29)
      (if (Bool.rec true false (decide ((addF 4 Nl (UInt32.add 0 (len.shiftLeft 3)) 0).2.land 1 = 0)) : Bool) = true
        then 1 else 0)).1.toNat =
      (Nh.toNat + len.toNat / 2 ^ 29 % 2 ^ 32 +
        (if Nl.toNat % 2 ^ 32 + 8 * len.toNat % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32 := by
  have hs : (len.shiftRight 29).toNat = len.toNat / 2 ^ 29 % 2 ^ 32 := by
    have e : len.shiftRight 29 = len >>> (29 : UInt32) := rfl
    have e2 : ∀ x y : UInt32, ShiftRight.shiftRight x y = HShiftRight.hShiftRight x y := fun _ _ => rfl
    rw [e]; simp only [e2]; rw [UInt32.toNat_shiftRight]; simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have := len.toNat_lt; omega
  have hNl := Nl.toNat_lt
  by_cases hc : Nl.toNat + 8 * len.toNat % 2 ^ 32 < 2 ^ 32
  · have h1 : (addF 4 Nl (UInt32.add 0 (len.shiftLeft 3)) 0).2.land 1 = 0 :=
      (addF_cf _ _).2 (by rw [shl3_toNat]; exact hc)
    simp only [h1, decide_true]
    rw [addF_toNat _ _ _ (by decide), hs]
    simp only [show ¬ (Nl.toNat % 2 ^ 32 + 8 * len.toNat % 2 ^ 32 ≥ 2 ^ 32) by omega, ite_false]
    rfl
  · have h1 : ¬ (addF 4 Nl (UInt32.add 0 (len.shiftLeft 3)) 0).2.land 1 = 0 := fun h =>
      hc (by have := (addF_cf _ _).1 h; rw [shl3_toNat] at this; exact this)
    simp only [h1, decide_false]
    rw [addF_toNat _ _ _ (by decide), hs]
    simp only [show (Nl.toNat % 2 ^ 32 + 8 * len.toNat % 2 ^ 32 ≥ 2 ^ 32) by omega, ite_true]
    rfl

end Solutions.ShaX
