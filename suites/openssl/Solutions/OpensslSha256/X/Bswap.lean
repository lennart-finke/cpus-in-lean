import Solutions.OpensslSha256.X.Shr
/-!
# `bswap`, as `cbv` leaves it, and its bytes

`bsw x` is the value `bswap` computes (the form of the execution layer); its little-endian bytes are
the big-endian bytes of `x` (`bsw_b0`..`bsw_b3`).
-/
namespace Solutions.ShaX

/-- `bswap`, as `cbv` leaves it. -/
def bsw (x : UInt32) : UInt32 :=
  (((x.shiftLeft 24).lor ((x.land 65280).shiftLeft 8)).lor ((x.shiftRight 8).land 65280)).lor (x.shiftRight 24)

theorem bsw_bit (x : UInt32) (i : Nat) (hi : i < 32) :
    (bsw x).toBitVec.getLsbD i = x.toBitVec.getLsbD (8 * (3 - i / 8) + i % 8) := by
  have h65 : ∀ j, j < 32 → (UInt32.toBitVec 65280).getLsbD j = decide (8 ≤ j ∧ j < 16) := by decide
  have g : ∀ j, 32 ≤ j → x.toBitVec.getLsbD j = false := fun j hj => BitVec.getLsbD_of_ge _ j hj
  have eo : ∀ a b : UInt32, (UInt32.lor a b).toBitVec = a.toBitVec ||| b.toBitVec := fun _ _ => rfl
  have ea : ∀ a b : UInt32, (UInt32.land a b).toBitVec = a.toBitVec &&& b.toBitVec := fun _ _ => rfl
  have s24 : ∀ a : UInt32, (UInt32.shiftLeft a 24).toBitVec = a.toBitVec <<< 24 := fun _ => rfl
  have s8 : ∀ a : UInt32, (UInt32.shiftLeft a 8).toBitVec = a.toBitVec <<< 8 := fun _ => rfl
  have r8 : ∀ a : UInt32, (UInt32.shiftRight a 8).toBitVec = a.toBitVec >>> 8 := fun _ => rfl
  have r24 : ∀ a : UInt32, (UInt32.shiftRight a 24).toBitVec = a.toBitVec >>> 24 := fun _ => rfl
  unfold bsw
  simp only [eo, ea, s24, s8, r8, r24, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) := by omega
  rcases this with h | h | h | h
  · rw [show 8 * (3 - i / 8) + i % 8 = 24 + i by omega, h65 _ (by omega), h65 _ (by omega)]
    simp [show i < 24 by omega, show ¬ 8 ≤ i by omega, show i < 8 by omega]
  · rw [show 8 * (3 - i / 8) + i % 8 = 8 + i by omega, h65 _ (by omega), h65 _ (by omega)]
    simp [show i < 24 by omega, show ¬ i < 8 by omega, g (24 + i) (by omega), show ¬ 8 ≤ i - 8 by omega,
      show 8 ≤ i by omega, show i < 16 by omega]
  · rw [show 8 * (3 - i / 8) + i % 8 = i - 8 by omega, h65 _ (by omega), h65 _ (by omega)]
    simp [show i < 24 by omega, show ¬ i < 8 by omega, g (24 + i) (by omega), show ¬ i < 16 by omega,
      show 8 ≤ i - 8 by omega, show i - 8 < 16 by omega, show i < 32 by omega]
  · rw [show 8 * (3 - i / 8) + i % 8 = i - 24 by omega, h65 _ (by omega), h65 _ (by omega)]
    simp [show ¬ i < 24 by omega, g (24 + i) (by omega), g (8 + i) (by omega), show ¬ i - 8 < 16 by omega,
      show i < 32 by omega]

theorem bsw_b0 (x : UInt32) : (bsw x).toUInt8 = ((x >>> 24)).toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp only [BitVec.toNat_umod, UInt32.toNat_toBitVec, UInt32.reduceToNat, BitVec.toNat_ofNat,
    show (32 : BitVec 32).toNat = 32 from rfl, Nat.reduceMod]
  rw [bsw_bit x _ (by omega)]
  congr 1
  omega

theorem bsw_b1 (x : UInt32) : ((bsw x) >>> 8).toUInt8 = ((x >>> 16)).toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp only [BitVec.toNat_umod, UInt32.toNat_toBitVec, UInt32.reduceToNat, BitVec.toNat_ofNat,
    show (32 : BitVec 32).toNat = 32 from rfl, Nat.reduceMod]
  rw [bsw_bit x _ (by omega)]
  congr 1
  omega

theorem bsw_b2 (x : UInt32) : ((bsw x) >>> 16).toUInt8 = ((x >>> 8)).toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp only [BitVec.toNat_umod, UInt32.toNat_toBitVec, UInt32.reduceToNat, BitVec.toNat_ofNat,
    show (32 : BitVec 32).toNat = 32 from rfl, Nat.reduceMod]
  rw [bsw_bit x _ (by omega)]
  congr 1
  omega

theorem bsw_b3 (x : UInt32) : ((bsw x) >>> 24).toUInt8 = (x).toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp only [BitVec.toNat_umod, UInt32.toNat_toBitVec, UInt32.reduceToNat, BitVec.toNat_ofNat,
    show (32 : BitVec 32).toNat = 32 from rfl, Nat.reduceMod]
  rw [bsw_bit x _ (by omega)]
  congr 1
  omega

end Solutions.ShaX
