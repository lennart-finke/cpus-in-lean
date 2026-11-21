import Solutions.OpensslX25519.I.TbMath
import Solutions.OpensslX25519.I.M121Arith
import Solutions.Exec.Bit
/-!
# The arithmetic of `fe_frombytes`: words as natural numbers

The operations of the run (`I/FbRun*`) as facts about `toNat` (prover Q): sums with a literal, `leal` shapes,
partial masks (`land_bits`: `a &&& (2^j - 2^s)` keeps bits `s … j-1`), subtraction, the carry of an addition
(`cfBit`, `bitU (cfB _)`), the 64-bit product by 19 and `shld`. The limbs, carries and values of `fe_frombytes`
(`fbH*`, `fbC*`, `fbh*`) as integers of the loaded words.
-/
namespace Solutions.OpensslX25519.I
open X86 Solutions.Exec Solutions.Exec.Mul Solutions.Exec.Shift Solutions.Exec.Bit Solutions.OpensslX25519

theorem tn_addk {v a b : UInt32} (k : Nat) (e : v = UInt32.add a b) (hb : b.toNat = k) :
    v.toNat = (a.toNat + k) % 2 ^ 32 := by
  rw [e, toNat_uadd, hb]

theorem tn_add2k {v a b c : UInt32} (k : Nat) (e : v = UInt32.add (UInt32.add a b) c) (hc : c.toNat = k) :
    v.toNat = ((a.toNat + b.toNat) % 2 ^ 32 + k) % 2 ^ 32 := by
  rw [e, toNat_uadd, toNat_uadd, hc]

theorem tn_shlk {v a b k : UInt32} (n m : Nat) (e : v = UInt32.add (UInt32.shiftLeft a k) b) (hk : k.toNat % 32 = n)
    (hb : b.toNat = m) : v.toNat = (a.toNat * 2 ^ n % 2 ^ 32 + m) % 2 ^ 32 := by
  rw [e, toNat_uadd, u32_shl, hk, nat_shl, hb]

theorem tn_leak {v a b c k : UInt32} (n m : Nat) (e : v = UInt32.add (UInt32.add a (UInt32.shiftLeft b k)) c)
    (hk : k.toNat % 32 = n) (hc : c.toNat = m) :
    v.toNat = ((a.toNat + b.toNat * 2 ^ n % 2 ^ 32) % 2 ^ 32 + m) % 2 ^ 32 := by
  rw [e, toNat_uadd, toNat_uadd, u32_shl, hk, nat_shl, hc]

theorem land_bits (a m j s : Nat) (hs : s ≤ 32) (ha : a < 2 ^ 32) (hm : m = (2 ^ j - 1) &&& (2 ^ 32 - 2 ^ s)) :
    a &&& m = a % 2 ^ j / 2 ^ s * 2 ^ s := by
  rw [hm, ← Nat.and_assoc, Nat.and_two_pow_sub_one_eq_mod,
    land_high _ _ hs (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem tn_landb {v a m : UInt32} (j s : Nat) (e : v = (logicF 4 (UInt32.land a m)).1) (hs : s ≤ 32)
    (hm : m.toNat = (2 ^ j - 1) &&& (2 ^ 32 - 2 ^ s)) : v.toNat = a.toNat % 2 ^ j / 2 ^ s * 2 ^ s := by
  rw [e, show (logicF 4 (UInt32.land a m)).1 = UInt32.land a m from rfl, show UInt32.land a m = a &&& m from rfl,
    UInt32.toNat_and]
  exact land_bits _ _ j s hs a.toNat_lt hm

theorem tn_sub {v a b : UInt32} (e : v = (subF 4 a b 0).1) : v.toNat = (a.toNat + 2 ^ 33 - b.toNat) % 2 ^ 32 := by
  rw [e, subF_fst_toNat a b 0 (by decide)]; rfl

theorem tn_adc {v a b g : UInt32} (e : v = (addF 4 a b (cfBit g)).1) :
    v.toNat = (a.toNat + b.toNat + (cfBit g).toNat) % 2 ^ 32 := by
  rw [e, addF_fst_toNat]

theorem tn_cf {g a b : UInt32} (e : g = (addF 4 a b 0).2) : (cfBit g).toNat = (a.toNat + b.toNat) / 2 ^ 32 := by
  rw [e, addF_cf]
  have := a.toNat_lt; have := b.toNat_lt
  split
  · rename_i h; simp only [UInt32.reduceToNat] at h ⊢; omega
  · rename_i h; simp only [UInt32.reduceToNat] at h ⊢; omega

theorem cfB_cfBit (g : UInt32) : (bitU (cfB g)).toNat = (cfBit g).toNat := by
  unfold bitU cfB cfBit b2u
  cases (g &&& Flag.CF != 0) <;> rfl

theorem tn_setb {v g : UInt32} (e : v = bitU (cfB g)) : v.toNat = (cfBit g).toNat := by
  rw [e, cfB_cfBit]

theorem tn_setb' {v g : UInt32} (e : v = UInt32.lor 0 (UInt32.land (bitU (cfB g)) 255)) :
    v.toNat = (cfBit g).toNat := by
  rw [e, ← cfB_cfBit]; unfold bitU; cases cfB g <;> rfl

theorem tn_mullo {v a : UInt32} (e : v = UInt64.toUInt32 (UInt64.mul (UInt32.toUInt64 a) 19)) :
    v.toNat = a.toNat * 19 % 2 ^ 32 := by
  have := a.toNat_lt
  rw [e, UInt64.toNat_toUInt32, show UInt64.mul (UInt32.toUInt64 a) 19 = a.toUInt64 * 19 from rfl, UInt64.toNat_mul,
    UInt32.toNat_toUInt64, show (19 : UInt64).toNat = 19 from rfl]
  omega

theorem tn_mulhi {v a : UInt32} (e : v = UInt64.toUInt32 (UInt64.shiftRight (UInt64.mul (UInt32.toUInt64 a) 19) 32)) :
    v.toNat = a.toNat * 19 / 2 ^ 32 := by
  have := a.toNat_lt
  rw [e, UInt64.toNat_toUInt32, u64_shr', show UInt64.mul (UInt32.toUInt64 a) 19 = a.toUInt64 * 19 from rfl,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, show (19 : UInt64).toNat = 19 from rfl,
    show (32 : UInt64).toNat % 64 = 32 from rfl]
  rw [Nat.mod_eq_of_lt (show a.toNat * 19 < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))

theorem tn_shld6 {v c a : UInt32} (e : v = sdR true c a 6) :
    v.toNat = (c.toNat * 2 ^ 32 + a.toNat) * 64 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
  rw [e, shld_toNat]

theorem tn_shld7 {v c a : UInt32} (e : v = sdR true c a 7) :
    v.toNat = (c.toNat * 2 ^ 32 + a.toNat) * 128 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
  rw [e, shld_toNat7]

/-- The word's signed value from a congruence and a range. -/
theorem sv_of_nat {w : UInt32} {E : Int} (h : (w.toNat : Int) = E % 2 ^ 32) (hb : -2 ^ 31 ≤ E ∧ E < 2 ^ 31) :
    sv w = E := sv_of_M32 h hb

end Solutions.OpensslX25519.I
