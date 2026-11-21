import X86
/-!
# Values computed by the (opaque) ALU functions

`cbv` leaves `X86.addF`, `X86.subF`, … unevaluated (`Solutions.Exec.Step`); these lemmas give their
32-bit results.
-/
namespace Solutions.Exec
open X86

theorem addF_fst (a b : UInt32) : (addF 4 a b 0).1 = a + b := by
  simp only [addF, addCore, Sz.mask]
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt64.toNat_add, UInt32.toNat_toUInt64,
    UInt32.toNat_add]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false, UInt32.reduceToNat]
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem subF_fst (a b : UInt32) : (subF 4 a b 0).1 = a - b := by
  simp only [subF, subCore, Sz.mask]
  simp only [show ((4 : UInt8) == 1) = false by decide, show ((4 : UInt8) == 2) = false by decide,
    Bool.false_eq_true, ite_false]
  apply UInt32.toNat_inj.1
  rw [UInt32.toNat_and, show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
  simp

end Solutions.Exec
