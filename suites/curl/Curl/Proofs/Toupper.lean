import Curl.Proofs.Code
import Curl.Spec.Hostcheck
/-!
# `Curl_touppermap`

The 256-byte table at `0x100E4C` that `Curl_raw_toupper` reads maps `a`–`z` to `A`–`Z` and every
other byte to itself (checked by evaluation), so two bytes have the same image exactly when the
specification's `lower` agrees on them.
-/
namespace Curl.Proofs
open Curl.Hostcheck Curl.Spec.Hostcheck

/-- ASCII upper case. -/
def upper (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

set_option maxRecDepth 100000 in
theorem touppermap_eq : ∀ c, c < 256 → (Image.byte (0xE4C + c)).toNat = upper c := by
  decide +kernel

theorem lower_toNat (c : UInt8) : (lower c).toNat = if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat + 32 else c.toNat := by
  unfold lower
  have := c.toNat_lt
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have h1 : (0x41 ≤ c && c ≤ 0x5A) = true := by
      simp [UInt8.le_iff_toNat_le]; omega
    rw [if_pos h1, if_pos h, UInt8.toNat_add]; simp; omega
  · have h1 : (0x41 ≤ c && c ≤ 0x5A) = false := by
      simp [UInt8.le_iff_toNat_le]; omega
    rw [if_neg (by simp [h1]), if_neg h]

/-- Equal upper case exactly when equal lower case. -/
theorem upper_eq_iff (a b : UInt8) : upper a.toNat = upper b.toNat ↔ lower a = lower b := by
  rw [← UInt8.toNat_inj, lower_toNat, lower_toNat]
  have := a.toNat_lt; have := b.toNat_lt
  unfold upper
  constructor <;> intro h <;> split at h <;> split at h <;> split <;> split <;> omega

end Curl.Proofs
