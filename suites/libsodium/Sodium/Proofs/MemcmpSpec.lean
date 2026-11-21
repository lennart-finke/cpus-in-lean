/-!
# The accumulator of `sodium_memcmp`

The function ORs together the XORs of the bytes at the same positions; the result is zero exactly
when the buffers are equal (`acc_eq_zero_iff`).
-/
namespace Sodium.Proofs.Memcmp

/-- The OR of the XORs of the first `i` byte pairs. -/
def acc (a b : List UInt8) (i : Nat) : UInt8 :=
  ((List.range i).map fun k => a.getD k 0 ^^^ b.getD k 0).foldl (· ||| ·) 0

theorem acc_zero (a b : List UInt8) : acc a b 0 = 0 := rfl

theorem acc_succ (a b : List UInt8) (i : Nat) :
    acc a b (i + 1) = acc a b i ||| (a.getD i 0 ^^^ b.getD i 0) := by
  simp [acc, List.range_succ, List.foldl_append]

theorem or_eq_zero_iff (x y : UInt8) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h' := congrArg UInt8.toNat h
    rw [UInt8.toNat_or] at h'
    simp only [UInt8.toNat_zero] at h'
    have := Nat.or_eq_zero_iff.1 h'
    exact ⟨UInt8.toNat_inj.1 (by simpa using this.1), UInt8.toNat_inj.1 (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem xor_eq_zero_iff (x y : UInt8) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [UInt8.xor_assoc] using this
  · rintro rfl; exact UInt8.xor_self

theorem acc_eq_zero_iff_lt (a b : List UInt8) (i : Nat) :
    acc a b i = 0 ↔ ∀ k, k < i → a.getD k 0 = b.getD k 0 := by
  induction i with
  | zero => simp [acc_zero]
  | succ i ih =>
    rw [acc_succ, or_eq_zero_iff, ih, xor_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h i (by omega)⟩

theorem acc_eq_zero_iff (a b : List UInt8) (h : a.length = b.length) :
    acc a b a.length = 0 ↔ a = b := by
  rw [acc_eq_zero_iff_lt]
  constructor
  · intro hk
    apply List.ext_getElem h
    intro k h1 h2
    have := hk k h1
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this
  · rintro rfl k _; rfl

end Sodium.Proofs.Memcmp
