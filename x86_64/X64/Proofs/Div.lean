import X64.Alu
namespace X64

/-- Unsigned division fails exactly on zero or an unrepresentable quotient. -/
theorem divU_none (sz : Sz) (a : Nat) (d : UInt64) :
    divU sz a d = none ↔ d = 0 ∨ a / d.toNat > sz.mask.toNat := by
  simp only [divU]
  split <;> rename_i hd
  · simp_all
  · split <;> simp_all

/-- Successful double-width division satisfies the mathematical division identity. -/
theorem divU_spec {sz : Sz} {a : Nat} {d q r : UInt64}
    (h : divU sz a d = some (q,r)) :
    d.toNat * q.toNat + r.toNat = a ∧ r.toNat < d.toNat ∧ q.toNat ≤ sz.mask.toNat := by
  simp only [divU] at h
  split at h
  · contradiction
  · rename_i hd
    split at h
    · contradiction
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hd0 : d.toNat ≠ 0 := by
        intro he; apply hd
        have hz : d = 0 := UInt64.toNat_inj.mp (show d.toNat = (0 : UInt64).toNat from he)
        simpa using hz
      have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hd0)
      have hbound := sz.mask.toNat_lt
      have hdBound := d.toNat_lt
      simp only [Nat.not_lt] at hq
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact ⟨Nat.div_add_mod a d.toNat, hr, hq⟩

/-- Signed division fails exactly on zero or an out-of-range signed quotient. -/
theorem divS_none (sz : Sz) (a d : Int) :
    divS sz a d = none ↔ d = 0 ∨
      a.tdiv d < -((2^(sz.bits.toNat - 1) : Nat) : Int) ∨
      a.tdiv d ≥ ((2^(sz.bits.toNat - 1) : Nat) : Int) := by
  simp only [divS]
  split <;> rename_i hd
  · simp_all
  · split <;> simp_all

/-- Successful signed division encodes the exact, bounded mathematical quotient
and remainder. The remainder has the dividend's sign (or is zero). -/
theorem divS_spec {sz : Sz} {a d : Int} {q r : UInt64}
    (h : divS sz a d = some (q,r)) :
    ∃ qi ri : Int, d * qi + ri = a ∧ ri.natAbs < d.natAbs ∧
      (ri = 0 ∨ ri.sign = a.sign) ∧
      -((2^(sz.bits.toNat-1) : Nat) : Int) ≤ qi ∧ qi < ((2^(sz.bits.toNat-1) : Nat) : Int) ∧
      q = (qi % (2^64 : Int)).toNat.toUInt64 ∧ r = (ri % (2^64 : Int)).toNat.toUInt64 := by
  simp only [divS] at h
  split at h
  · contradiction
  · rename_i hd
    split at h
    · contradiction
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hd0 : d ≠ 0 := by simpa using hd
      refine ⟨a.tdiv d, a.tmod d, Int.mul_tdiv_add_tmod a d, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hd0)
      · by_cases hdvd : d ∣ a
        · left; exact Int.tmod_eq_zero_of_dvd hdvd
        · right; rw [Int.sign_tmod]; simp [hdvd]
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at hq
        omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at hq
        omega

/-- The two mathematical halves of the unsigned product reconstruct the complete
product, including the 128-bit product used by MUL r/m64. -/
theorem mulWide_split (sz : Sz) (a b : UInt64) :
    2^sz.bits.toNat * (mulWide sz a b / 2^sz.bits.toNat) +
      mulWide sz a b % 2^sz.bits.toNat = (a &&& sz.mask).toNat * (b &&& sz.mask).toNat :=
  Nat.div_add_mod (mulWide sz a b) (2^sz.bits.toNat)

end X64
