import X86.Alu
import X86.Proofs.Basic
/-!
# Correctness of DIV and IDIV

`divU`/`divS` are the pure cores of DIV/IDIV (see `Exec.grp3`). A successful division
satisfies the division identity with the remainder bounded by the divisor; #DE is raised
exactly for a zero divisor or a quotient that does not fit the destination.
-/
namespace X86

theorem divU_spec {sz : Sz} {a : UInt64} {d q r : UInt32} (hsz : sz.mask.toNat < 2^32)
    (h : divU sz a d = some (q, r)) :
    q.toNat * d.toNat + r.toNat = a.toNat ∧ r.toNat < d.toNat ∧ q.toNat ≤ sz.mask.toNat := by
  simp only [divU] at h
  split at h
  · contradiction
  · rename_i hd
    split at h
    · contradiction
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd0 : d.toNat ≠ 0 := by
        intro h0; apply hd; simp [UInt32.toNat_inj.mp (show d.toNat = (0:UInt32).toNat by simpa using h0)]
      have hqle : a.toNat / d.toNat ≤ sz.mask.toNat := by
        simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt32.toNat_toUInt64,
          Nat.not_lt] at hq
        exact hq
      have hlt : a.toNat % d.toNat < d.toNat := Nat.mod_lt _ (Nat.pos_of_ne_zero hd0)
      have hd32 : d.toNat < 2^32 := d.toNat_lt
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_div, UInt64.toNat_mod, UInt32.toNat_toUInt64]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, hlt, hqle⟩
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _

theorem divU_none {sz : Sz} {a : UInt64} {d : UInt32} :
    divU sz a d = none ↔ d = 0 ∨ a.toNat / d.toNat > sz.mask.toNat := by
  simp only [divU]
  split
  · rename_i hd; simp_all
  · rename_i hd
    have hd' : d ≠ 0 := by simpa using hd
    split
    · rename_i hq
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt32.toNat_toUInt64] at hq
      simp [hq]
    · rename_i hq
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt32.toNat_toUInt64] at hq
      simp [hd', hq]

theorem divS_spec {bits : Nat} {a d q r : Int} (h : divS bits a d = some (q, r)) :
    d * q + r = a ∧ r.natAbs < d.natAbs ∧ (r = 0 ∨ r.sign = a.sign) ∧
    -((2 ^ (bits - 1) : Nat) : Int) ≤ q ∧ q < ((2 ^ (bits - 1) : Nat) : Int) := by
  simp only [divS] at h
  split at h
  · contradiction
  · rename_i hd
    split at h
    · contradiction
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd0 : d ≠ 0 := by simpa using hd
      refine ⟨Int.mul_tdiv_add_tmod a d, ?_, ?_, ?_⟩
      · rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hd0)
      · by_cases hdvd : d ∣ a
        · left; exact Int.tmod_eq_zero_of_dvd hdvd
        · right; rw [Int.sign_tmod]; simp [hdvd]
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at hq
        omega

theorem divS_none {bits : Nat} {a d : Int} :
    divS bits a d = none ↔ d = 0 ∨ a.tdiv d ≥ ((2 ^ (bits - 1) : Nat) : Int) ∨
      a.tdiv d < -((2 ^ (bits - 1) : Nat) : Int) := by
  simp only [divS]
  split
  · rename_i hd; simp_all
  · rename_i hd
    have hd' : d ≠ 0 := by simpa using hd
    split <;> rename_i hq <;> simp_all

end X86
