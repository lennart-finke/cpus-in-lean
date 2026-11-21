import Solutions.OpensslChacha20.Loops
import Solutions.OpensslChacha20.RunUtil
/-!
# The copy loop of `memcpy`, 64 iterations
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

/-- After `i` iterations: the first `i` bytes at `dst` are those at `src` in `M0`, and nothing else
changed. -/
def Copied (M0 M : ByteArray) (dst src : UInt32) (i : Nat) : Prop :=
  AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + 64) M0 M ∧
  ∀ k, k < i → M.get! (dst.toNat + k) = M0.get! (src.toNat + k)

theorem toUInt32_succ (i : Nat) : UInt32.add i.toUInt32 1 = (i + 1).toUInt32 := by
  apply UInt32.toNat_inj.1
  show (i.toUInt32 + 1).toNat = _
  simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

theorem toUInt32_toNat {i : Nat} (h : i < 2 ^ 32) : (i.toUInt32).toNat = i := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem u64_step (ic : UInt64) (a b : Nat) : ic + a.toUInt64 + (OfNat.ofNat b : UInt64) = ic + (a + b).toUInt64 := by
  rw [UInt64.add_assoc]
  congr 1
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  show _ = (a + b) % 2 ^ 64
  have : (OfNat.ofNat b : UInt64).toNat = b % 2 ^ 64 := rfl
  rw [this]
  omega

theorem copied_step {M0 M : ByteArray} {dst src : UInt32} {i : Nat} (h : Copied M0 M dst src i) (hi : i < 64)
    (hd : dst.toNat + 64 ≤ M0.size) (hs : src.toNat + 64 ≤ M0.size)
    (hdisj : dst.toNat + 64 ≤ src.toNat ∨ src.toNat + 64 ≤ dst.toNat) (hM : M0.size < 2 ^ 32) :
    Copied M0 (wrBytes M (dst.add i.toUInt32) 1 (UInt32.land (rdRaw M (src.add i.toUInt32) 1) 255)) dst src (i + 1) := by
  obtain ⟨ha, hb⟩ := h
  have hdi : (dst.add i.toUInt32).toNat = dst.toNat + i := by
    rw [toNat_uadd_of_lt] <;> rw [toUInt32_toNat (by omega)] <;> omega
  have hsi : (src.add i.toUInt32).toNat = src.toNat + i := by
    rw [toNat_uadd_of_lt] <;> rw [toUInt32_toNat (by omega)] <;> omega
  have hsz : M.size = M0.size := ha.1
  refine ⟨agreeOn_wrBytes1 ha (by rw [hsz, hdi]; omega) (by rw [hdi]; omega), fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [← hdi, get!_wr1_self (by rw [hdi, hsz]; omega), rdRaw1 (by rw [hsi, hsz]; omega), land255_toUInt8, hsi]
    exact ha.2 _ (by omega) (by omega)
  · rw [get!_wr1_other (by rw [hdi, hsz]; omega) (by rw [hdi]; omega)]
    exact hb k (by omega)

theorem memcpy_loop (H0 : CMem) (u dst src ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H0.get.size ≤ 4273995776) (hd : ByteRegion H0.get.size dst 64) (hs : ByteRegion H0.get.size src 64)
    (hdisj : dst.toNat + 64 ≤ src.toNat ∨ src.toNat + 64 ≤ dst.toNat) (hic : ic.toNat + 320 < 2 ^ 64) :
    ∃ (H : CMem) (f' ebx' : UInt32),
      Run img (St.m ⟨H0.get, dst, 64, src, ebx, u, ebp, 0, edi, 0x100420, efl f, ic⟩)
        (St.m ⟨H.get, dst, 64, src, ebx', u, ebp, 64, edi, 0x10042c, efl f', ic + (320 : Nat).toUInt64⟩) ∧
      Copied H0.get H.get dst src 64 := by
  -- the first 63 iterations
  have loop : ∀ i, i ≤ 63 → ∃ (H : CMem) (f' ebx' : UInt32),
      Run img (St.m ⟨H0.get, dst, 64, src, ebx, u, ebp, 0, edi, 0x100420, efl f, ic⟩)
        (St.m ⟨H.get, dst, 64, src, ebx', u, ebp, i.toUInt32, edi, 0x100420, efl f', ic + (5 * i).toUInt64⟩) ∧
      Copied H0.get H.get dst src i := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨H0, f, ebx, ?_, AgreeOn.refl _ _, fun k hk => absurd hk (by omega)⟩
      rw [show ic + (5 * 0 : Nat).toUInt64 = ic by simp]
      exact Run.refl _ _
    | succ i ih =>
      intro hi
      obtain ⟨H, f1, ebx1, hr, hc⟩ := ih (by omega)
      have hS : H.get.size = H0.get.size := hc.1.1
      obtain ⟨H', f2, e, hm⟩ := memcpy_cont H u dst src i.toUInt32 ebx1 ebp edi f1 (ic + (5 * i).toUInt64)
        (by rw [hS]; exact hsz) (by rw [hS]; exact hd) (by rw [hS]; exact hs)
        (by rw [toUInt32_toNat (by omega)]; omega)
      have hic' : (ic + (5 * i).toUInt64).toNat = ic.toNat + 5 * i := u64_add_toNat (by omega) (by omega)
      have hr2 := run_of_exN e (by show (ic + (5 * i).toUInt64).toNat + 5 < 2 ^ 64; rw [hic']; omega)
      rw [toUInt32_succ, u64_step] at hr2
      refine ⟨H', f2, rdRaw H.get (src.add i.toUInt32) 1, hr.trans hr2, ?_⟩
      rw [hm]
      exact copied_step hc (by omega) hd.1 hs.1 hdisj (by omega)
  obtain ⟨H, f1, ebx1, hr, hc⟩ := loop 63 (by omega)
  have hS : H.get.size = H0.get.size := hc.1.1
  obtain ⟨H', f2, e, hm⟩ := memcpy_exit H u dst src (63 : Nat).toUInt32 ebx1 ebp edi f1 (ic + (5 * 63).toUInt64)
    (by rw [hS]; exact hsz) (by rw [hS]; exact hd) (by rw [hS]; exact hs) (by decide)
  have hic' : (ic + (5 * 63).toUInt64).toNat = ic.toNat + 5 * 63 := u64_add_toNat (by omega) (by omega)
  have hr2 := run_of_exN e (by show (ic + (5 * 63).toUInt64).toNat + 5 < 2 ^ 64; rw [hic']; omega)
  rw [toUInt32_succ, u64_step] at hr2
  refine ⟨H', f2, _, hr.trans hr2, ?_⟩
  rw [hm]
  exact copied_step hc (by omega) hd.1 hs.1 hdisj (by omega)

end Solutions.OpensslChacha20
