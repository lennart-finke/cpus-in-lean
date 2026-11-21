import Solutions.OpensslChacha20.MemcpyLoop
/-!
# The keystream xor loop of `ChaCha20_ctr32`, `n` iterations
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

/-- After `i` iterations: the first `i` output bytes are the keystream bytes (at `ks`) xor the input
bytes, and nothing else changed. -/
def Xored (M0 M : ByteArray) (out inp ks : UInt32) (i : Nat) : Prop :=
  AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + i) M0 M ∧
  ∀ k, k < i → M.get! (out.toNat + k) = M0.get! (ks.toNat + k) ^^^ M0.get! (inp.toNat + k)

theorem xored_step {M0 M : ByteArray} {out inp T : UInt32} {n i : Nat} (h : Xored M0 M out inp (T.add 64) i)
    (hi : i < n) (hn : n ≤ 64) (hT : T.toNat + 128 ≤ M0.size)
    (hin : inp.toNat + n ≤ M0.size) (hout : out.toNat + n ≤ M0.size)
    (hio : inp = out ∨ inp.toNat + n ≤ out.toNat ∨ out.toNat + n ≤ inp.toNat)
    (hko : T.toNat + 128 ≤ out.toNat ∨ out.toNat + n ≤ T.toNat + 64) (hM : M0.size < 2 ^ 32) :
    Xored M0 (wrBytes M (out.add i.toUInt32) 1
      (UInt32.land (xorReg (rdRaw M ((T.add i.toUInt32).add 64) 1) (rdRaw M (inp.add i.toUInt32) 1)) 255))
      out inp (T.add 64) (i + 1) := by
  obtain ⟨ha, hb⟩ := h
  have hsz : M.size = M0.size := ha.1
  have hoi : (out.add i.toUInt32).toNat = out.toNat + i := by
    rw [toNat_uadd_of_lt] <;> rw [toUInt32_toNat (by omega)] <;> omega
  have hii : (inp.add i.toUInt32).toNat = inp.toNat + i := by
    rw [toNat_uadd_of_lt] <;> rw [toUInt32_toNat (by omega)] <;> omega
  have hT64 : (T.add 64).toNat = T.toNat + 64 := by rw [toNat_uadd_of_lt] <;> simp <;> omega
  have hTi : (T.add i.toUInt32).toNat = T.toNat + i := by
    rw [toNat_uadd_of_lt] <;> rw [toUInt32_toNat (by omega)] <;> omega
  have hki : ((T.add i.toUInt32).add 64).toNat = T.toNat + 64 + i := by
    rw [toNat_uadd_of_lt (by rw [hTi]; simp; omega), hTi]; simp; omega
  refine ⟨agreeOn_wrBytes1 (AgreeOn.mono ha (fun a h => ⟨h.1, by omega⟩)) (by rw [hsz, hoi]; omega)
    (by rw [hoi]; omega), fun k hk => ?_⟩
  by_cases hk' : k = i
  · subst hk'
    rw [← hoi, get!_wr1_self (by rw [hoi, hsz]; omega), xorReg_toUInt8, rdRaw1 (by rw [hki, hsz]; omega),
      rdRaw1 (by rw [hii, hsz]; omega), UInt8.toUInt8_toUInt32, UInt8.toUInt8_toUInt32, hki, hii, hT64]
    rw [ha.2 _ (by omega) (by omega), ha.2 _ (by omega) (by rcases hio with rfl | hio <;> omega)]
  · rw [get!_wr1_other (by rw [hoi, hsz]; omega) (by rw [hoi]; omega)]
    exact hb k (by omega)

theorem xor_loop (H0 : CMem) (T rem inp out n ecx edx f : UInt32) (ic : UInt64)
    (hsz : H0.get.size ≤ 4273995776) (hT : ByteRegion H0.get.size (T.add 64) 64) (hTn : T.toNat + 128 < 2 ^ 32)
    (hin : ByteRegion H0.get.size inp n.toNat) (hout : ByteRegion H0.get.size out n.toNat)
    (hn1 : 1 ≤ n.toNat) (hn : n.toNat ≤ 64)
    (hio : inp = out ∨ inp.toNat + n.toNat ≤ out.toNat ∨ out.toNat + n.toNat ≤ inp.toNat)
    (hko : T.toNat + 128 ≤ out.toNat ∨ out.toNat + n.toNat ≤ T.toNat + 64)
    (hic : ic.toNat + 6 * n.toNat < 2 ^ 64) :
    ∃ (H : CMem) (f' ecx' : UInt32),
      Run img (St.m ⟨H0.get, 0, ecx, edx, rem, T, inp, out, n, 0x1000d0, efl f, ic⟩)
        (St.m ⟨H.get, n, ecx', edx, rem, T, inp, out, n, 0x1000e1, efl f', ic + (6 * n.toNat).toUInt64⟩) ∧
      Xored H0.get H.get out inp (T.add 64) n.toNat := by
  have hT64 : (T.add 64).toNat = T.toNat + 64 := by rw [toNat_uadd_of_lt] <;> simp <;> omega
  have hT' : T.toNat + 128 ≤ H0.get.size := by have := hT.1; omega
  have loop : ∀ i, i ≤ n.toNat - 1 → ∃ (H : CMem) (f' ecx' : UInt32),
      Run img (St.m ⟨H0.get, 0, ecx, edx, rem, T, inp, out, n, 0x1000d0, efl f, ic⟩)
        (St.m ⟨H.get, i.toUInt32, ecx', edx, rem, T, inp, out, n, 0x1000d0, efl f', ic + (6 * i).toUInt64⟩) ∧
      Xored H0.get H.get out inp (T.add 64) i := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨H0, f, ecx, ?_, AgreeOn.refl _ _, fun k hk => absurd hk (by omega)⟩
      rw [show ic + (6 * 0 : Nat).toUInt64 = ic by simp]
      exact Run.refl _ _
    | succ i ih =>
      intro hi
      obtain ⟨H, f1, ecx1, hr, hc⟩ := ih (by omega)
      have hS : H.get.size = H0.get.size := hc.1.1
      obtain ⟨H', f2, e, hm⟩ := xor_cont H T i.toUInt32 ecx1 edx rem inp out n f1 (ic + (6 * i).toUInt64)
        (by rw [hS]; exact hsz) (by rw [hS]; exact hT) hTn (by rw [hS]; exact hin) (by rw [hS]; exact hout) hn
        (by rw [toUInt32_toNat (by omega)]; omega)
      have hic' : (ic + (6 * i).toUInt64).toNat = ic.toNat + 6 * i := u64_add_toNat (by omega) (by omega)
      have hr2 := run_of_exN e (by show (ic + (6 * i).toUInt64).toNat + 6 < 2 ^ 64; rw [hic']; omega)
      rw [toUInt32_succ, u64_step] at hr2
      refine ⟨H', f2, _, hr.trans hr2, ?_⟩
      rw [hm]
      exact xored_step hc (by omega) hn hT' hin.1 hout.1 hio (by rw [hT64] at *; omega) (by omega)
  obtain ⟨H, f1, ecx1, hr, hc⟩ := loop (n.toNat - 1) (by omega)
  have hS : H.get.size = H0.get.size := hc.1.1
  obtain ⟨H', f2, e, hm⟩ := xor_exit H T (n.toNat - 1).toUInt32 ecx1 edx rem inp out n f1
    (ic + (6 * (n.toNat - 1)).toUInt64)
    (by rw [hS]; exact hsz) (by rw [hS]; exact hT) hTn (by rw [hS]; exact hin) (by rw [hS]; exact hout) hn
    (by rw [toUInt32_toNat (by omega)]; omega)
  have hic' : (ic + (6 * (n.toNat - 1)).toUInt64).toNat = ic.toNat + 6 * (n.toNat - 1) :=
    u64_add_toNat (by omega) (by omega)
  have hr2 := run_of_exN e (by show (ic + (6 * (n.toNat - 1)).toUInt64).toNat + 6 < 2 ^ 64; rw [hic']; omega)
  rw [toUInt32_succ, u64_step, Nat.sub_add_cancel hn1,
    show 6 * (n.toNat - 1) + 6 = 6 * n.toNat by omega] at hr2
  have hnn : n.toNat.toUInt32 = n := by
    apply UInt32.toNat_inj.1; rw [toUInt32_toNat n.toNat_lt]
  rw [hnn] at hr2
  refine ⟨H', f2, _, hr.trans hr2, ?_⟩
  rw [hm]
  have := xored_step hc (n := n.toNat) (by omega) hn hT' hin.1 hout.1 hio (by rw [hT64] at *; omega) (by omega)
  rwa [Nat.sub_add_cancel hn1] at this

end Solutions.OpensslChacha20
