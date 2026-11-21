import Solutions.OpensslSha256.X.FinOut
/-!
# `SHA256_Final` from its first instruction, for any return address and stack (`fin_core`)
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (Good hOf tailOf tailOf_length hashWords_one hashWords_two)

set_option maxHeartbeats 4000000 in
theorem fin_core (H : CMem) (V ctx out ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64) (olen : Nat)
    (H0 : Array UInt32) (mdN : Nat) (msg : List UInt8) (hF : FF H.get V ctx out olen)
    (hra : rdRaw H.get (V.add 36) 4 = ra) (ho : rdRaw H.get (V.add 40) 4 = out) (hc : rdRaw H.get (V.add 44) 4 = ctx)
    (hC : CtxOk H.get ctx (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
      (msg.length % 64).toUInt32 mdN.toUInt32 (tailOf msg))
    (hlt : msg.length < Spec.Sha256.lenBound) (holen : (olen = 32 ∧ mdN = 32) ∨ (olen = 28 ∧ mdN = 28))
    (hic : ic.toNat ≤ 2 ^ 40) :
    ∃ (H' : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, V.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩)
        (St.m ⟨H'.get, 1, ecx', edx', ebx, V.add 40, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 112 ∨
        out.toNat ≤ a ∧ a < out.toNat + olen) H.get H'.get ∧
      (∀ i, i < olen / 4 → rdRaw H'.get (out + (4 * i).toUInt32) 4 = bsw (Spec.Sha256.hashWords H0 msg)[i]!) ∧
      (∀ i, i < 68 → H'.get.get! (ctx.toNat + 40 + i) = 0) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, hof, hoi, hoV, hoc⟩ := hF'
  have hT := tailOf_length msg
  have hn : ((msg.length % 64).toUInt32).toNat = (tailOf msg).length := by rw [hT]; exact toUInt32_lt (by omega)
  have hmd : (mdN.toUInt32 = 32 ∧ olen = 32) ∨ (mdN.toUInt32 = 28 ∧ olen = 28) := by
    rcases holen with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2 <;> simp [h1]
  -- the two paddings up to `0x100206`
  obtain ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hSV, Hw1, pre, hpl, hb3, hw3, hE⟩ :
      ∃ (H3 : CMem) (eax3 ecx3 edx3 f3 : UInt32) (ic3 : UInt64), ic3.toNat ≤ ic.toNat + 2 ^ 20 ∧
        Run img (St.m ⟨H.get, eax, ecx, edx, ebx, V.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩)
          (St.m ⟨H3.get, eax3, ecx3, edx3, out, V.add 12, ebp, ctx, ctx.add 40, 0x100206, efl f3, ic3⟩) ∧
        AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32 ∨
          ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 104) H.get H3.get ∧ SVF H3.get V esi edi ebx ra out ∧
        ∃ (Hw1 : Array UInt32) (pre : List UInt8), pre.length = 56 ∧
          (∀ i, i < 56 → H3.get.get! (ctx.toNat + 40 + i) = pre[i]!) ∧
          (∀ k, k < 8 → rdRaw H3.get (ctx + (4 * k).toUInt32) 4 = Hw1[k]!) ∧
          Ssl.Spec.Sha256.compress Hw1 (pre ++ be32 (8 * msg.length / 2 ^ 32).toUInt32 ++
            be32 (8 * msg.length).toUInt32) = Spec.Sha256.hashWords H0 msg := by
    by_cases h55 : (tailOf msg).length ≤ 55
    · obtain ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hSV, hb3⟩ := fin_A H V ctx out ra _ eax ecx edx ebx ebp
        esi edi f ic olen (tailOf msg) hF hra ho hc hC.num hn hC.buf h55 hic
      refine ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3.mono fun a h => by omega, hSV, hOf H0 msg, _,
        by simp; omega, hb3, words_agree a3 (fun a h1 h2 h3 => by omega) hcf hsz hC.h, ?_⟩
      rw [hashWords_one H0 msg (by omega) hlt, hT]
    · obtain ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hSV, hw3, hz3⟩ := fin_B H V ctx out ra _ eax ecx edx ebx ebp
        esi edi f ic olen (tailOf msg) (hOf H0 msg) hF hra ho hc hC.num hn hC.buf (by omega) (by omega) hC.h hic
      refine ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hSV, _, List.replicate 56 0, by simp,
        fun i hi => by rw [hz3 i hi, getElem!_pos _ i (by simp; omega), List.getElem_replicate], hw3, ?_⟩
      rw [hashWords_two H0 msg (by omega) hlt, hT]
  have hS3 : H3.get.size = H.get.size := a3.1
  have rd3 : ∀ (j v : UInt32), (j.toNat = ctx.toNat + 32 ∨ j.toNat = ctx.toNat + 36 ∨ j.toNat = ctx.toNat + 108) →
      rdRaw H.get j 4 = v → rdRaw H3.get j 4 = v := fun j v hj hv => by
    rw [rdRaw4_agree a3 (by omega) (fun k hk => by omega), hv]
  obtain ⟨H4, eax4, ecx4, edx4, f4, ic4, hic4, r4, a4, hw4, hz4⟩ := fin_C H3 V ctx out eax3 ecx3 edx3 ebp f3 ic3 olen
    Hw1 pre (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32 (hF.size hS3) hpl hb3 hw3
    (rd3 _ _ (by ao) hC.nl) (rd3 _ _ (by ao) hC.nh) (by omega)
  rw [hE] at hw4
  have hS4 : H4.get.size = H.get.size := by rw [a4.1, hS3]
  have hSV4 := hSV.agree a4 (fun a h1 h2 h3 => by omega) (by omega) (by omega)
  have hmd4 : rdRaw H4.get (ctx.add 108) 4 = mdN.toUInt32 := by
    rw [rdRaw4_agree a4 (by ao) (fun k hk => by ao)]; exact rd3 _ _ (by ao) hC.md
  have a34 : AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 112)
      H.get H4.get := (a3.mono fun a h => by omega).trans (a4.mono fun a h => by omega)
  rcases hmd with ⟨h32, hol⟩ | ⟨h28, hol⟩
  · subst hol
    obtain ⟨H5, f5, ic5, r5, a5, hw5⟩ := fin_D32 H4 V ctx out eax4 ecx4 edx4 ebp (ctx.add 40) f4 esi edi ebx ra ic4
      _ (hF.size hS4) hSV4 hw4 (by rw [hmd4, h32]) (by omega)
    refine ⟨H5, 32, edx4, f5, ic5, r3.trans (r4.trans r5), (a34.mono fun a h => by omega).trans
      (a5.mono fun a h => by omega), hw5, fun i hi => ?_⟩
    rw [a5.2 _ (by omega) (by omega)]; exact hz4 i hi
  · subst hol
    obtain ⟨H5, f5, ic5, r5, a5, hw5⟩ := fin_D28 H4 V ctx out eax4 ecx4 edx4 ebp (ctx.add 40) f4 esi edi ebx ra ic4
      _ (hF.size hS4) hSV4 hw4 (by rw [hmd4, h28]) (by omega)
    refine ⟨H5, 28, edx4, f5, ic5, r3.trans (r4.trans r5), (a34.mono fun a h => by omega).trans
      (a5.mono fun a h => by omega), hw5, fun i hi => ?_⟩
    rw [a5.2 _ (by omega) (by omega)]; exact hz4 i hi

end Solutions.ShaX
