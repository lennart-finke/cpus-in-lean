import Solutions.OpensslSha256.X.FinGlue2
/-!
# `SHA256_Final` from `0x100236`: the branch on `md_len` and the digest words

`fin_D32`: `md_len = 32`: eight words `bsw H[i]` at `md + 4 i`; `fin_D28`: `md_len = 28`: seven.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem ctx0 (ctx : UInt32) : ctx + (4 * 0 : Nat).toUInt32 = ctx := UInt32.add_zero ctx

set_option maxHeartbeats 4000000 in
theorem fin_D32 (H : CMem) (V ctx out eax ecx edx ebp edi f sesi sedi sebx ra : UInt32) (ic : UInt64)
    (Hf : Array UInt32) (hF : FF H.get V ctx out 32) (hS : SVF H.get V sesi sedi sebx ra out)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hf[k]!)
    (hm : rdRaw H.get (ctx.add 108) 4 = 32) (hic : ic.toNat ≤ 2 ^ 42) :
    ∃ (H' : CMem) (f' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H.get, eax, ecx, edx, out, V.add 16, ebp, ctx, edi, 0x100236, efl f, ic⟩)
        (St.m ⟨H'.get, 1, 32, edx, sebx, V.add 40, ebp, sesi, sedi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 32) H.get H'.get ∧
      ∀ i, i < 8 → rdRaw H'.get (out + (4 * i).toUInt32) 4 = bsw Hf[i]! := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, hof, hoi, hoV, hoc⟩ := hF
  obtain ⟨s0, s1, s2, s3, s4⟩ := hS
  have g0 := hw 0 (by decide); rw [ctx0] at g0
  obtain ⟨f1, e1⟩ := fin_h32 H V ctx eax ecx edx out ebp edi f ic hsz hhi (by omega) hcf hci (by omega) hm
  have r1 := exN_run (img := img) 8 _ _ e1 (by show ic.toNat + 8 < 2 ^ 64; omega)
  obtain ⟨H1, f2, e2, hm2⟩ := fin_o1 H V ctx out Hf[0]! Hf[1]! Hf[2]! eax 32 edx ebp edi f1 (ic + 8) hsz hhi
    (by omega) hcf hci (by omega) hof hoi (by omega) (by omega) g0 (hw 1 (by decide)) (hw 2 (by decide))
  have i8 : (ic + 8).toNat = ic.toNat + 8 := u64_tN 8 (by decide) (by omega)
  have r2 := exN_run (img := img) 9 _ _ e2 (by show (ic + 8).toNat + 9 < 2 ^ 64; omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]
  have a1 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 32) H.get H1.get := by rw [hm2]; agw
  have rd1 : ∀ (j v : UInt32), j.toNat + 4 ≤ H.get.size → (j.toNat + 4 ≤ out.toNat ∨ out.toNat + 32 ≤ j.toNat) →
      rdRaw H.get j 4 = v → rdRaw H1.get j 4 = v := fun j v h1 h2 hv => by
    rw [rdRaw4_agree a1 h1 (fun k hk => by omega), hv]
  have i17 : (ic + 8 + 9).toNat = ic.toNat + 17 := by rw [u64_tN (ic := ic + 8) 9 (by decide) (by omega), i8]
  obtain ⟨H2, f3, e3, hm3⟩ := fin_o2 H1 V ctx out Hf[3]! Hf[4]! Hf[5]! (bsw Hf[2]!) 32 edx ebp edi f2 (ic + 8 + 9)
    (by omega) (by omega) (by omega) (by omega) hci (by omega) (by omega) hoi (by omega) (by omega)
    (rd1 _ _ (by ao) (by ao) (hw 3 (by decide))) (rd1 _ _ (by ao) (by ao) (hw 4 (by decide)))
    (rd1 _ _ (by ao) (by ao) (hw 5 (by decide)))
  have r3 := exN_run (img := img) 9 _ _ e3 (by show (ic + 8 + 9).toNat + 9 < 2 ^ 64; omega)
  have hS2 : H2.get.size = H.get.size := by rw [hm3]; simp only [Solutions.Exec.size_wrBytes]; exact hS1
  have a2 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 32) H1.get H2.get := by rw [hm3]; agw
  have a12 := a1.trans a2
  have rd2 : ∀ (j v : UInt32), j.toNat + 4 ≤ H.get.size → (j.toNat + 4 ≤ out.toNat ∨ out.toNat + 32 ≤ j.toNat) →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := fun j v h1 h2 hv => by
    rw [rdRaw4_agree a12 h1 (fun k hk => by omega), hv]
  have i26 : (ic + 8 + 9 + 9).toNat = ic.toNat + 26 := by rw [u64_tN (ic := ic + 8 + 9) 9 (by decide) (by omega), i17]
  obtain ⟨H3, f4, e4, hm4⟩ := fin_o3 H2 V ctx out Hf[6]! Hf[7]! sesi sedi sebx ra (bsw Hf[5]!) 32 edx ebp edi f3
    (ic + 8 + 9 + 9) (by omega) (by omega) (by omega) (by omega) hci (by omega) (by omega) hoi (by omega) (by omega)
    (rd2 _ _ (by ao) (by ao) (hw 6 (by decide))) (rd2 _ _ (by ao) (by ao) (hw 7 (by decide)))
    (rd2 _ _ (by ao) (by ao) s0) (rd2 _ _ (by ao) (by ao) s1) (rd2 _ _ (by ao) (by ao) s2) (rd2 _ _ (by ao) (by ao) s3)
  have r4 := exN_run (img := img) 11 _ _ e4 (by show (ic + 8 + 9 + 9).toNat + 11 < 2 ^ 64; omega)
  have a3 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 32) H2.get H3.get := by rw [hm4]; agw
  refine ⟨H3, f4, _, r1.trans (r2.trans (r3.trans r4)), a12.trans a3, fun i hi => ?_⟩
  have hs3 : H3.get.size = H.get.size := by rw [a3.1, hS2]
  have rdo : ∀ (j : UInt32) (v : UInt32), j.toNat + 4 ≤ out.toNat + 32 → out.toNat ≤ j.toNat →
      rdRaw H3.get j 4 = v → rdRaw H3.get j 4 = v := fun _ _ _ _ h => h
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ctx0, hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 4) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 8) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 12) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 16) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 20) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 24) 4 = _; rw [hm4]; rdv
  · show rdRaw H3.get (out.add 28) 4 = _; rw [hm4]; rdv

set_option maxHeartbeats 4000000 in
theorem fin_D28 (H : CMem) (V ctx out eax ecx edx ebp edi f sesi sedi sebx ra : UInt32) (ic : UInt64)
    (Hf : Array UInt32) (hF : FF H.get V ctx out 28) (hS : SVF H.get V sesi sedi sebx ra out)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hf[k]!)
    (hm : rdRaw H.get (ctx.add 108) 4 = 28) (hic : ic.toNat ≤ 2 ^ 42) :
    ∃ (H' : CMem) (f' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H.get, eax, ecx, edx, out, V.add 16, ebp, ctx, edi, 0x100236, efl f, ic⟩)
        (St.m ⟨H'.get, 1, 28, edx, sebx, V.add 40, ebp, sesi, sedi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 28) H.get H'.get ∧
      ∀ i, i < 7 → rdRaw H'.get (out + (4 * i).toUInt32) 4 = bsw Hf[i]! := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, hof, hoi, hoV, hoc⟩ := hF
  obtain ⟨s0, s1, s2, s3, s4⟩ := hS
  have g0 := hw 0 (by decide); rw [ctx0] at g0
  obtain ⟨f1, e1⟩ := fin_h28 H V ctx eax ecx edx out ebp edi f ic hsz hhi (by omega) hcf hci (by omega) hm
  have r1 := exN_run (img := img) 6 _ _ e1 (by show ic.toNat + 6 < 2 ^ 64; omega)
  obtain ⟨H1, f2, e2, hm2⟩ := fin_p1 H V ctx out Hf[0]! Hf[1]! Hf[2]! eax 28 edx ebp edi f1 (ic + 6) hsz hhi
    (by omega) hcf hci (by omega) hof hoi (by omega) (by omega) g0 (hw 1 (by decide)) (hw 2 (by decide))
  have i6 : (ic + 6).toNat = ic.toNat + 6 := u64_tN 6 (by decide) (by omega)
  have r2 := exN_run (img := img) 9 _ _ e2 (by show (ic + 6).toNat + 9 < 2 ^ 64; omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]
  have a1 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 28) H.get H1.get := by rw [hm2]; agw
  have rd1 : ∀ (j v : UInt32), j.toNat + 4 ≤ H.get.size → (j.toNat + 4 ≤ out.toNat ∨ out.toNat + 28 ≤ j.toNat) →
      rdRaw H.get j 4 = v → rdRaw H1.get j 4 = v := fun j v h1 h2 hv => by
    rw [rdRaw4_agree a1 h1 (fun k hk => by omega), hv]
  have i15 : (ic + 6 + 9).toNat = ic.toNat + 15 := by rw [u64_tN (ic := ic + 6) 9 (by decide) (by omega), i6]
  obtain ⟨H2, f3, e3, hm3⟩ := fin_p2 H1 V ctx out Hf[3]! Hf[4]! Hf[5]! (bsw Hf[2]!) 28 edx ebp edi f2 (ic + 6 + 9)
    (by omega) (by omega) (by omega) (by omega) hci (by omega) (by omega) hoi (by omega) (by omega)
    (rd1 _ _ (by ao) (by ao) (hw 3 (by decide))) (rd1 _ _ (by ao) (by ao) (hw 4 (by decide)))
    (rd1 _ _ (by ao) (by ao) (hw 5 (by decide)))
  have r3 := exN_run (img := img) 9 _ _ e3 (by show (ic + 6 + 9).toNat + 9 < 2 ^ 64; omega)
  have hS2 : H2.get.size = H.get.size := by rw [hm3]; simp only [Solutions.Exec.size_wrBytes]; exact hS1
  have a2 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 28) H1.get H2.get := by rw [hm3]; agw
  have a12 := a1.trans a2
  have rd2 : ∀ (j v : UInt32), j.toNat + 4 ≤ H.get.size → (j.toNat + 4 ≤ out.toNat ∨ out.toNat + 28 ≤ j.toNat) →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := fun j v h1 h2 hv => by
    rw [rdRaw4_agree a12 h1 (fun k hk => by omega), hv]
  have i24 : (ic + 6 + 9 + 9).toNat = ic.toNat + 24 := by rw [u64_tN (ic := ic + 6 + 9) 9 (by decide) (by omega), i15]
  obtain ⟨H3, f4, e4, hm4⟩ := fin_p3 H2 V ctx out Hf[6]! sesi sedi sebx ra (bsw Hf[5]!) 28 edx ebp edi f3
    (ic + 6 + 9 + 9) (by omega) (by omega) (by omega) (by omega) hci (by omega) (by omega) hoi (by omega) (by omega)
    (rd2 _ _ (by ao) (by ao) (hw 6 (by decide)))
    (rd2 _ _ (by ao) (by ao) s0) (rd2 _ _ (by ao) (by ao) s1) (rd2 _ _ (by ao) (by ao) s2) (rd2 _ _ (by ao) (by ao) s3)
  have r4 := exN_run (img := img) 9 _ _ e4 (by show (ic + 6 + 9 + 9).toNat + 9 < 2 ^ 64; omega)
  have a3 : AgreeOn (fun a => out.toNat ≤ a ∧ a < out.toNat + 28) H2.get H3.get := by rw [hm4]; agw
  refine ⟨H3, f4, _, r1.trans (r2.trans (r3.trans r4)), a12.trans a3, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ctx0, hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 4) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 8) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv; rw [hm2]; rdv
  · show rdRaw H3.get (out.add 12) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 16) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 20) 4 = _; rw [hm4]; rdv; rw [hm3]; rdv
  · show rdRaw H3.get (out.add 24) 4 = _; rw [hm4]; rdv

end Solutions.ShaX
