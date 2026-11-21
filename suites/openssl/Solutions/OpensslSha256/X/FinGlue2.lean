import Solutions.OpensslSha256.X.FinGlue
import Solutions.OpensslSha256.X.FinRun2
import Solutions.OpensslSha256.X.FinRun3
/-!
# `SHA256_Final` from `0x100206`: the length block, the wipe, the digest

`fin_C`: the bit count big-endian in bytes 56..63 of the block, the block function, `num = 0`, the
buffer wiped. `fin_D32`/`fin_D28`: the digest words byte-swapped to `md`, and the return.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem lenblk_get (pre : List UInt8) (nh nl : UInt32) (hp : pre.length = 56) (i : Nat) (hi : i < 64) :
    (pre ++ be32 nh ++ be32 nl)[i]! =
      if i < 56 then pre[i]! else if i < 60 then (le32 (bsw nh))[i - 56]! else (le32 (bsw nl))[i - 60]! := by
  have h4 : ∀ v : UInt32, (be32 v).length = 4 := fun v => by rw [← le32_bsw]; rfl
  rw [le32_bsw, le32_bsw, getElem!_pos _ i (by simp [h4]; omega)]
  by_cases h1 : i < 56
  · rw [if_pos h1, List.getElem_append_left (by simp [h4]; omega), List.getElem_append_left (by omega),
      getElem!_pos pre i (by omega)]
  · rw [if_neg h1]
    by_cases h2 : i < 60
    · rw [if_pos h2, List.getElem_append_left (by simp [h4]; omega), List.getElem_append_right (by omega),
        getElem!_pos _ _ (by rw [h4]; omega)]
      simp [hp]
    · rw [if_neg h2, List.getElem_append_right (by simp [h4]; omega), getElem!_pos _ _ (by rw [h4]; omega)]
      simp [hp, h4]

set_option maxHeartbeats 4000000 in
/-- The length block, its compression, the wipe. -/
theorem fin_C (H : CMem) (V ctx out eax ecx edx ebp f : UInt32) (ic : UInt64) (olen : Nat) (Hw1 : Array UInt32)
    (pre : List UInt8) (nl nh : UInt32) (hF : FF H.get V ctx out olen) (hpl : pre.length = 56)
    (hb : ∀ i, i < 56 → H.get.get! (ctx.toNat + 40 + i) = pre[i]!)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw1[k]!)
    (hnl : rdRaw H.get (ctx.add 32) 4 = nl) (hnh : rdRaw H.get (ctx.add 36) 4 = nh) (hic : ic.toNat ≤ 2 ^ 41) :
    ∃ (H4 : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 20 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, out, V.add 12, ebp, ctx, ctx.add 40, 0x100206, efl f, ic⟩)
        (St.m ⟨H4.get, eax', ecx', edx', out, V.add 16, ebp, ctx, ctx.add 40, 0x100236, efl f', ic'⟩) ∧
      AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32 ∨
        ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108) H.get H4.get ∧
      (∀ k, k < 8 → rdRaw H4.get (ctx + (4 * k).toUInt32) 4 =
        (Ssl.Spec.Sha256.compress Hw1 (pre ++ be32 nh ++ be32 nl))[k]!) ∧
      (∀ i, i < 68 → H4.get.get! (ctx.toNat + 40 + i) = 0) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, -, -, -, -⟩ := hF'
  have c40 : (ctx.add 40).toNat = ctx.toNat + 40 := by ao
  have c96 : (ctx.add 96).toNat = ctx.toNat + 96 := by ao
  have c100 : (ctx.add 100).toNat = ctx.toNat + 100 := by ao
  have c104 : (ctx.add 104).toNat = ctx.toNat + 104 := by ao
  obtain ⟨H1, f1, e1, hm1⟩ := fin_f H V ctx (ctx.add 40) nl nh eax ecx edx out ebp f ic hsz hhi (by omega) hcf hci
    (by omega) hnl hnh
  have r1 := exN_run (img := img) 11 _ _ e1 (by show ic.toNat + 11 < 2 ^ 64; omega)
  have i1 : (ic + 11).toNat = ic.toNat + 11 := u64_tN 11 (by decide) (by omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have a1 : AgreeOn (fun a => V.toNat + 16 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat + 96 ≤ a ∧ a < ctx.toNat + 104)
      H.get H1.get := by rw [hm1]; agw
  have g16 : rdRaw H1.get (V.add 16) 4 = 0x100224 := by rw [hm1]; rdv
  have g20 : rdRaw H1.get (V.add 20) 4 = (1 : Nat).toUInt32 := by rw [hm1]; rdv; rfl
  have g96 : rdRaw H1.get (ctx.add 96) 4 = bsw nh := by rw [hm1]; rdv
  have g100 : rdRaw H1.get (ctx.add 100) 4 = bsw nl := by rw [hm1]; rdv
  have hw1 := words_agree a1 (fun a h1 h2 h3 => by omega) hcf hsz hw
  have hbl : Solutions.OpensslSha256.blks H1.get (ctx.add 40) 0 1 =
      Ssl.Spec.Sha256.blocks (pre ++ be32 nh ++ be32 nl) := by
    have hl : (pre ++ be32 nh ++ be32 nl).length = 64 := by
      simp only [List.length_append, hpl, ← le32_bsw]; rfl
    refine blks_eq H1.get (ctx.add 40) (by omega) 1 0 _ (by omega) (by rw [hl]) (fun k hk => ?_)
    rw [lenblk_get pre nh nl hpl k (by omega), c40, Nat.mul_zero, Nat.add_zero]
    by_cases h1 : k < 56
    · rw [if_pos h1, a1.2 _ (by omega) (by omega)]; exact hb k h1
    · rw [if_neg h1]
      by_cases h2 : k < 60
      · rw [if_pos h2, show ctx.toNat + 40 + k = (ctx.add 96).toNat + (k - 56) by omega,
          get!_of_rdRaw4' (by omega) g96 (k - 56) (by omega), getElem!_pos _ _ (by rw [le32_length']; omega)]
      · rw [if_neg h2, show ctx.toNat + 40 + k = (ctx.add 100).toNat + (k - 60) by omega,
          get!_of_rdRaw4' (by omega) g100 (k - 60) (by omega), getElem!_pos _ _ (by rw [le32_length']; omega)]
  obtain ⟨H2, fl2, eax2, ecx2, edx2, r2, a2, hw2⟩ := bdo_U H1 V ctx (ctx.add 40) 1 Hw1 0x100224 (bsw nl) out ebp ctx
    (ctx.add 40) f1 (ic + 11) (by omega) hlo (by omega) (by omega) (by omega) hci (by omega) (by decide) (by decide)
    (by omega) (by unfold OffCode; omega) (by omega) (by omega) g16 g20 hw1 (by omega)
  rw [hbl, Solutions.OpensslSha256.blocks_one _ (by simp only [List.length_append, hpl, ← le32_bsw]; rfl)] at hw2
  have hS2 : H2.get.size = H.get.size := by rw [a2.1, hS1]
  have i2 : (ic + 11 + (4029 * 1 + 38 : Nat).toUInt64).toNat = ic.toNat + 11 + 4067 := by
    rw [u64_toNat_add (by omega), i1]
  obtain ⟨H3, f3, e3, hm3⟩ := fin_g H2 V ctx (ctx.add 40) eax2 ecx2 edx2 out ebp fl2
    (ic + 11 + (4029 * 1 + 38 : Nat).toUInt64) (by omega) (by omega) (by omega) (by omega) hci (by omega)
  have r3 := exN_run (img := img) 5 _ _ e3 (by
    show (ic + 11 + (4029 * 1 + 38 : Nat).toUInt64).toNat + 5 < 2 ^ 64; omega)
  have hS3 : H3.get.size = H.get.size := by rw [hm3]; simp only [Solutions.Exec.size_wrBytes]; exact hS2
  have a3 : AgreeOn (fun a => V.toNat + 12 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat + 104 ≤ a ∧ a < ctx.toNat + 108)
      H2.get H3.get := by rw [hm3]; agw
  have k12 : rdRaw H3.get (V.add 12) 4 = 0x100236 := by rw [hm3]; rdv
  have k16 : rdRaw H3.get (V.add 16) 4 = ctx.add 40 := by rw [hm3]; rdv
  have k20 : rdRaw H3.get (V.add 20) 4 = 64 := by rw [hm3]; rdv
  have k104 : rdRaw H3.get (ctx.add 104) 4 = 0 := by rw [hm3]; rdv
  have h64 : (64 : UInt32).toNat = 64 := rfl
  have tW : (V - 8).toNat = V.toNat - 8 := tS (y := 8) 8 rfl (by omega)
  obtain ⟨H4, eax4, ecx4, edx4, f4, ic4, hic4, r4, a4, hz4⟩ := cleanse_V H3 V 0x100236 (ctx.add 40) 64 eax2 ecx2
    edx2 out ebp ctx (ctx.add 40) f3 (ic + 11 + (4029 * 1 + 38 : Nat).toUInt64 + 5) (by omega) (by omega)
    (by omega) (by unfold OffCode; omega) k12 k16 k20 (by rw [h64]; omega) (by rw [h64]; unfold OffCode; omega)
    (by rw [h64]; omega) (by rw [h64, u64_tN 5 (by decide) (by omega)]; omega)
  rw [h64, c40] at a4 hz4
  refine ⟨H4, eax4, ecx4, edx4, f4, ic4, ?_, r1.trans (r2.trans (r3.trans r4)),
    (((a1.mono fun a h => by omega).trans (a2.mono fun a h => by omega)).trans (a3.mono fun a h => by omega)).trans
      (a4.mono fun a h => by omega), ?_, fun i hi => ?_⟩
  · rw [u64_tN 5 (by decide) (by omega)] at hic4; omega
  · have a34 : AgreeOn (fun a => V.toNat - 8 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108)
        H2.get H4.get := (a3.mono fun a h => by omega).trans (a4.mono fun a h => by omega)
    exact words_agree a34 (fun a h1 h2 h3 => by omega) (by omega) (by omega) hw2
  · by_cases h1 : i < 64
    · exact hz4 i h1
    · rw [a4.2 _ (by omega) (by omega), show ctx.toNat + 40 + i = (ctx.add 104).toNat + (i - 64) by omega,
        get!_of_rdRaw4' (by omega) k104 (i - 64) (by omega)]
      have : i - 64 = 0 ∨ i - 64 = 1 ∨ i - 64 = 2 ∨ i - 64 = 3 := by omega
      rcases this with h | h | h | h <;> simp only [h] <;> rfl

end Solutions.ShaX
