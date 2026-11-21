import Solutions.OpensslSha256.X.UpdTail
import Solutions.OpensslSha256.X.UpdRun2
/-!
# `SHA256_Update` from `0x100111` (`num ≠ 0`)

`upd_small`: the chunk fits in the buffer: it is copied behind the `num` buffered bytes, `num += len`,
return. `upd_big`: the buffer is filled to 64 bytes from the chunk, the block function compresses it,
`num = 0`, the buffer is cleared; on to `0x10016b` with the rest of the chunk.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (blks)

set_option maxHeartbeats 2000000 in
theorem upd_small (H : CMem) (U ctx msg len num eax edx ebx f sesi sedi sebx sebp ra : UInt32) (ic : UInt64)
    (chunk : List UInt8) (hF : UF H.get U ctx) (hSV : SV H.get U sesi sedi sebx sebp ra)
    (hlen : chunk.length = len.toNat) (hl0 : 0 < len.toNat) (hM : MF H.get U ctx msg len.toNat)
    (hb : ∀ i, i < len.toNat → H.get.get! (msg.toNat + i) = chunk[i]!)
    (hn : rdRaw H.get (ctx.add 104) 4 = num) (hlt : ((num.add len).lor len).toNat < 64)
    (hlt' : num.toNat + len.toNat < 64) (hic : ic.toNat ≤ 2 ^ 49) :
    ∃ (H3 : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 41 ∧
      Run img (St.m ⟨H.get, eax, num, edx, ebx, U.add 24, len, ctx, msg, 0x100111, efl f, ic⟩)
        (St.m ⟨H3.get, 1, ecx', edx', sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat + 40 + num.toNat ≤ a ∧ a < ctx.toNat + 108)
        H.get H3.get ∧
      rdRaw H3.get (ctx.add 104) 4 = num + len ∧
      (∀ i, i < len.toNat → H3.get.get! (ctx.toNat + 40 + num.toNat + i) = chunk[i]!) := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF
  obtain ⟨s0, s1, s2, s3, s4⟩ := hSV
  have mf := hM.fit; have mi := hM.img; have ms := hM.stk; have mc := hM.c
  obtain ⟨H1, f1, e1, hm1⟩ := upd_as H U ctx msg len num eax edx ebx f ic hsz hhi (by omega) hlt
  have r1 := exN_run (img := img) 9 _ _ e1 (by show ic.toNat + 9 < 2 ^ 64; omega)
  have i1 : (ic + 9).toNat = ic.toNat + 9 := u64_tN 9 (by decide) (by omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have a1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24) H.get H1.get := by rw [hm1]; agw
  have g8 : rdRaw H1.get (U.add 8) 4 = 0x100127 := by rw [hm1]; rdv
  have g12 : rdRaw H1.get (U.add 12) 4 = (ctx.add num).add 40 := by rw [hm1]; rdv
  have g16 : rdRaw H1.get (U.add 16) 4 = msg := by rw [hm1]; rdv
  have g20 : rdRaw H1.get (U.add 20) 4 = len := by rw [hm1]; rdv
  have cd : ((ctx.add num).add 40).toNat = ctx.toNat + 40 + num.toNat := by ao
  obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r2, a2, hc2⟩ := memcpy_call H1 U 0x100127 ((ctx.add num).add 40) msg len
    ((ctx.add num).add 40) num edx ebx len ctx msg f1 (ic + 9) (by omega) (by omega) (by unfold OffCode; omega)
    g8 g12 g16 g20 (by omega) (by unfold OffCode; omega) (by omega) (by unfold OffCode; omega) (by omega)
    (by omega) (by omega) (by omega)
  have hS2 : H2.get.size = H.get.size := by rw [a2.1, hS1]
  have sv : ∀ (j : UInt32) (v : UInt32), (j.toNat = U.toNat + 24 ∨ j.toNat = U.toNat + 28 ∨
      j.toNat = U.toNat + 32 ∨ j.toNat = U.toNat + 36 ∨ j.toNat = U.toNat + 40 ∨ j.toNat = ctx.toNat + 104) →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := by
    intro j v hj hv
    rw [rdRaw4_agree a2 (by omega) (fun k hk => by omega), rdRaw4_agree a1 (by omega) (fun k hk => by omega), hv]
  obtain ⟨H3, f3, N, e3, hm3, hN⟩ := upd_se H2 U ctx msg len num sesi sedi sebx sebp ra eax2 ecx2 edx2 ebx f2 ic2
    (by omega) (by omega) (by omega) (by omega) hci (by omega) (sv _ _ (by ao) s0) (sv _ _ (by ao) s1)
    (sv _ _ (by ao) s2) (sv _ _ (by ao) s3) (sv _ _ (by ao) s4) (sv _ _ (by ao) hn)
  have r3 := exN_run (img := img) 9 _ _ e3 (by show ic2.toNat + 9 < 2 ^ 64; omega)
  have a3 : AgreeOn (fun a => ctx.toNat + 104 ≤ a ∧ a < ctx.toNat + 108) H2.get H3.get := by rw [hm3]; agw
  refine ⟨H3, ecx2, edx2, f3, ic2 + 9, ?_, r1.trans (r2.trans r3),
    ((a1.mono fun a h => Or.inl h).trans (a2.mono fun a h => by omega)).trans (a3.mono fun a h => by omega), ?_,
    fun i hi => ?_⟩
  · rw [u64_tN 9 (by decide) (by omega)]; omega
  · rw [hm3]; rdv; exact hN
  · rw [a3.2 _ (by omega) (by omega), ← cd, hc2 i hi, a1.2 _ (by omega) (by omega)]
    exact hb i hi

theorem buf_get (buf chunk : List UInt8) (k : Nat) (hk : k < 64) (hb : buf.length < 64)
    (hc : 64 - buf.length ≤ chunk.length) :
    (buf ++ chunk.take (64 - buf.length))[k]! = if k < buf.length then buf[k]! else chunk[k - buf.length]! := by
  have hl : (buf ++ chunk.take (64 - buf.length)).length = 64 := by
    rw [List.length_append, List.length_take]; omega
  rw [getElem!_pos _ k (by omega)]
  by_cases h : k < buf.length
  · rw [if_pos h, List.getElem_append_left h, getElem!_pos buf k h]
  · rw [if_neg h, List.getElem_append_right (by omega), List.getElem_take, getElem!_pos chunk _ (by omega)]

set_option maxHeartbeats 4000000 in
theorem upd_big (H : CMem) (U ctx msg len num eax edx ebx f : UInt32) (ic : UInt64)
    (chunk buf : List UInt8) (Hw : Array UInt32) (hF : UF H.get U ctx)
    (hlen : chunk.length = len.toNat) (hLl : len.toNat < 2 ^ 31) (hM : MF H.get U ctx msg len.toNat)
    (hb : ∀ i, i < len.toNat → H.get.get! (msg.toNat + i) = chunk[i]!)
    (hbuf : buf.length = num.toNat) (hn64 : num.toNat < 64)
    (hbb : ∀ i, i < num.toNat → H.get.get! (ctx.toNat + 40 + i) = buf[i]!)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw[k]!)
    (hlt : ¬ ((num.add len).lor len).toNat < 64) (hge : 64 ≤ num.toNat + len.toNat) (hic : ic.toNat ≤ 2 ^ 49) :
    ∃ (H6 : CMem) (eax' ecx' edx' L' P' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 41 ∧
      Run img (St.m ⟨H.get, eax, num, edx, ebx, U.add 24, len, ctx, msg, 0x100111, efl f, ic⟩)
        (St.m ⟨H6.get, eax', ecx', edx', 64 - num, U.add 24, L', ctx, P', 0x10016b, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat - 168 ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32 ∨
        ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108) H.get H6.get ∧
      L'.toNat = len.toNat - (64 - num.toNat) ∧ P'.toNat = msg.toNat + (64 - num.toNat) ∧
      (∀ k, k < 8 → rdRaw H6.get (ctx + (4 * k).toUInt32) 4 =
        ((Ssl.Spec.Sha256.blocks (buf ++ chunk.take (64 - buf.length))).foldl Ssl.Spec.Sha256.compress Hw)[k]!) ∧
      rdRaw H6.get (ctx.add 104) 4 = 0 := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF
  have mf := hM.fit; have mi := hM.img; have ms := hM.stk; have mc := hM.c
  obtain ⟨H1, f1, B, e1, hm1, hB⟩ := upd_ab H U ctx msg len num eax edx ebx f ic hsz hhi (by omega) hlt
  have hBn : B.toNat = 64 - num.toNat := by
    rw [hB, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show num.toNat ≤ 64; omega)]; rfl
  have r1 := exN_run (img := img) 11 _ _ e1 (by show ic.toNat + 11 < 2 ^ 64; omega)
  have i1 : (ic + 11).toNat = ic.toNat + 11 := u64_tN 11 (by decide) (by omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have a1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24) H.get H1.get := by rw [hm1]; agw
  have g8 : rdRaw H1.get (U.add 8) 4 = 0x10013e := by rw [hm1]; rdv
  have g12 : rdRaw H1.get (U.add 12) 4 = (ctx.add num).add 40 := by rw [hm1]; rdv
  have g16 : rdRaw H1.get (U.add 16) 4 = msg := by rw [hm1]; rdv
  have g20 : rdRaw H1.get (U.add 20) 4 = B := by rw [hm1]; rdv
  have cd : ((ctx.add num).add 40).toNat = ctx.toNat + 40 + num.toNat := by ao
  obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r2, a2, hc2⟩ := memcpy_call H1 U 0x10013e ((ctx.add num).add 40) msg B
    ((ctx.add num).add 40) num edx B len ctx msg f1 (ic + 11) (by omega) (by omega) (by unfold OffCode; omega)
    g8 g12 g16 g20 (by omega) (by unfold OffCode; omega) (by omega) (by unfold OffCode; omega) (by omega)
    (by omega) (by omega) (by omega)
  have hS2 : H2.get.size = H.get.size := by rw [a2.1, hS1]
  obtain ⟨H3, f3, e3, hm3⟩ := upd_b2 H2 U ctx eax2 ecx2 edx2 B len msg f2 ic2 (by omega) (by omega) (by omega)
  have r3 := exN_run (img := img) 5 _ _ e3 (by show ic2.toNat + 5 < 2 ^ 64; omega)
  have i3 : (ic2 + 5).toNat = ic2.toNat + 5 := u64_tN 5 (by decide) (by omega)
  have hS3 : H3.get.size = H.get.size := by rw [hm3]; simp only [Solutions.Exec.size_wrBytes]; exact hS2
  have a3 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24) H2.get H3.get := by rw [hm3]; agw
  have g16' : rdRaw H3.get (U.add 16) 4 = 0x10014d := by rw [hm3]; rdv
  have g20' : rdRaw H3.get (U.add 20) 4 = (1 : Nat).toUInt32 := by rw [hm3]; rdv; rfl
  have a123 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat + 40 + num.toNat ≤ a ∧ a < ctx.toNat + 104)
      H.get H3.get :=
    ((a1.mono fun a h => Or.inl h).trans (a2.mono fun a h => by omega)).trans (a3.mono fun a h => Or.inl h)
  have hw3 := words_agree a123 (fun a h1 h2 h3 => by omega) hcf hsz hw
  have hbl : blks H3.get (ctx.add 40) 0 1 = Ssl.Spec.Sha256.blocks (buf ++ chunk.take (64 - buf.length)) := by
    have c40 : (ctx.add 40).toNat = ctx.toNat + 40 := by ao
    refine blks_eq H3.get (ctx.add 40) (by omega) 1 0 _ (by omega)
      (by rw [List.length_append, List.length_take]; omega) (fun k hk => ?_)
    rw [buf_get buf chunk k (by omega) (by omega) (by omega), c40, Nat.mul_zero, Nat.add_zero]
    by_cases hk' : k < buf.length
    · rw [if_pos hk', a123.2 _ (by omega) (by omega)]
      exact hbb k (by omega)
    · rw [if_neg hk', a3.2 _ (by omega) (by omega),
        show ctx.toNat + 40 + k = ((ctx.add num).add 40).toNat + (k - num.toNat) by rw [cd]; omega,
        hc2 _ (by omega), a1.2 _ (by omega) (by omega), hb _ (by omega), hbuf]
  obtain ⟨H4, fl4, eax4, ecx4, edx4, r4, a4, hw4⟩ := bdo_U H3 U ctx (ctx.add 40) 1 Hw 0x10014d eax2 B len ctx msg
    f3 (ic2 + 5) (by omega) hlo (by omega) (by omega) (by omega) hci (by omega) (by decide) (by decide) (by ao)
    (by unfold OffCode; ao) (by ao) (by ao) g16' g20' hw3 (by omega)
  rw [hbl] at hw4
  have hS4 : H4.get.size = H.get.size := by rw [a4.1, hS3]
  have i4 : (ic2 + 5 + (4029 * 1 + 38 : Nat).toUInt64).toNat = ic2.toNat + 5 + 4067 := by
    rw [u64_toNat_add (by omega), i3]
  obtain ⟨H5, f5, L', P', e5, hm5, hL', hP'⟩ := upd_b3 H4 U ctx msg len B eax4 ecx4 edx4 fl4
    (ic2 + 5 + (4029 * 1 + 38 : Nat).toUInt64) (by omega) (by omega) (by omega) (by omega) hci (by omega)
  have r5 := exN_run (img := img) 9 _ _ e5 (by show (ic2 + 5 + (4029 * 1 + 38 : Nat).toUInt64).toNat + 9 < 2 ^ 64; omega)
  have i5 : (ic2 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 9).toNat = ic2.toNat + 5 + 4067 + 9 := by
    rw [u64_tN 9 (by decide) (by omega), i4]
  have hS5 : H5.get.size = H.get.size := by rw [hm5]; simp only [Solutions.Exec.size_wrBytes]; exact hS4
  have a5 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108)
      H4.get H5.get := by rw [hm5]; agw
  have k8 : rdRaw H5.get (U.add 8) 4 = 0x100168 := by rw [hm5]; rdv
  have k12 : rdRaw H5.get (U.add 12) 4 = ctx.add 40 := by rw [hm5]; rdv
  have k16 : rdRaw H5.get (U.add 16) 4 = 0 := by rw [hm5]; rdv
  have k20 : rdRaw H5.get (U.add 20) 4 = 64 := by rw [hm5]; rdv
  have h64 : (64 : UInt32).toNat = 64 := rfl
  obtain ⟨H6, eax6, ecx6, edx6, f6, ic6, hic6, r6, a6, hz6⟩ := memset_U H5 U 0x100168 (ctx.add 40) 0 64
    (ctx.add 40) ecx4 edx4 B L' ctx P' f5 (ic2 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 9) (by omega) (by omega)
    (by unfold OffCode; omega) k8 k12 k16 k20 (by rw [h64]; ao) (by rw [h64]; unfold OffCode; ao)
    (by rw [h64]; ao) (by rw [h64]; omega)
  rw [h64] at a6 hic6
  have c40' : (ctx.add 40).toNat = ctx.toNat + 40 := by ao
  rw [c40'] at a6 hz6
  have hS6 : H6.get.size = H.get.size := by rw [a6.1, hS5]
  obtain ⟨f7, e7⟩ := upd_b4 H6 U eax6 ecx6 edx6 B L' ctx P' f6 ic6 (by omega) (by omega) (by omega)
  have r7 := exN_run (img := img) 1 _ _ e7 (by show ic6.toNat + 1 < 2 ^ 64; omega)
  have hw6 := words_agree (a5.trans (a6.mono fun a h => by omega)) (fun a h1 h2 h3 => by omega) (by omega) (by omega) hw4
  refine ⟨H6, eax6, ecx6, edx6, L', P', f7, ic6 + 1, ?_, ?_, ?_, ?_, ?_, hw6, ?_⟩
  · rw [u64_tN 1 (by decide) (by omega)]; omega
  · rw [← hB]; exact r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7)))))
  · exact ((a123.mono fun a h => by omega).trans (a4.mono fun a h => by omega)).trans
      ((a5.mono fun a h => by omega).trans (a6.mono fun a h => by omega))
  · rw [hL', UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega), hBn]
  · rw [hP', UInt32.toNat_add, hBn]; exact Nat.mod_eq_of_lt (by omega)
  · have c104 : (ctx.add 104).toNat = ctx.toNat + 104 := by ao
    rw [rdRaw4_agree a6 (by omega) (fun k hk => by omega), hm5]; rdv

end Solutions.ShaX
