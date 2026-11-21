import Solutions.OpensslSha256.X.UpdMid
/-!
# `SHA256_Update`, for any return address and stack

`upd_core`: a call with the stack pointer at `U.add 40` (return address there, then `ctx`, `data`,
`len`) returns to the return address with `eax = 1`, the callee-saved registers restored, memory
changed only in the frame `[U - 168, U + 40)` and the context, and the context fields those after the
chunk (`updH`, `updB`, the bit count plus `8 len`, `num` plus `len` modulo 64).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem or_lt64 (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) :
    ((a.add b).lor b).toNat < 64 ↔ a.toNat + b.toNat < 64 := by
  have e : (a.add b).toNat = a.toNat + b.toNat := by rw [uadd_toNat]; exact Nat.mod_eq_of_lt h
  have e2 : ((a.add b).lor b).toNat = (a.add b).toNat ||| b.toNat := UInt32.toNat_or _ _
  rw [e2, e]
  constructor
  · intro h1; exact Nat.lt_of_le_of_lt Nat.left_le_or h1
  · intro h1; exact Nat.or_lt_two_pow (n := 6) (by omega) (by omega)

/-- The bit count words after `len` more bytes. -/
def NlOk (nl nl' : UInt32) (len : Nat) : Prop := nl'.toNat = (nl.toNat + 8 * len) % 2 ^ 32
def NhOk (nl nh nh' : UInt32) (len : Nat) : Prop :=
  nh'.toNat = (nh.toNat + len / 2 ^ 29 % 2 ^ 32 +
    (if nl.toNat % 2 ^ 32 + 8 * len % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32

theorem updH_nil (Hw : Array UInt32) (chunk : List UInt8) :
    updH Hw [] chunk = (Ssl.Spec.Sha256.blocks (chunk.take (64 * (chunk.length / 64)))).foldl
      Ssl.Spec.Sha256.compress Hw := by
  unfold updH jOf
  simp only [List.length_nil, if_true, Nat.zero_add, List.take_zero, List.nil_append, List.drop_zero, Nat.sub_zero]
  split
  · rename_i h; rw [show chunk.length / 64 = 0 by omega, Nat.mul_zero, List.take_zero]; rfl
  · rfl

theorem updB_nil (chunk : List UInt8) : updB [] chunk = chunk.drop (64 * (chunk.length / 64)) := by
  unfold updB jOf
  simp only [List.length_nil, if_true, Nat.zero_add, List.nil_append, List.drop_zero, Nat.sub_zero]
  split
  · rename_i h; rw [show chunk.length / 64 = 0 by omega, Nat.mul_zero, List.drop_zero]
  · rfl

/-- After the entry pieces: the stack pointer at `U.add 24`, `ebp = len`, `esi = ctx`, `edi = data`. -/
def S1 (M : ByteArray) (U ctx msg len eax ecx edx ebx f : UInt32) (ic : UInt64) : Machine :=
  St.m ⟨M, eax, ecx, edx, ebx, U.add 24, len, ctx, msg, 0x1000f8, efl f, ic⟩

/-- The state at the return. -/
def SR (M : ByteArray) (U ecx edx sesi sedi sebx sebp ra f : UInt32) (ic : UInt64) : Machine :=
  St.m ⟨M, 1, ecx, edx, sebx, U.add 44, sebp, sesi, sedi, ra, efl f, ic⟩

/-- The writes of an `Update`. -/
def RU (U ctx : UInt32) (a : Nat) : Prop :=
  U.toNat - 168 ≤ a ∧ a < U.toNat + 40 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 108

set_option maxHeartbeats 4000000 in
/-- `num = 0`, `len ≠ 0`. -/
theorem upd_caseZ (H : CMem) (U ctx msg len eax ecx edx ebx f sesi sedi sebx sebp ra : UInt32) (ic : UInt64)
    (chunk : List UInt8) (Hw : Array UInt32) (nl nh md : UInt32) (hF : UF H.get U ctx)
    (hSV : SV H.get U sesi sedi sebx sebp ra) (hlen : chunk.length = len.toNat) (hl0 : 0 < len.toNat)
    (hLl : len.toNat < 2 ^ 31) (hM : MF H.get U ctx msg len.toNat)
    (hb : ∀ i, i < len.toNat → H.get.get! (msg.toNat + i) = chunk[i]!)
    (hC : CtxOk H.get ctx Hw nl nh 0 md []) (hic : ic.toNat ≤ 2 ^ 45) :
    ∃ (H' : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 43 ∧
      Run img (S1 H.get U ctx msg len eax ecx edx ebx f ic) (SR H'.get U ecx' edx' sesi sedi sebx sebp ra f' ic') ∧
      AgreeOn (RU U ctx) H.get H'.get ∧
      ∃ nl' nh' : UInt32, NlOk nl nl' len.toNat ∧ NhOk nl nh nh' len.toNat ∧
        CtxOk H'.get ctx (updH Hw [] chunk) nl' nh' (len.toNat % 64).toUInt32 md (updB [] chunk) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF'
  have mf := hM.fit; have mi := hM.img; have ms := hM.stk; have mc := hM.c
  obtain ⟨H2, f2, eax2, NL, NH, e2, hm2, hNL, hNH⟩ := upd_p2z H U ctx msg len nl nh 0 eax ecx edx ebx f ic hsz
    hhi (by omega) hcf hci hC.nl hC.nh hC.num rfl
  have r2 := exN_run (img := img) 8 _ _ e2 (by show ic.toNat + 8 < 2 ^ 64; omega)
  have hS2 : H2.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]
  have a2 : AgreeOn (fun a => ctx.toNat + 32 ≤ a ∧ a < ctx.toNat + 40) H.get H2.get := by rw [hm2]; agw
  have hw2 := words_agree a2 (fun a h1 h2 h3 => by omega) hcf hsz hC.h
  have rd2 : ∀ (j v : UInt32), (j.toNat + 4 ≤ ctx.toNat + 32 ∨ ctx.toNat + 40 ≤ j.toNat) → j.toNat + 4 ≤ H.get.size →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := fun j v hj hj' hv => by
    rw [rdRaw4_agree a2 hj' (fun k hk => by omega), hv]
  obtain ⟨s0, s1, s2, s3, s4⟩ := hSV
  have hSV2 : SV H2.get U sesi sedi sebx sebp ra :=
    ⟨rd2 _ _ (by ao) (by ao) s0, rd2 _ _ (by ao) (by ao) s1, rd2 _ _ (by ao) (by ao) s2,
      rd2 _ _ (by ao) (by ao) s3, rd2 _ _ (by ao) (by ao) s4⟩
  have hn2 := rd2 _ _ (by ao) (by ao) hC.num
  have hb2 := bytes_agree a2 (fun i hi h3 => by omega) mf hb
  obtain ⟨H3, ecx3, edx3, f3, ic3, hic3, r3, a3, hw3, hn3, hb3⟩ := upd_t H2 U ctx len msg eax2 0 edx ebx f2 sesi sedi
    sebx sebp ra (ic + 8) Hw chunk (hF.size hS2) hSV2 hLl hlen (fun _ => hM.size hS2) hb2 hw2 hn2
    (by rw [u64_tN 8 (by decide) (by omega)]; omega)
  have a23 : AgreeOn (RU U ctx) H.get H3.get :=
    (a2.mono fun a h => by unfold RU; omega).trans (a3.mono fun a h => by unfold RU; omega)
  have rd3 : ∀ (j v : UInt32), (j.toNat = ctx.toNat + 32 ∨ j.toNat = ctx.toNat + 36 ∨ j.toNat = ctx.toNat + 108) →
      rdRaw H2.get j 4 = v → rdRaw H3.get j 4 = v := fun j v hj hv => by
    rw [rdRaw4_agree a3 (by omega) (fun k hk => by omega), hv]
  have i8 : (ic + 8).toNat = ic.toNat + 8 := u64_tN 8 (by decide) (by omega)
  refine ⟨H3, ecx3, edx3, f3, ic3, by omega, r2.trans r3, a23, NL, NH, hNL, ?_, ?_⟩
  · unfold NhOk; rw [hNH]
  · refine ⟨?_, rd3 _ _ (by ao) (by rw [hm2]; rdv), rd3 _ _ (by ao) (by rw [hm2]; rdv), hn3,
      rd3 _ _ (by ao) (rd2 _ _ (by ao) (by ao) hC.md), ?_⟩
    · rw [updH_nil, hlen]; exact hw3
    · rw [updB_nil, hlen]
      intro i hi
      rw [List.length_drop, hlen] at hi
      exact hb3 i (by omega)

set_option maxHeartbeats 4000000 in
/-- `num ≠ 0`: the bit count, then the small or the big path. -/
theorem upd_caseN (H : CMem) (U ctx msg len eax ecx edx ebx f sesi sedi sebx sebp ra : UInt32) (ic : UInt64)
    (chunk buf : List UInt8) (Hw : Array UInt32) (nl nh md : UInt32) (hF : UF H.get U ctx)
    (hSV : SV H.get U sesi sedi sebx sebp ra) (hlen : chunk.length = len.toNat) (hl0 : 0 < len.toNat)
    (hLl : len.toNat < 2 ^ 31) (hM : MF H.get U ctx msg len.toNat)
    (hb : ∀ i, i < len.toNat → H.get.get! (msg.toNat + i) = chunk[i]!) (hB0 : buf.length ≠ 0) (hB64 : buf.length < 64)
    (hC : CtxOk H.get ctx Hw nl nh buf.length.toUInt32 md buf) (hic : ic.toNat ≤ 2 ^ 45) :
    ∃ (H' : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 43 ∧
      Run img (S1 H.get U ctx msg len eax ecx edx ebx f ic) (SR H'.get U ecx' edx' sesi sedi sebx sebp ra f' ic') ∧
      AgreeOn (RU U ctx) H.get H'.get ∧
      ∃ nl' nh' : UInt32, NlOk nl nl' len.toNat ∧ NhOk nl nh nh' len.toNat ∧
        CtxOk H'.get ctx (updH Hw buf chunk) nl' nh' ((buf.length + len.toNat) % 64).toUInt32 md (updB buf chunk) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF'
  have mf := hM.fit; have mi := hM.img; have ms := hM.stk; have mc := hM.c
  have hnum : (buf.length.toUInt32).toNat = buf.length := toUInt32_lt (by omega)
  obtain ⟨H2, f2, eax2, NL, NH, e2, hm2, hNL, hNH⟩ := upd_p2n H U ctx msg len nl nh buf.length.toUInt32 eax ecx edx
    ebx f ic hsz hhi (by omega) hcf hci hC.nl hC.nh hC.num (by rw [hnum]; exact hB0)
  have r2 := exN_run (img := img) 8 _ _ e2 (by show ic.toNat + 8 < 2 ^ 64; omega)
  have i2 : (ic + 8).toNat = ic.toNat + 8 := u64_tN 8 (by decide) (by omega)
  have hS2 : H2.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]
  have a2 : AgreeOn (fun a => ctx.toNat + 32 ≤ a ∧ a < ctx.toNat + 40) H.get H2.get := by rw [hm2]; agw
  have hw2 := words_agree a2 (fun a h1 h2 h3 => by omega) hcf hsz hC.h
  have rd2 : ∀ (j v : UInt32), (j.toNat + 4 ≤ ctx.toNat + 32 ∨ ctx.toNat + 40 ≤ j.toNat) → j.toNat + 4 ≤ H.get.size →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := fun j v hj hj' hv => by
    rw [rdRaw4_agree a2 hj' (fun k hk => by omega), hv]
  obtain ⟨s0, s1, s2, s3, s4⟩ := hSV
  have hSV2 : SV H2.get U sesi sedi sebx sebp ra :=
    ⟨rd2 _ _ (by ao) (by ao) s0, rd2 _ _ (by ao) (by ao) s1, rd2 _ _ (by ao) (by ao) s2,
      rd2 _ _ (by ao) (by ao) s3, rd2 _ _ (by ao) (by ao) s4⟩
  have hn2 := rd2 _ _ (by ao) (by ao) hC.num
  have hmd2 := rd2 _ _ (by ao) (by ao) hC.md
  have hb2 := bytes_agree a2 (fun i hi h3 => by omega) mf hb
  have hbb2 : ∀ i, i < buf.length → H2.get.get! (ctx.toNat + 40 + i) = buf[i]! := fun i hi => by
    rw [a2.2 _ (by omega) (by omega)]; exact hC.buf i hi
  by_cases hs : buf.length + len.toNat < 64
  · obtain ⟨H3, ecx3, edx3, f3, ic3, hic3, r3, a3, hn3, hb3⟩ := upd_small H2 U ctx msg len buf.length.toUInt32 eax2
      edx ebx f2 sesi sedi sebx sebp ra (ic + 8) chunk (hF.size hS2) hSV2 hlen hl0 (hM.size hS2) hb2 hn2
      ((or_lt64 _ _ (by omega)).2 (by rw [hnum]; exact hs)) (by rw [hnum]; exact hs) (by omega)
    rw [hnum] at a3 hb3
    have rd3 : ∀ (j v : UInt32), (j.toNat = ctx.toNat + 32 ∨ j.toNat = ctx.toNat + 36 ∨ j.toNat = ctx.toNat + 108) →
        rdRaw H2.get j 4 = v → rdRaw H3.get j 4 = v := fun j v hj hv => by
      rw [rdRaw4_agree a3 (by omega) (fun k hk => by omega), hv]
    have hw3 := words_agree a3 (fun a h1 h2 h3 => by omega) (by omega) (by omega) hw2
    refine ⟨H3, ecx3, edx3, f3, ic3, by omega, r2.trans r3,
      (a2.mono fun a h => by unfold RU; omega).trans (a3.mono fun a h => by unfold RU; omega), NL, NH, hNL, hNH, ?_⟩
    have eH : updH Hw buf chunk = Hw := by unfold updH; rw [hlen, if_pos hs]
    have eB : updB buf chunk = buf ++ chunk := by unfold updB; rw [hlen, if_pos hs]
    rw [eH, eB]
    refine ⟨hw3, rd3 _ _ (by ao) (by rw [hm2]; rdv), rd3 _ _ (by ao) (by rw [hm2]; rdv), ?_, rd3 _ _ (by ao) hmd2, ?_⟩
    · rw [hn3]; apply UInt32.toNat_inj.1
      rw [UInt32.toNat_add, hnum, toUInt32_toNat_mod]; omega
    · intro i hi
      rw [List.length_append, hlen] at hi
      by_cases hi' : i < buf.length
      · rw [a3.2 _ (by omega) (by omega), hbb2 i hi', getElem!_pos (buf ++ chunk) i (by rw [List.length_append]; omega),
          List.getElem_append_left hi', getElem!_pos buf i hi']
      · rw [show ctx.toNat + 40 + i = ctx.toNat + 40 + buf.length + (i - buf.length) by omega, hb3 _ (by omega),
          getElem!_pos (buf ++ chunk) i (by rw [List.length_append]; omega), List.getElem_append_right (by omega),
          getElem!_pos chunk _ (by omega)]
  · have hge : 64 ≤ buf.length.toUInt32.toNat + len.toNat := by rw [hnum]; omega
    obtain ⟨H6, eax6, ecx6, edx6, L', P', f6, ic6, hic6, r6, a6, hL', hP', hw6, hn6⟩ := upd_big H2 U ctx msg len
      buf.length.toUInt32 eax2 edx ebx f2 (ic + 8) chunk buf Hw (hF.size hS2) hlen hLl (hM.size hS2) hb2 hnum.symm
      (by omega) (by rw [hnum]; exact hbb2) hw2 (fun h => hs (by rw [← hnum]; exact (or_lt64 _ _ (by omega)).1 h)) hge
      (by omega)
    rw [hnum] at hL' hP'
    have hS6 : H6.get.size = H.get.size := by rw [a6.1, hS2]
    have rd6 : ∀ (j v : UInt32), (j.toNat = U.toNat + 24 ∨ j.toNat = U.toNat + 28 ∨ j.toNat = U.toNat + 32 ∨
        j.toNat = U.toNat + 36 ∨ j.toNat = U.toNat + 40 ∨ j.toNat = ctx.toNat + 32 ∨ j.toNat = ctx.toNat + 36 ∨
        j.toNat = ctx.toNat + 108) → rdRaw H2.get j 4 = v → rdRaw H6.get j 4 = v := fun j v hj hv => by
      rw [rdRaw4_agree a6 (by omega) (fun k hk => by omega), hv]
    obtain ⟨t0, t1, t2, t3, t4⟩ := hSV2
    have hSV6 : SV H6.get U sesi sedi sebx sebp ra :=
      ⟨rd6 _ _ (by ao) t0, rd6 _ _ (by ao) t1, rd6 _ _ (by ao) t2, rd6 _ _ (by ao) t3, rd6 _ _ (by ao) t4⟩
    have hrest : (chunk.drop (64 - buf.length)).length = L'.toNat := by rw [List.length_drop, hL', hlen]
    have hb6 : ∀ i, i < L'.toNat → H6.get.get! (P'.toNat + i) = (chunk.drop (64 - buf.length))[i]! := by
      intro i hi
      rw [hP', a6.2 _ (by omega) (by omega), Nat.add_assoc, hb2 _ (by omega),
        getElem!_pos chunk _ (by omega), getElem!_pos (chunk.drop _) i (by rw [List.length_drop]; omega),
        List.getElem_drop]
    obtain ⟨H7, ecx7, edx7, f7, ic7, hic7, r7, a7, hw7, hn7, hb7⟩ := upd_t H6 U ctx L' P' eax6 ecx6 edx6
      (64 - buf.length.toUInt32) f6 sesi sedi sebx sebp ra ic6 _ (chunk.drop (64 - buf.length)) (hF.size hS6) hSV6
      (by omega) hrest (fun h => ((hM.size hS6).sub (q := P') (m := L'.toNat) (by omega) (by omega))) hb6 hw6 hn6
      (by omega)
    have rd7 : ∀ (j v : UInt32), (j.toNat = ctx.toNat + 32 ∨ j.toNat = ctx.toNat + 36 ∨ j.toNat = ctx.toNat + 108) →
        rdRaw H6.get j 4 = v → rdRaw H7.get j 4 = v := fun j v hj hv => by
      rw [rdRaw4_agree a7 (by omega) (fun k hk => by omega), hv]
    refine ⟨H7, ecx7, edx7, f7, ic7, by omega, r2.trans (r6.trans r7),
      ((a2.mono fun a h => by unfold RU; omega).trans (a6.mono fun a h => by unfold RU; omega)).trans
        (a7.mono fun a h => by unfold RU; omega), NL, NH, hNL, hNH, ?_⟩
    have hj : jOf buf = 64 - buf.length := by unfold jOf; rw [if_neg hB0]
    have eH : updH Hw buf chunk = (Ssl.Spec.Sha256.blocks ((chunk.drop (64 - buf.length)).take
        (64 * (L'.toNat / 64)))).foldl Ssl.Spec.Sha256.compress
        ((Ssl.Spec.Sha256.blocks (buf ++ chunk.take (64 - buf.length))).foldl Ssl.Spec.Sha256.compress Hw) := by
      unfold updH; rw [hlen, if_neg hs, hj, hL']
    have eB : updB buf chunk = (chunk.drop (64 - buf.length)).drop (64 * (L'.toNat / 64)) := by
      unfold updB; rw [hlen, if_neg hs, hj, hL']
    rw [eH, eB]
    refine ⟨hw7, rd7 _ _ (by ao) (rd6 _ _ (by ao) (by rw [hm2]; rdv)),
      rd7 _ _ (by ao) (rd6 _ _ (by ao) (by rw [hm2]; rdv)), ?_, rd7 _ _ (by ao) (rd6 _ _ (by ao) hmd2), ?_⟩
    · rw [hn7]; apply UInt32.toNat_inj.1; rw [toUInt32_toNat_mod, toUInt32_toNat_mod, hL']; omega
    · intro i hi
      rw [List.length_drop, hrest] at hi
      exact hb7 i (by omega)

end Solutions.ShaX
