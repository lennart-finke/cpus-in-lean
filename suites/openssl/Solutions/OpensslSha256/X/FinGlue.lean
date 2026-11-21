import Solutions.OpensslSha256.X.FinSpec
import Solutions.OpensslSha256.X.FinRun1
/-!
# `SHA256_Final` up to `0x100206`: the padded block(s) before the length words

The stack pointer at the entry is `V.add 36`. `fin_A`: the padding fits (`num ≤ 55`): the buffer
becomes `buf ++ [0x80] ++ zeros` up to byte 56. `fin_B`: it does not: that block is compressed, and
the buffer becomes 56 zero bytes.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

/-- The frame, the context and the output of a `Final` (`olen` output bytes). -/
structure FF (M : ByteArray) (V ctx out : UInt32) (olen : Nat) : Prop where
  sz : M.size ≤ 4273995776
  lo : 168 ≤ V.toNat
  hi : V.toNat + 48 ≤ M.size
  img : V.toNat + 48 ≤ 1048576 ∨ 1048576 + 4944 + 168 ≤ V.toNat
  cfit : ctx.toNat + 112 ≤ M.size
  cimg : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576
  cV : ctx.toNat + 112 + 168 ≤ V.toNat ∨ V.toNat + 48 ≤ ctx.toNat
  ofit : out.toNat + olen ≤ M.size
  oimg : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + olen ≤ 1048576
  oV : out.toNat + olen + 168 ≤ V.toNat ∨ V.toNat + 48 ≤ out.toNat
  oc : out.toNat + olen ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ out.toNat

theorem FF.size {M M' : ByteArray} {V ctx out : UInt32} {olen : Nat} (h : FF M V ctx out olen)
    (hs : M'.size = M.size) : FF M' V ctx out olen :=
  ⟨by rw [hs]; exact h.sz, h.lo, by rw [hs]; exact h.hi, h.img, by rw [hs]; exact h.cfit, h.cimg, h.cV,
    by rw [hs]; exact h.ofit, h.oimg, h.oV, h.oc⟩

/-- The saved words of a `Final` frame. -/
structure SVF (M : ByteArray) (V sesi sedi sebx ra out : UInt32) : Prop where
  s0 : rdRaw M (V.add 24) 4 = sesi
  s1 : rdRaw M (V.add 28) 4 = sedi
  s2 : rdRaw M (V.add 32) 4 = sebx
  s3 : rdRaw M (V.add 36) 4 = ra
  s4 : rdRaw M (V.add 40) 4 = out

theorem SVF.agree {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {V sesi sedi sebx ra out : UInt32}
    (hP : ∀ a, V.toNat + 24 ≤ a → a < V.toNat + 44 → ¬ P a) (hs : V.toNat + 48 ≤ A.size)
    (hA : A.size ≤ 4273995776) (hS : SVF A V sesi sedi sebx ra out) : SVF B V sesi sedi sebx ra out := by
  have r : ∀ (b : UInt32) (k : Nat) (v : UInt32), 24 ≤ k → k ≤ 40 → b.toNat = V.toNat + k →
      rdRaw A b 4 = v → rdRaw B b 4 = v := by
    intro b k v h1 h2 hk hv
    rw [rdRaw4_agree h (by rw [hk]; omega) (fun j hj => hP _ (by rw [hk]; omega) (by rw [hk]; omega)), hv]
  exact ⟨r _ 24 _ (by decide) (by decide) (by ao) hS.s0, r _ 28 _ (by decide) (by decide) (by ao) hS.s1,
    r _ 32 _ (by decide) (by decide) (by ao) hS.s2, r _ 36 _ (by decide) (by decide) (by ao) hS.s3,
    r _ 40 _ (by decide) (by decide) (by ao) hS.s4⟩

/-- The padded block before the length words, one-block case. -/
theorem pad1_get (buf : List UInt8) (i : Nat) (hb : buf.length ≤ 55) (hi : i < 56) :
    (buf ++ [0x80] ++ List.replicate (55 - buf.length) 0)[i]! =
      if i < buf.length then buf[i]! else if i = buf.length then 0x80 else 0 := by
  have hl : (buf ++ [0x80] ++ List.replicate (55 - buf.length) 0).length = 56 := by simp; omega
  rw [getElem!_pos _ i (by omega)]
  by_cases h1 : i < buf.length
  · rw [if_pos h1, List.getElem_append_left (by simp; omega), List.getElem_append_left h1, getElem!_pos buf i h1]
  · rw [if_neg h1]
    by_cases h2 : i = buf.length
    · subst h2; rw [if_pos rfl, List.getElem_append_left (by simp), List.getElem_append_right (by omega)]; simp
    · rw [if_neg h2, List.getElem_append_right (by simp; omega)]; simp

set_option maxHeartbeats 4000000 in
/-- The padding fits: the `0x80` byte and zeros up to byte 56 of the block. -/
theorem fin_A (H : CMem) (V ctx out ra n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64) (olen : Nat)
    (buf : List UInt8) (hF : FF H.get V ctx out olen) (hra : rdRaw H.get (V.add 36) 4 = ra)
    (ho : rdRaw H.get (V.add 40) 4 = out)
    (hc : rdRaw H.get (V.add 44) 4 = ctx) (hn : rdRaw H.get (ctx.add 104) 4 = n) (hnb : n.toNat = buf.length)
    (hbuf : ∀ i, i < buf.length → H.get.get! (ctx.toNat + 40 + i) = buf[i]!) (hlt : buf.length ≤ 55)
    (hic : ic.toNat ≤ 2 ^ 40) :
    ∃ (H3 : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 20 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, V.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩)
        (St.m ⟨H3.get, eax', ecx', edx', out, V.add 12, ebp, ctx, ctx.add 40, 0x100206, efl f', ic'⟩) ∧
      AgreeOn (fun a => V.toNat - 8 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 96)
        H.get H3.get ∧ SVF H3.get V esi edi ebx ra out ∧
      (∀ i, i < 56 → H3.get.get! (ctx.toNat + 40 + i) = (buf ++ [0x80] ++ List.replicate (55 - buf.length) 0)[i]!) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, -, -, -, -⟩ := hF'
  have hn1 : (n.add 1).toNat = n.toNat + 1 := by ao
  obtain ⟨H1, f1, N1, D, e1, hm1, hN1, hD⟩ := fin_a1 H V ctx n eax ecx edx ebx ebp esi edi f ic hsz hhi (by omega)
    hcf hci (by omega) hc hn (by omega) (by rw [hn1]; omega)
  subst hN1 hD
  have r1 := exN_run (img := img) 10 _ _ e1 (by show ic.toNat + 10 < 2 ^ 64; omega)
  have i1 : (ic + 10).toNat = ic.toNat + 10 := u64_tN 10 (by decide) (by omega)
  have cb : ((ctx.add n).add 40).toNat = ctx.toNat + 40 + n.toNat := by ao
  have aW : AgreeOn (fun a => V.toNat + 24 ≤ a ∧ a < V.toNat + 36) H.get
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) := by agw
  have hW1s : (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi).size =
      H.get.size := aW.1
  have hS1 : H1.get.size = H.get.size := by rw [hm1, size_wrBytes1 (by rw [cb, hW1s]; omega), hW1s]
  have g1 : ∀ j, H1.get.get! j = if j = ctx.toNat + 40 + n.toNat then 128 else
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi).get! j := by
    intro j; rw [hm1, get!_wrBytes1 (by rw [cb, hW1s]; omega), cb]; rfl
  have a1 : AgreeOn (fun a => V.toNat + 24 ≤ a ∧ a < V.toNat + 36 ∨ a = ctx.toNat + 40 + n.toNat) H.get H1.get :=
    ⟨hS1, fun a ha hP => by rw [g1, if_neg (fun h => hP (Or.inr h))]; exact aW.2 a ha (fun h => hP (Or.inl h))⟩
  have ho1 : rdRaw H1.get (V.add 40) 4 = out := by
    rw [rdRaw4_agree a1 (by ao) (fun k hk => by ao)]; exact ho
  obtain ⟨H2, f2, A, C, e2, hm2, hA, hC⟩ := fin_e H1 V ctx out (n.add 1) (ctx.add 40) n edx ebx ebp f1 (ic + 10)
    (by omega) (by omega) (by omega) ho1
  have r2 := exN_run (img := img) 8 _ _ e2 (by show (ic + 10).toNat + 8 < 2 ^ 64; omega)
  have i2 : (ic + 10 + 8).toNat = ic.toNat + 18 := by rw [u64_tN (ic := ic + 10) 8 (by decide) (by omega), i1]
  have hS2 : H2.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]; exact hS1
  have a2 : AgreeOn (fun a => V.toNat + 8 ≤ a ∧ a < V.toNat + 24) H1.get H2.get := by rw [hm2]; agw
  have hAn : A.toNat = ctx.toNat + 40 + n.toNat + 1 := by rw [hA, UInt32.toNat_add]; ao
  have hCn : C.toNat = 55 - n.toNat := by
    rw [hC, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hn1]; show _ ≤ 56; omega), hn1]
    simp only [UInt32.reduceToNat]; omega
  have k8 : rdRaw H2.get (V.add 8) 4 = 0x100206 := by rw [hm2]; rdv
  have k12 : rdRaw H2.get (V.add 12) 4 = A := by rw [hm2]; rdv
  have k16 : rdRaw H2.get (V.add 16) 4 = 0 := by rw [hm2]; rdv
  have k20 : rdRaw H2.get (V.add 20) 4 = C := by rw [hm2]; rdv
  obtain ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hz3⟩ := memset_U H2 V 0x100206 A 0 C (n.add 1) A C out ebp
    ctx (ctx.add 40) f2 (ic + 10 + 8) (by omega) (by omega) (by unfold OffCode; omega) k8 k12 k16 k20
    (by omega) (by unfold OffCode; omega) (by omega) (by omega)
  rw [hAn, hCn] at a3 hz3
  have aB : AgreeOn (fun a => a = ctx.toNat + 40 + n.toNat)
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) H1.get :=
    ⟨by rw [hS1, hW1s], fun a ha hP => by rw [g1, if_neg hP]⟩
  have sv : ∀ (j v : UInt32), (j.toNat = V.toNat + 24 ∨ j.toNat = V.toNat + 28 ∨ j.toNat = V.toNat + 32 ∨
      j.toNat = V.toNat + 36 ∨ j.toNat = V.toNat + 40) →
      rdRaw (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) j 4 = v →
      rdRaw H3.get j 4 = v :=
    fun j v hj hv => by
      rw [rdRaw4_agree a3 (by omega) (fun k hk => by omega), rdRaw4_agree a2 (by omega) (fun k hk => by omega),
        rdRaw4_agree aB (by ao) (fun k hk => by omega), hv]
  have hSV : SVF H3.get V esi edi ebx ra out :=
    ⟨sv _ _ (by ao) (by rdv), sv _ _ (by ao) (by rdv), sv _ _ (by ao) (by rdv),
      sv _ _ (by ao) (by rdv; exact hra), sv _ _ (by ao) (by rdv; exact ho)⟩
  refine ⟨H3, eax3, ecx3, edx3, f3, ic3, by omega, r1.trans (r2.trans r3),
    ((a1.mono fun a h => by omega).trans (a2.mono fun a h => by omega)).trans (a3.mono fun a h => by omega),
    hSV, fun i hi => ?_⟩
  rw [pad1_get buf i hlt hi]
  by_cases h1 : i < buf.length
  · rw [if_pos h1, a3.2 _ (by omega) (by omega), a2.2 _ (by omega) (by omega), a1.2 _ (by omega) (by omega)]
    exact hbuf i h1
  · rw [if_neg h1]
    by_cases h2 : i = buf.length
    · rw [if_pos h2, a3.2 _ (by omega) (by omega), a2.2 _ (by omega) (by omega), g1, if_pos (by omega)]; try rfl
    · rw [if_neg h2, show ctx.toNat + 40 + i = ctx.toNat + 40 + n.toNat + 1 + (i - n.toNat - 1) by omega]
      exact hz3 _ (by omega)

/-- The padded block, two-block case. -/
theorem pad2_get (buf : List UInt8) (i : Nat) (hb : 56 ≤ buf.length) (hb' : buf.length < 64) (hi : i < 64) :
    (buf ++ [0x80] ++ List.replicate (63 - buf.length) 0)[i]! =
      if i < buf.length then buf[i]! else if i = buf.length then 0x80 else 0 := by
  have hl : (buf ++ [0x80] ++ List.replicate (63 - buf.length) 0).length = 64 := by simp; omega
  rw [getElem!_pos _ i (by omega)]
  by_cases h1 : i < buf.length
  · rw [if_pos h1, List.getElem_append_left (by simp; omega), List.getElem_append_left h1, getElem!_pos buf i h1]
  · rw [if_neg h1]
    by_cases h2 : i = buf.length
    · subst h2; rw [if_pos rfl, List.getElem_append_left (by simp), List.getElem_append_right (by omega)]; simp
    · rw [if_neg h2, List.getElem_append_right (by simp; omega)]; simp

set_option maxHeartbeats 4000000 in
/-- The padding does not fit: the first padded block compressed, then 56 zero bytes. -/
theorem fin_B (H : CMem) (V ctx out ra n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64) (olen : Nat)
    (buf : List UInt8) (Hw : Array UInt32) (hF : FF H.get V ctx out olen) (hra : rdRaw H.get (V.add 36) 4 = ra)
    (ho : rdRaw H.get (V.add 40) 4 = out)
    (hc : rdRaw H.get (V.add 44) 4 = ctx) (hn : rdRaw H.get (ctx.add 104) 4 = n) (hnb : n.toNat = buf.length)
    (hbuf : ∀ i, i < buf.length → H.get.get! (ctx.toNat + 40 + i) = buf[i]!) (hge : 56 ≤ buf.length)
    (hb64 : buf.length < 64) (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw[k]!)
    (hic : ic.toNat ≤ 2 ^ 40) :
    ∃ (H7 : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 20 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, V.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩)
        (St.m ⟨H7.get, eax', ecx', edx', out, V.add 12, ebp, ctx, ctx.add 40, 0x100206, efl f', ic'⟩) ∧
      AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32 ∨
        ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 104) H.get H7.get ∧ SVF H7.get V esi edi ebx ra out ∧
      (∀ k, k < 8 → rdRaw H7.get (ctx + (4 * k).toUInt32) 4 =
        (Ssl.Spec.Sha256.compress Hw (buf ++ [0x80] ++ List.replicate (63 - buf.length) 0))[k]!) ∧
      (∀ i, i < 56 → H7.get.get! (ctx.toNat + 40 + i) = 0) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcV, -, -, -, -⟩ := hF'
  have hn1 : (n.add 1).toNat = n.toNat + 1 := by ao
  obtain ⟨H1, f1, N1, D, e1, hm1, hN1, hD⟩ := fin_a2 H V ctx n eax ecx edx ebx ebp esi edi f ic hsz hhi (by omega)
    hcf hci (by omega) hc hn (by omega) (by rw [hn1]; omega)
  subst hN1 hD
  have r1 := exN_run (img := img) 10 _ _ e1 (by show ic.toNat + 10 < 2 ^ 64; omega)
  have i1 : (ic + 10).toNat = ic.toNat + 10 := u64_tN 10 (by decide) (by omega)
  have cb : ((ctx.add n).add 40).toNat = ctx.toNat + 40 + n.toNat := by ao
  have c40 : (ctx.add 40).toNat = ctx.toNat + 40 := by ao
  have aW : AgreeOn (fun a => V.toNat + 24 ≤ a ∧ a < V.toNat + 36) H.get
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) := by agw
  have hS1 : H1.get.size = H.get.size := by rw [hm1, size_wrBytes1 (by rw [cb, aW.1]; omega), aW.1]
  have g1 : ∀ j, H1.get.get! j = if j = ctx.toNat + 40 + n.toNat then 128 else
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi).get! j := by
    intro j; rw [hm1, get!_wrBytes1 (by rw [cb, aW.1]; omega), cb]; rfl
  have a1 : AgreeOn (fun a => V.toNat + 24 ≤ a ∧ a < V.toNat + 36 ∨ a = ctx.toNat + 40 + n.toNat) H.get H1.get :=
    ⟨hS1, fun a ha hP => by rw [g1, if_neg (fun h => hP (Or.inr h))]; exact aW.2 a ha (fun h => hP (Or.inl h))⟩
  obtain ⟨H2, f2, A, C, e2, hm2, hA, hC⟩ := fin_b H1 V ctx n (n.add 1) (ctx.add 40) edx ebx ebp f1 (ic + 10)
    (by omega) (by omega) (by omega)
  have r2 := exN_run (img := img) 7 _ _ e2 (by show (ic + 10).toNat + 7 < 2 ^ 64; omega)
  have i2 : (ic + 10 + 7).toNat = ic.toNat + 17 := by rw [u64_tN (ic := ic + 10) 7 (by decide) (by omega), i1]
  have hS2 : H2.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]; exact hS1
  have a2 : AgreeOn (fun a => V.toNat + 8 ≤ a ∧ a < V.toNat + 24) H1.get H2.get := by rw [hm2]; agw
  have hAn : A.toNat = ctx.toNat + 40 + n.toNat + 1 := by rw [hA, UInt32.toNat_add, hn1, c40]; omega
  have hCn : C.toNat = 63 - n.toNat := by
    rw [hC, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show _ ≤ 63; omega)]; rfl
  have k8 : rdRaw H2.get (V.add 8) 4 = 0x1001dc := by rw [hm2]; rdv
  have k12 : rdRaw H2.get (V.add 12) 4 = A := by rw [hm2]; rdv
  have k16 : rdRaw H2.get (V.add 16) 4 = 0 := by rw [hm2]; rdv
  have k20 : rdRaw H2.get (V.add 20) 4 = C := by rw [hm2]; rdv
  obtain ⟨H3, eax3, ecx3, edx3, f3, ic3, hic3, r3, a3, hz3⟩ := memset_U H2 V 0x1001dc A 0 C A n C ebx ebp
    ctx (ctx.add 40) f2 (ic + 10 + 7) (by omega) (by omega) (by unfold OffCode; omega) k8 k12 k16 k20
    (by omega) (by unfold OffCode; omega) (by omega) (by omega)
  rw [hAn, hCn] at a3 hz3
  have hS3 : H3.get.size = H.get.size := by rw [a3.1, hS2]
  obtain ⟨H4, f4, e4, hm4⟩ := fin_c H3 V ctx (ctx.add 40) eax3 ecx3 edx3 ebx ebp f3 ic3 (by omega) (by omega)
    (by omega)
  have r4 := exN_run (img := img) 5 _ _ e4 (by show ic3.toNat + 5 < 2 ^ 64; omega)
  have hS4 : H4.get.size = H.get.size := by rw [hm4]; simp only [Solutions.Exec.size_wrBytes]; exact hS3
  have a4 : AgreeOn (fun a => V.toNat + 8 ≤ a ∧ a < V.toNat + 24) H3.get H4.get := by rw [hm4]; agw
  have g16 : rdRaw H4.get (V.add 16) 4 = 0x1001ea := by rw [hm4]; rdv
  have g20 : rdRaw H4.get (V.add 20) 4 = (1 : Nat).toUInt32 := by rw [hm4]; rdv; rfl
  have a14 : AgreeOn (fun a => V.toNat + 4 ≤ a ∧ a < V.toNat + 36 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 104)
      H.get H4.get :=
    (((a1.mono fun a h => by omega).trans (a2.mono fun a h => by omega)).trans (a3.mono fun a h => by omega)).trans
      (a4.mono fun a h => by omega)
  have hw4 := words_agree a14 (fun a h1 h2 h3 => by omega) hcf hsz hw
  have hbl : Solutions.OpensslSha256.blks H4.get (ctx.add 40) 0 1 =
      Ssl.Spec.Sha256.blocks (buf ++ [0x80] ++ List.replicate (63 - buf.length) 0) := by
    refine blks_eq H4.get (ctx.add 40) (by omega) 1 0 _ (by omega) (by simp; omega) (fun k hk => ?_)
    rw [pad2_get buf k hge hb64 (by omega), c40, Nat.mul_zero, Nat.add_zero, a4.2 _ (by omega) (by omega)]
    by_cases h1 : k < buf.length
    · rw [if_pos h1, a3.2 _ (by omega) (by omega), a2.2 _ (by omega) (by omega), a1.2 _ (by omega) (by omega)]
      exact hbuf k h1
    · rw [if_neg h1]
      by_cases h2 : k = buf.length
      · rw [if_pos h2, a3.2 _ (by omega) (by omega), a2.2 _ (by omega) (by omega), g1, if_pos (by omega)]; try rfl
      · rw [if_neg h2, show ctx.toNat + 40 + k = ctx.toNat + 40 + n.toNat + 1 + (k - n.toNat - 1) by omega]
        exact hz3 _ (by omega)
  obtain ⟨H5, fl5, eax5, ecx5, edx5, r5, a5, hw5⟩ := bdo_U H4 V ctx (ctx.add 40) 1 Hw 0x1001ea eax3 ebx ebp ctx
    (ctx.add 40) f4 (ic3 + 5) (by omega) hlo (by omega) (by omega) (by omega) hci (by omega) (by decide) (by decide)
    (by omega) (by unfold OffCode; omega) (by omega) (by omega) g16 g20 hw4
    (by rw [u64_tN 5 (by decide) (by omega)]; omega)
  rw [hbl, Solutions.OpensslSha256.blocks_one _ (by simp; omega)] at hw5
  have hS5 : H5.get.size = H.get.size := by rw [a5.1, hS4]
  obtain ⟨f6, Z, e6, hZ⟩ := fin_d H5 V eax5 ecx5 edx5 ebx ebp ctx (ctx.add 40) fl5
    (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64) (by omega) (by omega) (by omega)
  subst hZ
  have i5 : (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64).toNat = ic3.toNat + 5 + 4067 := by
    rw [u64_toNat_add (by rw [u64_tN 5 (by decide) (by omega)]; omega), u64_tN 5 (by decide) (by omega)]
  have r6 := exN_run (img := img) 2 _ _ e6 (by
    show (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64).toNat + 2 < 2 ^ 64; omega)
  have ho5 : rdRaw H5.get (V.add 40) 4 = out := by
    rw [rdRaw4_agree a5 (by ao) (fun k hk => by ao), rdRaw4_agree a14 (by ao) (fun k hk => by ao)]; exact ho
  obtain ⟨H6, f7, A2, C2, e7, hm7, hA2, hC2⟩ := fin_e H5 V ctx out 0 (ctx.add 40) ecx5 edx5 ebx ebp f6
    (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 2) (by omega) (by omega) (by omega) ho5
  have r7 := exN_run (img := img) 8 _ _ e7 (by
    show (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 2).toNat + 8 < 2 ^ 64
    rw [u64_tN 2 (by decide) (by omega)]; omega)
  have hS6 : H6.get.size = H.get.size := by rw [hm7]; simp only [Solutions.Exec.size_wrBytes]; exact hS5
  have a6 : AgreeOn (fun a => V.toNat + 8 ≤ a ∧ a < V.toNat + 24) H5.get H6.get := by rw [hm7]; agw
  have hA2n : A2.toNat = ctx.toNat + 40 := by rw [hA2, UInt32.toNat_add, c40]; simp; omega
  have hC2n : C2.toNat = 56 := by rw [hC2]; rfl
  have m8 : rdRaw H6.get (V.add 8) 4 = 0x100206 := by rw [hm7]; rdv
  have m12 : rdRaw H6.get (V.add 12) 4 = A2 := by rw [hm7]; rdv
  have m16 : rdRaw H6.get (V.add 16) 4 = 0 := by rw [hm7]; rdv
  have m20 : rdRaw H6.get (V.add 20) 4 = C2 := by rw [hm7]; rdv
  have i7 : (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 2 + 8).toNat = ic3.toNat + 5 + 4067 + 10 := by
    rw [u64_tN 8 (by decide) (by rw [u64_tN 2 (by decide) (by omega)]; omega), u64_tN 2 (by decide) (by omega), i5]
  obtain ⟨H7, eax7, ecx7, edx7, f8, ic8, hic8, r8, a8, hz8⟩ := memset_U H6 V 0x100206 A2 0 C2 0 A2 C2 out ebp
    ctx (ctx.add 40) f7 (ic3 + 5 + (4029 * 1 + 38 : Nat).toUInt64 + 2 + 8) (by omega) (by omega)
    (by unfold OffCode; omega) m8 m12 m16 m20 (by omega) (by unfold OffCode; omega) (by omega) (by omega)
  rw [hA2n, hC2n] at a8 hz8
  have W1e : AgreeOn (fun a => a = ctx.toNat + 40 + n.toNat)
      (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) H1.get :=
    ⟨by rw [hS1, aW.1], fun a ha hP => by rw [g1, if_neg hP]⟩
  have sv : ∀ (j v : UInt32), (j.toNat = V.toNat + 24 ∨ j.toNat = V.toNat + 28 ∨ j.toNat = V.toNat + 32 ∨
      j.toNat = V.toNat + 36 ∨ j.toNat = V.toNat + 40) →
      rdRaw (wrBytes (wrBytes (wrBytes H.get (V.add 32) 4 ebx) (V.add 28) 4 edi) (V.add 24) 4 esi) j 4 = v →
      rdRaw H7.get j 4 = v := fun j v hj hv => by
    have a18 : AgreeOn (fun a => V.toNat - 168 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 104)
        H1.get H7.get :=
      ((((((a2.mono fun a h => by omega).trans (a3.mono fun a h => by omega)).trans (a4.mono fun a h => by omega)).trans
        (a5.mono fun a h => by omega)).trans (a6.mono fun a h => by omega)).trans (a8.mono fun a h => by omega))
    rw [rdRaw4_agree a18 (by omega) (fun k hk => by omega), rdRaw4_agree W1e (by ao) (fun k hk => by omega), hv]
  have hSV : SVF H7.get V esi edi ebx ra out :=
    ⟨sv _ _ (by ao) (by rdv), sv _ _ (by ao) (by rdv), sv _ _ (by ao) (by rdv),
      sv _ _ (by ao) (by rdv; exact hra), sv _ _ (by ao) (by rdv; exact ho)⟩
  refine ⟨H7, eax7, ecx7, edx7, f8, ic8, by omega,
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans r8)))))),
    (((a14.mono fun a h => by omega).trans (a5.mono fun a h => by omega)).trans (a6.mono fun a h => by omega)).trans
      (a8.mono fun a h => by omega), hSV, ?_, fun i hi => hz8 i hi⟩
  have a68 : AgreeOn (fun a => V.toNat + 4 ≤ a ∧ a < V.toNat + 24 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 96)
      H5.get H7.get := (a6.mono fun a h => by omega).trans (a8.mono fun a h => by omega)
  exact words_agree a68 (fun a h1 h2 h3 => by omega) (by omega) (by omega) hw5

end Solutions.ShaX
