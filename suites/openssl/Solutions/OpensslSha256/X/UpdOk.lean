import Solutions.OpensslSha256.X.UpdCore
/-!
# `SHA256_Update`: the call, for any return address and stack (`upd_core`)
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

/-- The context fields survive writes elsewhere. -/
theorem CtxOk.agree {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {ctx : UInt32} {Hw : Array UInt32}
    {nl nh num md : UInt32} {buf : List UInt8}
    (hP : ∀ a, ctx.toNat ≤ a → a < ctx.toNat + 112 → ¬ P a) (hc : ctx.toNat + 112 ≤ A.size)
    (hs : A.size ≤ 4273995776) (hb : buf.length ≤ 64) (hC : CtxOk A ctx Hw nl nh num md buf) :
    CtxOk B ctx Hw nl nh num md buf := by
  have r : ∀ (a : UInt32) (k : Nat) (v : UInt32), k + 4 ≤ 112 → a.toNat = ctx.toNat + k →
      rdRaw A a 4 = v → rdRaw B a 4 = v := by
    intro a k v hk hck hv
    rw [rdRaw4_agree h (by rw [hck]; omega) (fun j hj => hP _ (by rw [hck]; omega) (by rw [hck]; omega)), hv]
  exact ⟨words_agree h (fun a h1 h2 => hP a h1 (by omega)) hc hs hC.h, r _ 32 _ (by decide) (by ao) hC.nl,
    r _ 36 _ (by decide) (by ao) hC.nh, r _ 104 _ (by decide) (by ao) hC.num, r _ 108 _ (by decide) (by ao) hC.md,
    fun i hi => by rw [h.2 _ (by omega) (hP _ (by omega) (by omega))]; exact hC.buf i hi⟩

set_option maxHeartbeats 4000000 in
/-- A call of `SHA256_Update` with the stack pointer at `U.add 40`. -/
theorem upd_core (H : CMem) (U ctx msg len ra eax ecx edx ebx ebp esi edi f : UInt32) (chunk buf : List UInt8)
    (Hw : Array UInt32) (nl nh md : UInt32) (hF : UF H.get U ctx) (hlen : chunk.length = len.toNat)
    (hLl : len.toNat < 2 ^ 31) (hM : 0 < len.toNat → MF H.get U ctx msg len.toNat)
    (hb : ∀ i, i < len.toNat → H.get.get! (msg.toNat + i) = chunk[i]!)
    (hra : rdRaw H.get (U.add 40) 4 = ra) (hc : rdRaw H.get (U.add 44) 4 = ctx)
    (hm : rdRaw H.get (U.add 48) 4 = msg) (hl : rdRaw H.get (U.add 52) 4 = len)
    (hB64 : buf.length < 64) (hC : CtxOk H.get ctx Hw nl nh buf.length.toUInt32 md buf) (ic : UInt64)
    (hic : ic.toNat ≤ 2 ^ 40) :
    ∃ (H' : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 44 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 40, ebp, esi, edi, 0x1000e0, efl f, ic⟩)
        (SR H'.get U ecx' edx' esi edi ebx ebp ra f' ic') ∧
      AgreeOn (RU U ctx) H.get H'.get ∧
      ∃ nl' nh' : UInt32, NlOk nl nl' len.toNat ∧ NhOk nl nh nh' len.toNat ∧
        CtxOk H'.get ctx (updH Hw buf chunk) nl' nh' ((buf.length + len.toNat) % 64).toUInt32 md
          (updB buf chunk) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF'
  by_cases h0 : len.toNat = 0
  · have hlz : len = 0 := UInt32.toNat_inj.1 (by rw [h0]; rfl)
    obtain ⟨H1, f1, e1, hm1⟩ := upd_zero H U ra eax ecx edx ebx ebp esi edi f ic hsz hhi (by omega) hra
      (by rw [hl, hlz])
    have r1 := exN_run (img := img) 13 _ _ e1 (by show ic.toNat + 13 < 2 ^ 64; omega)
    have a1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 40) H.get H1.get := by rw [hm1]; agw
    have hc0 : chunk = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hc0
    have eH : updH Hw buf [] = Hw := by unfold updH; rw [if_pos (by simp only [List.length_nil]; omega)]
    have eB : updB buf [] = buf := by unfold updB; rw [if_pos (by simp; omega), List.append_nil]
    refine ⟨H1, ecx, edx, f1, ic + 13, by rw [u64_tN 13 (by decide) (by omega)]; omega, r1, a1.mono fun a h => by unfold RU; omega, nl, nh,
      by unfold NlOk; rw [h0]; have := nl.toNat_lt; omega, ?_, ?_⟩
    · unfold NhOk; rw [h0]; have := nl.toNat_lt; have := nh.toNat_lt
      simp only [Nat.mul_zero, Nat.zero_div, Nat.zero_mod, Nat.add_zero]
      rw [if_neg (by omega)]; omega
    · rw [eH, eB, h0, Nat.add_zero, Nat.mod_eq_of_lt hB64]
      exact CtxOk.agree a1 (fun a h1 h2 h3 => by omega) hcf hsz (by omega) hC
  · obtain ⟨H1, f1, e1, hm1⟩ := upd_p1 H U ctx msg len eax ecx edx ebx ebp esi edi f ic hsz hhi (by omega) hc hm hl h0
    have r1 := exN_run (img := img) 9 _ _ e1 (by show ic.toNat + 9 < 2 ^ 64; omega)
    have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
    have a1 : AgreeOn (fun a => U.toNat + 24 ≤ a ∧ a < U.toNat + 40) H.get H1.get := by rw [hm1]; agw
    have hSV1 : SV H1.get U esi edi ebx ebp ra :=
      ⟨by rw [hm1]; rdv, by rw [hm1]; rdv, by rw [hm1]; rdv, by rw [hm1]; rdv, by rw [hm1]; rdv; exact hra⟩
    have hM' := hM (by omega)
    have mf := hM'.fit; have ms := hM'.stk
    have hC1 := CtxOk.agree a1 (fun a h1 h2 h3 => by omega) hcf hsz (by omega) hC
    have hb1 := bytes_agree a1 (fun i hi h3 => by omega) mf hb
    have hi9 : (ic + 9).toNat ≤ 2 ^ 45 := by rw [u64_tN 9 (by decide) (by omega)]; omega
    by_cases hb0 : buf.length = 0
    · have hbn : buf = [] := List.eq_nil_of_length_eq_zero hb0
      subst hbn
      obtain ⟨H2, ecx2, edx2, f2, ic2, hic2, r2, a2, nl', nh', hnl, hnh, hC2⟩ := upd_caseZ H1 U ctx msg len eax ecx edx
        ebx f1 esi edi ebx ebp ra (ic + 9) chunk Hw nl nh md (hF.size hS1) hSV1 hlen (by omega) hLl
        (hM'.size hS1) hb1 hC1 hi9
      refine ⟨H2, ecx2, edx2, f2, ic2, by rw [u64_tN 9 (by decide) (by omega)] at hic2; omega, r1.trans r2,
        (a1.mono fun a h => by unfold RU; omega).trans a2, nl', nh', hnl, hnh, ?_⟩
      simpa using hC2
    · obtain ⟨H2, ecx2, edx2, f2, ic2, hic2, r2, a2, nl', nh', hnl, hnh, hC2⟩ := upd_caseN H1 U ctx msg len eax ecx edx
        ebx f1 esi edi ebx ebp ra (ic + 9) chunk buf Hw nl nh md (hF.size hS1) hSV1 hlen (by omega) hLl
        (hM'.size hS1) hb1 hb0 hB64 hC1 hi9
      exact ⟨H2, ecx2, edx2, f2, ic2, by rw [u64_tN 9 (by decide) (by omega)] at hic2; omega, r1.trans r2, (a1.mono fun a h => by unfold RU; omega).trans a2,
        nl', nh', hnl, hnh, hC2⟩

end Solutions.ShaX
