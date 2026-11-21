import Solutions.OpensslSha256.X.UpdRun3
import Solutions.OpensslSha256.X.UpdSpec
/-!
# `SHA256_Update` from `0x10016b`: the whole blocks of the rest of the chunk, then the tail

At `0x10016b` the stack pointer is `U.add 24`, `ebp` holds the number `L` of bytes left, `edi` points
at them, `esi` at the context. `upd_t1`: the block function on the `L / 64` whole blocks (if any), up
to `0x100189`; `upd_t2`: the `L % 64` bytes left copied into the buffer (if any), `num` set, the return.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (blks)

theorem ctxk_toNat (ctx : UInt32) (k : Nat) (hk : k < 8) (h : ctx.toNat + 112 ≤ 4273995776) :
    (ctx + (4 * k).toUInt32).toNat = ctx.toNat + 4 * k := by
  rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)

/-- The hash words survive writes elsewhere. -/
theorem words_agree {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {ctx : UInt32} {Hw : Array UInt32}
    (hP : ∀ a, ctx.toNat ≤ a → a < ctx.toNat + 32 → ¬ P a) (hc : ctx.toNat + 112 ≤ A.size)
    (hs : A.size ≤ 4273995776)
    (hw : ∀ k, k < 8 → rdRaw A (ctx + (4 * k).toUInt32) 4 = Hw[k]!) :
    ∀ k, k < 8 → rdRaw B (ctx + (4 * k).toUInt32) 4 = Hw[k]! := by
  intro k hk
  have e := ctxk_toNat ctx k hk (by omega)
  rw [rdRaw4_agree h (by rw [e]; omega) (fun j hj => hP _ (by rw [e]; omega) (by rw [e]; omega))]
  exact hw k hk

/-- Bytes survive writes elsewhere. -/
theorem bytes_agree {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {p : UInt32} {n : Nat}
    {L : List UInt8} (hP : ∀ i, i < n → ¬ P (p.toNat + i)) (hp : p.toNat + n ≤ A.size)
    (hb : ∀ i, i < n → A.get! (p.toNat + i) = L[i]!) : ∀ i, i < n → B.get! (p.toNat + i) = L[i]! := by
  intro i hi
  rw [h.2 _ (by omega) (hP i hi)]; exact hb i hi

theorem shr6_eq (L : UInt32) : L >>> 6 = (L.toNat / 64).toUInt32 := by
  apply UInt32.toNat_inj.1; rw [u32_shr6, toUInt32_toNat_mod]; have := L.toNat_lt; omega

set_option maxHeartbeats 2000000 in
/-- The whole blocks. -/
theorem upd_t1 (H : CMem) (U ctx L p eax ecx edx ebx f : UInt32) (ic : UInt64) (Hw : Array UInt32)
    (rest : List UInt8) (hF : UF H.get U ctx) (hLl : L.toNat < 2 ^ 31) (hL : rest.length = L.toNat)
    (hp : 0 < L.toNat → MF H.get U ctx p L.toNat)
    (hb : ∀ i, i < L.toNat → H.get.get! (p.toNat + i) = rest[i]!)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw[k]!) (hic : ic.toNat ≤ 2 ^ 50) :
    ∃ (H2 : CMem) (A ecx' edx' R P' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 40 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 24, L, ctx, p, 0x10016b, efl f, ic⟩)
        (St.m ⟨H2.get, A, ecx', edx', ebx, U.add 24, R, ctx, P', 0x100189, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat - 168 ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32) H.get H2.get ∧
      R.toNat = L.toNat % 64 ∧ P'.toNat = p.toNat + 64 * (L.toNat / 64) ∧
      (∀ k, k < 8 → rdRaw H2.get (ctx + (4 * k).toUInt32) 4 =
        ((Ssl.Spec.Sha256.blocks (rest.take (64 * (L.toNat / 64)))).foldl Ssl.Spec.Sha256.compress Hw)[k]!) := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF
  have hq : (UInt32.shiftRight L 6).toNat = L.toNat / 64 := u32_shr6 L
  by_cases h0 : L.toNat / 64 = 0
  · obtain ⟨f1, e1⟩ := upd_c1z H U L eax ecx edx ebx ctx p f ic hsz hhi (by omega) (by rw [hq]; exact h0)
    have r1 := exN_run (img := img) 3 _ _ e1 (by show ic.toNat + 3 < 2 ^ 64; omega)
    refine ⟨H, UInt32.shiftRight L 6, ecx, edx, L, p, f1, ic + 3, by rw [u64_tN 3 (by decide) (by omega)]; omega, r1,
      AgreeOn.refl _ _, by omega, by omega, fun k hk => ?_⟩
    rw [h0, Nat.mul_zero, List.take_zero]; exact hw k hk
  · have hpm := hp (by omega)
    have mf := hpm.fit; have mi := hpm.img; have ms := hpm.stk; have mc := hpm.c
    obtain ⟨f1, e1⟩ := upd_c1n H U L eax ecx edx ebx ctx p f ic hsz hhi (by omega) (by rw [hq]; exact h0)
    have r1 := exN_run (img := img) 3 _ _ e1 (by show ic.toNat + 3 < 2 ^ 64; omega)
    have i1 : (ic + 3).toNat = ic.toNat + 3 := u64_tN 3 (by decide) (by omega)
    obtain ⟨H1, f2, e2, hm2⟩ := upd_c2 H U (UInt32.shiftRight L 6) ctx p ecx edx ebx L f1 (ic + 3) hsz hhi (by omega)
    have r2 := exN_run (img := img) 4 _ _ e2 (by show (ic + 3).toNat + 4 < 2 ^ 64; omega)
    have i2 : (ic + 3 + 4).toNat = ic.toNat + 7 := by rw [u64_tN (ic := ic + 3) 4 (by decide) (by omega), i1]
    have hS1 : H1.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]
    have a1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24) H.get H1.get := by rw [hm2]; agw
    have g16 : rdRaw H1.get (U.add 16) 4 = 0x10017c := by rw [hm2]; rdv
    have g20 : rdRaw H1.get (U.add 20) 4 = (L.toNat / 64).toUInt32 := by rw [hm2]; rdv; exact shr6_eq L
    have hw1 := words_agree a1 (fun a h1 h2 h3 => by omega) hcf hsz hw
    have hb1 := bytes_agree a1 (fun i hi h3 => by omega) mf hb
    obtain ⟨H2, fl3, eax3, ecx3, edx3, r3, a3, hw3⟩ := bdo_U H1 U ctx p (L.toNat / 64) Hw 0x10017c (UInt32.shiftRight L 6) ebx L ctx p
      f2 (ic + 3 + 4) (by omega) hlo (by omega) (by omega) (by omega) hci (by omega) (by omega) (by omega) (by omega)
      (by unfold OffCode; omega) (by omega) (by omega) g16 g20 hw1 (by omega)
    have hbl : blks H1.get p 0 (L.toNat / 64) = Ssl.Spec.Sha256.blocks (rest.take (64 * (L.toNat / 64))) :=
      blks_eq H1.get p (by omega) (L.toNat / 64) 0 _ (by omega) (by rw [List.length_take]; omega)
        (fun k hk => by
          rw [Nat.mul_zero, Nat.add_zero, hb1 k (by omega), getElem!_pos rest k (by omega),
            getElem!_pos (rest.take _) k (by rw [List.length_take]; omega), List.getElem_take])
    rw [hbl] at hw3
    have hS2 : H2.get.size = H.get.size := by rw [a3.1, hS1]
    have i3 : (ic + 3 + 4 + (4029 * (L.toNat / 64) + 38).toUInt64).toNat = ic.toNat + 7 + (4029 * (L.toNat / 64) + 38) := by
      rw [u64_toNat_add (by omega), i2]
    obtain ⟨f4, A, R, P', e4, hA, hR, hP⟩ := upd_c3 H2 U L p eax3 ecx3 edx3 ebx ctx fl3
      (ic + 3 + 4 + (4029 * (L.toNat / 64) + 38).toUInt64) (by omega) (by omega) (by omega)
    have r4 := exN_run (img := img) 5 _ _ e4 (by
      show (ic + 3 + 4 + (4029 * (L.toNat / 64) + 38).toUInt64).toNat + 5 < 2 ^ 64; omega)
    refine ⟨H2, A, ecx3, edx3, R, P', f4, _, ?_, r1.trans (r2.trans (r3.trans r4)),
      (a1.mono fun a h => Or.inl ⟨by omega, h.2⟩).trans a3, ?_, ?_, hw3⟩
    · rw [u64_tN 5 (by decide) (by omega), i3]; omega
    · rw [hR, u32_lo]
    · rw [hP, UInt32.toNat_add, u32_hi]; exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 2000000 in
/-- The tail. -/
theorem upd_t2 (H : CMem) (U ctx R P A ecx edx ebx f sesi sedi sebx sebp ra : UInt32) (ic : UInt64)
    (tl : List UInt8) (hF : UF H.get U ctx) (hSV : SV H.get U sesi sedi sebx sebp ra) (hR : R.toNat < 64)
    (htl : tl.length = R.toNat) (hp : 0 < R.toNat → MF H.get U ctx P R.toNat)
    (hb : ∀ i, i < R.toNat → H.get.get! (P.toNat + i) = tl[i]!)
    (hn0 : rdRaw H.get (ctx.add 104) 4 = 0) (hic : ic.toNat ≤ 2 ^ 50) :
    ∃ (H3 : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 40 ∧
      Run img (St.m ⟨H.get, A, ecx, edx, ebx, U.add 24, R, ctx, P, 0x100189, efl f, ic⟩)
        (St.m ⟨H3.get, 1, ecx', edx', sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108) H.get H3.get ∧
      rdRaw H3.get (ctx.add 104) 4 = R ∧ (∀ i, i < R.toNat → H3.get.get! (ctx.toNat + 40 + i) = tl[i]!) := by
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF
  obtain ⟨s0, s1, s2, s3, s4⟩ := hSV
  by_cases hr : R.toNat = 0
  · obtain ⟨f1, e1⟩ := upd_dz H U R sesi sedi sebx sebp ra A ecx edx ebx ctx P f ic hsz hhi (by omega)
      s0 s1 s2 s3 s4 hr
    have r1 := exN_run (img := img) 8 _ _ e1 (by show ic.toNat + 8 < 2 ^ 64; omega)
    have hR0 : R = 0 := UInt32.toNat_inj.1 (by rw [hr]; rfl)
    refine ⟨H, ecx, edx, f1, ic + 8, by rw [u64_tN 8 (by decide) (by omega)]; omega, r1, AgreeOn.refl _ _,
      by rw [hn0, hR0], fun i hi => absurd hi (by omega)⟩
  · have hpm := hp (by omega)
    have mf := hpm.fit; have mi := hpm.img; have ms := hpm.stk; have mc := hpm.c
    obtain ⟨H1, f1, e1, hm1⟩ := upd_dn H U ctx R P A ecx edx ebx f ic hsz hhi (by omega) hcf hci (by omega) hr
    have r1 := exN_run (img := img) 8 _ _ e1 (by show ic.toNat + 8 < 2 ^ 64; omega)
    have i1 : (ic + 8).toNat = ic.toNat + 8 := u64_tN 8 (by decide) (by omega)
    have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
    have a1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108)
        H.get H1.get := by rw [hm1]; agw
    have g8 : rdRaw H1.get (U.add 8) 4 = 0x10019b := by rw [hm1]; rdv
    have g12 : rdRaw H1.get (U.add 12) 4 = ctx.add 40 := by rw [hm1]; rdv
    have g16 : rdRaw H1.get (U.add 16) 4 = P := by rw [hm1]; rdv
    have g20 : rdRaw H1.get (U.add 20) 4 = R := by rw [hm1]; rdv
    have c40 : (ctx.add 40).toNat = ctx.toNat + 40 := by ao
    obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r2, a2, hc2⟩ := memcpy_call H1 U 0x10019b (ctx.add 40) P R A ecx edx
      ebx R (ctx.add 40) P f1 (ic + 8) (by omega) (by omega) (by unfold OffCode; omega) g8 g12 g16 g20
      (by omega) (by unfold OffCode; omega) (by omega) (by unfold OffCode; omega) (by omega) (by omega)
      (by omega) (by omega)
    have hS2 : H2.get.size = H.get.size := by rw [a2.1, hS1]
    have sv : ∀ (j : UInt32) (v : UInt32), (j.toNat = U.toNat + 24 ∨ j.toNat = U.toNat + 28 ∨
        j.toNat = U.toNat + 32 ∨ j.toNat = U.toNat + 36 ∨ j.toNat = U.toNat + 40) →
        rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := by
      intro j v hj hv
      rw [rdRaw4_agree a2 (by omega) (fun k hk => by omega), rdRaw4_agree a1 (by omega) (fun k hk => by omega), hv]
    obtain ⟨f3, e3⟩ := upd_d3 H2 U sesi sedi sebx sebp ra eax2 ecx2 edx2 ebx R (ctx.add 40) P f2 ic2 (by omega)
      (by omega) (by omega) (sv _ _ (by ao) s0) (sv _ _ (by ao) s1) (sv _ _ (by ao) s2) (sv _ _ (by ao) s3)
      (sv _ _ (by ao) s4)
    have r3 := exN_run (img := img) 7 _ _ e3 (by show ic2.toNat + 7 < 2 ^ 64; omega)
    refine ⟨H2, ecx2, edx2, f3, ic2 + 7, ?_, r1.trans (r2.trans r3),
      a1.trans (a2.mono fun a h => by omega), ?_, fun i hi => ?_⟩
    · rw [u64_tN 7 (by decide) (by omega)]; omega
    · have c104 : (ctx.add 104).toNat = ctx.toNat + 104 := by ao
      rw [rdRaw4_agree a2 (by omega) (fun k hk => by omega), hm1]; rdv
    · rw [show ctx.toNat + 40 + i = (ctx.add 40).toNat + i by rw [c40], hc2 i hi, a1.2 _ (by omega) (by omega)]
      exact hb i hi

set_option maxHeartbeats 2000000 in
/-- From `0x10016b` to the return. -/
theorem upd_t (H : CMem) (U ctx L p eax ecx edx ebx f sesi sedi sebx sebp ra : UInt32) (ic : UInt64)
    (Hw : Array UInt32) (rest : List UInt8) (hF : UF H.get U ctx) (hSV : SV H.get U sesi sedi sebx sebp ra)
    (hLl : L.toNat < 2 ^ 31) (hL : rest.length = L.toNat) (hp : 0 < L.toNat → MF H.get U ctx p L.toNat)
    (hb : ∀ i, i < L.toNat → H.get.get! (p.toNat + i) = rest[i]!)
    (hw : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw[k]!)
    (hn0 : rdRaw H.get (ctx.add 104) 4 = 0) (hic : ic.toNat ≤ 2 ^ 49) :
    ∃ (H3 : CMem) (ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 2 ^ 41 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 24, L, ctx, p, 0x10016b, efl f, ic⟩)
        (St.m ⟨H3.get, 1, ecx', edx', sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat - 168 ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32 ∨
        ctx.toNat + 40 ≤ a ∧ a < ctx.toNat + 108) H.get H3.get ∧
      (∀ k, k < 8 → rdRaw H3.get (ctx + (4 * k).toUInt32) 4 =
        ((Ssl.Spec.Sha256.blocks (rest.take (64 * (L.toNat / 64)))).foldl Ssl.Spec.Sha256.compress Hw)[k]!) ∧
      rdRaw H3.get (ctx.add 104) 4 = (L.toNat % 64).toUInt32 ∧
      (∀ i, i < L.toNat % 64 → H3.get.get! (ctx.toNat + 40 + i) = (rest.drop (64 * (L.toNat / 64)))[i]!) := by
  have hF' := hF
  obtain ⟨hsz, hlo, hhi, himg, hcf, hci, hcU⟩ := hF'
  obtain ⟨H2, A, ecx2, edx2, R, P', f2, ic2, hic2, r1, a1, hR, hP, hw2⟩ :=
    upd_t1 H U ctx L p eax ecx edx ebx f ic Hw rest hF hLl hL hp hb hw (by omega)
  have hS2 : H2.get.size = H.get.size := a1.1
  obtain ⟨s0, s1, s2, s3, s4⟩ := hSV
  have sv : ∀ (j : UInt32) (v : UInt32), (j.toNat = U.toNat + 24 ∨ j.toNat = U.toNat + 28 ∨
      j.toNat = U.toNat + 32 ∨ j.toNat = U.toNat + 36 ∨ j.toNat = U.toNat + 40 ∨ j.toNat = ctx.toNat + 104) →
      rdRaw H.get j 4 = v → rdRaw H2.get j 4 = v := by
    intro j v hj hv
    rw [rdRaw4_agree a1 (by omega) (fun k hk => by omega), hv]
  have hSV2 : SV H2.get U sesi sedi sebx sebp ra :=
    ⟨sv _ _ (by ao) s0, sv _ _ (by ao) s1, sv _ _ (by ao) s2, sv _ _ (by ao) s3, sv _ _ (by ao) s4⟩
  have hn2 := sv _ _ (by ao) hn0
  have htl : (rest.drop (64 * (L.toNat / 64))).length = R.toNat := by rw [List.length_drop, hR]; omega
  have hb2 : ∀ i, i < R.toNat → H2.get.get! (P'.toNat + i) = (rest.drop (64 * (L.toNat / 64)))[i]! := by
    intro i hi
    have hpm := hp (by omega)
    have mf := hpm.fit; have ms := hpm.stk; have mc := hpm.c
    rw [hP, a1.2 _ (by omega) (by omega), Nat.add_assoc, hb _ (by omega),
      getElem!_pos rest _ (by omega), getElem!_pos (rest.drop _) i (by rw [List.length_drop]; omega),
      List.getElem_drop]
  obtain ⟨H3, ecx3, edx3, f3, ic3, hic3, r2, a2, hn3, hb3⟩ := upd_t2 H2 U ctx R P' A ecx2 edx2 ebx f2 sesi sedi sebx
    sebp ra ic2 _ (hF.size hS2) hSV2 (by omega) htl
    (fun h => ((hp (by omega)).sub (q := P') (m := R.toNat) (by rw [hP]; omega) (by rw [hP, hR]; omega)).size hS2)
    hb2 hn2
    (by omega)
  refine ⟨H3, ecx3, edx3, f3, ic3, by omega, r1.trans r2, (a1.mono fun a h => by omega).trans
    (a2.mono fun a h => by omega), words_agree a2 (fun a h1 h2 h3 => by omega) (by omega) (by omega) hw2,
    by rw [hn3]; apply UInt32.toNat_inj.1; rw [toUInt32_toNat_mod]; omega, fun i hi => hb3 i (by omega)⟩

end Solutions.ShaX
