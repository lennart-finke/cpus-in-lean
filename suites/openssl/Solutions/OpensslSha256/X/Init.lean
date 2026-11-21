import Solutions.OpensslSha256.X.InitRun
import Solutions.OpensslSha256.X.Tac
/-!
# `SHA256_Init` and `SHA224_Init`

The call: `init*_a`, `memset(ctx, 0, 112)` (`init_pre`), `init*_b1..b3` (`init_post`), both stated for
any Init whose pieces have the shapes of `InitRun` (the two differ only in addresses and constants). The
context bytes after it are `Good` for the empty message: the initial hash words, zero bit count and
buffer count, and the digest length.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (lw Good hOf tailOf)

theorem lw_mem {M : ByteArray} {a b : UInt32} {n k : Nat} (hk : k + 4 ≤ n) (hfit : a.toNat + n ≤ M.size)
    (hM : M.size < 2 ^ 32) (hb : b.toNat = a.toNat + k) : lw (memBytes M a n) k = rdRaw M b 4 := by
  rw [lw_memBytes hk hfit hM]
  congr 1
  apply UInt32.toNat_inj.1
  rw [hb, UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)

theorem good_init (H0 : Array UInt32) (md : Nat) (st : List UInt8) (hl : st.length = 112)
    (hh : ∀ k, k < 8 → lw st (4 * k) = H0[k]!) (h32 : lw st 32 = 0) (h36 : lw st 36 = 0) (h104 : lw st 104 = 0)
    (h108 : lw st 108 = md.toUInt32) : Good H0 md [] st :=
  ⟨hl, by unfold Ssl.Spec.Sha256.lenBound; simp, hh, h32, h36, h104, fun i hi => absurd hi (by simp), h108⟩

/-- Before the `memset` call of an Init: the piece `_a` and the call. -/
theorem init_pre (eA rA : UInt32)
    (pa : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size →
      (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) → rdRaw H.get (U.add 28) 4 = ctx →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, eA, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 4, ebp, ctx, edi, 0x101220, efl f', ic + 6⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (U.add 20) 4 esi) (U.add 16) 4 0x70)
          (U.add 12) 4 0) (U.add 8) 4 ctx) (U.add 4) 4 rA)
    (H : CMem) (U ctx ra eax ecx edx ebx ebp esi edi f : UInt32)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size) (hUc : OffCode U 32)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : OffCode ctx 112)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat)
    (hra : rdRaw H.get (U.add 24) 4 = ra) (hctx : rdRaw H.get (U.add 28) 4 = ctx) :
    ∃ (H2 : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ 600 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, eA, efl f, 0⟩)
        (St.m ⟨H2.get, eax', ecx', edx', ebx, U.add 8, ebp, ctx, edi, rA, efl f', ic'⟩) ∧
      AgreeOn (fun a => (U.toNat ≤ a ∧ a < U.toNat + 24) ∨ (ctx.toNat ≤ a ∧ a < ctx.toNat + 112)) H.get H2.get ∧
      rdRaw H2.get (U.add 20) 4 = esi ∧ rdRaw H2.get (U.add 24) 4 = ra ∧
      (∀ i, i < 112 → H2.get.get! (ctx.toNat + i) = 0) := by
  obtain ⟨H1, f1, e1, hm1⟩ := pa H U ctx eax ecx edx ebx ebp esi edi f 0 hsz (by omega) hUc hctx
  have r1 := exN_run (img := img) 6 _ _ e1 (by show (0 : UInt64).toNat + 6 < 2 ^ 64; decide)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have g4 : rdRaw H1.get (U.add 4) 4 = rA := by rw [hm1]; rdv
  have g8 : rdRaw H1.get (U.add 8) 4 = ctx := by rw [hm1]; rdv
  have g12 : rdRaw H1.get (U.add 12) 4 = 0 := by rw [hm1]; rdv
  have g16 : rdRaw H1.get (U.add 16) 4 = 112 := by rw [hm1]; rdv
  have g20 : rdRaw H1.get (U.add 20) 4 = esi := by rw [hm1]; rdv
  have g24 : rdRaw H1.get (U.add 24) 4 = ra := by rw [hm1]; rdv; exact hra
  have a1 : AgreeOn (fun a => (U.toNat ≤ a ∧ a < U.toNat + 24) ∨ (ctx.toNat ≤ a ∧ a < ctx.toNat + 112)) H.get H1.get := by
    rw [hm1]; agw
  have h112 : (112 : UInt32).toNat = 112 := rfl
  obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r2, hA2, hz2⟩ := memset_call H1 U rA ctx 0 112
    eax ecx edx ebx ebp ctx edi f1 (0 + 6) (by omega) (by omega) (by unfold OffCode at hUc ⊢; omega) g4 g8 g12 g16
    (by rw [h112]; omega) (by rw [h112]; exact hcc) (by rw [h112]; omega) (by rw [h112]; decide)
  rw [h112] at hic2 hz2 hA2
  refine ⟨H2, eax2, ecx2, edx2, f2, ic2, by rw [show ((0 : UInt64) + 6).toNat = 6 from rfl] at hic2; omega, r1.trans r2,
    a1.trans (hA2.mono fun a h => by omega), ?_, ?_, fun i hi => by rw [hz2 i hi]; rfl⟩
  · rw [rdRaw4_agree hA2 (by ao) (fun k hk => by ao), g20]
  · rw [rdRaw4_agree hA2 (by ao) (fun k hk => by ao), g24]

/-- After the `memset` call of an Init: the pieces `_b1`, `_b2`, `_b3`. -/
theorem init_post (e1 e2 e3 w0 w1 w2 w3 w4 w5 w6 w7 md : UInt32)
    (p1 : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      ctx.toNat + 112 ≤ H.get.size → (1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576) →
      (ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, ctx, edi, e1, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e2, efl f', ic + 5⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx) 4 w0) (ctx.add 4) 4 w1) (ctx.add 8) 4 w2) (ctx.add 12) 4 w3)
    (p2 : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      ctx.toNat + 112 ≤ H.get.size → (1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576) →
      (ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e2, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e3, efl f', ic + 5⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx.add 16) 4 w4) (ctx.add 20) 4 w5)
          (ctx.add 24) 4 w6) (ctx.add 28) 4 w7) (ctx.add 108) 4 md)
    (p3 : ∀ (H : CMem) (U ctx sv ra eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      rdRaw H.get (U.add 20) 4 = sv → rdRaw H.get (U.add 24) 4 = ra →
      ∃ f' : UInt32,
        exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e3, efl f, ic⟩ =
          some ⟨H.get, 1, ecx, edx, ebx, U.add 28, ebp, sv, edi, ra, efl f', ic + 3⟩)
    (H : CMem) (U ctx ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size) (hUc : OffCode U 32)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : OffCode ctx 112)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) (hic : ic.toNat ≤ 600)
    (hsv : rdRaw H.get (U.add 20) 4 = esi) (hra : rdRaw H.get (U.add 24) 4 = ra)
    (hz : ∀ i, i < 112 → H.get.get! (ctx.toNat + i) = 0) :
    ∃ (H3 : CMem) (f' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, ctx, edi, e1, efl f, ic⟩)
        (St.m ⟨H3.get, 1, ecx, edx, ebx, U.add 28, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => ctx.toNat ≤ a ∧ a < ctx.toNat + 112) H.get H3.get ∧
      rdRaw H3.get ctx 4 = w0 ∧ rdRaw H3.get (ctx.add 4) 4 = w1 ∧ rdRaw H3.get (ctx.add 8) 4 = w2 ∧
      rdRaw H3.get (ctx.add 12) 4 = w3 ∧ rdRaw H3.get (ctx.add 16) 4 = w4 ∧ rdRaw H3.get (ctx.add 20) 4 = w5 ∧
      rdRaw H3.get (ctx.add 24) 4 = w6 ∧ rdRaw H3.get (ctx.add 28) 4 = w7 ∧
      rdRaw H3.get (ctx.add 32) 4 = 0 ∧ rdRaw H3.get (ctx.add 36) 4 = 0 ∧
      rdRaw H3.get (ctx.add 104) 4 = 0 ∧ rdRaw H3.get (ctx.add 108) 4 = md := by
  obtain ⟨H1, f1, e1', hm1⟩ := p1 H U ctx eax ecx edx ebx ebp edi f ic hsz hU hUc hc hcc hcU
  have r1 := exN_run (img := img) 5 _ _ e1' (by show ic.toNat + 5 < 2 ^ 64; omega)
  have hS1 : H1.get.size = H.get.size := by rw [hm1]; simp only [Solutions.Exec.size_wrBytes]
  have hi1 : (ic + 5).toNat = ic.toNat + 5 := u64_tN 5 (by decide) (by omega)
  obtain ⟨H2, f2, e2', hm2⟩ := p2 H1 U ctx eax ecx edx ebx ebp edi f1 (ic + 5) (by omega) (by omega) hUc
    (by omega) hcc hcU
  have r2 := exN_run (img := img) 5 _ _ e2' (by show (ic + 5).toNat + 5 < 2 ^ 64; omega)
  have hS2 : H2.get.size = H.get.size := by rw [hm2]; simp only [Solutions.Exec.size_wrBytes]; exact hS1
  have hi2 : (ic + 5 + 5).toNat = ic.toNat + 10 := by rw [u64_tN (ic := ic + 5) 5 (by decide) (by omega), hi1]
  have g20 : rdRaw H2.get (U.add 20) 4 = esi := by rw [hm2]; rdv; rw [hm1]; rdv; exact hsv
  have g24 : rdRaw H2.get (U.add 24) 4 = ra := by rw [hm2]; rdv; rw [hm1]; rdv; exact hra
  obtain ⟨f3, e3'⟩ := p3 H2 U ctx esi ra eax ecx edx ebx ebp edi f2 (ic + 5 + 5) (by omega) (by omega) hUc g20 g24
  have r3 := exN_run (img := img) 3 _ _ e3' (by show (ic + 5 + 5).toNat + 3 < 2 ^ 64; omega)
  have a1 : AgreeOn (fun a => ctx.toNat ≤ a ∧ a < ctx.toNat + 112) H.get H1.get := by rw [hm1]; agw
  have a2 : AgreeOn (fun a => ctx.toNat ≤ a ∧ a < ctx.toNat + 112) H1.get H2.get := by rw [hm2]; agw
  refine ⟨H2, f3, _, r1.trans (r2.trans r3), a1.trans a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm2]; rdv; rw [hm1]; rdv
  · rw [hm2]; rdv; rw [hm1]; rdv
  · rw [hm2]; rdv; rw [hm1]; rdv
  · rw [hm2]; rdv; rw [hm1]; rdv
  · rw [hm2]; rdv
  · rw [hm2]; rdv
  · rw [hm2]; rdv
  · rw [hm2]; rdv
  · rw [hm2]; rdv; rw [hm1]; rdv; exact rd_zero_at 32 (by decide) hc hsz hz
  · rw [hm2]; rdv; rw [hm1]; rdv; exact rd_zero_at 36 (by decide) hc hsz hz
  · rw [hm2]; rdv; rw [hm1]; rdv; exact rd_zero_at 104 (by decide) hc hsz hz
  · rw [hm2]; rdv

/-- The words of the context after an Init make it `Good` for the empty message. -/
theorem good_of_words (H0 : Array UInt32) (md : Nat) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt32)
    (hH0 : H0 = #[w0, w1, w2, w3, w4, w5, w6, w7]) (M : ByteArray) (ctx : UInt32)
    (hM : M.size ≤ 4273995776) (hc : ctx.toNat + 112 ≤ M.size)
    (h0 : rdRaw M ctx 4 = w0) (h1 : rdRaw M (ctx.add 4) 4 = w1) (h2 : rdRaw M (ctx.add 8) 4 = w2)
    (h3 : rdRaw M (ctx.add 12) 4 = w3) (h4 : rdRaw M (ctx.add 16) 4 = w4) (h5 : rdRaw M (ctx.add 20) 4 = w5)
    (h6 : rdRaw M (ctx.add 24) 4 = w6) (h7 : rdRaw M (ctx.add 28) 4 = w7)
    (h32 : rdRaw M (ctx.add 32) 4 = 0) (h36 : rdRaw M (ctx.add 36) 4 = 0)
    (h104 : rdRaw M (ctx.add 104) 4 = 0) (h108 : rdRaw M (ctx.add 108) 4 = md.toUInt32) :
    Good H0 md [] (memBytes M ctx 112) := by
  have hM' : M.size < 2 ^ 32 := by omega
  subst hH0
  refine good_init _ _ _ (memBytes_length _ _ _) (fun k hk => ?_) ?_ ?_ ?_ ?_
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lw_mem (b := ctx) (by decide) hc hM' (by omega), h0]; rfl
    · rw [lw_mem (b := ctx.add 4) (by decide) hc hM' (by ao), h1]; rfl
    · rw [lw_mem (b := ctx.add 8) (by decide) hc hM' (by ao), h2]; rfl
    · rw [lw_mem (b := ctx.add 12) (by decide) hc hM' (by ao), h3]; rfl
    · rw [lw_mem (b := ctx.add 16) (by decide) hc hM' (by ao), h4]; rfl
    · rw [lw_mem (b := ctx.add 20) (by decide) hc hM' (by ao), h5]; rfl
    · rw [lw_mem (b := ctx.add 24) (by decide) hc hM' (by ao), h6]; rfl
    · rw [lw_mem (b := ctx.add 28) (by decide) hc hM' (by ao), h7]; rfl
  · rw [lw_mem (b := ctx.add 32) (by decide) hc hM' (by ao), h32]
  · rw [lw_mem (b := ctx.add 36) (by decide) hc hM' (by ao), h36]
  · rw [lw_mem (b := ctx.add 104) (by decide) hc hM' (by ao), h104]
  · rw [lw_mem (b := ctx.add 108) (by decide) hc hM' (by ao), h108]

/-- An Init whose pieces have the shapes of `InitRun`. -/
theorem init_ok_gen (eA rA e2 e3 w0 w1 w2 w3 w4 w5 w6 w7 mdw : UInt32) (H0 : Array UInt32) (md : Nat)
    (hH0 : H0 = #[w0, w1, w2, w3, w4, w5, w6, w7]) (hmd : md.toUInt32 = mdw)
    (pa : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size →
      (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) → rdRaw H.get (U.add 28) 4 = ctx →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, eA, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 4, ebp, ctx, edi, 0x101220, efl f', ic + 6⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (U.add 20) 4 esi) (U.add 16) 4 0x70)
          (U.add 12) 4 0) (U.add 8) 4 ctx) (U.add 4) 4 rA)
    (p1 : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      ctx.toNat + 112 ≤ H.get.size → (1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576) →
      (ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, ctx, edi, rA, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e2, efl f', ic + 5⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx) 4 w0) (ctx.add 4) 4 w1) (ctx.add 8) 4 w2) (ctx.add 12) 4 w3)
    (p2 : ∀ (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      ctx.toNat + 112 ≤ H.get.size → (1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576) →
      (ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) →
      ∃ (H' : CMem) (f' : UInt32),
        exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e2, efl f, ic⟩ =
          some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e3, efl f', ic + 5⟩ ∧
        H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx.add 16) 4 w4) (ctx.add 20) 4 w5)
          (ctx.add 24) 4 w6) (ctx.add 28) 4 w7) (ctx.add 108) 4 mdw)
    (p3 : ∀ (H : CMem) (U ctx sv ra eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64),
      H.get.size ≤ 4273995776 → U.toNat + 32 ≤ H.get.size → (1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) →
      rdRaw H.get (U.add 20) 4 = sv → rdRaw H.get (U.add 24) 4 = ra →
      ∃ f' : UInt32,
        exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, e3, efl f, ic⟩ =
          some ⟨H.get, 1, ecx, edx, ebx, U.add 28, ebp, sv, edi, ra, efl f', ic + 3⟩)
    (c : Caller) (ctx : UInt32) (hpre : InitPre c ctx) :
    Returns img (c.enter eA) stackBound (InRange ctx ctxSize) fun m1 =>
      m1.cpu.eax = 1 ∧ Good H0 md [] (bytesAt m1 ctx ctxSize) := by
  obtain ⟨hC, hB⟩ := hpre
  have hS := spOk_of hC
  simp only [List.length_cons, List.length_nil] at hS
  have hX := bufOk_of hB (by decide) hS.lo
  unfold ctxSize at hX ⊢
  obtain ⟨H, hH⟩ : ∃ H : CMem, H.get = c.mem := ⟨cmemOf hC, rfl⟩
  have hHs : H.get.size = c.mem.size := by rw [hH]
  have hlo := hS.lo; have hhi := hS.hi; have himg := hS.img; have hsz := hS.sz
  have xf := hX.fit; have xi := hX.img; have xs := hX.stk
  have tU : (c.sp - 24).toNat = c.sp.toNat - 24 := frame_tN 24 24 rfl (by omega)
  have hUc : OffCode (c.sp - 24) 32 := by unfold OffCode; omega
  have hcc : OffCode ctx 112 := by unfold OffCode; omega
  have hcU : ctx.toNat + 112 ≤ (c.sp - 24).toNat ∨ (c.sp - 24).toNat + 32 ≤ ctx.toNat := by omega
  have hret := frame_ret hC H hH 24
  have hctx : rdRaw H.get ((c.sp - 24).add 28) 4 = ctx := by
    have := calls_arg hC 0 (by simp)
    rw [show (28 : UInt32) = 24 + 4 from rfl, sp_frame, hH]; show rdBytes c.mem (c.sp + 4) 4 = ctx; simpa using this
  clear himg xi xs hX hS hB
  obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r1, hA1, hsv, hra, hz⟩ := init_pre eA rA pa H (c.sp - 24) ctx
    Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags
    (by omega) (by omega) hUc (by omega) hcc hcU hret hctx
  have hS2 : H2.get.size = c.mem.size := by rw [hA1.1, hHs]
  obtain ⟨H3, f3, ic3, r2, hA2, h0, h1, h2, h3, h4, h5, h6, h7, h32, h36, h104, h108⟩ := init_post rA e2 e3
    w0 w1 w2 w3 w4 w5 w6 w7 mdw p1 p2 p3 H2 (c.sp - 24) ctx Image.sym_halt eax2 ecx2 edx2 c.regs.ebx c.regs.ebp
    c.regs.esi c.regs.edi f2 ic2 (by omega) (by omega) hUc (by omega) hcc hcU hic2 hsv hra hz
  have hS3 : H3.get.size = c.mem.size := by rw [hA2.1, hS2]
  have e28 : (c.sp - 24).add 28 = c.sp + 4 := by rw [show (28 : UInt32) = 24 + 4 from rfl, sp_frame]
  rw [e28] at r2
  refine returns_of_run c _ _ _ H3.get 1 ecx2 edx2 _ _
    (fun a => ((c.sp - 24).toNat ≤ a ∧ a < (c.sp - 24).toNat + 24) ∨ (ctx.toNat ≤ a ∧ a < ctx.toNat + 112))
    (by rw [enter_frame c H hH 24]; exact r1.trans r2) ?_ ?_ ⟨rfl, ?_⟩
  · rw [hH] at hA1
    exact hA1.trans (hA2.mono fun a h => Or.inr h)
  · intro a ha
    rw [inRange_iff, inRange_iff, stack_lo c hlo]
    omega
  · show Good _ _ _ (memBytes H3.get ctx 112)
    exact good_of_words H0 md w0 w1 w2 w3 w4 w5 w6 w7 hH0 H3.get ctx (by omega) (by omega)
      h0 h1 h2 h3 h4 h5 h6 h7 h32 h36 h104 (by rw [h108, hmd])

theorem init256_ok (c : Caller) (ctx : UInt32) (hpre : InitPre c ctx) :
    Returns img (c.enter Image.sym_SHA256_Init) stackBound (InRange ctx ctxSize) fun m1 =>
      m1.cpu.eax = 1 ∧ Good Ssl.Spec.Sha256.H0_256 32 [] (bytesAt m1 ctx ctxSize) :=
  init_ok_gen 0x100060 0x10006f 0x10008d 0x1000b0 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
    0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19 32 _ 32 rfl rfl init256_a init256_b1 init256_b2 init256_b3 c ctx hpre

theorem init224_ok (c : Caller) (ctx : UInt32) (hpre : InitPre c ctx) :
    Returns img (c.enter Image.sym_SHA224_Init) stackBound (InRange ctx ctxSize) fun m1 =>
      m1.cpu.eax = 1 ∧ Good Ssl.Spec.Sha256.H0_224 28 [] (bytesAt m1 ctx ctxSize) :=
  init_ok_gen 0x100000 0x10000f 0x10002d 0x100050 0xc1059ed8 0x367cd507 0x3070dd17 0xf70e5939
    0xffc00b31 0x68581511 0x64f98fa7 0xbefa4fa4 28 _ 28 rfl rfl init224_a init224_b1 init224_b2 init224_b3 c ctx hpre

end Solutions.ShaX
