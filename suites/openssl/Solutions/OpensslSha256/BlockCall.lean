import Solutions.OpensslSha256.BlockLoop
/-!
# A call of `sha256_block_data_order`, as a run of machine states

`bdo_call`: from the entry `0x100340` (the stack pointer `S` at the return address `ra`, the block
count `n` above it; `ecx` the context, `edx` the data) to the return to `ra`, for any memory holding
the image: the eight context words become the hash words compressed over the `n` blocks, the
callee-saved registers are restored, and memory changes only in the context words and the frame
`[S - 184, S + 8)`.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256 Ssl.Spec.Sha256

/-- The image is in memory, which ends below `ramTop`. -/
structure ImgOk (M : ByteArray) : Prop where
  sz : M.size ≤ ramTop
  img : imgBase + imgSize ≤ M.size
  code : ∀ i, i < imgSize → M.get! (imgBase + i) = Image.byte i

/-- The address facts of a call of the block function with `n ≥ 1` blocks. -/
structure BdoOk (M : ByteArray) (S ctx data : UInt32) (n : Nat) : Prop where
  npos : 0 < n
  nlt : n < 2 ^ 26
  slo : 184 ≤ S.toNat
  shi : S.toNat + 20 ≤ M.size
  simg : S.toNat + 20 ≤ imgBase ∨ imgBase + imgSize + 184 ≤ S.toNat
  cfit : ctx.toNat + 32 ≤ M.size
  cimg : ctx.toNat + 32 ≤ imgBase ∨ imgBase + imgSize ≤ ctx.toNat
  csp : ctx.toNat + 32 + 184 ≤ S.toNat ∨ S.toNat + 20 ≤ ctx.toNat
  dfit : data.toNat + 64 * n ≤ M.size
  dimg : data.toNat + 64 * n ≤ imgBase ∨ imgBase + imgSize ≤ data.toNat
  dsp : data.toNat + 64 * n + 184 ≤ S.toNat ∨ S.toNat + 20 ≤ data.toNat
  dctx : data.toNat + 64 * n ≤ ctx.toNat ∨ ctx.toNat + 32 ≤ data.toNat

theorem sub184_toNat {S : UInt32} (h : 184 ≤ S.toNat) : (S - 184).toNat = S.toNat - 184 := by
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp

/-- The environment of the call. -/
def bdoEnv (M : ByteArray) (S ctx data : UInt32) (n : Nat) (hI : ImgOk M) (hB : BdoOk M S ctx data n) : Env where
  M0 := M
  sp := S - 184
  ctx := ctx
  blk := data
  hsz := hI.sz
  himg := hI.img
  hcode := hI.code
  hsp := by rw [sub184_toNat hB.slo]; have := hB.shi; have := hB.slo; omega
  hctx := hB.cfit
  hblk := by have := hB.dfit; have := hB.npos; omega
  sp_img := by rw [sub184_toNat hB.slo]; have := hB.simg; have := hB.slo; omega
  ctx_img := hB.cimg
  blk_img := by have := hB.dimg; have := hB.npos; omega
  ctx_sp := by rw [sub184_toNat hB.slo]; have := hB.csp; have := hB.slo; omega
  blk_sp := by rw [sub184_toNat hB.slo]; have := hB.dsp; have := hB.slo; have := hB.npos; omega
  blk_ctx := by have := hB.dctx; have := hB.npos; omega

theorem bdoEnv_data {M : ByteArray} {S ctx data : UInt32} {n : Nat} (hI : ImgOk M) (hB : BdoOk M S ctx data n) :
    DataOk (bdoEnv M S ctx data n hI hB) n where
  fit := hB.dfit
  img := hB.dimg
  sp := by
    show data.toNat + 64 * n ≤ (S - 184).toNat ∨ (S - 184).toNat + 204 ≤ data.toNat
    rw [sub184_toNat hB.slo]; have := hB.dsp; have := hB.slo; omega
  ctx := hB.dctx

theorem slotAddr_bdo {M : ByteArray} {S ctx data : UInt32} {n : Nat} (hI : ImgOk M) (hB : BdoOk M S ctx data n)
    (j : Nat) (hj : j < 56) :
    (slotAddr (bdoEnv M S ctx data n hI hB) j).toNat = if j < 48 then S.toNat - 184 + 4 * j else ctx.toNat + 4 * (j - 48) := by
  rw [slotAddr_toNat _ j hj]
  show (if j < 48 then (S - 184).toNat + 4 * j else ctx.toNat + 4 * (j - 48)) = _
  rw [sub184_toNat hB.slo]

theorem rd_slot_eq {M : ByteArray} {a b : UInt32} (h : a.toNat = b.toNat) : rdBytes M a 4 = rdBytes M b 4 := by
  rw [UInt32.toNat_inj.1 h]

set_option maxHeartbeats 2000000 in
/-- A call of the block function. -/
theorem bdo_call (M : ByteArray) (S ctx data : UInt32) (n : Nat) (H : Array UInt32) (ra eax ebx ebp esi edi fl : UInt32)
    (ic : UInt64) (hI : ImgOk M) (hB : BdoOk M S ctx data n)
    (hra : rdBytes M S 4 = ra) (hn : rdBytes M (S + 4) 4 = n.toUInt32)
    (hH : ∀ k, k < 8 → rdBytes M (ctx + (4 * k).toUInt32) 4 = H[k]!)
    (hic : ic.toNat + (4029 * n + 38) < 2 ^ 64) :
    ∃ (M' : ByteArray) (fl' eax' ecx' edx' : UInt32),
      Run img (St.m ⟨M, eax, ctx, data, ebx, S, ebp, esi, edi, 0x100340, efl fl, ic⟩)
        (St.m ⟨M', eax', ecx', edx', ebx, S + 4, ebp, esi, edi, ra, efl fl', ic + (4029 * n + 38).toUInt64⟩) ∧
      M'.size = M.size ∧
      (∀ a, a < M.size → (a < S.toNat - 184 ∨ S.toNat + 8 ≤ a) → (a < ctx.toNat ∨ ctx.toNat + 32 ≤ a) →
        M'.get! a = M.get! a) ∧
      (∀ k, k < 8 → rdBytes M' (ctx + (4 * k).toUInt32) 4 = ((blks M data 0 n).foldl compress H)[k]!) := by
  let V := bdoEnv M S ctx data n hI hB
  have hspV : V.sp + 184 = S := by show S - 184 + 184 = S; exact u32_add_sub S 184
  have hseg := bdo_seg V n (bdoEnv_data hI hB) hB.npos hB.nlt H ebp ebx edi esi ra
  let r0 : R := ⟨eax, ctx, data, ebx, S, ebp, esi, edi⟩
  let F0 : Nat → UInt32 := fun j => rdBytes M (slotAddr V j) 4
  obtain ⟨r1, F1, hs⟩ := hseg r0 F0
  have hsl : ∀ j, j < 56 → (slotAddr V j).toNat = if j < 48 then S.toNat - 184 + 4 * j else ctx.toNat + 4 * (j - 48) :=
    slotAddr_bdo hI hB
  have hsz := hI.sz; have := hB.shi; have := hB.cfit; have := hB.slo
  have hctxk : ∀ k, k < 8 → (ctx + (4 * k).toUInt32).toNat = ctx.toNat + 4 * k := by
    intro k hk
    rw [UInt32.toNat_add]; simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    unfold ramTop at hsz
    rw [Nat.mod_eq_of_lt (a := 4 * k) (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have hall : AllEq F0 ([(46, ra), (47, n.toUInt32), (48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!), (52, H[4]!),
      (53, H[5]!), (54, H[6]!), (55, H[7]!)] : List (Nat × UInt32)) := by
    have e46 : F0 46 = ra := by
      show rdBytes M (slotAddr V 46) 4 = ra
      rw [← hra]; apply rd_slot_eq; rw [hsl 46 (by decide)]; simp; omega
    have e47 : F0 47 = n.toUInt32 := by
      show rdBytes M (slotAddr V 47) 4 = _
      rw [← hn]; apply rd_slot_eq; rw [hsl 47 (by decide)]
      rw [UInt32.toNat_add]; unfold ramTop at hsz; simp; omega
    have ec : ∀ k, k < 8 → F0 (48 + k) = H[k]! := by
      intro k hk
      show rdBytes M (slotAddr V (48 + k)) 4 = _
      rw [← hH k hk]; apply rd_slot_eq; rw [hsl (48 + k) (by omega), hctxk k hk, if_neg (by omega)]; omega
    exact ⟨e46, e47, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide), ec 4 (by decide),
      ec 5 (by decide), ec 6 (by decide), ec 7 (by decide), trivial⟩
  have hInv : Inv V M (updL F0 ([(46, ra), (47, n.toUInt32), (48, H[0]!), (49, H[1]!), (50, H[2]!), (51, H[3]!),
      (52, H[4]!), (53, H[5]!), (54, H[6]!), (55, H[7]!)] : List (Nat × UInt32))) :=
    ⟨rfl, fun _ _ _ => rfl, fun j _ => by rw [updL_self F0 _ hall j]⟩
  have hr0 : { r0 with esp := V.sp + 184, ecx := V.ctx, edx := V.blk, ebp := ebp, ebx := ebx, edi := edi, esi := esi } = r0 := by
    exact R.ext' rfl rfl rfl rfl hspV rfl rfl rfl
  dsimp only at hs
  rw [hr0] at hs
  obtain ⟨M', fl', hrun, hI'⟩ := hs M fl ic hInv hic
  refine ⟨M', fl', r1.eax, r1.ecx, r1.edx, ?_, hI'.size, fun a ha h1 h2 => ?_, fun k hk => ?_⟩
  · have e : V.sp + 188 = S + 4 := by
      show S - 184 + 188 = S + 4
      apply UInt32.toNat_inj.1
      have := hB.slo
      rw [UInt32.toNat_add, UInt32.toNat_add, sub184_toNat hB.slo]
      simp only [UInt32.reduceToNat]
      omega
    have hrun' : Run img (conc M r0 fl 0x100340 ic) (conc M' { r1 with ebx := ebx, esp := S + 4, ebp := ebp, esi := esi, edi := edi }
        fl' ra (ic + (4029 * n + 38).toUInt64)) := by
      rw [← e]; exact hrun
    exact hrun'
  · refine hI'.out a ha fun hin => ?_
    have e1 : (S - 184).toNat = S.toNat - 184 := sub184_toNat hB.slo
    have := hB.slo
    rcases hin with h | h
    · change (S - 184).toNat ≤ a ∧ a < (S - 184).toNat + 192 at h; omega
    · change ctx.toNat ≤ a ∧ a < ctx.toNat + 32 at h; omega
  · have hw := hI'.slot (48 + k) (by omega)
    simp only [updL, upd] at hw
    rw [rd_slot_eq (b := slotAddr V (48 + k)) (by rw [hsl (48 + k) (by omega), hctxk k hk, if_neg (by omega)]; omega), hw]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Solutions.OpensslSha256
