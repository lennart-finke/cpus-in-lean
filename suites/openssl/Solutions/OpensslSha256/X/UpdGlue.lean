import Solutions.OpensslSha256.X.Tac
import Solutions.OpensslSha256.BlockCall
/-!
# Calls inside `SHA256_Update` and `SHA256_Final`, in the frame of the caller

The stack pointer of the caller is `U.add 24` before it pushes the arguments of a call. `bdo_U`: the
block function called with the stack pointer at `U.add 16` (its return address there, the count at
`U.add 20`); `memset_U`: `memset` called with the stack pointer at `U.add 8`. The memory after the
block function is again a `CMem` (`cmem_of`). `blks_eq`: the blocks the block function reads are the
`blocks` of the bytes in memory. `CtxOk`: the fields of the context in memory.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
open Solutions.OpensslSha256 (ImgOk BdoOk bdo_call blks blkAt bAddr imgBase imgSize)

/-- A memory that agrees with a `CMem` on the image is one. -/
def cmem_of (H : CMem) (M : ByteArray) (hs : M.size = H.get.size)
    (hi : ∀ i, i < 4944 → M.get! (1048576 + i) = H.get.get! (1048576 + i)) : CMem :=
  ⟨M, by rw [hs]; exact H.fits, fun i hi' => by rw [show Image.base.toNat = 1048576 from rfl, hi i hi']; exact H.ok i hi'⟩

theorem cmem_of_get (H : CMem) (M : ByteArray) (hs) (hi) : (cmem_of H M hs hi).get = M := rfl

theorem imgOk_of (H : CMem) (hsz : H.get.size ≤ 4273995776) : ImgOk H.get where
  sz := hsz
  img := H.fits
  code := fun i hi => H.ok i hi

theorem uadd_add (U : UInt32) (a b : UInt32) : U.add a + b = U.add (a + b) := UInt32.add_assoc U a b

theorem uadd_uadd (U : UInt32) (a b : UInt32) : (U.add a).add b = U.add (a + b) := UInt32.add_assoc U a b

/-- The block function, called with the stack pointer at `U.add 16`. -/
theorem bdo_U (H : CMem) (U ctx data : UInt32) (n : Nat) (Hw : Array UInt32) (ra eax ebx ebp esi edi fl : UInt32)
    (ic : UInt64) (hsz : H.get.size ≤ 4273995776) (hlo : 168 ≤ U.toNat) (hhi : U.toNat + 36 ≤ H.get.size)
    (himg : U.toNat + 36 ≤ 1048576 ∨ 1048576 + 4944 + 168 ≤ U.toNat)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : OffCode ctx 112)
    (hcU : ctx.toNat + 112 + 168 ≤ U.toNat ∨ U.toNat + 36 ≤ ctx.toNat)
    (hn0 : 0 < n) (hn : n < 2 ^ 26) (hd : data.toNat + 64 * n ≤ H.get.size) (hdc : OffCode data (64 * n))
    (hdU : data.toNat + 64 * n + 168 ≤ U.toNat ∨ U.toNat + 36 ≤ data.toNat)
    (hdx : data.toNat + 64 * n ≤ ctx.toNat ∨ ctx.toNat + 32 ≤ data.toNat)
    (hra : rdRaw H.get (U.add 16) 4 = ra) (hnw : rdRaw H.get (U.add 20) 4 = n.toUInt32)
    (hH : ∀ k, k < 8 → rdRaw H.get (ctx + (4 * k).toUInt32) 4 = Hw[k]!)
    (hic : ic.toNat + (4029 * n + 38) < 2 ^ 64) :
    ∃ (H' : CMem) (fl' eax' ecx' edx' : UInt32),
      Run img (St.m ⟨H.get, eax, ctx, data, ebx, U.add 16, ebp, esi, edi, 0x100340, efl fl, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, U.add 20, ebp, esi, edi, ra, efl fl', ic + (4029 * n + 38).toUInt64⟩) ∧
      AgreeOn (fun a => U.toNat - 168 ≤ a ∧ a < U.toNat + 24 ∨ ctx.toNat ≤ a ∧ a < ctx.toNat + 32) H.get H'.get ∧
      (∀ k, k < 8 → rdRaw H'.get (ctx + (4 * k).toUInt32) 4 = ((blks H.get data 0 n).foldl Ssl.Spec.Sha256.compress Hw)[k]!) := by
  unfold OffCode at hcc hdc
  have t16 : (U.add 16).toNat = U.toNat + 16 := by ao
  have hB : BdoOk H.get (U.add 16) ctx data n :=
    { npos := hn0, nlt := hn, slo := by omega, shi := by omega,
      simg := by unfold imgBase imgSize; omega, cfit := by omega, cimg := by unfold imgBase imgSize; omega,
      csp := by omega, dfit := hd, dimg := by unfold imgBase imgSize; omega, dsp := by omega, dctx := hdx }
  have e4 : U.add 16 + 4 = U.add 20 := uadd_add U 16 4
  obtain ⟨M', fl', eax', ecx', edx', hr, hs, ho, hw⟩ := bdo_call H.get (U.add 16) ctx data n Hw ra eax ebx ebp esi edi fl ic
    (imgOk_of H hsz) hB hra (by rw [e4]; exact hnw) hH hic
  have hi : ∀ i, i < 4944 → M'.get! (1048576 + i) = H.get.get! (1048576 + i) := fun i hi' =>
    ho _ (by have hf : 1048576 + 4944 ≤ H.get.size := H.fits; omega) (by omega) (by omega)
  refine ⟨cmem_of H M' hs hi, fl', eax', ecx', edx', by rw [cmem_of_get, ← e4]; exact hr, ⟨hs, fun a ha hn' => ?_⟩, hw⟩
  rw [cmem_of_get]
  exact ho a ha (by omega) (by omega)

/-- `memset`, called with the stack pointer at `U.add 8`. -/
theorem memset_U (H : CMem) (U ra dst c n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 24 ≤ H.get.size) (hUc : OffCode U 24)
    (hra : rdRaw H.get (U.add 8) 4 = ra) (hdst : rdRaw H.get (U.add 12) 4 = dst)
    (hc : rdRaw H.get (U.add 16) 4 = c) (hn : rdRaw H.get (U.add 20) 4 = n)
    (hd : dst.toNat + n.toNat ≤ H.get.size) (hdc : OffCode dst n.toNat)
    (hdU : dst.toNat + n.toNat ≤ U.toNat + 4 ∨ U.toNat + 24 ≤ dst.toNat)
    (hic : ic.toNat + 4 * n.toNat + 30 < 2 ^ 64) :
    ∃ (H' : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 4 * n.toNat + 22 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, esi, edi, 0x101220, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, U.add 12, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat + 4 ≤ a ∧ a < U.toNat + 8 ∨ dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H.get H'.get ∧
      ∀ i, i < n.toNat → H'.get.get! (dst.toNat + i) = c.toUInt8 := by
  unfold OffCode at hUc
  have t4 : (U.add 4).toNat = U.toNat + 4 := by ao
  have e : ∀ k : UInt32, (U.add 4).add k = U.add (4 + k) := fun k => uadd_uadd U 4 k
  obtain ⟨H', eax', ecx', edx', f', ic', hic', hr, ha, hb⟩ := memset_call H (U.add 4) ra dst c n eax ecx edx ebx ebp
    esi edi f ic hsz (by omega) (by unfold OffCode; omega) (by rw [e]; exact hra) (by rw [e]; exact hdst)
    (by rw [e]; exact hc) (by rw [e]; exact hn) hd hdc (by omega) hic
  rw [e, e] at hr
  refine ⟨H', eax', ecx', edx', f', ic', hic', hr, ha.mono fun a h => by omega, hb⟩

theorem blkAt_eq (M : ByteArray) (d : UInt32) (L : List UInt8) (i : Nat) (hM : M.size < 2 ^ 32)
    (hfit : d.toNat + 64 * i + 64 ≤ M.size) (hL : 64 ≤ L.length)
    (hb : ∀ k, k < 64 → M.get! (d.toNat + 64 * i + k) = L[k]!) : blkAt M d i = L.take 64 := by
  have hb' : (bAddr d i).toNat = d.toNat + 64 * i := by
    unfold bAddr
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  unfold blkAt
  apply List.ext_getElem
  · rw [memBytes_length, List.length_take]; omega
  · intro k h1 h2
    rw [memBytes_length] at h1
    have e := memBytes_get (M := M) (a := bAddr d i) (n := 64) (i := k) h1 (by rw [hb']; omega) hM
    rw [getElem!_pos _ k (by rw [memBytes_length]; exact h1)] at e
    rw [e, hb', hb k h1, getElem!_pos L k (by omega), List.getElem_take]

/-- The blocks the block function reads, as `blocks` of the bytes. -/
theorem blks_eq (M : ByteArray) (d : UInt32) (hM : M.size < 2 ^ 32) :
    ∀ (n i : Nat) (L : List UInt8), d.toNat + 64 * (i + n) ≤ M.size → L.length = 64 * n →
      (∀ k, k < 64 * n → M.get! (d.toNat + 64 * i + k) = L[k]!) → blks M d i n = Ssl.Spec.Sha256.blocks L := by
  intro n
  induction n with
  | zero =>
    intro i L _ hL _
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ n ih =>
    intro i L hfit hL hb
    rw [Solutions.OpensslSha256.blocks_cons64 L (by omega)]
    show blkAt M d i :: blks M d (i + 1) n = _
    rw [blkAt_eq M d L i hM (by omega) (by omega) (fun k hk => hb k (by omega))]
    congr 1
    apply ih (i + 1) (L.drop 64) (by omega) (by rw [List.length_drop]; omega)
    intro k hk
    rw [show d.toNat + 64 * (i + 1) + k = d.toNat + 64 * i + (64 + k) by omega, hb (64 + k) (by omega)]
    rw [getElem!_pos L (64 + k) (by omega), getElem!_pos (L.drop 64) k (by rw [List.length_drop]; omega),
      List.getElem_drop]

end Solutions.ShaX
