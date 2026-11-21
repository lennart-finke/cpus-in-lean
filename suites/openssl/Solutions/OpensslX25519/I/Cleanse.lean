import Solutions.OpensslX25519.I.LadHead2
import Solutions.OpensslX25519.I.MemCall
/-!
# `OPENSSL_cleanse(ptr, len)` (`0x103e80`) as a callee

`movl 0x10b7ac, %eax` (the pointer `memset_func` in the image, which holds `memset`, `memset_ptr`); push
`len`, `0`, `ptr`; `call *%eax`; `addl $0xc, %esp ; retl`. The frame is `[L, L + 32)`: `memset`'s saved
`esi` at `L`, the return address into `OPENSSL_cleanse` at `L + 4`, the arguments of `memset` at `L + 8`,
the return address at `L + 20`, `ptr` and `len` at `L + 24`, `L + 28`. Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte Solutions.Exec.Shift

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
theorem cl_a (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 32)
    (eax ecx edx ebx ebp esi edi fl p n : UInt32) (lp : rdRaw N.get (UInt32.add L 24) 4 = p)
    (ln : rdRaw N.get (UInt32.add L 28) 4 = n) (hfit : 0x100000 + 47024 ≤ N.get.size)
    (hm : rdRaw N.get 0x10b7ac 4 = 0x103f60) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x103e80, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF (stF N L 32 16 n hS (by decide)) L 32 12 0 stF_FB (by decide)) L 32 8 p stF_FB (by decide))
        L 32 4 0x103e91 stF_FB (by decide)).get, 0x103f60, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103f60, efl fl,
        icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst lp ln
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
  rw [hm]

/-- `addl $0xc, %esp ; retl` -/
theorem cl_b (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 32)
    (eax ecx edx ebx ebp esi edi fl ret : UInt32) (lr : rdRaw N.get (UInt32.add L 20) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103e91, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 24, ebp, esi, edi, ret, efl (addF 4 (UInt32.add L 8) 12 0).2,
        icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  subst lr
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

theorem icAdd_zero' (x : UInt64) : icAdd x 0 = x := rfl

/-- The word at `0x10b7ac` (`memset_func`) is `memset`. -/
theorem memset_ptr (H : XMem) : rdRaw H.get 0x10b7ac 4 = 0x103f60 := by
  have hf : 1048576 + 47024 ≤ H.get.size := H.fits
  have hb : (1095596 : UInt32).toNat = 1095596 := rfl
  have e0 : H.get.get! 1095596 = Image.byte 47020 := H.ok 47020 (by decide)
  have e1 : H.get.get! (1095596 + 1) = Image.byte 47021 := H.ok 47021 (by decide)
  have e2 : H.get.get! (1095596 + 2) = Image.byte 47022 := H.ok 47022 (by decide)
  have e3 : H.get.get! (1095596 + 3) = Image.byte 47023 := H.ok 47023 (by decide)
  unfold rdRaw
  rw [rdBytes4_eq (by rw [hb]; omega), hb, e0, e1, e2, e3]
  decide

/-- A call `OPENSSL_cleanse(ptr, len)`, `len ≥ 1`: the `len` bytes at `ptr` become zero. -/
theorem cleanse_call (G : XMem) (L ret ptr len eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 32) (lr : rdRaw G.get (UInt32.add L 20) 4 = ret)
    (lp : rdRaw G.get (UInt32.add L 24) 4 = ptr) (ll : rdRaw G.get (UInt32.add L 28) 4 = len)
    (hn : 1 ≤ len.toNat) (hd : ptr.toNat + len.toNat ≤ G.get.size)
    (hdi : ptr.toNat + len.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ ptr.toNat)
    (hdL : ptr.toNat + len.toNat ≤ L.toNat ∨ L.toNat + 32 ≤ ptr.toNat)
    (hic : ic0.toNat + 4 * len.toNat + 40 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x103e80, efl fl, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 24, ebp, esi, edi, ret, efl fl',
          icAdd ic0 (4 * len.toNat + 29)⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 20 ≤ x) ∧ (x < ptr.toNat ∨ ptr.toNat + len.toNat ≤ x)) ∧
      ∀ a : UInt32, ptr.toNat ≤ a.toNat → a.toNat < ptr.toNat + len.toNat → memByte N.get a = 0 := by
  have htop := hS.top
  have F0 : Frame G L 32 [(20, ret)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lr⟩
    · simp at hl
  have R1 := cl_a ic0 (by omega) G L hS eax ecx edx ebx ebp esi edi fl ptr len lp ll G.fits (memset_ptr G)
  have FA := (((F0.wrF 16 (j := 16) (v := len) (h := hS) (hj := by decide) rfl rfl).wrF 12 (j := 12)
    (v := 0) (h := stF_FB) (hj := by decide) rfl rfl).wrF 8 (j := 8) (v := ptr) (h := stF_FB) (hj := by decide)
    rfl rfl).wrF 4 (j := 4) (v := 0x103e91) (h := stF_FB) (hj := by decide) rfl rfl
  generalize hM1 : stF (stF (stF (stF G L 32 16 len hS (by decide)) L 32 12 0 stF_FB (by decide)) L 32 8 ptr stF_FB
    (by decide)) L 32 4 0x103e91 stF_FB (by decide) = M1 at R1 FA
  have P1 : Pres G M1 (OutF L 20) := by
    rw [← hM1]
    exact ((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide)
  have hS1 : FB M1.get.size L 32 := hS.pres P1
  have hS1' : FB M1.get.size L 20 := ⟨hS1.top, by have := hS1.fit; omega, by have := hS1.img; omega⟩
  have hsz1 : M1.get.size = G.get.size := P1.1
  obtain ⟨M2, eax2, ecx2, edx2, fl2, R2, P2, B2⟩ := memset_call M1 L 0x103e91 ptr 0 len 0x103f60 ecx edx ebx ebp esi edi
    fl (icAdd ic0 5) hS1' (FA.rd (rfl : List.lookup 4 _ = some _) 4 rfl) (FA.rd (rfl : List.lookup 8 _ = some _) 8 rfl)
    (FA.rd (rfl : List.lookup 12 _ = some _) 12 rfl) (FA.rd (rfl : List.lookup 16 _ = some _) 16 rfl) hn
    (by rw [hsz1]; exact hd) hdi (by omega) (by rw [icAdd_toNat _ _ (by omega)]; omega)
  rw [icAdd_zero', icAdd_add ic0 5 (4 * len.toNat + 22)] at R2
  have e20 : (UInt32.add L 20).toNat = L.toNat + 20 := hS.add_toNat (j := 20) (by decide)
  have lr2 : rdRaw M2.get (UInt32.add L 20) 4 = ret := by
    rw [P2.rd hS1.top (by rw [e20]; have := hS1.fit; omega) (fun j hj => by rw [e20]; omega)]
    exact FA.rd (rfl : List.lookup 20 _ = some ret) 20 rfl
  have R3 := cl_b (icAdd ic0 (5 + (4 * len.toNat + 22))) (icB' (k := 2) (by omega)) M2 L (hS1.pres P2) eax2 ecx2 edx2
    ebx ebp esi edi fl2 ret lr2
  have e3 : icAdd (icAdd ic0 (5 + (4 * len.toNat + 22))) 2 = icAdd ic0 (4 * len.toNat + 29) := by
    rw [icAdd_add]; congr 1; omega
  rw [e3, icAdd_zero'] at R3
  refine ⟨M2, _, _, _, _, R1.trans (R2.trans R3), (P1.trans P2).mono fun x hx => ⟨?_, ⟨?_, hx.2⟩⟩, B2⟩
  · unfold OutF; rcases hx.1 with h | h <;> omega
  · rcases hx.1 with h | h <;> omega

end Solutions.OpensslX25519.I
