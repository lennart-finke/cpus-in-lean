import Solutions.OpensslX25519.I.TbBase
/-!
# `fe_frombytes` (`0x1036f0`): the ends of its run

The frame is `L = sp - 68` (`FB L 72`): the four pushes put `ebp`, `ebx`, `edi`, `esi` at `L + 64 … L + 52`,
`subl $0x30` sets `esp = L + 4` (the return address of the calls to `load_3`/`load_4` goes to `L`); the output
pointer is reloaded from `L + 48` and the ten limbs stored; then `addl $0x30`, the pops and `retl` (return
address at `L + 68`). Counts relative to a variable `ic` (prover Q).
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `pushl %ebp ; pushl %ebx ; pushl %edi ; pushl %esi` -/
theorem fb_pro (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G : XMem) (L : UInt32) (hS : FB G.get.size L 72)
    (l : List (Nat × UInt32)) (hF : Frame G L 72 l) (eax ecx edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 68, ebp, esi, edi, 0x1036f0, efl f, icAdd ic 0⟩)
      (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add L 52, ebp, esi, edi, 0x1036f4, efl f, icAdd ic 4⟩) ∧
      Frame N' L 72 ((52, esi) :: (56, edi) :: (60, ebx) :: (64, ebp) :: l) ∧
      Pres G N' (OutF L 68) := by
  refine ⟨stF (stF (stF (stF G L 72 64 ebp hS (by decide)) L 72 60 ebx stF_FB (by decide))
    L 72 56 edi stF_FB (by decide)) L 72 52 esi stF_FB (by decide), run_of_runI (k := 4) ?_ (icB hic (by decide)),
    (((hF.wrF 64 rfl rfl).wrF 60 rfl rfl).wrF 56 rfl rfl).wrF 52 rfl rfl,
    ((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide)⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF
  cbv

theorem fb_esp_sub (L : UInt32) : (subF 4 (UInt32.add L 52) 48 0).1 = UInt32.add L 4 := by
  rw [subF_fst]
  show L + 52 - 48 = L + 4
  rw [show (52 : UInt32) = 4 + 48 from rfl, ← UInt32.add_assoc, UInt32.add_sub_cancel]

/-- `subl $0x30, %esp` -/
theorem fb_sub (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 72)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 52, ebp, esi, edi, 0x1036f4, efl f, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1036f7, efl (subF 4 (UInt32.add L 52) 48 0).2,
        icAdd ic 1⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 52, ebp, esi, edi, 0x1036f4, efl f, icAdd ic 0⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (subF 4 (UInt32.add L 52) 48 0).1, ebp, esi, edi, 0x1036f7,
        efl (subF 4 (UInt32.add L 52) 48 0).2, icAdd ic 1⟩) := by
    cbv
  rw [fb_esp_sub] at h
  exact run_of_runI h (icB hic (by decide))

/-- `movl 0x2c(%esp), %eax ; movl 0xc(%esp), %ebp ; movl %ebp, (%eax) ; movl 0x8(%esp), %ebp ;
movl %ebp, 0x4(%eax) ; movl 0x4(%esp), %ebp ; movl %ebp, 0x8(%eax) ; movl 0x18(%esp), %ebp ; movl %ebp, 0xc(%eax)` -/
theorem fb_o1 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G N : XMem) (L hp : UInt32) (hS : FB N.get.size L 72)
    (hH : FB N.get.size hp 40) (hd : hp.toNat + 40 ≤ L.toNat ∨ L.toNat + 72 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N L 72 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH L 68 hp))
    (eax ecx edx ebx ebp esi edi f w0 w1 w2 w3 : UInt32) (lp : l.lookup 48 = some hp) (l0 : l.lookup 16 = some w0)
    (l1 : l.lookup 12 = some w1) (l2 : l.lookup 8 = some w2) (l3 : l.lookup 28 = some w3) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1038cf, efl f, icAdd ic 0⟩)
      (St.m ⟨N'.get, hp, ecx, edx, ebx, UInt32.add L 4, w3, esi, edi, 0x1038ee, efl f, icAdd ic 9⟩) ∧
      Frame N' L 72 l ∧ Frame N' hp 40 ((12, w3) :: (8, w2) :: (4, w1) :: (0, w0) :: lh) ∧
      Pres G N' (OutH L 68 hp) := by
  refine ⟨stF (stF (stF (stF0 N hp 40 w0 hH (by decide)) hp 40 4 w1 stF0_FB (by decide)) hp 40 8 w2 stF_FB
    (by decide)) hp 40 12 w3 stF_FB (by decide), run_of_runI (k := 9) ?_ (icB hic (by decide)),
    (((hF.wrH0 hS hd).wrH (hS.size_eq (by simp only [stF_size, stF0_size])) hd).wrH
      (hS.size_eq (by simp only [stF_size, stF0_size])) hd).wrH (hS.size_eq (by simp only [stF_size, stF0_size])) hd,
    ((hFH.wrF0).wrF 4 rfl rfl |>.wrF 8 rfl rfl).wrF 12 rfl rfl,
    ((hP.wrH0).wrH.wrH).wrH⟩
  have rp := hF.rd lp 48 rfl
  have r0 := hF.rd l0 16 rfl; have r1 := hF.rd l1 12 rfl; have r2 := hF.rd l2 8 rfl; have r3 := hF.rd l3 28 rfl
  subst rp r0 r1 r2 r3
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

/-- `movl (%esp), %ebp ; movl %ebp, 0x10(%eax) ; movl %edi, 0x14(%eax) ; movl %ebx, 0x18(%eax) ;
movl %edx, 0x1c(%eax)` -/
theorem fb_o2 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G N : XMem) (L hp : UInt32) (hS : FB N.get.size L 72)
    (hH : FB N.get.size hp 40) (hd : hp.toNat + 40 ≤ L.toNat ∨ L.toNat + 72 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N L 72 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH L 68 hp))
    (ecx edx ebx ebp esi edi f w4 : UInt32) (l4 : l.lookup 4 = some w4) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, hp, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1038ee, efl f, icAdd ic 0⟩)
      (St.m ⟨N'.get, hp, ecx, edx, ebx, UInt32.add L 4, w4, esi, edi, 0x1038fd, efl f, icAdd ic 5⟩) ∧
      Frame N' L 72 l ∧ Frame N' hp 40 ((28, edx) :: (24, ebx) :: (20, edi) :: (16, w4) :: lh) ∧
      Pres G N' (OutH L 68 hp) := by
  refine ⟨stF (stF (stF (stF N hp 40 16 w4 hH (by decide)) hp 40 20 edi stF_FB (by decide)) hp 40 24 ebx stF_FB
    (by decide)) hp 40 28 edx stF_FB (by decide), run_of_runI (k := 5) ?_ (icB hic (by decide)),
    (((hF.wrH hS hd).wrH (hS.size_eq (by simp only [stF_size])) hd).wrH
      (hS.size_eq (by simp only [stF_size])) hd).wrH (hS.size_eq (by simp only [stF_size])) hd,
    (((hFH.wrF 16 rfl rfl).wrF 20 rfl rfl).wrF 24 rfl rfl).wrF 28 rfl rfl,
    (((hP.wrH).wrH).wrH).wrH⟩
  have r4 := hF.rd l4 4 rfl
  subst r4
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

/-- `movl %esi, 0x20(%eax) ; movl %ecx, 0x24(%eax)` -/
theorem fb_o3 (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G N : XMem) (L hp : UInt32) (hS : FB N.get.size L 72)
    (hH : FB N.get.size hp 40) (hd : hp.toNat + 40 ≤ L.toNat ∨ L.toNat + 72 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N L 72 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH L 68 hp))
    (ecx edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, hp, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x1038fd, efl f, icAdd ic 0⟩)
      (St.m ⟨N'.get, hp, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103903, efl f, icAdd ic 2⟩) ∧
      Frame N' L 72 l ∧ Frame N' hp 40 ((36, ecx) :: (32, esi) :: lh) ∧
      Pres G N' (OutH L 68 hp) := by
  refine ⟨stF (stF N hp 40 32 esi hH (by decide)) hp 40 36 ecx stF_FB (by decide),
    run_of_runI (k := 2) ?_ (icB hic (by decide)),
    (hF.wrH hS hd).wrH (hS.size_eq (by simp only [stF_size])) hd,
    (hFH.wrF 32 rfl rfl).wrF 36 rfl rfl,
    (hP.wrH).wrH⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

theorem fb_esp_add (L : UInt32) : (addF 4 (UInt32.add L 4) 48 0).1 = UInt32.add L 52 := by
  rw [addF_fst]
  show L + 4 + 48 = L + 52
  rw [UInt32.add_assoc]; rfl

/-- `addl $0x30, %esp` -/
theorem fb_add (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 72)
    (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103903, efl f, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 52, ebp, esi, edi, 0x103906,
        efl (addF 4 (UInt32.add L 4) 48 0).2, icAdd ic 1⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103903, efl f, icAdd ic 0⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (addF 4 (UInt32.add L 4) 48 0).1, ebp, esi, edi, 0x103906,
        efl (addF 4 (UInt32.add L 4) 48 0).2, icAdd ic 1⟩) := by
    cbv
  rw [fb_esp_add] at h
  exact run_of_runI h (icB hic (by decide))

/-- `popl %esi ; popl %edi ; popl %ebx ; popl %ebp ; retl` -/
theorem fb_epi (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 72)
    (eax ecx edx ebx ebp esi edi f esi0 edi0 ebx0 ebp0 ret : UInt32)
    (l1 : rdRaw N.get (UInt32.add L 52) 4 = esi0) (l2 : rdRaw N.get (UInt32.add L 56) 4 = edi0)
    (l3 : rdRaw N.get (UInt32.add L 60) 4 = ebx0) (l4 : rdRaw N.get (UInt32.add L 64) 4 = ebp0)
    (l5 : rdRaw N.get (UInt32.add L 68) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 52, ebp, esi, edi, 0x103906, efl f, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add L 72, ebp0, esi0, edi0, ret, efl f, icAdd ic 5⟩) := by
  subst l1 l2 l3 l4 l5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  cbv

end Solutions.OpensslX25519.I
