import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
import Solutions.Exec.Alu
/-!
# The run of `fe_mul`: prologue, output stores, epilogue

The pieces of the run of `fe_mul` around its body (`SqRun*`): the four pushes and the frame
allocation, the ten stores into the output buffer `hp` (loaded from the frame), and the frame
release, the four pops and the return. The stack pointer after `subl $0x32c, %esp` and after
`addl $0x32c, %esp` is rewritten to `fb` and `fb + 812`.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

set_option exec.addrSub true in
/-- `pushl %ebp ; pushl %ebx ; pushl %edi ; pushl %esi` (fe_mul) -/
theorem mul_pro (G : XMem) (fb : UInt32) (hS : FB G.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame G fb 836 l) (eax ecx edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add fb 828, ebp, esi, edi, 0x100c20, efl f, 0⟩)
      (St.m ⟨N'.get, eax, ecx, edx, ebx, UInt32.add fb 812, ebp, esi, edi, 0x100c24, efl f, 4⟩) ∧
      Frame N' fb 836 ((812, esi) :: (816, edi) :: (820, ebx) :: (824, ebp) :: l) ∧
      Pres G N' (OutF fb 828) := by
  refine ⟨stF (stF (stF (stF G fb 836 824 ebp hS (by decide)) fb 836 820 ebx stF_FB (by decide))
    fb 836 816 edi stF_FB (by decide)) fb 836 812 esi stF_FB (by decide), run_of_runOk (k := 4) ?_,
    (((hF.wrF 824 rfl rfl).wrF 820 rfl rfl).wrF 816 rfl rfl).wrF 812 rfl rfl,
    ((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide)⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF
  cbv

theorem esp_sub812 (fb : UInt32) : (subF 4 (UInt32.add fb 812) 812 0).1 = fb := by
  rw [subF_fst]; show fb + 812 - 812 = fb; exact UInt32.add_sub_cancel _ _

/-- `subl $0x32c, %esp` -/
theorem mul_sub (N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add fb 812, ebp, esi, edi, 0x100c24, efl f, 4⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, fb, ebp, esi, edi, 0x100c2a, efl (subF 4 (UInt32.add fb 812) 812 0).2, 5⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runOk img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add fb 812, ebp, esi, edi, 0x100c24, efl f, 4⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (subF 4 (UInt32.add fb 812) 812 0).1, ebp, esi, edi, 0x100c2a,
        efl (subF 4 (UInt32.add fb 812) 812 0).2, 5⟩) := by
    cbv
  rw [esp_sub812] at h
  exact run_of_runOk h

/-- `movl 0x328(%esp), %ecx`: the output pointer. -/
theorem mul_ld (N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, fb, ebp, esi, edi, 0x101be2, efl f, 869⟩)
      (St.m ⟨N.get, eax, rdRaw N.get (UInt32.add fb 808) 4, edx, ebx, fb, ebp, esi, edi, 0x101be9, efl f, 870⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  apply run_of_runOk (k := 1)
  cbv


/-- `movl %eax, (%ecx) ; movl %edx, 0x4(%ecx) ; movl 0x34(%esp), %eax ; movl %eax, 0x8(%ecx) ;
movl 0x20(%esp), %eax ; movl %eax, 0xc(%ecx)` -/
theorem mul_o1 (G N : XMem) (fb hp : UInt32) (hS : FB N.get.size fb 836) (hH : FB N.get.size hp 40)
    (hd : hp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH fb 828 hp))
    (eax edx ebx ebp esi edi f w2 w3 : UInt32) (l2 : l.lookup 52 = some w2) (l3 : l.lookup 32 = some w3) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, eax, hp, edx, ebx, fb, ebp, esi, edi, 0x101be9, efl f, 870⟩)
      (St.m ⟨N'.get, w3, hp, edx, ebx, fb, ebp, esi, edi, 0x101bfc, efl f, 876⟩) ∧
      Frame N' fb 836 l ∧ Frame N' hp 40 ((12, w3) :: (8, w2) :: (4, edx) :: (0, eax) :: lh) ∧
      Pres G N' (OutH fb 828 hp) := by
  refine ⟨stF (stF (stF (stF0 N hp 40 eax hH (by decide)) hp 40 4 edx stF0_FB (by decide)) hp 40 8 w2 stF_FB
    (by decide)) hp 40 12 w3 stF_FB (by decide), run_of_runOk (k := 6) ?_,
    (((hF.wrH0 hS hd).wrH (hS.size_eq (by simp only [stF_size, stF0_size])) hd).wrH
      (hS.size_eq (by simp only [stF_size, stF0_size])) hd).wrH (hS.size_eq (by simp only [stF_size, stF0_size])) hd,
    ((hFH.wrF0).wrF 4 rfl rfl |>.wrF 8 rfl rfl).wrF 12 rfl rfl,
    ((hP.wrH0).wrH.wrH).wrH⟩
  have r2 := hF.rd l2 52 rfl; have r3 := hF.rd l3 32 rfl
  subst r2 r3
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

/-- `movl 0x10(%esp), %eax ; movl %eax, 0x10(%ecx) ; movl %edi, 0x14(%ecx) ; movl (%esp), %eax ;
movl %eax, 0x18(%ecx) ; movl 0x18(%esp), %eax` -/
theorem mul_o2 (G N : XMem) (fb hp : UInt32) (hS : FB N.get.size fb 836) (hH : FB N.get.size hp 40)
    (hd : hp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH fb 828 hp))
    (eax edx ebx ebp esi edi f w4 w6 w7 : UInt32) (l4 : l.lookup 16 = some w4) (l6 : l.lookup 0 = some w6)
    (l7 : l.lookup 24 = some w7) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, eax, hp, edx, ebx, fb, ebp, esi, edi, 0x101bfc, efl f, 876⟩)
      (St.m ⟨N'.get, w7, hp, edx, ebx, fb, ebp, esi, edi, 0x101c10, efl f, 882⟩) ∧
      Frame N' fb 836 l ∧ Frame N' hp 40 ((24, w6) :: (20, edi) :: (16, w4) :: lh) ∧
      Pres G N' (OutH fb 828 hp) := by
  refine ⟨stF (stF (stF N hp 40 16 w4 hH (by decide)) hp 40 20 edi stF_FB (by decide)) hp 40 24 w6 stF_FB
    (by decide), run_of_runOk (k := 6) ?_,
    ((hF.wrH hS hd).wrH (hS.size_eq (by simp only [stF_size])) hd).wrH (hS.size_eq (by simp only [stF_size])) hd,
    ((hFH.wrF 16 rfl rfl).wrF 20 rfl rfl).wrF 24 rfl rfl,
    ((hP.wrH).wrH).wrH⟩
  have r4 := hF.rd l4 16 rfl; have r6 := hF.rd0 l6; have r7 := hF.rd l7 24 rfl
  subst r4 r6 r7
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

/-- `movl %eax, 0x1c(%ecx) ; movl %ebx, 0x20(%ecx) ; movl %ebp, 0x24(%ecx)` -/
theorem mul_o3 (G N : XMem) (fb hp : UInt32) (hS : FB N.get.size fb 836) (hH : FB N.get.size hp 40)
    (hd : hp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ hp.toNat) (l lh : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hFH : Frame N hp 40 lh) (hP : Pres G N (OutH fb 828 hp))
    (eax edx ebx ebp esi edi f : UInt32) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, eax, hp, edx, ebx, fb, ebp, esi, edi, 0x101c10, efl f, 882⟩)
      (St.m ⟨N'.get, eax, hp, edx, ebx, fb, ebp, esi, edi, 0x101c19, efl f, 885⟩) ∧
      Frame N' fb 836 l ∧ Frame N' hp 40 ((36, ebp) :: (32, ebx) :: (28, eax) :: lh) ∧
      Pres G N' (OutH fb 828 hp) := by
  refine ⟨stF (stF (stF N hp 40 28 eax hH (by decide)) hp 40 32 ebx stF_FB (by decide)) hp 40 36 ebp stF_FB
    (by decide), run_of_runOk (k := 3) ?_,
    ((hF.wrH hS hd).wrH (hS.size_eq (by simp only [stF_size])) hd).wrH (hS.size_eq (by simp only [stF_size])) hd,
    ((hFH.wrF 28 rfl rfl).wrF 32 rfl rfl).wrF 36 rfl rfl,
    ((hP.wrH).wrH).wrH⟩
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img; have h4 := hH.fit; have h5 := hH.img
  clear hF hFH hP
  cbv

theorem esp_add812 (fb : UInt32) : (addF 4 fb 812 0).1 = UInt32.add fb 812 := addF_fst _ _

/-- `addl $0x32c, %esp` -/
theorem mul_add (N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (eax ecx edx ebx ebp esi edi f : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, fb, ebp, esi, edi, 0x101c19, efl f, 885⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add fb 812, ebp, esi, edi, 0x101c1f, efl (addF 4 fb 812 0).2, 886⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runOk img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, fb, ebp, esi, edi, 0x101c19, efl f, 885⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (addF 4 fb 812 0).1, ebp, esi, edi, 0x101c1f,
        efl (addF 4 fb 812 0).2, 886⟩) := by
    cbv
  rw [esp_add812] at h
  exact run_of_runOk h

/-- `popl %esi ; popl %edi ; popl %ebx ; popl %ebp ; retl` -/
theorem mul_epi (N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (eax ecx edx ebx ebp esi edi f esi0 edi0 ebx0 ebp0 ret : UInt32)
    (l1 : l.lookup 812 = some esi0) (l2 : l.lookup 816 = some edi0) (l3 : l.lookup 820 = some ebx0)
    (l4 : l.lookup 824 = some ebp0) (l5 : l.lookup 828 = some ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add fb 812, ebp, esi, edi, 0x101c1f, efl f, 886⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add fb 832, ebp0, esi0, edi0, ret, efl f, 891⟩) := by
  have r1 := hF.rd l1 812 rfl; have r2 := hF.rd l2 816 rfl; have r3 := hF.rd l3 820 rfl
  have r4 := hF.rd l4 824 rfl; have r5 := hF.rd l5 828 rfl
  subst r1 r2 r3 r4 r5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF
  apply run_of_runOk (k := 5)
  cbv

end Solutions.OpensslX25519
