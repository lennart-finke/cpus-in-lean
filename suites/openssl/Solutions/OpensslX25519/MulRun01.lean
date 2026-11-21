import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 0–5

Generated (`gen/genmulmain.py`) from the disassembly: each piece runs at most eight instructions (at
most four stores) by `cbv` from a memory `N` whose frame words are listed in `l`, and states the
values it computes as single-operation equations over its inputs.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- movl %ecx, 0x328(%esp) ; movl (%edx), %eax ; movl %eax, 0x44(%esp) ; movl 0x4(%edx), %eax ; movl %eax, 0x34(%esp) ; movl 0x8(%edx), %eax ; movl %eax, 0x6c(%esp) ; movl 0xc(%edx), %eax -/
theorem mul_p0 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (a0 hp fp ebx0 ebp0 esi0 edi0 g0 x1 x2 x3 x4 : UInt32)
        (l_x1 : rdRaw N.get fp 4 = x1)
    (l_x2 : rdRaw N.get (UInt32.add fp 4) 4 = x2)
    (l_x3 : rdRaw N.get (UInt32.add fp 8) 4 = x3)
    (l_x4 : rdRaw N.get (UInt32.add fp 12) 4 = x4)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ fp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, a0, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c2a, efl g0, 5⟩)
      (St.m ⟨N'.get, x4, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c48, efl g0, 13⟩) ∧
      Frame N' fb 836 ((108, x3) :: (52, x2) :: (68, x1) :: (808, hp) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 808 hp hS (by decide)) fb 836 68 x1 stF_FB (by decide)) fb 836 52 x2 stF_FB (by decide)) fb 836 108 x3 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 808 rfl rfl).wrF 68 rfl rfl).wrF 52 rfl rfl).wrF 108 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  
  subst l_x1
  subst l_x2
  subst l_x3
  subst l_x4
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x68(%esp) ; movl 0x10(%edx), %eax ; movl %eax, 0x64(%esp) ; movl 0x14(%edx), %eax ; movl %eax, 0x60(%esp) ; movl 0x18(%edx), %eax ; movl %eax, 0x5c(%esp) ; movl 0x1c(%edx), %eax -/
theorem mul_p1 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x4 hp fp ebx0 ebp0 esi0 edi0 g0 x5 x6 x7 x8 : UInt32)
        (l_x5 : rdRaw N.get (UInt32.add fp 16) 4 = x5)
    (l_x6 : rdRaw N.get (UInt32.add fp 20) 4 = x6)
    (l_x7 : rdRaw N.get (UInt32.add fp 24) 4 = x7)
    (l_x8 : rdRaw N.get (UInt32.add fp 28) 4 = x8)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ fp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x4, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c48, efl g0, 13⟩)
      (St.m ⟨N'.get, x8, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c64, efl g0, 21⟩) ∧
      Frame N' fb 836 ((92, x7) :: (96, x6) :: (100, x5) :: (104, x4) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 104 x4 hS (by decide)) fb 836 100 x5 stF_FB (by decide)) fb 836 96 x6 stF_FB (by decide)) fb 836 92 x7 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 104 rfl rfl).wrF 100 rfl rfl).wrF 96 rfl rfl).wrF 92 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  
  subst l_x5
  subst l_x6
  subst l_x7
  subst l_x8
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x58(%esp) ; movl 0x20(%edx), %eax ; movl %eax, 0x50(%esp) ; movl 0x24(%edx), %eax ; movl %eax, 0x1e8(%esp) ; movl 0x340(%esp), %eax ; movl (%eax), %ecx ; movl %ecx, 0x2c(%esp) -/
theorem mul_p2 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x8 hp fp ebx0 ebp0 esi0 edi0 g0 x9 x10 gp x11 : UInt32)
        (l_x9 : rdRaw N.get (UInt32.add fp 32) 4 = x9)
    (l_x10 : rdRaw N.get (UInt32.add fp 36) 4 = x10)
    (l_gp : l.lookup 832 = some gp)
    (l_x11 : rdRaw N.get gp 4 = x11)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ fp.toNat)
    (hgp : gp.toNat + 40 ≤ N.get.size)
    (hgp' : gp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ gp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x8, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c64, efl g0, 21⟩)
      (St.m ⟨N'.get, gp, x11, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c86, efl g0, 29⟩) ∧
      Frame N' fb 836 ((44, x11) :: (488, x10) :: (80, x9) :: (88, x8) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 88 x8 hS (by decide)) fb 836 80 x9 stF_FB (by decide)) fb 836 488 x10 stF_FB (by decide)) fb 836 44 x11 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 88 rfl rfl).wrF 80 rfl rfl).wrF 488 rfl rfl).wrF 44 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  
  subst l_x9
  subst l_x10
  have r_gp := hF.rd l_gp 832 rfl; subst r_gp
  subst l_x11
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x4(%eax), %ecx ; movl 0x8(%eax), %edx ; movl 0xc(%eax), %esi ; movl 0x10(%eax), %edi ; movl 0x14(%eax), %ebx ; movl 0x18(%eax), %ebp ; movl %ebp, 0x1c(%esp) ; movl 0x1c(%eax), %ebp -/
theorem mul_p3 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (gp x11 fp ebx0 ebp0 esi0 edi0 g0 x12 x13 x14 x15 x16 x17 x18 : UInt32)
        (l_x12 : rdRaw N.get (UInt32.add gp 4) 4 = x12)
    (l_x13 : rdRaw N.get (UInt32.add gp 8) 4 = x13)
    (l_x14 : rdRaw N.get (UInt32.add gp 12) 4 = x14)
    (l_x15 : rdRaw N.get (UInt32.add gp 16) 4 = x15)
    (l_x16 : rdRaw N.get (UInt32.add gp 20) 4 = x16)
    (l_x17 : rdRaw N.get (UInt32.add gp 24) 4 = x17)
    (l_x18 : rdRaw N.get (UInt32.add gp 28) 4 = x18)
    (hgp : gp.toNat + 40 ≤ N.get.size)
    (hgp' : gp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ gp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, gp, x11, fp, ebx0, fb, ebp0, esi0, edi0, 0x100c86, efl g0, 29⟩)
      (St.m ⟨N'.get, gp, x12, x13, x16, fb, x18, x14, x15, 0x100c9f, efl g0, 37⟩) ∧
      Frame N' fb 836 ((28, x17) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 28 x17 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 28 rfl rfl), (hP.wrF (by decide))⟩
  
  subst l_x12
  subst l_x13
  subst l_x14
  subst l_x15
  subst l_x16
  subst l_x17
  subst l_x18
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebp, 0x28(%esp) ; movl 0x20(%eax), %ebp ; movl %ebp, 0x20(%esp) ; movl 0x24(%eax), %eax ; movl %eax, 0x14(%esp) ; leal (%ecx,%ecx,8), %eax ; leal (%ecx,%eax,2), %eax ; movl %ecx, 0x8(%esp) -/
theorem mul_p4 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (gp x12 x13 x16 x18 x14 x15 g0 x19 x20 v21 v22 : UInt32)
        (l_x19 : rdRaw N.get (UInt32.add gp 32) 4 = x19)
    (l_x20 : rdRaw N.get (UInt32.add gp 36) 4 = x20)
    (hgp : gp.toNat + 40 ≤ N.get.size)
    (hgp' : gp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 836 ≤ gp.toNat)
    (e_v21 : v21 = UInt32.add x12 (UInt32.shiftLeft x12 3))
    (e_v22 : v22 = UInt32.add x12 (UInt32.shiftLeft v21 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, gp, x12, x13, x16, fb, x18, x14, x15, 0x100c9f, efl g0, 37⟩)
      (St.m ⟨N'.get, v22, x12, x13, x16, fb, x19, x14, x15, 0x100cbb, efl g0, 45⟩) ∧
      Frame N' fb 836 ((8, x12) :: (20, x20) :: (32, x19) :: (40, x18) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 40 x18 hS (by decide)) fb 836 32 x19 stF_FB (by decide)) fb 836 20 x20 stF_FB (by decide)) fb 836 8 x12 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 40 rfl rfl).wrF 32 rfl rfl).wrF 20 rfl rfl).wrF 8 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_v22
  subst e_v21
  subst l_x19
  subst l_x20
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x54(%esp) ; movl %edx, 0x4(%esp) ; leal (%edx,%edx,8), %eax ; leal (%edx,%eax,2), %eax ; movl %eax, 0x4c(%esp) ; leal (%esi,%esi,8), %eax ; leal (%esi,%eax,2), %eax ; movl %esi, 0x18(%esp) -/
theorem mul_p5 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v22 x12 x13 x16 x19 x14 x15 g0 v23 v24 v25 v26 : UInt32)
        (e_v23 : v23 = UInt32.add x13 (UInt32.shiftLeft x13 3))
    (e_v24 : v24 = UInt32.add x13 (UInt32.shiftLeft v23 1))
    (e_v25 : v25 = UInt32.add x14 (UInt32.shiftLeft x14 3))
    (e_v26 : v26 = UInt32.add x14 (UInt32.shiftLeft v25 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v22, x12, x13, x16, fb, x19, x14, x15, 0x100cbb, efl g0, 45⟩)
      (St.m ⟨N'.get, v26, x12, x13, x16, fb, x19, x14, x15, 0x100cd7, efl g0, 53⟩) ∧
      Frame N' fb 836 ((24, x14) :: (76, v24) :: (4, x13) :: (84, v22) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 84 v22 hS (by decide)) fb 836 4 x13 stF_FB (by decide)) fb 836 76 v24 stF_FB (by decide)) fb 836 24 x14 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 84 rfl rfl).wrF 4 rfl rfl).wrF 76 rfl rfl).wrF 24 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_v26
  subst e_v25
  subst e_v24
  subst e_v23
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
