import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 12–17

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

/-- imull %ebp ; movl %edx, 0x284(%esp) ; movl %eax, 0x27c(%esp) ; movl %edi, %eax ; imull %ebp ; movl %edx, 0x2d8(%esp) ; movl %eax, 0x2d0(%esp) ; movl %ebx, %eax -/
theorem mul_p12 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x16 x12 v52 x18 x1 x17 g53 v54 v55 g56 v57 v58 g59 : UInt32)
        (e_v54 : v54 = UInt64.toUInt32 (imulCore 4 x16 x1).1)
    (e_v55 : v55 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x16 x1).1 32))
    (e_g56 : g56 = mixF g53 (ovfBits (imulCore 4 x16 x1).2) 2049)
    (e_v57 : v57 = UInt64.toUInt32 (imulCore 4 x17 x1).1)
    (e_v58 : v58 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x17 x1).1 32))
    (e_g59 : g59 = mixF g56 (ovfBits (imulCore 4 x17 x1).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x16, x12, v52, x18, fb, x1, x16, x17, 0x100d97, efl g53, 101⟩)
      (St.m ⟨N'.get, x18, x12, v58, x18, fb, x1, x16, x17, 0x100dbb, efl g59, 109⟩) ∧
      Frame N' fb 836 ((720, v57) :: (728, v58) :: (636, v54) :: (644, v55) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 644 v55 hS (by decide)) fb 836 636 v54 stF_FB (by decide)) fb 836 728 v58 stF_FB (by decide)) fb 836 720 v57 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 644 rfl rfl).wrF 636 rfl rfl).wrF 728 rfl rfl).wrF 720 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g59
  subst e_v58
  subst e_v57
  subst e_g56
  subst e_v55
  subst e_v54
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ebp ; movl %edx, 0x2fc(%esp) ; movl %eax, 0x2f8(%esp) ; movl 0x20(%esp), %eax ; imull %ebp ; movl %edx, 0x314(%esp) ; movl %eax, 0x310(%esp) ; movl 0x14(%esp), %eax -/
theorem mul_p13 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x18 x12 v58 x1 x16 x17 g59 x19 x20 v60 v61 g62 v63 v64 g65 : UInt32)
        (l_x19 : l.lookup 32 = some x19)
    (l_x20 : l.lookup 20 = some x20)
    (e_v60 : v60 = UInt64.toUInt32 (imulCore 4 x18 x1).1)
    (e_v61 : v61 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x18 x1).1 32))
    (e_g62 : g62 = mixF g59 (ovfBits (imulCore 4 x18 x1).2) 2049)
    (e_v63 : v63 = UInt64.toUInt32 (imulCore 4 x19 x1).1)
    (e_v64 : v64 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x19 x1).1 32))
    (e_g65 : g65 = mixF g62 (ovfBits (imulCore 4 x19 x1).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x18, x12, v58, x18, fb, x1, x16, x17, 0x100dbb, efl g59, 109⟩)
      (St.m ⟨N'.get, x20, x12, v64, x18, fb, x1, x16, x17, 0x100de3, efl g65, 117⟩) ∧
      Frame N' fb 836 ((784, v63) :: (788, v64) :: (760, v60) :: (764, v61) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 764 v61 hS (by decide)) fb 836 760 v60 stF_FB (by decide)) fb 836 788 v64 stF_FB (by decide)) fb 836 784 v63 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 764 rfl rfl).wrF 760 rfl rfl).wrF 788 rfl rfl).wrF 784 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g65
  subst e_v64
  subst e_v63
  subst e_g62
  subst e_v61
  subst e_v60
  have r_x19 := hF.rd l_x19 32 rfl; subst r_x19
  have r_x20 := hF.rd l_x20 20 rfl; subst r_x20
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ebp ; movl %edx, 0x324(%esp) ; movl %eax, 0x320(%esp) ; movl 0x2c(%esp), %ebp ; movl %ebp, %eax ; movl 0x34(%esp), %ecx ; imull %ecx ; movl %eax, 0x14(%esp) -/
theorem mul_p14 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x20 x12 v64 x18 x1 x16 x17 g65 x11 x2 v66 v67 g68 v69 v70 g71 : UInt32)
        (l_x11 : l.lookup 44 = some x11)
    (l_x2 : l.lookup 52 = some x2)
    (e_v66 : v66 = UInt64.toUInt32 (imulCore 4 x20 x1).1)
    (e_v67 : v67 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x20 x1).1 32))
    (e_g68 : g68 = mixF g65 (ovfBits (imulCore 4 x20 x1).2) 2049)
    (e_v69 : v69 = UInt64.toUInt32 (imulCore 4 x11 x2).1)
    (e_v70 : v70 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x2).1 32))
    (e_g71 : g71 = mixF g68 (ovfBits (imulCore 4 x11 x2).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x20, x12, v64, x18, fb, x1, x16, x17, 0x100de3, efl g65, 117⟩)
      (St.m ⟨N'.get, v69, x2, v70, x18, fb, x11, x16, x17, 0x100e03, efl g71, 125⟩) ∧
      Frame N' fb 836 ((20, v69) :: (800, v66) :: (804, v67) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 804 v67 hS (by decide)) fb 836 800 v66 stF_FB (by decide)) fb 836 20 v69 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 804 rfl rfl).wrF 800 rfl rfl).wrF 20 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g71
  subst e_v70
  subst e_v69
  subst e_g68
  subst e_v67
  subst e_v66
  have r_x11 := hF.rd l_x11 44 rfl; subst r_x11
  have r_x2 := hF.rd l_x2 52 rfl; subst r_x2
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x44(%esp) ; leal (%ecx,%ecx,1), %edi ; movl 0x8(%esp), %eax ; imull %edi ; movl %edx, 0x288(%esp) ; movl %eax, 0x280(%esp) ; movl 0x4(%esp), %eax ; imull %ecx -/
theorem mul_p15 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v69 x2 v70 x18 x11 x16 x17 g71 x12 x13 v72 v73 v74 g75 v76 v77 g78 : UInt32)
        (l_x12 : l.lookup 8 = some x12)
    (l_x13 : l.lookup 4 = some x13)
    (e_v72 : v72 = UInt32.add x2 x2)
    (e_v73 : v73 = UInt64.toUInt32 (imulCore 4 x12 v72).1)
    (e_v74 : v74 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 v72).1 32))
    (e_g75 : g75 = mixF g71 (ovfBits (imulCore 4 x12 v72).2) 2049)
    (e_v76 : v76 = UInt64.toUInt32 (imulCore 4 x13 x2).1)
    (e_v77 : v77 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x2).1 32))
    (e_g78 : g78 = mixF g75 (ovfBits (imulCore 4 x13 x2).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v69, x2, v70, x18, fb, x11, x16, x17, 0x100e03, efl g71, 125⟩)
      (St.m ⟨N'.get, v76, x2, v77, x18, fb, x11, x16, v72, 0x100e24, efl g78, 133⟩) ∧
      Frame N' fb 836 ((640, v73) :: (648, v74) :: (68, v70) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 68 v70 hS (by decide)) fb 836 648 v74 stF_FB (by decide)) fb 836 640 v73 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 68 rfl rfl).wrF 648 rfl rfl).wrF 640 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g78
  subst e_v77
  subst e_v76
  subst e_g75
  subst e_v74
  subst e_v73
  subst e_v72
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x2d4(%esp) ; movl %eax, 0x2cc(%esp) ; movl 0x18(%esp), %eax ; imull %edi ; movl %edx, 0x1e0(%esp) ; movl %eax, 0x1d8(%esp) ; movl (%esp), %eax ; imull %ecx -/
theorem mul_p16 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v76 x2 v77 x18 x11 x16 v72 g78 x14 x15 v79 v80 g81 v82 v83 g84 : UInt32)
        (l_x14 : l.lookup 24 = some x14)
    (l_x15 : l.lookup 0 = some x15)
    (e_v79 : v79 = UInt64.toUInt32 (imulCore 4 x14 v72).1)
    (e_v80 : v80 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x14 v72).1 32))
    (e_g81 : g81 = mixF g78 (ovfBits (imulCore 4 x14 v72).2) 2049)
    (e_v82 : v82 = UInt64.toUInt32 (imulCore 4 x15 x2).1)
    (e_v83 : v83 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x15 x2).1 32))
    (e_g84 : g84 = mixF g81 (ovfBits (imulCore 4 x15 x2).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v76, x2, v77, x18, fb, x11, x16, v72, 0x100e24, efl g78, 133⟩)
      (St.m ⟨N'.get, v82, x2, v83, x18, fb, x11, x16, v72, 0x100e4b, efl g84, 141⟩) ∧
      Frame N' fb 836 ((472, v79) :: (480, v80) :: (716, v76) :: (724, v77) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 724 v77 hS (by decide)) fb 836 716 v76 stF_FB (by decide)) fb 836 480 v80 stF_FB (by decide)) fb 836 472 v79 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 724 rfl rfl).wrF 716 rfl rfl).wrF 480 rfl rfl).wrF 472 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g84
  subst e_v83
  subst e_v82
  subst e_g81
  subst e_v80
  subst e_v79
  have r_x14 := hF.rd l_x14 24 rfl; subst r_x14
  have r_x15 := hF.rd0 l_x15; subst r_x15
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x254(%esp) ; movl %eax, 0x250(%esp) ; movl %esi, %eax ; imull %edi ; movl %edx, 0x2ac(%esp) ; movl %eax, 0x2a4(%esp) ; movl 0x1c(%esp), %esi ; movl %esi, %eax -/
theorem mul_p17 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v82 x2 v83 x18 x11 x16 v72 g84 x17 v85 v86 g87 : UInt32)
        (l_x17 : l.lookup 28 = some x17)
    (e_v85 : v85 = UInt64.toUInt32 (imulCore 4 x16 v72).1)
    (e_v86 : v86 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x16 v72).1 32))
    (e_g87 : g87 = mixF g84 (ovfBits (imulCore 4 x16 v72).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v82, x2, v83, x18, fb, x11, x16, v72, 0x100e4b, efl g84, 141⟩)
      (St.m ⟨N'.get, x17, x2, v86, x18, fb, x11, x17, v72, 0x100e71, efl g87, 149⟩) ∧
      Frame N' fb 836 ((676, v85) :: (684, v86) :: (592, v82) :: (596, v83) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 596 v83 hS (by decide)) fb 836 592 v82 stF_FB (by decide)) fb 836 684 v86 stF_FB (by decide)) fb 836 676 v85 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 596 rfl rfl).wrF 592 rfl rfl).wrF 684 rfl rfl).wrF 676 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g87
  subst e_v86
  subst e_v85
  have r_x17 := hF.rd l_x17 28 rfl; subst r_x17
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
