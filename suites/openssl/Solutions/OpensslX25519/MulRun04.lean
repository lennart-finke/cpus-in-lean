import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 18–23

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

/-- imull %ecx ; movl %edx, 0x2e0(%esp) ; movl %eax, 0x2dc(%esp) ; movl %ebx, %eax ; imull %edi ; movl %edx, 0x304(%esp) ; movl %eax, 0x300(%esp) ; movl 0x20(%esp), %eax -/
theorem mul_p18 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x17 x2 v86 x18 x11 v72 g87 x19 v88 v89 g90 v91 v92 g93 : UInt32)
        (l_x19 : l.lookup 32 = some x19)
    (e_v88 : v88 = UInt64.toUInt32 (imulCore 4 x17 x2).1)
    (e_v89 : v89 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x17 x2).1 32))
    (e_g90 : g90 = mixF g87 (ovfBits (imulCore 4 x17 x2).2) 2049)
    (e_v91 : v91 = UInt64.toUInt32 (imulCore 4 x18 v72).1)
    (e_v92 : v92 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x18 v72).1 32))
    (e_g93 : g93 = mixF g90 (ovfBits (imulCore 4 x18 v72).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x17, x2, v86, x18, fb, x11, x17, v72, 0x100e71, efl g87, 149⟩)
      (St.m ⟨N'.get, x19, x2, v92, x18, fb, x11, x17, v72, 0x100e97, efl g93, 157⟩) ∧
      Frame N' fb 836 ((768, v91) :: (772, v92) :: (732, v88) :: (736, v89) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 736 v89 hS (by decide)) fb 836 732 v88 stF_FB (by decide)) fb 836 772 v92 stF_FB (by decide)) fb 836 768 v91 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 736 rfl rfl).wrF 732 rfl rfl).wrF 772 rfl rfl).wrF 768 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g93
  subst e_v92
  subst e_v91
  subst e_g90
  subst e_v89
  subst e_v88
  have r_x19 := hF.rd l_x19 32 rfl; subst r_x19
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ecx ; movl %edx, 0x31c(%esp) ; movl %eax, 0x318(%esp) ; movl 0x10(%esp), %ecx ; movl %ecx, %eax ; imull %edi ; movl %edx, 0x1a4(%esp) ; movl %eax, 0x1a0(%esp) -/
theorem mul_p19 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x19 x2 v92 x18 x11 x17 v72 g93 v38 v94 v95 g96 v97 v98 g99 : UInt32)
        (l_v38 : l.lookup 16 = some v38)
    (e_v94 : v94 = UInt64.toUInt32 (imulCore 4 x19 x2).1)
    (e_v95 : v95 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x19 x2).1 32))
    (e_g96 : g96 = mixF g93 (ovfBits (imulCore 4 x19 x2).2) 2049)
    (e_v97 : v97 = UInt64.toUInt32 (imulCore 4 v38 v72).1)
    (e_v98 : v98 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v38 v72).1 32))
    (e_g99 : g99 = mixF g96 (ovfBits (imulCore 4 v38 v72).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x19, x2, v92, x18, fb, x11, x17, v72, 0x100e97, efl g93, 157⟩)
      (St.m ⟨N'.get, v97, v38, v98, x18, fb, x11, x17, v72, 0x100ebd, efl g99, 165⟩) ∧
      Frame N' fb 836 ((416, v97) :: (420, v98) :: (792, v94) :: (796, v95) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 796 v95 hS (by decide)) fb 836 792 v94 stF_FB (by decide)) fb 836 420 v98 stF_FB (by decide)) fb 836 416 v97 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 796 rfl rfl).wrF 792 rfl rfl).wrF 420 rfl rfl).wrF 416 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g99
  subst e_v98
  subst e_v97
  subst e_g96
  subst e_v95
  subst e_v94
  have r_v38 := hF.rd l_v38 16 rfl; subst r_v38
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebp, %eax ; movl 0x6c(%esp), %ebx ; imull %ebx ; movl %edx, 0x258(%esp) ; movl %eax, 0x34(%esp) ; movl 0x8(%esp), %edi ; movl %edi, %eax ; imull %ebx -/
theorem mul_p20 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v97 v38 v98 x18 x11 x17 v72 g99 x3 x12 v100 v101 g102 v103 v104 g105 : UInt32)
        (l_x3 : l.lookup 108 = some x3)
    (l_x12 : l.lookup 8 = some x12)
    (e_v100 : v100 = UInt64.toUInt32 (imulCore 4 x11 x3).1)
    (e_v101 : v101 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x3).1 32))
    (e_g102 : g102 = mixF g99 (ovfBits (imulCore 4 x11 x3).2) 2049)
    (e_v103 : v103 = UInt64.toUInt32 (imulCore 4 x12 x3).1)
    (e_v104 : v104 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 x3).1 32))
    (e_g105 : g105 = mixF g102 (ovfBits (imulCore 4 x12 x3).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v97, v38, v98, x18, fb, x11, x17, v72, 0x100ebd, efl g99, 165⟩)
      (St.m ⟨N'.get, v103, v38, v104, x3, fb, x11, x17, x12, 0x100ed8, efl g105, 173⟩) ∧
      Frame N' fb 836 ((52, v100) :: (600, v101) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF N fb 836 600 v101 hS (by decide)) fb 836 52 v100 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((hF.wrF 600 rfl rfl).wrF 52 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g105
  subst e_v104
  subst e_v103
  subst e_g102
  subst e_v101
  subst e_v100
  have r_x3 := hF.rd l_x3 108 rfl; subst r_x3
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x2a8(%esp) ; movl %eax, 0x2a0(%esp) ; movl 0x4(%esp), %ebp ; movl %ebp, %eax ; imull %ebx ; movl %edx, 0x19c(%esp) ; movl %eax, 0x194(%esp) ; movl 0x18(%esp), %eax -/
theorem mul_p21 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v103 v38 v104 x3 x11 x17 x12 g105 x13 x14 v106 v107 g108 : UInt32)
        (l_x13 : l.lookup 4 = some x13)
    (l_x14 : l.lookup 24 = some x14)
    (e_v106 : v106 = UInt64.toUInt32 (imulCore 4 x13 x3).1)
    (e_v107 : v107 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x3).1 32))
    (e_g108 : g108 = mixF g105 (ovfBits (imulCore 4 x13 x3).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v103, v38, v104, x3, fb, x11, x17, x12, 0x100ed8, efl g105, 173⟩)
      (St.m ⟨N'.get, x14, v38, v107, x3, fb, x13, x17, x12, 0x100f00, efl g108, 181⟩) ∧
      Frame N' fb 836 ((404, v106) :: (412, v107) :: (672, v103) :: (680, v104) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 680 v104 hS (by decide)) fb 836 672 v103 stF_FB (by decide)) fb 836 412 v107 stF_FB (by decide)) fb 836 404 v106 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 680 rfl rfl).wrF 672 rfl rfl).wrF 412 rfl rfl).wrF 404 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g108
  subst e_v107
  subst e_v106
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have r_x14 := hF.rd l_x14 24 rfl; subst r_x14
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ebx ; movl %edx, 0x218(%esp) ; movl %eax, 0x210(%esp) ; movl (%esp), %eax ; imull %ebx ; movl %edx, 0x274(%esp) ; movl %eax, 0x270(%esp) ; movl 0xc(%esp), %eax -/
theorem mul_p22 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x14 v38 v107 x3 x13 x17 x12 g108 x15 x16 v109 v110 g111 v112 v113 g114 : UInt32)
        (l_x15 : l.lookup 0 = some x15)
    (l_x16 : l.lookup 12 = some x16)
    (e_v109 : v109 = UInt64.toUInt32 (imulCore 4 x14 x3).1)
    (e_v110 : v110 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x14 x3).1 32))
    (e_g111 : g111 = mixF g108 (ovfBits (imulCore 4 x14 x3).2) 2049)
    (e_v112 : v112 = UInt64.toUInt32 (imulCore 4 x15 x3).1)
    (e_v113 : v113 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x15 x3).1 32))
    (e_g114 : g114 = mixF g111 (ovfBits (imulCore 4 x15 x3).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x14, v38, v107, x3, fb, x13, x17, x12, 0x100f00, efl g108, 181⟩)
      (St.m ⟨N'.get, x16, v38, v113, x3, fb, x13, x17, x12, 0x100f27, efl g114, 189⟩) ∧
      Frame N' fb 836 ((624, v112) :: (628, v113) :: (528, v109) :: (536, v110) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 536 v110 hS (by decide)) fb 836 528 v109 stF_FB (by decide)) fb 836 628 v113 stF_FB (by decide)) fb 836 624 v112 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 536 rfl rfl).wrF 528 rfl rfl).wrF 628 rfl rfl).wrF 624 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g114
  subst e_v113
  subst e_v112
  subst e_g111
  subst e_v110
  subst e_v109
  have r_x15 := hF.rd0 l_x15; subst r_x15
  have r_x16 := hF.rd l_x16 12 rfl; subst r_x16
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ebx ; movl %edx, 0x2bc(%esp) ; movl %eax, 0x2b8(%esp) ; movl %esi, %eax ; imull %ebx ; movl %edx, 0x2e8(%esp) ; movl %eax, 0x2e4(%esp) ; movl 0x28(%esp), %eax -/
theorem mul_p23 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x16 v38 v113 x3 x13 x17 x12 g114 x18 v115 v116 g117 v118 v119 g120 : UInt32)
        (l_x18 : l.lookup 40 = some x18)
    (e_v115 : v115 = UInt64.toUInt32 (imulCore 4 x16 x3).1)
    (e_v116 : v116 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x16 x3).1 32))
    (e_g117 : g117 = mixF g114 (ovfBits (imulCore 4 x16 x3).2) 2049)
    (e_v118 : v118 = UInt64.toUInt32 (imulCore 4 x17 x3).1)
    (e_v119 : v119 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x17 x3).1 32))
    (e_g120 : g120 = mixF g117 (ovfBits (imulCore 4 x17 x3).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x16, v38, v113, x3, fb, x13, x17, x12, 0x100f27, efl g114, 189⟩)
      (St.m ⟨N'.get, x18, v38, v119, x3, fb, x13, x17, x12, 0x100f4d, efl g120, 197⟩) ∧
      Frame N' fb 836 ((740, v118) :: (744, v119) :: (696, v115) :: (700, v116) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 700 v116 hS (by decide)) fb 836 696 v115 stF_FB (by decide)) fb 836 744 v119 stF_FB (by decide)) fb 836 740 v118 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 700 rfl rfl).wrF 696 rfl rfl).wrF 744 rfl rfl).wrF 740 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g120
  subst e_v119
  subst e_v118
  subst e_g117
  subst e_v116
  subst e_v115
  have r_x18 := hF.rd l_x18 40 rfl; subst r_x18
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
