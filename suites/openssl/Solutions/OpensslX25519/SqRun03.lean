import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 12–17

Generated (`.lake/scratch/i/gensq.py`) from the disassembly: each piece runs at most eight
instructions (at most four stores) by `cbv` from a memory `N` whose frame words are listed in `l`,
and states the values it computes as single-operation equations over its inputs.
-/
namespace Solutions.OpensslX25519
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- movl %eax, 0x14c(%esp) ; movl %ecx, %eax ; imull %edi ; movl %eax, 0x17c(%esp) ; movl %edx, 0x184(%esp) ; movl 0x18(%esp), %ecx ; leal (%ecx,%ecx,1), %eax ; movl %eax, 0x40(%esp) -/
theorem sq_p12 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v62 x7 v63 x5 v53 x6 v46 g64 x8 v65 v66 g67 v68 : UInt32)
        (l_x8 : l.lookup 24 = some x8)
    (e_v65 : v65 = UInt64.toUInt32 (imulCore 4 x7 v46).1)
    (e_v66 : v66 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x7 v46).1 32))
    (e_g67 : g67 = mixF g64 (ovfBits (imulCore 4 x7 v46).2) 2049)
    (e_v68 : v68 = UInt32.add x8 x8) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v62, x7, v63, x5, fb, v53, x6, v46, 0x1024de, efl g64, 96⟩)
      (St.m ⟨N'.get, v68, x8, v66, x5, fb, v53, x6, v46, 0x102502, efl g67, 104⟩) ∧
      Frame N' fb 468 ((64, v68) :: (388, v66) :: (380, v65) :: (332, v62) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 332 v62 hS (by decide)) fb 468 380 v65 stF_FB (by decide)) fb 468 388 v66 stF_FB (by decide)) fb 468 64 v68 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 332 rfl rfl).wrF 380 rfl rfl).wrF 388 rfl rfl).wrF 64 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_v68
  subst e_g67
  subst e_v66
  subst e_v65
  have r_x8 := hF.rd l_x8 24 rfl; subst r_x8
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %edi ; movl %edx, 0x198(%esp) ; movl %eax, 0x194(%esp) ; movl 0x24(%esp), %eax ; imull %edi ; movl %eax, 0x1a4(%esp) ; movl %edx, 0x1a8(%esp) ; imull $0x26, 0x48(%esp), %eax -/
theorem sq_p13 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v68 x8 v66 x5 v53 x6 v46 g67 x9 x10 v69 v70 g71 v72 v73 g74 v75 g76 : UInt32)
        (l_x9 : l.lookup 36 = some x9)
    (l_x10 : l.lookup 72 = some x10)
    (e_v69 : v69 = UInt64.toUInt32 (imulCore 4 v68 v46).1)
    (e_v70 : v70 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v68 v46).1 32))
    (e_g71 : g71 = mixF g67 (ovfBits (imulCore 4 v68 v46).2) 2049)
    (e_v72 : v72 = UInt64.toUInt32 (imulCore 4 x9 v46).1)
    (e_v73 : v73 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x9 v46).1 32))
    (e_g74 : g74 = mixF g71 (ovfBits (imulCore 4 x9 v46).2) 2049)
    (e_v75 : v75 = UInt32.land (UInt64.toUInt32 (imulCore 4 x10 38).1) 4294967295)
    (e_g76 : g76 = mixF g74 (ovfBits (imulCore 4 x10 38).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v68, x8, v66, x5, fb, v53, x6, v46, 0x102502, efl g67, 104⟩)
      (St.m ⟨N'.get, v75, x8, v73, x5, fb, v53, x6, v46, 0x10252b, efl g76, 112⟩) ∧
      Frame N' fb 468 ((424, v73) :: (420, v72) :: (404, v69) :: (408, v70) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 408 v70 hS (by decide)) fb 468 404 v69 stF_FB (by decide)) fb 468 420 v72 stF_FB (by decide)) fb 468 424 v73 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 408 rfl rfl).wrF 404 rfl rfl).wrF 420 rfl rfl).wrF 424 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g76
  subst e_v75
  subst e_g74
  subst e_v73
  subst e_v72
  subst e_g71
  subst e_v70
  subst e_v69
  have r_x9 := hF.rd l_x9 36 rfl; subst r_x9
  have r_x10 := hF.rd l_x10 72 rfl; subst r_x10
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x44(%esp) ; imull %edi ; movl %edx, 0xd4(%esp) ; movl %eax, 0xcc(%esp) ; movl 0x4(%esp), %edi ; movl %edi, %eax ; imull %edi ; movl %eax, 0x10(%esp) -/
theorem sq_p14 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v75 x8 v73 x5 v53 x6 v46 g76 x3 v77 v78 g79 v80 v81 g82 : UInt32)
        (l_x3 : l.lookup 4 = some x3)
    (e_v77 : v77 = UInt64.toUInt32 (imulCore 4 v75 v46).1)
    (e_v78 : v78 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v75 v46).1 32))
    (e_g79 : g79 = mixF g76 (ovfBits (imulCore 4 v75 v46).2) 2049)
    (e_v80 : v80 = UInt64.toUInt32 (imulCore 4 x3 x3).1)
    (e_v81 : v81 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x3 x3).1 32))
    (e_g82 : g82 = mixF g79 (ovfBits (imulCore 4 x3 x3).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v75, x8, v73, x5, fb, v53, x6, v46, 0x10252b, efl g76, 112⟩)
      (St.m ⟨N'.get, v80, x8, v81, x5, fb, v53, x6, x3, 0x10254b, efl g82, 120⟩) ∧
      Frame N' fb 468 ((16, v80) :: (204, v77) :: (212, v78) :: (68, v75) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 68 v75 hS (by decide)) fb 468 212 v78 stF_FB (by decide)) fb 468 204 v77 stF_FB (by decide)) fb 468 16 v80 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 68 rfl rfl).wrF 212 rfl rfl).wrF 204 rfl rfl).wrF 16 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g82
  subst e_v81
  subst e_v80
  subst e_g79
  subst e_v78
  subst e_v77
  have r_x3 := hF.rd l_x3 4 rfl; subst r_x3
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x28(%esp) ; addl %edi, %edi ; movl %edi, %eax ; imull 0xc(%esp) ; movl %edx, 0x4c(%esp) ; movl %eax, 0x2c(%esp) ; movl %ebx, %eax ; imull %edi -/
theorem sq_p15 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v80 x8 v81 x5 v53 x6 x3 g82 x4 v83 g84 v85 v86 g87 v88 v89 g90 : UInt32)
        (l_x4 : l.lookup 12 = some x4)
    (e_v83 : v83 = (addF 4 x3 x3 0).1)
    (e_g84 : g84 = (addF 4 x3 x3 0).2)
    (e_v85 : v85 = UInt64.toUInt32 (imulCore 4 v83 x4).1)
    (e_v86 : v86 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v83 x4).1 32))
    (e_g87 : g87 = mixF g84 (ovfBits (imulCore 4 v83 x4).2) 2049)
    (e_v88 : v88 = UInt64.toUInt32 (imulCore 4 x5 v83).1)
    (e_v89 : v89 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x5 v83).1 32))
    (e_g90 : g90 = mixF g87 (ovfBits (imulCore 4 x5 v83).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v80, x8, v81, x5, fb, v53, x6, x3, 0x10254b, efl g82, 120⟩)
      (St.m ⟨N'.get, v88, x8, v89, x5, fb, v53, x6, v83, 0x102563, efl g90, 128⟩) ∧
      Frame N' fb 468 ((44, v85) :: (76, v86) :: (40, v81) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF N fb 468 40 v81 hS (by decide)) fb 468 76 v86 stF_FB (by decide)) fb 468 44 v85 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 40 rfl rfl).wrF 76 rfl rfl).wrF 44 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g90
  subst e_v89
  subst e_v88
  subst e_g87
  subst e_v86
  subst e_v85
  subst e_g84
  subst e_v83
  have r_x4 := hF.rd l_x4 12 rfl; subst r_x4
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x12c(%esp) ; movl %eax, 0x128(%esp) ; movl (%esp), %eax ; imull %edi ; movl %edx, 0x158(%esp) ; movl %eax, 0x154(%esp) ; movl 0x30(%esp), %esi ; movl %esi, %eax -/
theorem sq_p16 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v88 x8 v89 x5 v53 x6 v83 g90 x7 v91 v92 g93 : UInt32)
        (l_x6 : l.lookup 0 = some x6)
    (l_x7 : l.lookup 48 = some x7)
    (e_v91 : v91 = UInt64.toUInt32 (imulCore 4 x6 v83).1)
    (e_v92 : v92 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x6 v83).1 32))
    (e_g93 : g93 = mixF g90 (ovfBits (imulCore 4 x6 v83).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v88, x8, v89, x5, fb, v53, x6, v83, 0x102563, efl g90, 128⟩)
      (St.m ⟨N'.get, x7, x8, v92, x5, fb, v53, x7, v83, 0x10258a, efl g93, 136⟩) ∧
      Frame N' fb 468 ((340, v91) :: (344, v92) :: (296, v88) :: (300, v89) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 300 v89 hS (by decide)) fb 468 296 v88 stF_FB (by decide)) fb 468 344 v92 stF_FB (by decide)) fb 468 340 v91 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 300 rfl rfl).wrF 296 rfl rfl).wrF 344 rfl rfl).wrF 340 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g93
  subst e_v92
  subst e_v91
  have r_x6 := hF.rd0 l_x6; subst r_x6
  have r_x7 := hF.rd l_x7 48 rfl; subst r_x7
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %edi ; movl %edx, 0x170(%esp) ; movl %eax, 0x16c(%esp) ; movl %ecx, %eax ; imull %edi ; movl %edx, 0x190(%esp) ; movl %eax, 0x18c(%esp) ; movl 0x20(%esp), %ebx -/
theorem sq_p17 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (x7 x8 v92 x5 v53 v83 g93 v14 v94 v95 g96 v97 v98 g99 : UInt32)
        (l_v14 : l.lookup 32 = some v14)
    (e_v94 : v94 = UInt64.toUInt32 (imulCore 4 x7 v83).1)
    (e_v95 : v95 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x7 v83).1 32))
    (e_g96 : g96 = mixF g93 (ovfBits (imulCore 4 x7 v83).2) 2049)
    (e_v97 : v97 = UInt64.toUInt32 (imulCore 4 x8 v83).1)
    (e_v98 : v98 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x8 v83).1 32))
    (e_g99 : g99 = mixF g96 (ovfBits (imulCore 4 x8 v83).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x7, x8, v92, x5, fb, v53, x7, v83, 0x10258a, efl g93, 136⟩)
      (St.m ⟨N'.get, v97, x8, v98, v14, fb, v53, x7, v83, 0x1025b0, efl g99, 144⟩) ∧
      Frame N' fb 468 ((396, v97) :: (400, v98) :: (364, v94) :: (368, v95) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 368 v95 hS (by decide)) fb 468 364 v94 stF_FB (by decide)) fb 468 400 v98 stF_FB (by decide)) fb 468 396 v97 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 368 rfl rfl).wrF 364 rfl rfl).wrF 400 rfl rfl).wrF 396 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g99
  subst e_v98
  subst e_v97
  subst e_g96
  subst e_v95
  subst e_v94
  have r_v14 := hF.rd l_v14 32 rfl; subst r_v14
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
