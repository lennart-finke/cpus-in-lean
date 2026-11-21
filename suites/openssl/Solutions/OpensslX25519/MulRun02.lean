import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 6–11

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

/-- movl %eax, 0x48(%esp) ; movl %edi, (%esp) ; leal (%edi,%edi,8), %eax ; leal (%edi,%eax,2), %eax ; movl %eax, 0x40(%esp) ; movl %ebx, 0xc(%esp) ; leal (%ebx,%ebx,8), %eax ; leal (%ebx,%eax,2), %eax -/
theorem mul_p6 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v26 x12 x13 x16 x19 x14 x15 g0 v27 v28 v29 v30 : UInt32)
        (e_v27 : v27 = UInt32.add x15 (UInt32.shiftLeft x15 3))
    (e_v28 : v28 = UInt32.add x15 (UInt32.shiftLeft v27 1))
    (e_v29 : v29 = UInt32.add x16 (UInt32.shiftLeft x16 3))
    (e_v30 : v30 = UInt32.add x16 (UInt32.shiftLeft v29 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v26, x12, x13, x16, fb, x19, x14, x15, 0x100cd7, efl g0, 53⟩)
      (St.m ⟨N'.get, v30, x12, x13, x16, fb, x19, x14, x15, 0x100cf2, efl g0, 61⟩) ∧
      Frame N' fb 836 ((12, x16) :: (64, v28) :: (0, x15) :: (72, v26) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF0 (stF N fb 836 72 v26 hS (by decide)) fb 836 x15 stF_FB (by decide)) fb 836 64 v28 stF0_FB (by decide)) fb 836 12 x16 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 72 rfl rfl).wrF0).wrF 64 rfl rfl).wrF 12 rfl rfl), ((((hP.wrF (by decide)).wrF0 (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_v30
  subst e_v29
  subst e_v28
  subst e_v27
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x3c(%esp) ; movl 0x1c(%esp), %edi ; leal (%edi,%edi,8), %eax ; leal (%edi,%eax,2), %eax ; movl %eax, 0x38(%esp) ; movl 0x28(%esp), %ebx ; leal (%ebx,%ebx,8), %eax ; leal (%ebx,%eax,2), %eax -/
theorem mul_p7 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v30 x12 x13 x16 x19 x14 x15 g0 x17 x18 v31 v32 v33 v34 : UInt32)
        (l_x17 : l.lookup 28 = some x17)
    (l_x18 : l.lookup 40 = some x18)
    (e_v31 : v31 = UInt32.add x17 (UInt32.shiftLeft x17 3))
    (e_v32 : v32 = UInt32.add x17 (UInt32.shiftLeft v31 1))
    (e_v33 : v33 = UInt32.add x18 (UInt32.shiftLeft x18 3))
    (e_v34 : v34 = UInt32.add x18 (UInt32.shiftLeft v33 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v30, x12, x13, x16, fb, x19, x14, x15, 0x100cf2, efl g0, 61⟩)
      (St.m ⟨N'.get, v34, x12, x13, x18, fb, x19, x14, x17, 0x100d0e, efl g0, 69⟩) ∧
      Frame N' fb 836 ((56, v32) :: (60, v30) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF N fb 836 60 v30 hS (by decide)) fb 836 56 v32 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((hF.wrF 60 rfl rfl).wrF 56 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_v34
  subst e_v33
  subst e_v32
  subst e_v31
  have r_x17 := hF.rd l_x17 28 rfl; subst r_x17
  have r_x18 := hF.rd l_x18 40 rfl; subst r_x18
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x30(%esp) ; movl 0x20(%esp), %edx ; leal (%edx,%edx,8), %eax ; leal (%edx,%eax,2), %eax ; movl %eax, 0x24(%esp) ; movl 0x14(%esp), %edx ; leal (%edx,%edx,8), %eax ; leal (%edx,%eax,2), %eax -/
theorem mul_p8 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v34 x12 x13 x18 x19 x14 x17 g0 x20 v35 v36 v37 v38 : UInt32)
        (l_x19 : l.lookup 32 = some x19)
    (l_x20 : l.lookup 20 = some x20)
    (e_v35 : v35 = UInt32.add x19 (UInt32.shiftLeft x19 3))
    (e_v36 : v36 = UInt32.add x19 (UInt32.shiftLeft v35 1))
    (e_v37 : v37 = UInt32.add x20 (UInt32.shiftLeft x20 3))
    (e_v38 : v38 = UInt32.add x20 (UInt32.shiftLeft v37 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v34, x12, x13, x18, fb, x19, x14, x17, 0x100d0e, efl g0, 69⟩)
      (St.m ⟨N'.get, v38, x12, x20, x18, fb, x19, x14, x17, 0x100d2a, efl g0, 77⟩) ∧
      Frame N' fb 836 ((36, v36) :: (48, v34) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF N fb 836 48 v34 hS (by decide)) fb 836 36 v36 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((hF.wrF 48 rfl rfl).wrF 36 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_v38
  subst e_v37
  subst e_v36
  subst e_v35
  have r_x19 := hF.rd l_x19 32 rfl; subst r_x19
  have r_x20 := hF.rd l_x20 20 rfl; subst r_x20
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x10(%esp) ; movl 0x2c(%esp), %eax ; movl 0x44(%esp), %ebp ; imull %ebp ; movl %edx, 0x214(%esp) ; movl %eax, 0x20c(%esp) ; movl %ecx, %eax ; imull %ebp -/
theorem mul_p9 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v38 x12 x20 x18 x19 x14 x17 g0 x11 x1 v39 v40 g41 v42 v43 g44 : UInt32)
        (l_x11 : l.lookup 44 = some x11)
    (l_x1 : l.lookup 68 = some x1)
    (e_v39 : v39 = UInt64.toUInt32 (imulCore 4 x11 x1).1)
    (e_v40 : v40 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x1).1 32))
    (e_g41 : g41 = mixF g0 (ovfBits (imulCore 4 x11 x1).2) 2049)
    (e_v42 : v42 = UInt64.toUInt32 (imulCore 4 x12 x1).1)
    (e_v43 : v43 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 x1).1 32))
    (e_g44 : g44 = mixF g41 (ovfBits (imulCore 4 x12 x1).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v38, x12, x20, x18, fb, x19, x14, x17, 0x100d2a, efl g0, 77⟩)
      (St.m ⟨N'.get, v42, x12, v43, x18, fb, x1, x14, x17, 0x100d4a, efl g44, 85⟩) ∧
      Frame N' fb 836 ((524, v39) :: (532, v40) :: (16, v38) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 16 v38 hS (by decide)) fb 836 532 v40 stF_FB (by decide)) fb 836 524 v39 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 16 rfl rfl).wrF 532 rfl rfl).wrF 524 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g44
  subst e_v43
  subst e_v42
  subst e_g41
  subst e_v40
  subst e_v39
  have r_x11 := hF.rd l_x11 44 rfl; subst r_x11
  have r_x1 := hF.rd l_x1 68 rfl; subst r_x1
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x234(%esp) ; movl %eax, 0x224(%esp) ; movl 0x4(%esp), %eax ; imull %ebp ; movl %edx, 0x2b4(%esp) ; movl %eax, 0x2b0(%esp) ; movl %esi, %eax ; imull %ebp -/
theorem mul_p10 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v42 x12 v43 x18 x1 x14 x17 g44 x13 v45 v46 g47 v48 v49 g50 : UInt32)
        (l_x13 : l.lookup 4 = some x13)
    (e_v45 : v45 = UInt64.toUInt32 (imulCore 4 x13 x1).1)
    (e_v46 : v46 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x1).1 32))
    (e_g47 : g47 = mixF g44 (ovfBits (imulCore 4 x13 x1).2) 2049)
    (e_v48 : v48 = UInt64.toUInt32 (imulCore 4 x14 x1).1)
    (e_v49 : v49 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x14 x1).1 32))
    (e_g50 : g50 = mixF g47 (ovfBits (imulCore 4 x14 x1).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v42, x12, v43, x18, fb, x1, x14, x17, 0x100d4a, efl g44, 85⟩)
      (St.m ⟨N'.get, v48, x12, v49, x18, fb, x1, x14, x17, 0x100d70, efl g50, 93⟩) ∧
      Frame N' fb 836 ((688, v45) :: (692, v46) :: (548, v42) :: (564, v43) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 564 v43 hS (by decide)) fb 836 548 v42 stF_FB (by decide)) fb 836 692 v46 stF_FB (by decide)) fb 836 688 v45 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 564 rfl rfl).wrF 548 rfl rfl).wrF 692 rfl rfl).wrF 688 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g50
  subst e_v49
  subst e_v48
  subst e_g47
  subst e_v46
  subst e_v45
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x2f4(%esp) ; movl %eax, 0x2f0(%esp) ; movl (%esp), %eax ; imull %ebp ; movl %edx, 0x22c(%esp) ; movl %eax, 0x220(%esp) ; movl 0xc(%esp), %esi ; movl %esi, %eax -/
theorem mul_p11 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v48 x12 v49 x18 x1 x14 x17 g50 x15 x16 v51 v52 g53 : UInt32)
        (l_x15 : l.lookup 0 = some x15)
    (l_x16 : l.lookup 12 = some x16)
    (e_v51 : v51 = UInt64.toUInt32 (imulCore 4 x15 x1).1)
    (e_v52 : v52 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x15 x1).1 32))
    (e_g53 : g53 = mixF g50 (ovfBits (imulCore 4 x15 x1).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v48, x12, v49, x18, fb, x1, x14, x17, 0x100d70, efl g50, 93⟩)
      (St.m ⟨N'.get, x16, x12, v52, x18, fb, x1, x16, x17, 0x100d97, efl g53, 101⟩) ∧
      Frame N' fb 836 ((544, v51) :: (556, v52) :: (752, v48) :: (756, v49) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 756 v49 hS (by decide)) fb 836 752 v48 stF_FB (by decide)) fb 836 556 v52 stF_FB (by decide)) fb 836 544 v51 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 756 rfl rfl).wrF 752 rfl rfl).wrF 556 rfl rfl).wrF 544 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g53
  subst e_v52
  subst e_v51
  have r_x15 := hF.rd0 l_x15; subst r_x15
  have r_x16 := hF.rd l_x16 12 rfl; subst r_x16
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
