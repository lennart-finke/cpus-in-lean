import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 0–5

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

/-- movl %ecx, 0x1bc(%esp) ; movl (%edx), %eax ; movl 0x4(%edx), %esi ; movl %esi, 0x8(%esp) ; movl 0x8(%edx), %ebx ; movl %ebx, 0x4(%esp) ; movl 0xc(%edx), %ebp ; movl 0x10(%edx), %ecx -/
theorem sq_p0 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (a0 hp fp ebx0 ebp0 esi0 edi0 g0 x1 x2 x3 x4 x5 : UInt32)
        (l_x1 : rdRaw N.get fp 4 = x1)
    (l_x2 : rdRaw N.get (UInt32.add fp 4) 4 = x2)
    (l_x3 : rdRaw N.get (UInt32.add fp 8) 4 = x3)
    (l_x4 : rdRaw N.get (UInt32.add fp 12) 4 = x4)
    (l_x5 : rdRaw N.get (UInt32.add fp 16) 4 = x5)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 468 ≤ fp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, a0, hp, fp, ebx0, fb, ebp0, esi0, edi0, 0x10236a, efl g0, 5⟩)
      (St.m ⟨N'.get, x1, x5, fp, x3, fb, x4, x2, edi0, 0x102387, efl g0, 13⟩) ∧
      Frame N' fb 468 ((4, x3) :: (8, x2) :: (444, hp) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF N fb 468 444 hp hS (by decide)) fb 468 8 x2 stF_FB (by decide)) fb 468 4 x3 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 444 rfl rfl).wrF 8 rfl rfl).wrF 4 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  
  subst l_x1
  subst l_x2
  subst l_x3
  subst l_x4
  subst l_x5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ecx, 0x14(%esp) ; movl 0x14(%edx), %ecx ; movl %ecx, (%esp) ; movl 0x18(%edx), %ecx ; movl 0x1c(%edx), %edi ; movl %edi, 0x18(%esp) ; movl 0x20(%edx), %edi ; movl %edi, 0x24(%esp) -/
theorem sq_p1 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (x1 x5 fp x3 x4 x2 edi0 g0 x6 x7 x8 x9 : UInt32)
        (l_x6 : rdRaw N.get (UInt32.add fp 20) 4 = x6)
    (l_x7 : rdRaw N.get (UInt32.add fp 24) 4 = x7)
    (l_x8 : rdRaw N.get (UInt32.add fp 28) 4 = x8)
    (l_x9 : rdRaw N.get (UInt32.add fp 32) 4 = x9)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 468 ≤ fp.toNat) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x1, x5, fp, x3, fb, x4, x2, edi0, 0x102387, efl g0, 13⟩)
      (St.m ⟨N'.get, x1, x7, fp, x3, fb, x4, x2, x9, 0x1023a2, efl g0, 21⟩) ∧
      Frame N' fb 468 ((36, x9) :: (24, x8) :: (0, x6) :: (20, x5) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF0 (stF N fb 468 20 x5 hS (by decide)) fb 468 x6 stF_FB (by decide)) fb 468 24 x8 stF0_FB (by decide)) fb 468 36 x9 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 20 rfl rfl).wrF0).wrF 24 rfl rfl).wrF 36 rfl rfl), ((((hP.wrF (by decide)).wrF0 (by decide)).wrF (by decide)).wrF (by decide))⟩
  
  subst l_x6
  subst l_x7
  subst l_x8
  subst l_x9
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x24(%edx), %edx ; movl %edx, 0x48(%esp) ; leal (%ecx,%ecx,8), %edx ; leal (%ecx,%edx,2), %edx ; movl %edx, 0x38(%esp) ; leal (%edi,%edi,8), %edx ; leal (%edi,%edx,2), %edx ; movl %edx, 0x20(%esp) -/
theorem sq_p2 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (x1 x7 fp x3 x4 x2 x9 g0 x10 v11 v12 v13 v14 : UInt32)
        (l_x10 : rdRaw N.get (UInt32.add fp 36) 4 = x10)
    (hfp : fp.toNat + 40 ≤ N.get.size)
    (hfp' : fp.toNat + 40 ≤ fb.toNat ∨ fb.toNat + 468 ≤ fp.toNat)
    (e_v11 : v11 = UInt32.add x7 (UInt32.shiftLeft x7 3))
    (e_v12 : v12 = UInt32.add x7 (UInt32.shiftLeft v11 1))
    (e_v13 : v13 = UInt32.add x9 (UInt32.shiftLeft x9 3))
    (e_v14 : v14 = UInt32.add x9 (UInt32.shiftLeft v13 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x1, x7, fp, x3, fb, x4, x2, x9, 0x1023a2, efl g0, 21⟩)
      (St.m ⟨N'.get, x1, x7, v14, x3, fb, x4, x2, x9, 0x1023bd, efl g0, 29⟩) ∧
      Frame N' fb 468 ((32, v14) :: (56, v12) :: (72, x10) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF N fb 468 72 x10 hS (by decide)) fb 468 56 v12 stF_FB (by decide)) fb 468 32 v14 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 72 rfl rfl).wrF 56 rfl rfl).wrF 32 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_v14
  subst e_v13
  subst e_v12
  subst e_v11
  subst l_x10
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- leal (%eax,%eax,1), %edi ; imull %eax ; movl %edx, 0x104(%esp) ; movl %eax, 0x100(%esp) ; movl %edi, %eax ; imull %esi ; movl %edx, 0x138(%esp) ; movl %eax, 0x134(%esp) -/
theorem sq_p3 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (x1 x7 v14 x3 x4 x2 x9 g0 v15 v16 v17 g18 v19 v20 g21 : UInt32)
        (e_v15 : v15 = UInt32.add x1 x1)
    (e_v16 : v16 = UInt64.toUInt32 (imulCore 4 x1 x1).1)
    (e_v17 : v17 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x1 x1).1 32))
    (e_g18 : g18 = mixF g0 (ovfBits (imulCore 4 x1 x1).2) 2049)
    (e_v19 : v19 = UInt64.toUInt32 (imulCore 4 v15 x2).1)
    (e_v20 : v20 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v15 x2).1 32))
    (e_g21 : g21 = mixF g18 (ovfBits (imulCore 4 v15 x2).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x1, x7, v14, x3, fb, x4, x2, x9, 0x1023bd, efl g0, 29⟩)
      (St.m ⟨N'.get, v19, x7, v20, x3, fb, x4, x2, v15, 0x1023e2, efl g21, 37⟩) ∧
      Frame N' fb 468 ((308, v19) :: (312, v20) :: (256, v16) :: (260, v17) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 260 v17 hS (by decide)) fb 468 256 v16 stF_FB (by decide)) fb 468 312 v20 stF_FB (by decide)) fb 468 308 v19 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 260 rfl rfl).wrF 256 rfl rfl).wrF 312 rfl rfl).wrF 308 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g21
  subst e_v20
  subst e_v19
  subst e_g18
  subst e_v17
  subst e_v16
  subst e_v15
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebx, %eax ; imull %edi ; movl %edx, 0x120(%esp) ; movl %eax, 0x110(%esp) ; movl %ebp, %eax ; imull %edi ; movl %edx, 0x114(%esp) ; movl %eax, 0x108(%esp) -/
theorem sq_p4 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v19 x7 v20 x3 x4 x2 v15 g21 v22 v23 g24 v25 v26 g27 : UInt32)
        (e_v22 : v22 = UInt64.toUInt32 (imulCore 4 x3 v15).1)
    (e_v23 : v23 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x3 v15).1 32))
    (e_g24 : g24 = mixF g21 (ovfBits (imulCore 4 x3 v15).2) 2049)
    (e_v25 : v25 = UInt64.toUInt32 (imulCore 4 x4 v15).1)
    (e_v26 : v26 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x4 v15).1 32))
    (e_g27 : g27 = mixF g24 (ovfBits (imulCore 4 x4 v15).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v19, x7, v20, x3, fb, x4, x2, v15, 0x1023e2, efl g21, 37⟩)
      (St.m ⟨N'.get, v25, x7, v26, x3, fb, x4, x2, v15, 0x102406, efl g27, 45⟩) ∧
      Frame N' fb 468 ((264, v25) :: (276, v26) :: (272, v22) :: (288, v23) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 288 v23 hS (by decide)) fb 468 272 v22 stF_FB (by decide)) fb 468 276 v26 stF_FB (by decide)) fb 468 264 v25 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 288 rfl rfl).wrF 272 rfl rfl).wrF 276 rfl rfl).wrF 264 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g27
  subst e_v26
  subst e_v25
  subst e_g24
  subst e_v23
  subst e_v22
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x14(%esp), %ebx ; movl %ebx, %eax ; imull %edi ; movl %edx, 0x11c(%esp) ; movl %eax, 0x10c(%esp) ; movl (%esp), %esi ; movl %esi, %eax ; imull %edi -/
theorem sq_p5 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v25 x7 v26 x3 x4 x2 v15 g27 x5 x6 v28 v29 g30 v31 v32 g33 : UInt32)
        (l_x5 : l.lookup 20 = some x5)
    (l_x6 : l.lookup 0 = some x6)
    (e_v28 : v28 = UInt64.toUInt32 (imulCore 4 x5 v15).1)
    (e_v29 : v29 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x5 v15).1 32))
    (e_g30 : g30 = mixF g27 (ovfBits (imulCore 4 x5 v15).2) 2049)
    (e_v31 : v31 = UInt64.toUInt32 (imulCore 4 x6 v15).1)
    (e_v32 : v32 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x6 v15).1 32))
    (e_g33 : g33 = mixF g30 (ovfBits (imulCore 4 x6 v15).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v25, x7, v26, x3, fb, x4, x2, v15, 0x102406, efl g27, 45⟩)
      (St.m ⟨N'.get, v31, x7, v32, x5, fb, x4, x6, v15, 0x102423, efl g33, 53⟩) ∧
      Frame N' fb 468 ((268, v28) :: (284, v29) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF N fb 468 284 v29 hS (by decide)) fb 468 268 v28 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((hF.wrF 284 rfl rfl).wrF 268 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g33
  subst e_v32
  subst e_v31
  subst e_g30
  subst e_v29
  subst e_v28
  have r_x5 := hF.rd l_x5 20 rfl; subst r_x5
  have r_x6 := hF.rd0 l_x6; subst r_x6
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
