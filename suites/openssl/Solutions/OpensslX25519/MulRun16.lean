import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 90–95

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

/-- subl %eax, %ebx ; movl %ebx, 0xc(%esp) ; movl 0x34(%esp), %ebx ; movl %ebx, %eax ; addl $0x2000000, %eax -/
theorem mul_p90 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v624 v580 v620 v514 v622 v570 g625 v568 v626 g627 v628 g629 : UInt32)
        (l_v568 : l.lookup 52 = some v568)
    (e_v626 : v626 = (subF 4 v514 v624 0).1)
    (e_g627 : g627 = (subF 4 v514 v624 0).2)
    (e_v628 : v628 = (addF 4 v568 33554432 0).1)
    (e_g629 : g629 = (addF 4 v568 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v624, v580, v620, v514, fb, v622, v570, v622, 0x1018ab, efl g625, 695⟩)
      (St.m ⟨N'.get, v628, v580, v620, v568, fb, v622, v570, v622, 0x1018bc, efl g629, 700⟩) ∧
      Frame N' fb 836 ((12, v626) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 12 v626 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF 12 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g629
  subst e_v628
  subst e_g627
  subst e_v626
  have r_v568 := hF.rd l_v568 52 rfl; subst r_v568
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %esi ; movl %eax, %ecx ; shrdl $0x1a, %esi, %ecx ; sarl $0x1a, %esi ; movl 0x20(%esp), %edx ; addl 0x2a0(%esp), %edx ; movl 0x278(%esp), %edi ; adcl 0x2a8(%esp), %edi -/
theorem mul_p91 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v628 v580 v620 v568 v622 v570 g629 v130 v103 v131 v104 v630 g631 v632 g633 v634 g635 v636 g637 v638 g639 : UInt32)
        (l_v130 : l.lookup 32 = some v130)
    (l_v103 : l.lookup 672 = some v103)
    (l_v131 : l.lookup 632 = some v131)
    (l_v104 : l.lookup 680 = some v104)
    (e_v630 : v630 = (addF 4 v570 0 (cfBit g629)).1)
    (e_g631 : g631 = (addF 4 v570 0 (cfBit g629)).2)
    (e_v632 : v632 = sdR false v628 v630 26)
    (e_g633 : g633 = sdF false v628 v630 26)
    (e_v634 : v634 = sarR v630 26)
    (e_g635 : g635 = sarF v630 26)
    (e_v636 : v636 = (addF 4 v130 v103 0).1)
    (e_g637 : g637 = (addF 4 v130 v103 0).2)
    (e_v638 : v638 = (addF 4 v131 v104 (cfBit g637)).1)
    (e_g639 : g639 = (addF 4 v131 v104 (cfBit g637)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v628, v580, v620, v568, fb, v622, v570, v622, 0x1018bc, efl g629, 700⟩)
      (St.m ⟨N'.get, v628, v632, v636, v568, fb, v622, v634, v638, 0x1018e1, efl g639, 708⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g639
  subst e_v638
  subst e_g637
  subst e_v636
  subst e_g635
  subst e_v634
  subst e_g633
  subst e_v632
  subst e_g631
  subst e_v630
  have r_v130 := hF.rd l_v130 32 rfl; subst r_v130
  have r_v103 := hF.rd l_v103 672 rfl; subst r_v103
  have r_v131 := hF.rd l_v131 632 rfl; subst r_v131
  have r_v104 := hF.rd l_v104 680 rfl; subst r_v104
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x2cc(%esp), %edx ; adcl 0x2d4(%esp), %edi ; addl 0x2f0(%esp), %edx ; adcl 0x2f4(%esp), %edi ; addl 0x48(%esp), %edx ; adcl 0x40(%esp), %edi ; addl 0x12c(%esp), %edx ; adcl 0x134(%esp), %edi -/
theorem mul_p92 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v628 v632 v636 v568 v622 v634 v638 g639 v76 v77 v48 v49 v326 v327 v298 v299 v640 g641 v642 g643 v644 g645 v646 g647 v648 g649 v650 g651 v652 g653 v654 g655 : UInt32)
        (l_v76 : l.lookup 716 = some v76)
    (l_v77 : l.lookup 724 = some v77)
    (l_v48 : l.lookup 752 = some v48)
    (l_v49 : l.lookup 756 = some v49)
    (l_v326 : l.lookup 72 = some v326)
    (l_v327 : l.lookup 64 = some v327)
    (l_v298 : l.lookup 300 = some v298)
    (l_v299 : l.lookup 308 = some v299)
    (e_v640 : v640 = (addF 4 v636 v76 0).1)
    (e_g641 : g641 = (addF 4 v636 v76 0).2)
    (e_v642 : v642 = (addF 4 v638 v77 (cfBit g641)).1)
    (e_g643 : g643 = (addF 4 v638 v77 (cfBit g641)).2)
    (e_v644 : v644 = (addF 4 v640 v48 0).1)
    (e_g645 : g645 = (addF 4 v640 v48 0).2)
    (e_v646 : v646 = (addF 4 v642 v49 (cfBit g645)).1)
    (e_g647 : g647 = (addF 4 v642 v49 (cfBit g645)).2)
    (e_v648 : v648 = (addF 4 v644 v326 0).1)
    (e_g649 : g649 = (addF 4 v644 v326 0).2)
    (e_v650 : v650 = (addF 4 v646 v327 (cfBit g649)).1)
    (e_g651 : g651 = (addF 4 v646 v327 (cfBit g649)).2)
    (e_v652 : v652 = (addF 4 v648 v298 0).1)
    (e_g653 : g653 = (addF 4 v648 v298 0).2)
    (e_v654 : v654 = (addF 4 v650 v299 (cfBit g653)).1)
    (e_g655 : g655 = (addF 4 v650 v299 (cfBit g653)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v628, v632, v636, v568, fb, v622, v634, v638, 0x1018e1, efl g639, 708⟩)
      (St.m ⟨N'.get, v628, v632, v652, v568, fb, v622, v634, v654, 0x101913, efl g655, 716⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g655
  subst e_v654
  subst e_g653
  subst e_v652
  subst e_g651
  subst e_v650
  subst e_g649
  subst e_v648
  subst e_g647
  subst e_v646
  subst e_g645
  subst e_v644
  subst e_g643
  subst e_v642
  subst e_g641
  subst e_v640
  have r_v76 := hF.rd l_v76 716 rfl; subst r_v76
  have r_v77 := hF.rd l_v77 724 rfl; subst r_v77
  have r_v48 := hF.rd l_v48 752 rfl; subst r_v48
  have r_v49 := hF.rd l_v49 756 rfl; subst r_v49
  have r_v326 := hF.rd l_v326 72 rfl; subst r_v326
  have r_v327 := hF.rd l_v327 64 rfl; subst r_v327
  have r_v298 := hF.rd l_v298 300 rfl; subst r_v298
  have r_v299 := hF.rd l_v299 308 rfl; subst r_v299
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x15c(%esp), %edx ; adcl 0x164(%esp), %edi ; addl 0x190(%esp), %edx ; adcl 0x198(%esp), %edi ; addl 0x1d4(%esp), %edx ; adcl 0x1dc(%esp), %edi ; addl 0x21c(%esp), %edx ; adcl 0x228(%esp), %edi -/
theorem mul_p93 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v628 v632 v652 v568 v622 v634 v654 g655 v271 v272 v243 v244 v216 v217 v188 v189 v656 g657 v658 g659 v660 g661 v662 g663 v664 g665 v666 g667 v668 g669 v670 g671 : UInt32)
        (l_v271 : l.lookup 348 = some v271)
    (l_v272 : l.lookup 356 = some v272)
    (l_v243 : l.lookup 400 = some v243)
    (l_v244 : l.lookup 408 = some v244)
    (l_v216 : l.lookup 468 = some v216)
    (l_v217 : l.lookup 476 = some v217)
    (l_v188 : l.lookup 540 = some v188)
    (l_v189 : l.lookup 552 = some v189)
    (e_v656 : v656 = (addF 4 v652 v271 0).1)
    (e_g657 : g657 = (addF 4 v652 v271 0).2)
    (e_v658 : v658 = (addF 4 v654 v272 (cfBit g657)).1)
    (e_g659 : g659 = (addF 4 v654 v272 (cfBit g657)).2)
    (e_v660 : v660 = (addF 4 v656 v243 0).1)
    (e_g661 : g661 = (addF 4 v656 v243 0).2)
    (e_v662 : v662 = (addF 4 v658 v244 (cfBit g661)).1)
    (e_g663 : g663 = (addF 4 v658 v244 (cfBit g661)).2)
    (e_v664 : v664 = (addF 4 v660 v216 0).1)
    (e_g665 : g665 = (addF 4 v660 v216 0).2)
    (e_v666 : v666 = (addF 4 v662 v217 (cfBit g665)).1)
    (e_g667 : g667 = (addF 4 v662 v217 (cfBit g665)).2)
    (e_v668 : v668 = (addF 4 v664 v188 0).1)
    (e_g669 : g669 = (addF 4 v664 v188 0).2)
    (e_v670 : v670 = (addF 4 v666 v189 (cfBit g669)).1)
    (e_g671 : g671 = (addF 4 v666 v189 (cfBit g669)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v628, v632, v652, v568, fb, v622, v634, v654, 0x101913, efl g655, 716⟩)
      (St.m ⟨N'.get, v628, v632, v668, v568, fb, v622, v634, v670, 0x10194b, efl g671, 724⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g671
  subst e_v670
  subst e_g669
  subst e_v668
  subst e_g667
  subst e_v666
  subst e_g665
  subst e_v664
  subst e_g663
  subst e_v662
  subst e_g661
  subst e_v660
  subst e_g659
  subst e_v658
  subst e_g657
  subst e_v656
  have r_v271 := hF.rd l_v271 348 rfl; subst r_v271
  have r_v272 := hF.rd l_v272 356 rfl; subst r_v272
  have r_v243 := hF.rd l_v243 400 rfl; subst r_v243
  have r_v244 := hF.rd l_v244 408 rfl; subst r_v244
  have r_v216 := hF.rd l_v216 468 rfl; subst r_v216
  have r_v217 := hF.rd l_v217 476 rfl; subst r_v217
  have r_v188 := hF.rd l_v188 540 rfl; subst r_v188
  have r_v189 := hF.rd l_v189 552 rfl; subst r_v189
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl %ecx, %edx ; movl %edx, 0x20(%esp) ; adcl %esi, %edi ; andl $0xfc000000, %eax -/
theorem mul_p94 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v628 v632 v668 v568 v622 v634 v670 g671 v672 g673 v674 g675 v676 g677 : UInt32)
        (e_v672 : v672 = (addF 4 v668 v632 0).1)
    (e_g673 : g673 = (addF 4 v668 v632 0).2)
    (e_v674 : v674 = (addF 4 v670 v634 (cfBit g673)).1)
    (e_g675 : g675 = (addF 4 v670 v634 (cfBit g673)).2)
    (e_v676 : v676 = (logicF 4 (UInt32.land v628 4227858432)).1)
    (e_g677 : g677 = (logicF 4 (UInt32.land v628 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v628, v632, v668, v568, fb, v622, v634, v670, 0x10194b, efl g671, 724⟩)
      (St.m ⟨N'.get, v676, v632, v672, v568, fb, v622, v634, v674, 0x101958, efl g677, 728⟩) ∧
      Frame N' fb 836 ((32, v672) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 32 v672 hS (by decide)), run_of_runOk (k := 4) ?_, (hF.wrF 32 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g677
  subst e_v676
  subst e_g675
  subst e_v674
  subst e_g673
  subst e_v672
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, %ebx ; movl %ebx, 0x34(%esp) ; movl (%esp), %esi ; movl %esi, %eax ; addl $0x2000000, %eax -/
theorem mul_p95 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v676 v632 v672 v568 v622 v634 v674 g677 v620 v678 g679 v680 g681 : UInt32)
        (l_v620 : l.lookup 0 = some v620)
    (e_v678 : v678 = (subF 4 v568 v676 0).1)
    (e_g679 : g679 = (subF 4 v568 v676 0).2)
    (e_v680 : v680 = (addF 4 v620 33554432 0).1)
    (e_g681 : g681 = (addF 4 v620 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v676, v632, v672, v568, fb, v622, v634, v674, 0x101958, efl g677, 728⟩)
      (St.m ⟨N'.get, v680, v632, v672, v678, fb, v622, v620, v674, 0x101968, efl g681, 733⟩) ∧
      Frame N' fb 836 ((52, v678) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 52 v678 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF 52 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g681
  subst e_v680
  subst e_g679
  subst e_v678
  have r_v620 := hF.rd0 l_v620; subst r_v620
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
