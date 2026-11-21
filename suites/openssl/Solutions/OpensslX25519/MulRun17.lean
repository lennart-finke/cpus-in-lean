import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 96–101

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

/-- adcl $0x0, %ebp ; movl %eax, %ecx ; shrdl $0x1a, %ebp, %ecx ; sarl $0x1a, %ebp ; movl 0x18(%esp), %ebx ; addl 0x1e4(%esp), %ebx ; movl 0x1a8(%esp), %edx ; adcl 0x1ec(%esp), %edx -/
theorem mul_p96 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v680 v632 v672 v678 v622 v620 v674 g681 v252 v225 v253 v226 v682 g683 v684 g685 v686 g687 v688 g689 v690 g691 : UInt32)
        (l_v252 : l.lookup 24 = some v252)
    (l_v225 : l.lookup 484 = some v225)
    (l_v253 : l.lookup 424 = some v253)
    (l_v226 : l.lookup 492 = some v226)
    (e_v682 : v682 = (addF 4 v622 0 (cfBit g681)).1)
    (e_g683 : g683 = (addF 4 v622 0 (cfBit g681)).2)
    (e_v684 : v684 = sdR false v680 v682 26)
    (e_g685 : g685 = sdF false v680 v682 26)
    (e_v686 : v686 = sarR v682 26)
    (e_g687 : g687 = sarF v682 26)
    (e_v688 : v688 = (addF 4 v252 v225 0).1)
    (e_g689 : g689 = (addF 4 v252 v225 0).2)
    (e_v690 : v690 = (addF 4 v253 v226 (cfBit g689)).1)
    (e_g691 : g691 = (addF 4 v253 v226 (cfBit g689)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v680, v632, v672, v678, fb, v622, v620, v674, 0x101968, efl g681, 733⟩)
      (St.m ⟨N'.get, v680, v684, v690, v688, fb, v686, v620, v674, 0x10198d, efl g691, 741⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g691
  subst e_v690
  subst e_g689
  subst e_v688
  subst e_g687
  subst e_v686
  subst e_g685
  subst e_v684
  subst e_g683
  subst e_v682
  have r_v252 := hF.rd l_v252 24 rfl; subst r_v252
  have r_v225 := hF.rd l_v225 484 rfl; subst r_v225
  have r_v253 := hF.rd l_v253 424 rfl; subst r_v253
  have r_v226 := hF.rd l_v226 492 rfl; subst r_v226
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x230(%esp), %ebx ; adcl 0x238(%esp), %edx ; addl 0x25c(%esp), %ebx ; adcl 0x260(%esp), %edx ; addl 0x28c(%esp), %ebx ; adcl 0x290(%esp), %edx ; addl 0x2b8(%esp), %ebx ; adcl 0x2bc(%esp), %edx -/
theorem mul_p97 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v680 v684 v690 v688 v686 v620 v674 g691 v198 v199 v170 v171 v143 v144 v115 v116 v692 g693 v694 g695 v696 g697 v698 g699 v700 g701 v702 g703 v704 g705 v706 g707 : UInt32)
        (l_v198 : l.lookup 560 = some v198)
    (l_v199 : l.lookup 568 = some v199)
    (l_v170 : l.lookup 604 = some v170)
    (l_v171 : l.lookup 608 = some v171)
    (l_v143 : l.lookup 652 = some v143)
    (l_v144 : l.lookup 656 = some v144)
    (l_v115 : l.lookup 696 = some v115)
    (l_v116 : l.lookup 700 = some v116)
    (e_v692 : v692 = (addF 4 v688 v198 0).1)
    (e_g693 : g693 = (addF 4 v688 v198 0).2)
    (e_v694 : v694 = (addF 4 v690 v199 (cfBit g693)).1)
    (e_g695 : g695 = (addF 4 v690 v199 (cfBit g693)).2)
    (e_v696 : v696 = (addF 4 v692 v170 0).1)
    (e_g697 : g697 = (addF 4 v692 v170 0).2)
    (e_v698 : v698 = (addF 4 v694 v171 (cfBit g697)).1)
    (e_g699 : g699 = (addF 4 v694 v171 (cfBit g697)).2)
    (e_v700 : v700 = (addF 4 v696 v143 0).1)
    (e_g701 : g701 = (addF 4 v696 v143 0).2)
    (e_v702 : v702 = (addF 4 v698 v144 (cfBit g701)).1)
    (e_g703 : g703 = (addF 4 v698 v144 (cfBit g701)).2)
    (e_v704 : v704 = (addF 4 v700 v115 0).1)
    (e_g705 : g705 = (addF 4 v700 v115 0).2)
    (e_v706 : v706 = (addF 4 v702 v116 (cfBit g705)).1)
    (e_g707 : g707 = (addF 4 v702 v116 (cfBit g705)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v680, v684, v690, v688, fb, v686, v620, v674, 0x10198d, efl g691, 741⟩)
      (St.m ⟨N'.get, v680, v684, v706, v704, fb, v686, v620, v674, 0x1019c5, efl g707, 749⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g707
  subst e_v706
  subst e_g705
  subst e_v704
  subst e_g703
  subst e_v702
  subst e_g701
  subst e_v700
  subst e_g699
  subst e_v698
  subst e_g697
  subst e_v696
  subst e_g695
  subst e_v694
  subst e_g693
  subst e_v692
  have r_v198 := hF.rd l_v198 560 rfl; subst r_v198
  have r_v199 := hF.rd l_v199 568 rfl; subst r_v199
  have r_v170 := hF.rd l_v170 604 rfl; subst r_v170
  have r_v171 := hF.rd l_v171 608 rfl; subst r_v171
  have r_v143 := hF.rd l_v143 652 rfl; subst r_v143
  have r_v144 := hF.rd l_v144 656 rfl; subst r_v144
  have r_v115 := hF.rd l_v115 696 rfl; subst r_v115
  have r_v116 := hF.rd l_v116 700 rfl; subst r_v116
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x2dc(%esp), %ebx ; adcl 0x2e0(%esp), %edx ; addl 0x2f8(%esp), %ebx ; adcl 0x2fc(%esp), %edx ; addl 0x38(%esp), %ebx ; adcl 0x3c(%esp), %edx ; addl 0x154(%esp), %ebx ; adcl 0x158(%esp), %edx -/
theorem mul_p98 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v680 v684 v706 v704 v686 v620 v674 g707 v88 v89 v60 v61 v338 v339 v310 v311 v708 g709 v710 g711 v712 g713 v714 g715 v716 g717 v718 g719 v720 g721 v722 g723 : UInt32)
        (l_v88 : l.lookup 732 = some v88)
    (l_v89 : l.lookup 736 = some v89)
    (l_v60 : l.lookup 760 = some v60)
    (l_v61 : l.lookup 764 = some v61)
    (l_v338 : l.lookup 56 = some v338)
    (l_v339 : l.lookup 60 = some v339)
    (l_v310 : l.lookup 340 = some v310)
    (l_v311 : l.lookup 344 = some v311)
    (e_v708 : v708 = (addF 4 v704 v88 0).1)
    (e_g709 : g709 = (addF 4 v704 v88 0).2)
    (e_v710 : v710 = (addF 4 v706 v89 (cfBit g709)).1)
    (e_g711 : g711 = (addF 4 v706 v89 (cfBit g709)).2)
    (e_v712 : v712 = (addF 4 v708 v60 0).1)
    (e_g713 : g713 = (addF 4 v708 v60 0).2)
    (e_v714 : v714 = (addF 4 v710 v61 (cfBit g713)).1)
    (e_g715 : g715 = (addF 4 v710 v61 (cfBit g713)).2)
    (e_v716 : v716 = (addF 4 v712 v338 0).1)
    (e_g717 : g717 = (addF 4 v712 v338 0).2)
    (e_v718 : v718 = (addF 4 v714 v339 (cfBit g717)).1)
    (e_g719 : g719 = (addF 4 v714 v339 (cfBit g717)).2)
    (e_v720 : v720 = (addF 4 v716 v310 0).1)
    (e_g721 : g721 = (addF 4 v716 v310 0).2)
    (e_v722 : v722 = (addF 4 v718 v311 (cfBit g721)).1)
    (e_g723 : g723 = (addF 4 v718 v311 (cfBit g721)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v680, v684, v706, v704, fb, v686, v620, v674, 0x1019c5, efl g707, 749⟩)
      (St.m ⟨N'.get, v680, v684, v722, v720, fb, v686, v620, v674, 0x1019f7, efl g723, 757⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g723
  subst e_v722
  subst e_g721
  subst e_v720
  subst e_g719
  subst e_v718
  subst e_g717
  subst e_v716
  subst e_g715
  subst e_v714
  subst e_g713
  subst e_v712
  subst e_g711
  subst e_v710
  subst e_g709
  subst e_v708
  have r_v88 := hF.rd l_v88 732 rfl; subst r_v88
  have r_v89 := hF.rd l_v89 736 rfl; subst r_v89
  have r_v60 := hF.rd l_v60 760 rfl; subst r_v60
  have r_v61 := hF.rd l_v61 764 rfl; subst r_v61
  have r_v338 := hF.rd l_v338 56 rfl; subst r_v338
  have r_v339 := hF.rd l_v339 60 rfl; subst r_v339
  have r_v310 := hF.rd l_v310 340 rfl; subst r_v310
  have r_v311 := hF.rd l_v311 344 rfl; subst r_v311
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl %ecx, %ebx ; adcl %ebp, %edx ; movl %edx, %ecx ; andl $0xfc000000, %eax -/
theorem mul_p99 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v680 v684 v722 v720 v686 v620 v674 g723 v724 g725 v726 g727 v728 g729 : UInt32)
        (e_v724 : v724 = (addF 4 v720 v684 0).1)
    (e_g725 : g725 = (addF 4 v720 v684 0).2)
    (e_v726 : v726 = (addF 4 v722 v686 (cfBit g725)).1)
    (e_g727 : g727 = (addF 4 v722 v686 (cfBit g725)).2)
    (e_v728 : v728 = (logicF 4 (UInt32.land v680 4227858432)).1)
    (e_g729 : g729 = (logicF 4 (UInt32.land v680 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v680, v684, v722, v720, fb, v686, v620, v674, 0x1019f7, efl g723, 757⟩)
      (St.m ⟨N'.get, v728, v726, v726, v724, fb, v686, v620, v674, 0x101a02, efl g729, 761⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 4) ?_, hF, hP⟩
  subst e_g729
  subst e_v728
  subst e_g727
  subst e_v726
  subst e_g725
  subst e_v724
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, %esi ; movl %esi, (%esp) ; movl 0x20(%esp), %edx ; movl %edx, %eax ; addl $0x1000000, %eax -/
theorem mul_p100 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v728 v726 v724 v686 v620 v674 g729 v672 v730 g731 v732 g733 : UInt32)
        (l_v672 : l.lookup 32 = some v672)
    (e_v730 : v730 = (subF 4 v620 v728 0).1)
    (e_g731 : g731 = (subF 4 v620 v728 0).2)
    (e_v732 : v732 = (addF 4 v672 16777216 0).1)
    (e_g733 : g733 = (addF 4 v672 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v728, v726, v726, v724, fb, v686, v620, v674, 0x101a02, efl g729, 761⟩)
      (St.m ⟨N'.get, v732, v726, v672, v724, fb, v686, v730, v674, 0x101a12, efl g733, 766⟩) ∧
      Frame N' fb 836 ((0, v730) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF0 N fb 836 v730 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF0), (hP.wrF0 (by decide))⟩
  subst e_g733
  subst e_v732
  subst e_g731
  subst e_v730
  have r_v672 := hF.rd l_v672 32 rfl; subst r_v672
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %edi ; movl %eax, %esi ; shrdl $0x19, %edi, %esi ; sarl $0x19, %edi ; addl 0x1c(%esp), %esi ; movl %esi, 0x10(%esp) ; adcl 0x28(%esp), %edi ; andl $0xfe000000, %eax -/
theorem mul_p101 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v732 v726 v672 v724 v686 v730 v674 g733 v520 v522 v734 g735 v736 g737 v738 g739 v740 g741 v742 g743 v744 g745 : UInt32)
        (l_v520 : l.lookup 28 = some v520)
    (l_v522 : l.lookup 40 = some v522)
    (e_v734 : v734 = (addF 4 v674 0 (cfBit g733)).1)
    (e_g735 : g735 = (addF 4 v674 0 (cfBit g733)).2)
    (e_v736 : v736 = sdR false v732 v734 25)
    (e_g737 : g737 = sdF false v732 v734 25)
    (e_v738 : v738 = sarR v734 25)
    (e_g739 : g739 = sarF v734 25)
    (e_v740 : v740 = (addF 4 v736 v520 0).1)
    (e_g741 : g741 = (addF 4 v736 v520 0).2)
    (e_v742 : v742 = (addF 4 v738 v522 (cfBit g741)).1)
    (e_g743 : g743 = (addF 4 v738 v522 (cfBit g741)).2)
    (e_v744 : v744 = (logicF 4 (UInt32.land v732 4261412864)).1)
    (e_g745 : g745 = (logicF 4 (UInt32.land v732 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v732, v726, v672, v724, fb, v686, v730, v674, 0x101a12, efl g733, 766⟩)
      (St.m ⟨N'.get, v744, v726, v672, v724, fb, v686, v740, v742, 0x101a2f, efl g745, 774⟩) ∧
      Frame N' fb 836 ((16, v740) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 16 v740 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 16 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g745
  subst e_v744
  subst e_g743
  subst e_v742
  subst e_g741
  subst e_v740
  subst e_g739
  subst e_v738
  subst e_g737
  subst e_v736
  subst e_g735
  subst e_v734
  have r_v520 := hF.rd l_v520 28 rfl; subst r_v520
  have r_v522 := hF.rd l_v522 40 rfl; subst r_v522
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
