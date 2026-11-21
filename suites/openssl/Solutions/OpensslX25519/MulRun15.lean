import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 84–89

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

/-- addl %ecx, %edx ; movl %edx, 0x34(%esp) ; adcl %edi, %esi ; andl $0xfe000000, %eax -/
theorem mul_p84 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v524 v528 v564 v460 v516 v566 v530 g567 v568 g569 v570 g571 v572 g573 : UInt32)
        (e_v568 : v568 = (addF 4 v564 v528 0).1)
    (e_g569 : g569 = (addF 4 v564 v528 0).2)
    (e_v570 : v570 = (addF 4 v566 v530 (cfBit g569)).1)
    (e_g571 : g571 = (addF 4 v566 v530 (cfBit g569)).2)
    (e_v572 : v572 = (logicF 4 (UInt32.land v524 4261412864)).1)
    (e_g573 : g573 = (logicF 4 (UInt32.land v524 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v524, v528, v564, v460, fb, v516, v566, v530, 0x1017f1, efl g567, 657⟩)
      (St.m ⟨N'.get, v572, v528, v568, v460, fb, v516, v570, v530, 0x1017fe, efl g573, 661⟩) ∧
      Frame N' fb 836 ((52, v568) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 52 v568 hS (by decide)), run_of_runOk (k := 4) ?_, (hF.wrF 52 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g573
  subst e_v572
  subst e_g571
  subst e_v570
  subst e_g569
  subst e_v568
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, %ebx ; movl %ebx, 0x14(%esp) ; movl 0xc(%esp), %ebx ; movl %ebx, %eax ; addl $0x1000000, %eax -/
theorem mul_p85 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v572 v528 v568 v460 v516 v570 v530 g573 v514 v574 g575 v576 g577 : UInt32)
        (l_v514 : l.lookup 12 = some v514)
    (e_v574 : v574 = (subF 4 v460 v572 0).1)
    (e_g575 : g575 = (subF 4 v460 v572 0).2)
    (e_v576 : v576 = (addF 4 v514 16777216 0).1)
    (e_g577 : g577 = (addF 4 v514 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v572, v528, v568, v460, fb, v516, v570, v530, 0x1017fe, efl g573, 661⟩)
      (St.m ⟨N'.get, v576, v528, v568, v514, fb, v516, v570, v530, 0x10180f, efl g577, 666⟩) ∧
      Frame N' fb 836 ((20, v574) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 20 v574 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF 20 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g577
  subst e_v576
  subst e_g575
  subst e_v574
  have r_v514 := hF.rd l_v514 12 rfl; subst r_v514
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %ebp ; movl %eax, %ecx ; shrdl $0x19, %ebp, %ecx ; sarl $0x19, %ebp ; movl (%esp), %edx ; addl 0x1bc(%esp), %edx ; movl 0x180(%esp), %edi ; adcl 0x1c0(%esp), %edi -/
theorem mul_p86 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v576 v528 v568 v514 v516 v570 v530 g577 v222 v195 v223 v196 v578 g579 v580 g581 v582 g583 v584 g585 v586 g587 : UInt32)
        (l_v222 : l.lookup 0 = some v222)
    (l_v195 : l.lookup 444 = some v195)
    (l_v223 : l.lookup 384 = some v223)
    (l_v196 : l.lookup 448 = some v196)
    (e_v578 : v578 = (addF 4 v516 0 (cfBit g577)).1)
    (e_g579 : g579 = (addF 4 v516 0 (cfBit g577)).2)
    (e_v580 : v580 = sdR false v576 v578 25)
    (e_g581 : g581 = sdF false v576 v578 25)
    (e_v582 : v582 = sarR v578 25)
    (e_g583 : g583 = sarF v578 25)
    (e_v584 : v584 = (addF 4 v222 v195 0).1)
    (e_g585 : g585 = (addF 4 v222 v195 0).2)
    (e_v586 : v586 = (addF 4 v223 v196 (cfBit g585)).1)
    (e_g587 : g587 = (addF 4 v223 v196 (cfBit g585)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v576, v528, v568, v514, fb, v516, v570, v530, 0x10180f, efl g577, 666⟩)
      (St.m ⟨N'.get, v576, v580, v584, v514, fb, v582, v570, v586, 0x101833, efl g587, 674⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g587
  subst e_v586
  subst e_g585
  subst e_v584
  subst e_g583
  subst e_v582
  subst e_g581
  subst e_v580
  subst e_g579
  subst e_v578
  have r_v222 := hF.rd0 l_v222; subst r_v222
  have r_v195 := hF.rd l_v195 444 rfl; subst r_v195
  have r_v223 := hF.rd l_v223 384 rfl; subst r_v223
  have r_v196 := hF.rd l_v196 448 rfl; subst r_v196
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x204(%esp), %edx ; adcl 0x208(%esp), %edi ; addl 0x248(%esp), %edx ; adcl 0x24c(%esp), %edi ; addl 0x270(%esp), %edx ; adcl 0x274(%esp), %edi ; addl 0x2a4(%esp), %edx ; adcl 0x2ac(%esp), %edi -/
theorem mul_p87 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v576 v580 v584 v514 v582 v570 v586 g587 v167 v168 v140 v141 v112 v113 v85 v86 v588 g589 v590 g591 v592 g593 v594 g595 v596 g597 v598 g599 v600 g601 v602 g603 : UInt32)
        (l_v167 : l.lookup 516 = some v167)
    (l_v168 : l.lookup 520 = some v168)
    (l_v140 : l.lookup 584 = some v140)
    (l_v141 : l.lookup 588 = some v141)
    (l_v112 : l.lookup 624 = some v112)
    (l_v113 : l.lookup 628 = some v113)
    (l_v85 : l.lookup 676 = some v85)
    (l_v86 : l.lookup 684 = some v86)
    (e_v588 : v588 = (addF 4 v584 v167 0).1)
    (e_g589 : g589 = (addF 4 v584 v167 0).2)
    (e_v590 : v590 = (addF 4 v586 v168 (cfBit g589)).1)
    (e_g591 : g591 = (addF 4 v586 v168 (cfBit g589)).2)
    (e_v592 : v592 = (addF 4 v588 v140 0).1)
    (e_g593 : g593 = (addF 4 v588 v140 0).2)
    (e_v594 : v594 = (addF 4 v590 v141 (cfBit g593)).1)
    (e_g595 : g595 = (addF 4 v590 v141 (cfBit g593)).2)
    (e_v596 : v596 = (addF 4 v592 v112 0).1)
    (e_g597 : g597 = (addF 4 v592 v112 0).2)
    (e_v598 : v598 = (addF 4 v594 v113 (cfBit g597)).1)
    (e_g599 : g599 = (addF 4 v594 v113 (cfBit g597)).2)
    (e_v600 : v600 = (addF 4 v596 v85 0).1)
    (e_g601 : g601 = (addF 4 v596 v85 0).2)
    (e_v602 : v602 = (addF 4 v598 v86 (cfBit g601)).1)
    (e_g603 : g603 = (addF 4 v598 v86 (cfBit g601)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v576, v580, v584, v514, fb, v582, v570, v586, 0x101833, efl g587, 674⟩)
      (St.m ⟨N'.get, v576, v580, v600, v514, fb, v582, v570, v602, 0x10186b, efl g603, 682⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g603
  subst e_v602
  subst e_g601
  subst e_v600
  subst e_g599
  subst e_v598
  subst e_g597
  subst e_v596
  subst e_g595
  subst e_v594
  subst e_g593
  subst e_v592
  subst e_g591
  subst e_v590
  subst e_g589
  subst e_v588
  have r_v167 := hF.rd l_v167 516 rfl; subst r_v167
  have r_v168 := hF.rd l_v168 520 rfl; subst r_v168
  have r_v140 := hF.rd l_v140 584 rfl; subst r_v140
  have r_v141 := hF.rd l_v141 588 rfl; subst r_v141
  have r_v112 := hF.rd l_v112 624 rfl; subst r_v112
  have r_v113 := hF.rd l_v113 628 rfl; subst r_v113
  have r_v85 := hF.rd l_v85 676 rfl; subst r_v85
  have r_v86 := hF.rd l_v86 684 rfl; subst r_v86
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x2d0(%esp), %edx ; adcl 0x2d8(%esp), %edi ; addl 0x4c(%esp), %edx ; adcl 0x54(%esp), %edi ; addl 0x100(%esp), %edx ; adcl 0x104(%esp), %edi ; addl 0x130(%esp), %edx ; adcl 0x138(%esp), %edi -/
theorem mul_p88 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v576 v580 v600 v514 v582 v570 v602 g603 v57 v58 v335 v336 v307 v308 v280 v281 v604 g605 v606 g607 v608 g609 v610 g611 v612 g613 v614 g615 v616 g617 v618 g619 : UInt32)
        (l_v57 : l.lookup 720 = some v57)
    (l_v58 : l.lookup 728 = some v58)
    (l_v335 : l.lookup 76 = some v335)
    (l_v336 : l.lookup 84 = some v336)
    (l_v307 : l.lookup 256 = some v307)
    (l_v308 : l.lookup 260 = some v308)
    (l_v280 : l.lookup 304 = some v280)
    (l_v281 : l.lookup 312 = some v281)
    (e_v604 : v604 = (addF 4 v600 v57 0).1)
    (e_g605 : g605 = (addF 4 v600 v57 0).2)
    (e_v606 : v606 = (addF 4 v602 v58 (cfBit g605)).1)
    (e_g607 : g607 = (addF 4 v602 v58 (cfBit g605)).2)
    (e_v608 : v608 = (addF 4 v604 v335 0).1)
    (e_g609 : g609 = (addF 4 v604 v335 0).2)
    (e_v610 : v610 = (addF 4 v606 v336 (cfBit g609)).1)
    (e_g611 : g611 = (addF 4 v606 v336 (cfBit g609)).2)
    (e_v612 : v612 = (addF 4 v608 v307 0).1)
    (e_g613 : g613 = (addF 4 v608 v307 0).2)
    (e_v614 : v614 = (addF 4 v610 v308 (cfBit g613)).1)
    (e_g615 : g615 = (addF 4 v610 v308 (cfBit g613)).2)
    (e_v616 : v616 = (addF 4 v612 v280 0).1)
    (e_g617 : g617 = (addF 4 v612 v280 0).2)
    (e_v618 : v618 = (addF 4 v614 v281 (cfBit g617)).1)
    (e_g619 : g619 = (addF 4 v614 v281 (cfBit g617)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v576, v580, v600, v514, fb, v582, v570, v602, 0x10186b, efl g603, 682⟩)
      (St.m ⟨N'.get, v576, v580, v616, v514, fb, v582, v570, v618, 0x10189d, efl g619, 690⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g619
  subst e_v618
  subst e_g617
  subst e_v616
  subst e_g615
  subst e_v614
  subst e_g613
  subst e_v612
  subst e_g611
  subst e_v610
  subst e_g609
  subst e_v608
  subst e_g607
  subst e_v606
  subst e_g605
  subst e_v604
  have r_v57 := hF.rd l_v57 720 rfl; subst r_v57
  have r_v58 := hF.rd l_v58 728 rfl; subst r_v58
  have r_v335 := hF.rd l_v335 76 rfl; subst r_v335
  have r_v336 := hF.rd l_v336 84 rfl; subst r_v336
  have r_v307 := hF.rd l_v307 256 rfl; subst r_v307
  have r_v308 := hF.rd l_v308 260 rfl; subst r_v308
  have r_v280 := hF.rd l_v280 304 rfl; subst r_v280
  have r_v281 := hF.rd l_v281 312 rfl; subst r_v281
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl %ecx, %edx ; movl %edx, (%esp) ; adcl %ebp, %edi ; movl %edi, %ebp ; andl $0xfe000000, %eax -/
theorem mul_p89 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v576 v580 v616 v514 v582 v570 v618 g619 v620 g621 v622 g623 v624 g625 : UInt32)
        (e_v620 : v620 = (addF 4 v616 v580 0).1)
    (e_g621 : g621 = (addF 4 v616 v580 0).2)
    (e_v622 : v622 = (addF 4 v618 v582 (cfBit g621)).1)
    (e_g623 : g623 = (addF 4 v618 v582 (cfBit g621)).2)
    (e_v624 : v624 = (logicF 4 (UInt32.land v576 4261412864)).1)
    (e_g625 : g625 = (logicF 4 (UInt32.land v576 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v576, v580, v616, v514, fb, v582, v570, v618, 0x10189d, efl g619, 690⟩)
      (St.m ⟨N'.get, v624, v580, v620, v514, fb, v622, v570, v622, 0x1018ab, efl g625, 695⟩) ∧
      Frame N' fb 836 ((0, v620) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF0 N fb 836 v620 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF0), (hP.wrF0 (by decide))⟩
  subst e_g625
  subst e_v624
  subst e_g623
  subst e_v622
  subst e_g621
  subst e_v620
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
