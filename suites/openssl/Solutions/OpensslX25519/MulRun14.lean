import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 78–83

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

/-- addl 0x27c(%esp), %ebx ; adcl 0x284(%esp), %ebp ; addl 0x98(%esp), %ebx ; adcl 0x9c(%esp), %ebp ; addl 0xb8(%esp), %ebx ; adcl 0xc0(%esp), %ebp ; addl 0xe0(%esp), %ebx ; adcl 0xe8(%esp), %ebp -/
theorem mul_p78 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v470 v472 v476 v490 v492 v474 v462 g493 v54 v55 v332 v333 v304 v305 v277 v278 v494 g495 v496 g497 v498 g499 v500 g501 v502 g503 v504 g505 v506 g507 v508 g509 : UInt32)
        (l_v54 : l.lookup 636 = some v54)
    (l_v55 : l.lookup 644 = some v55)
    (l_v332 : l.lookup 152 = some v332)
    (l_v333 : l.lookup 156 = some v333)
    (l_v304 : l.lookup 184 = some v304)
    (l_v305 : l.lookup 192 = some v305)
    (l_v277 : l.lookup 224 = some v277)
    (l_v278 : l.lookup 232 = some v278)
    (e_v494 : v494 = (addF 4 v490 v54 0).1)
    (e_g495 : g495 = (addF 4 v490 v54 0).2)
    (e_v496 : v496 = (addF 4 v492 v55 (cfBit g495)).1)
    (e_g497 : g497 = (addF 4 v492 v55 (cfBit g495)).2)
    (e_v498 : v498 = (addF 4 v494 v332 0).1)
    (e_g499 : g499 = (addF 4 v494 v332 0).2)
    (e_v500 : v500 = (addF 4 v496 v333 (cfBit g499)).1)
    (e_g501 : g501 = (addF 4 v496 v333 (cfBit g499)).2)
    (e_v502 : v502 = (addF 4 v498 v304 0).1)
    (e_g503 : g503 = (addF 4 v498 v304 0).2)
    (e_v504 : v504 = (addF 4 v500 v305 (cfBit g503)).1)
    (e_g505 : g505 = (addF 4 v500 v305 (cfBit g503)).2)
    (e_v506 : v506 = (addF 4 v502 v277 0).1)
    (e_g507 : g507 = (addF 4 v502 v277 0).2)
    (e_v508 : v508 = (addF 4 v504 v278 (cfBit g507)).1)
    (e_g509 : g509 = (addF 4 v504 v278 (cfBit g507)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v470, v472, v476, v490, fb, v492, v474, v462, 0x1016f6, efl g493, 614⟩)
      (St.m ⟨N'.get, v470, v472, v476, v506, fb, v508, v474, v462, 0x10172e, efl g509, 622⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g509
  subst e_v508
  subst e_g507
  subst e_v506
  subst e_g505
  subst e_v504
  subst e_g503
  subst e_v502
  subst e_g501
  subst e_v500
  subst e_g499
  subst e_v498
  subst e_g497
  subst e_v496
  subst e_g495
  subst e_v494
  have r_v54 := hF.rd l_v54 636 rfl; subst r_v54
  have r_v55 := hF.rd l_v55 644 rfl; subst r_v55
  have r_v332 := hF.rd l_v332 152 rfl; subst r_v332
  have r_v333 := hF.rd l_v333 156 rfl; subst r_v333
  have r_v304 := hF.rd l_v304 184 rfl; subst r_v304
  have r_v305 := hF.rd l_v305 192 rfl; subst r_v305
  have r_v277 := hF.rd l_v277 224 rfl; subst r_v277
  have r_v278 := hF.rd l_v278 232 rfl; subst r_v278
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x110(%esp), %ebx ; adcl 0x118(%esp), %ebp ; addl %edx, %ebx ; movl %ebx, 0xc(%esp) ; adcl %esi, %ebp ; andl $0xfc000000, %eax -/
theorem mul_p79 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v470 v472 v476 v506 v508 v474 v462 g509 v249 v250 v510 g511 v512 g513 v514 g515 v516 g517 v518 g519 : UInt32)
        (l_v249 : l.lookup 272 = some v249)
    (l_v250 : l.lookup 280 = some v250)
    (e_v510 : v510 = (addF 4 v506 v249 0).1)
    (e_g511 : g511 = (addF 4 v506 v249 0).2)
    (e_v512 : v512 = (addF 4 v508 v250 (cfBit g511)).1)
    (e_g513 : g513 = (addF 4 v508 v250 (cfBit g511)).2)
    (e_v514 : v514 = (addF 4 v510 v476 0).1)
    (e_g515 : g515 = (addF 4 v510 v476 0).2)
    (e_v516 : v516 = (addF 4 v512 v474 (cfBit g515)).1)
    (e_g517 : g517 = (addF 4 v512 v474 (cfBit g515)).2)
    (e_v518 : v518 = (logicF 4 (UInt32.land v470 4227858432)).1)
    (e_g519 : g519 = (logicF 4 (UInt32.land v470 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v470, v472, v476, v506, fb, v508, v474, v462, 0x10172e, efl g509, 622⟩)
      (St.m ⟨N'.get, v518, v472, v476, v514, fb, v516, v474, v462, 0x101749, efl g519, 628⟩) ∧
      Frame N' fb 836 ((12, v514) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 12 v514 hS (by decide)), run_of_runOk (k := 6) ?_, (hF.wrF 12 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g519
  subst e_v518
  subst e_g517
  subst e_v516
  subst e_g515
  subst e_v514
  subst e_g513
  subst e_v512
  subst e_g511
  subst e_v510
  have r_v249 := hF.rd l_v249 272 rfl; subst r_v249
  have r_v250 := hF.rd l_v250 280 rfl; subst r_v250
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, 0x1c(%esp) ; sbbl %ecx, 0x28(%esp) ; movl 0x14(%esp), %ebx ; movl %ebx, %eax ; addl $0x1000000, %eax -/
theorem mul_p80 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v518 v472 v476 v514 v516 v474 v462 g519 v416 v418 v460 v520 g521 v522 g523 v524 g525 : UInt32)
        (l_v416 : l.lookup 28 = some v416)
    (l_v418 : l.lookup 40 = some v418)
    (l_v460 : l.lookup 20 = some v460)
    (e_v520 : v520 = (subF 4 v416 v518 0).1)
    (e_g521 : g521 = (subF 4 v416 v518 0).2)
    (e_v522 : v522 = (subF 4 v418 v472 (cfBit g521)).1)
    (e_g523 : g523 = (subF 4 v418 v472 (cfBit g521)).2)
    (e_v524 : v524 = (addF 4 v460 16777216 0).1)
    (e_g525 : g525 = (addF 4 v460 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v518, v472, v476, v514, fb, v516, v474, v462, 0x101749, efl g519, 628⟩)
      (St.m ⟨N'.get, v524, v472, v476, v460, fb, v516, v474, v462, 0x10175c, efl g525, 633⟩) ∧
      Frame N' fb 836 ((40, v522) :: (28, v520) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF N fb 836 28 v520 hS (by decide)) fb 836 40 v522 stF_FB (by decide)), run_of_runOk (k := 5) ?_, ((hF.wrF 28 rfl rfl).wrF 40 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g525
  subst e_v524
  subst e_g523
  subst e_v522
  subst e_g521
  subst e_v520
  have r_v416 := hF.rd l_v416 28 rfl; subst r_v416
  have r_v418 := hF.rd l_v418 40 rfl; subst r_v418
  have r_v460 := hF.rd l_v460 20 rfl; subst r_v460
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %edi ; movl %eax, %ecx ; shrdl $0x19, %edi, %ecx ; sarl $0x19, %edi ; movl 0x34(%esp), %edx ; addl 0x280(%esp), %edx ; movl 0x258(%esp), %esi ; adcl 0x288(%esp), %esi -/
theorem mul_p81 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v524 v472 v476 v460 v516 v474 v462 g525 v100 v73 v101 v74 v526 g527 v528 g529 v530 g531 v532 g533 v534 g535 : UInt32)
        (l_v100 : l.lookup 52 = some v100)
    (l_v73 : l.lookup 640 = some v73)
    (l_v101 : l.lookup 600 = some v101)
    (l_v74 : l.lookup 648 = some v74)
    (e_v526 : v526 = (addF 4 v462 0 (cfBit g525)).1)
    (e_g527 : g527 = (addF 4 v462 0 (cfBit g525)).2)
    (e_v528 : v528 = sdR false v524 v526 25)
    (e_g529 : g529 = sdF false v524 v526 25)
    (e_v530 : v530 = sarR v526 25)
    (e_g531 : g531 = sarF v526 25)
    (e_v532 : v532 = (addF 4 v100 v73 0).1)
    (e_g533 : g533 = (addF 4 v100 v73 0).2)
    (e_v534 : v534 = (addF 4 v101 v74 (cfBit g533)).1)
    (e_g535 : g535 = (addF 4 v101 v74 (cfBit g533)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v524, v472, v476, v460, fb, v516, v474, v462, 0x10175c, efl g525, 633⟩)
      (St.m ⟨N'.get, v524, v528, v532, v460, fb, v516, v534, v530, 0x101781, efl g535, 641⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g535
  subst e_v534
  subst e_g533
  subst e_v532
  subst e_g531
  subst e_v530
  subst e_g529
  subst e_v528
  subst e_g527
  subst e_v526
  have r_v100 := hF.rd l_v100 52 rfl; subst r_v100
  have r_v73 := hF.rd l_v73 640 rfl; subst r_v73
  have r_v101 := hF.rd l_v101 600 rfl; subst r_v101
  have r_v74 := hF.rd l_v74 648 rfl; subst r_v74
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x2b0(%esp), %edx ; adcl 0x2b4(%esp), %esi ; addl 0xbc(%esp), %edx ; adcl 0xc4(%esp), %esi ; addl 0xe4(%esp), %edx ; adcl 0xec(%esp), %esi ; addl 0x114(%esp), %edx ; adcl 0x11c(%esp), %esi -/
theorem mul_p82 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v524 v528 v532 v460 v516 v534 v530 g535 v45 v46 v323 v324 v295 v296 v268 v269 v536 g537 v538 g539 v540 g541 v542 g543 v544 g545 v546 g547 v548 g549 v550 g551 : UInt32)
        (l_v45 : l.lookup 688 = some v45)
    (l_v46 : l.lookup 692 = some v46)
    (l_v323 : l.lookup 188 = some v323)
    (l_v324 : l.lookup 196 = some v324)
    (l_v295 : l.lookup 228 = some v295)
    (l_v296 : l.lookup 236 = some v296)
    (l_v268 : l.lookup 276 = some v268)
    (l_v269 : l.lookup 284 = some v269)
    (e_v536 : v536 = (addF 4 v532 v45 0).1)
    (e_g537 : g537 = (addF 4 v532 v45 0).2)
    (e_v538 : v538 = (addF 4 v534 v46 (cfBit g537)).1)
    (e_g539 : g539 = (addF 4 v534 v46 (cfBit g537)).2)
    (e_v540 : v540 = (addF 4 v536 v323 0).1)
    (e_g541 : g541 = (addF 4 v536 v323 0).2)
    (e_v542 : v542 = (addF 4 v538 v324 (cfBit g541)).1)
    (e_g543 : g543 = (addF 4 v538 v324 (cfBit g541)).2)
    (e_v544 : v544 = (addF 4 v540 v295 0).1)
    (e_g545 : g545 = (addF 4 v540 v295 0).2)
    (e_v546 : v546 = (addF 4 v542 v296 (cfBit g545)).1)
    (e_g547 : g547 = (addF 4 v542 v296 (cfBit g545)).2)
    (e_v548 : v548 = (addF 4 v544 v268 0).1)
    (e_g549 : g549 = (addF 4 v544 v268 0).2)
    (e_v550 : v550 = (addF 4 v546 v269 (cfBit g549)).1)
    (e_g551 : g551 = (addF 4 v546 v269 (cfBit g549)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v524, v528, v532, v460, fb, v516, v534, v530, 0x101781, efl g535, 641⟩)
      (St.m ⟨N'.get, v524, v528, v548, v460, fb, v516, v550, v530, 0x1017b9, efl g551, 649⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g551
  subst e_v550
  subst e_g549
  subst e_v548
  subst e_g547
  subst e_v546
  subst e_g545
  subst e_v544
  subst e_g543
  subst e_v542
  subst e_g541
  subst e_v540
  subst e_g539
  subst e_v538
  subst e_g537
  subst e_v536
  have r_v45 := hF.rd l_v45 688 rfl; subst r_v45
  have r_v46 := hF.rd l_v46 692 rfl; subst r_v46
  have r_v323 := hF.rd l_v323 188 rfl; subst r_v323
  have r_v324 := hF.rd l_v324 196 rfl; subst r_v324
  have r_v295 := hF.rd l_v295 228 rfl; subst r_v295
  have r_v296 := hF.rd l_v296 236 rfl; subst r_v296
  have r_v268 := hF.rd l_v268 276 rfl; subst r_v268
  have r_v269 := hF.rd l_v269 284 rfl; subst r_v269
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x144(%esp), %edx ; adcl 0x148(%esp), %esi ; addl 0x174(%esp), %edx ; adcl 0x178(%esp), %esi ; addl 0x1ac(%esp), %edx ; adcl 0x1b4(%esp), %esi ; addl 0x1f4(%esp), %edx ; adcl 0x1fc(%esp), %esi -/
theorem mul_p83 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v524 v528 v548 v460 v516 v550 v530 g551 v240 v241 v213 v214 v185 v186 v158 v159 v552 g553 v554 g555 v556 g557 v558 g559 v560 g561 v562 g563 v564 g565 v566 g567 : UInt32)
        (l_v240 : l.lookup 324 = some v240)
    (l_v241 : l.lookup 328 = some v241)
    (l_v213 : l.lookup 372 = some v213)
    (l_v214 : l.lookup 376 = some v214)
    (l_v185 : l.lookup 428 = some v185)
    (l_v186 : l.lookup 436 = some v186)
    (l_v158 : l.lookup 500 = some v158)
    (l_v159 : l.lookup 508 = some v159)
    (e_v552 : v552 = (addF 4 v548 v240 0).1)
    (e_g553 : g553 = (addF 4 v548 v240 0).2)
    (e_v554 : v554 = (addF 4 v550 v241 (cfBit g553)).1)
    (e_g555 : g555 = (addF 4 v550 v241 (cfBit g553)).2)
    (e_v556 : v556 = (addF 4 v552 v213 0).1)
    (e_g557 : g557 = (addF 4 v552 v213 0).2)
    (e_v558 : v558 = (addF 4 v554 v214 (cfBit g557)).1)
    (e_g559 : g559 = (addF 4 v554 v214 (cfBit g557)).2)
    (e_v560 : v560 = (addF 4 v556 v185 0).1)
    (e_g561 : g561 = (addF 4 v556 v185 0).2)
    (e_v562 : v562 = (addF 4 v558 v186 (cfBit g561)).1)
    (e_g563 : g563 = (addF 4 v558 v186 (cfBit g561)).2)
    (e_v564 : v564 = (addF 4 v560 v158 0).1)
    (e_g565 : g565 = (addF 4 v560 v158 0).2)
    (e_v566 : v566 = (addF 4 v562 v159 (cfBit g565)).1)
    (e_g567 : g567 = (addF 4 v562 v159 (cfBit g565)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v524, v528, v548, v460, fb, v516, v550, v530, 0x1017b9, efl g551, 649⟩)
      (St.m ⟨N'.get, v524, v528, v564, v460, fb, v516, v566, v530, 0x1017f1, efl g567, 657⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g567
  subst e_v566
  subst e_g565
  subst e_v564
  subst e_g563
  subst e_v562
  subst e_g561
  subst e_v560
  subst e_g559
  subst e_v558
  subst e_g557
  subst e_v556
  subst e_g555
  subst e_v554
  subst e_g553
  subst e_v552
  have r_v240 := hF.rd l_v240 324 rfl; subst r_v240
  have r_v241 := hF.rd l_v241 328 rfl; subst r_v241
  have r_v213 := hF.rd l_v213 372 rfl; subst r_v213
  have r_v214 := hF.rd l_v214 376 rfl; subst r_v214
  have r_v185 := hF.rd l_v185 428 rfl; subst r_v185
  have r_v186 := hF.rd l_v186 436 rfl; subst r_v186
  have r_v158 := hF.rd l_v158 500 rfl; subst r_v158
  have r_v159 := hF.rd l_v159 508 rfl; subst r_v159
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
