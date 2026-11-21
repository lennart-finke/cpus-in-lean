import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 72–77

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

/-- adcl 0x84(%esp), %edi ; addl 0xa0(%esp), %eax ; adcl 0xa4(%esp), %edi ; addl 0xc8(%esp), %eax ; adcl 0xcc(%esp), %edi ; addl 0xf0(%esp), %eax ; adcl 0xf4(%esp), %edi ; addl 0x124(%esp), %eax -/
theorem mul_p72 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v428 v420 v422 v424 v418 v426 v382 g429 v321 v292 v293 v265 v266 v237 v238 v210 v430 g431 v432 g433 v434 g435 v436 g437 v438 g439 v440 g441 v442 g443 v444 g445 : UInt32)
        (l_v321 : l.lookup 132 = some v321)
    (l_v292 : l.lookup 160 = some v292)
    (l_v293 : l.lookup 164 = some v293)
    (l_v265 : l.lookup 200 = some v265)
    (l_v266 : l.lookup 204 = some v266)
    (l_v237 : l.lookup 240 = some v237)
    (l_v238 : l.lookup 244 = some v238)
    (l_v210 : l.lookup 292 = some v210)
    (e_v430 : v430 = (addF 4 v382 v321 (cfBit g429)).1)
    (e_g431 : g431 = (addF 4 v382 v321 (cfBit g429)).2)
    (e_v432 : v432 = (addF 4 v428 v292 0).1)
    (e_g433 : g433 = (addF 4 v428 v292 0).2)
    (e_v434 : v434 = (addF 4 v430 v293 (cfBit g433)).1)
    (e_g435 : g435 = (addF 4 v430 v293 (cfBit g433)).2)
    (e_v436 : v436 = (addF 4 v432 v265 0).1)
    (e_g437 : g437 = (addF 4 v432 v265 0).2)
    (e_v438 : v438 = (addF 4 v434 v266 (cfBit g437)).1)
    (e_g439 : g439 = (addF 4 v434 v266 (cfBit g437)).2)
    (e_v440 : v440 = (addF 4 v436 v237 0).1)
    (e_g441 : g441 = (addF 4 v436 v237 0).2)
    (e_v442 : v442 = (addF 4 v438 v238 (cfBit g441)).1)
    (e_g443 : g443 = (addF 4 v438 v238 (cfBit g441)).2)
    (e_v444 : v444 = (addF 4 v440 v210 0).1)
    (e_g445 : g445 = (addF 4 v440 v210 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v428, v420, v422, v424, fb, v418, v426, v382, 0x10161b, efl g429, 575⟩)
      (St.m ⟨N'.get, v444, v420, v422, v424, fb, v418, v426, v442, 0x101653, efl g445, 583⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g445
  subst e_v444
  subst e_g443
  subst e_v442
  subst e_g441
  subst e_v440
  subst e_g439
  subst e_v438
  subst e_g437
  subst e_v436
  subst e_g435
  subst e_v434
  subst e_g433
  subst e_v432
  subst e_g431
  subst e_v430
  have r_v321 := hF.rd l_v321 132 rfl; subst r_v321
  have r_v292 := hF.rd l_v292 160 rfl; subst r_v292
  have r_v293 := hF.rd l_v293 164 rfl; subst r_v293
  have r_v265 := hF.rd l_v265 200 rfl; subst r_v265
  have r_v266 := hF.rd l_v266 204 rfl; subst r_v266
  have r_v237 := hF.rd l_v237 240 rfl; subst r_v237
  have r_v238 := hF.rd l_v238 244 rfl; subst r_v238
  have r_v210 := hF.rd l_v210 292 rfl; subst r_v210
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl 0x120(%esp), %edi ; addl 0x14c(%esp), %eax ; adcl 0x150(%esp), %edi ; addl 0x17c(%esp), %eax ; adcl 0x184(%esp), %edi ; addl 0x1c4(%esp), %eax ; adcl 0x1c8(%esp), %edi ; addl %esi, %eax -/
theorem mul_p73 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v444 v420 v422 v424 v418 v426 v442 g445 v211 v182 v183 v155 v156 v127 v128 v446 g447 v448 g449 v450 g451 v452 g453 v454 g455 v456 g457 v458 g459 v460 g461 : UInt32)
        (l_v211 : l.lookup 288 = some v211)
    (l_v182 : l.lookup 332 = some v182)
    (l_v183 : l.lookup 336 = some v183)
    (l_v155 : l.lookup 380 = some v155)
    (l_v156 : l.lookup 388 = some v156)
    (l_v127 : l.lookup 452 = some v127)
    (l_v128 : l.lookup 456 = some v128)
    (e_v446 : v446 = (addF 4 v442 v211 (cfBit g445)).1)
    (e_g447 : g447 = (addF 4 v442 v211 (cfBit g445)).2)
    (e_v448 : v448 = (addF 4 v444 v182 0).1)
    (e_g449 : g449 = (addF 4 v444 v182 0).2)
    (e_v450 : v450 = (addF 4 v446 v183 (cfBit g449)).1)
    (e_g451 : g451 = (addF 4 v446 v183 (cfBit g449)).2)
    (e_v452 : v452 = (addF 4 v448 v155 0).1)
    (e_g453 : g453 = (addF 4 v448 v155 0).2)
    (e_v454 : v454 = (addF 4 v450 v156 (cfBit g453)).1)
    (e_g455 : g455 = (addF 4 v450 v156 (cfBit g453)).2)
    (e_v456 : v456 = (addF 4 v452 v127 0).1)
    (e_g457 : g457 = (addF 4 v452 v127 0).2)
    (e_v458 : v458 = (addF 4 v454 v128 (cfBit g457)).1)
    (e_g459 : g459 = (addF 4 v454 v128 (cfBit g457)).2)
    (e_v460 : v460 = (addF 4 v456 v426 0).1)
    (e_g461 : g461 = (addF 4 v456 v426 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v444, v420, v422, v424, fb, v418, v426, v442, 0x101653, efl g445, 583⟩)
      (St.m ⟨N'.get, v460, v420, v422, v424, fb, v418, v426, v458, 0x101686, efl g461, 591⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g461
  subst e_v460
  subst e_g459
  subst e_v458
  subst e_g457
  subst e_v456
  subst e_g455
  subst e_v454
  subst e_g453
  subst e_v452
  subst e_g451
  subst e_v450
  subst e_g449
  subst e_v448
  subst e_g447
  subst e_v446
  have r_v211 := hF.rd l_v211 288 rfl; subst r_v211
  have r_v182 := hF.rd l_v182 332 rfl; subst r_v182
  have r_v183 := hF.rd l_v183 336 rfl; subst r_v183
  have r_v155 := hF.rd l_v155 380 rfl; subst r_v155
  have r_v156 := hF.rd l_v156 388 rfl; subst r_v156
  have r_v127 := hF.rd l_v127 452 rfl; subst r_v127
  have r_v128 := hF.rd l_v128 456 rfl; subst r_v128
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x14(%esp) ; adcl %ebx, %edi ; andl $0xfc000000, %ecx -/
theorem mul_p74 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v460 v420 v422 v424 v418 v426 v458 g461 v462 g463 v464 g465 : UInt32)
        (e_v462 : v462 = (addF 4 v458 v424 (cfBit g461)).1)
    (e_g463 : g463 = (addF 4 v458 v424 (cfBit g461)).2)
    (e_v464 : v464 = (logicF 4 (UInt32.land v420 4227858432)).1)
    (e_g465 : g465 = (logicF 4 (UInt32.land v420 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v460, v420, v422, v424, fb, v418, v426, v458, 0x101686, efl g461, 591⟩)
      (St.m ⟨N'.get, v460, v464, v422, v424, fb, v418, v426, v462, 0x101692, efl g465, 594⟩) ∧
      Frame N' fb 836 ((20, v460) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 20 v460 hS (by decide)), run_of_runOk (k := 3) ?_, (hF.wrF 20 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g465
  subst e_v464
  subst e_g463
  subst e_v462
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %ecx, 0x4(%esp) ; sbbl %edx, 0x8(%esp) ; movl 0x1c(%esp), %eax ; addl $0x2000000, %eax -/
theorem mul_p75 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v460 v464 v422 v424 v418 v426 v462 g465 v376 v378 v416 v466 g467 v468 g469 v470 g471 : UInt32)
        (l_v376 : l.lookup 4 = some v376)
    (l_v378 : l.lookup 8 = some v378)
    (l_v416 : l.lookup 28 = some v416)
    (e_v466 : v466 = (subF 4 v376 v464 0).1)
    (e_g467 : g467 = (subF 4 v376 v464 0).2)
    (e_v468 : v468 = (subF 4 v378 v422 (cfBit g467)).1)
    (e_g469 : g469 = (subF 4 v378 v422 (cfBit g467)).2)
    (e_v470 : v470 = (addF 4 v416 33554432 0).1)
    (e_g471 : g471 = (addF 4 v416 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v460, v464, v422, v424, fb, v418, v426, v462, 0x101692, efl g465, 594⟩)
      (St.m ⟨N'.get, v470, v464, v422, v424, fb, v418, v426, v462, 0x1016a3, efl g471, 598⟩) ∧
      Frame N' fb 836 ((8, v468) :: (4, v466) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF N fb 836 4 v466 hS (by decide)) fb 836 8 v468 stF_FB (by decide)), run_of_runOk (k := 4) ?_, ((hF.wrF 4 rfl rfl).wrF 8 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g471
  subst e_v470
  subst e_g469
  subst e_v468
  subst e_g467
  subst e_v466
  have r_v376 := hF.rd l_v376 4 rfl; subst r_v376
  have r_v378 := hF.rd l_v378 8 rfl; subst r_v378
  have r_v416 := hF.rd l_v416 28 rfl; subst r_v416
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebp, %ecx ; adcl $0x0, %ecx ; movl %ecx, %esi ; sarl $0x1a, %esi ; movl %eax, %edx ; shrdl $0x1a, %ecx, %edx ; movl 0xc(%esp), %ebx ; addl 0x188(%esp), %ebx -/
theorem mul_p76 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v470 v464 v422 v424 v418 v426 v462 g471 v191 v164 v472 g473 v474 g475 v476 g477 v478 g479 : UInt32)
        (l_v191 : l.lookup 12 = some v191)
    (l_v164 : l.lookup 392 = some v164)
    (e_v472 : v472 = (addF 4 v418 0 (cfBit g471)).1)
    (e_g473 : g473 = (addF 4 v418 0 (cfBit g471)).2)
    (e_v474 : v474 = sarR v472 26)
    (e_g475 : g475 = sarF v472 26)
    (e_v476 : v476 = sdR false v470 v472 26)
    (e_g477 : g477 = sdF false v470 v472 26)
    (e_v478 : v478 = (addF 4 v191 v164 0).1)
    (e_g479 : g479 = (addF 4 v191 v164 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v470, v464, v422, v424, fb, v418, v426, v462, 0x1016a3, efl g471, 598⟩)
      (St.m ⟨N'.get, v470, v472, v476, v478, fb, v418, v474, v462, 0x1016be, efl g479, 606⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g479
  subst e_v478
  subst e_g477
  subst e_v476
  subst e_g475
  subst e_v474
  subst e_g473
  subst e_v472
  have r_v191 := hF.rd l_v191 12 rfl; subst r_v191
  have r_v164 := hF.rd l_v164 392 rfl; subst r_v164
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x128(%esp), %ebp ; adcl 0x18c(%esp), %ebp ; addl 0x1cc(%esp), %ebx ; adcl 0x1d0(%esp), %ebp ; addl 0x210(%esp), %ebx ; adcl 0x218(%esp), %ebp ; addl 0x250(%esp), %ebx ; adcl 0x254(%esp), %ebp -/
theorem mul_p77 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v470 v472 v476 v478 v418 v474 v462 g479 v192 v165 v137 v138 v109 v110 v82 v83 v480 g481 v482 g483 v484 g485 v486 g487 v488 g489 v490 g491 v492 g493 : UInt32)
        (l_v192 : l.lookup 296 = some v192)
    (l_v165 : l.lookup 396 = some v165)
    (l_v137 : l.lookup 460 = some v137)
    (l_v138 : l.lookup 464 = some v138)
    (l_v109 : l.lookup 528 = some v109)
    (l_v110 : l.lookup 536 = some v110)
    (l_v82 : l.lookup 592 = some v82)
    (l_v83 : l.lookup 596 = some v83)
    (e_v480 : v480 = (addF 4 v192 v165 (cfBit g479)).1)
    (e_g481 : g481 = (addF 4 v192 v165 (cfBit g479)).2)
    (e_v482 : v482 = (addF 4 v478 v137 0).1)
    (e_g483 : g483 = (addF 4 v478 v137 0).2)
    (e_v484 : v484 = (addF 4 v480 v138 (cfBit g483)).1)
    (e_g485 : g485 = (addF 4 v480 v138 (cfBit g483)).2)
    (e_v486 : v486 = (addF 4 v482 v109 0).1)
    (e_g487 : g487 = (addF 4 v482 v109 0).2)
    (e_v488 : v488 = (addF 4 v484 v110 (cfBit g487)).1)
    (e_g489 : g489 = (addF 4 v484 v110 (cfBit g487)).2)
    (e_v490 : v490 = (addF 4 v486 v82 0).1)
    (e_g491 : g491 = (addF 4 v486 v82 0).2)
    (e_v492 : v492 = (addF 4 v488 v83 (cfBit g491)).1)
    (e_g493 : g493 = (addF 4 v488 v83 (cfBit g491)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v470, v472, v476, v478, fb, v418, v474, v462, 0x1016be, efl g479, 606⟩)
      (St.m ⟨N'.get, v470, v472, v476, v490, fb, v492, v474, v462, 0x1016f6, efl g493, 614⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g493
  subst e_v492
  subst e_g491
  subst e_v490
  subst e_g489
  subst e_v488
  subst e_g487
  subst e_v486
  subst e_g485
  subst e_v484
  subst e_g483
  subst e_v482
  subst e_g481
  subst e_v480
  have r_v192 := hF.rd l_v192 296 rfl; subst r_v192
  have r_v165 := hF.rd l_v165 396 rfl; subst r_v165
  have r_v137 := hF.rd l_v137 460 rfl; subst r_v137
  have r_v138 := hF.rd l_v138 464 rfl; subst r_v138
  have r_v109 := hF.rd l_v109 528 rfl; subst r_v109
  have r_v110 := hF.rd l_v110 536 rfl; subst r_v110
  have r_v82 := hF.rd l_v82 592 rfl; subst r_v82
  have r_v83 := hF.rd l_v83 596 rfl; subst r_v83
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
