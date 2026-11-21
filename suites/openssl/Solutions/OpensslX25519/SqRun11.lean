import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 60–65

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

/-- subl %eax, %edi ; movl %edi, 0x1c(%esp) ; movl 0x4(%esp), %ebp ; movl %ebp, %eax ; addl $0x2000000, %eax -/
theorem sq_p60 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v406 v386 v404 v376 v388 v338 g407 v374 v408 g409 v410 g411 : UInt32)
        (l_v374 : l.lookup 4 = some v374)
    (e_v408 : v408 = (subF 4 v338 v406 0).1)
    (e_g409 : g409 = (subF 4 v338 v406 0).2)
    (e_v410 : v410 = (addF 4 v374 33554432 0).1)
    (e_g411 : g411 = (addF 4 v374 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v406, v386, v404, v376, fb, v388, v404, v338, 0x102a9e, efl g407, 434⟩)
      (St.m ⟨N'.get, v410, v386, v404, v376, fb, v374, v404, v408, 0x102aaf, efl g411, 439⟩) ∧
      Frame N' fb 468 ((28, v408) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF N fb 468 28 v408 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF 28 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g411
  subst e_v410
  subst e_g409
  subst e_v408
  have r_v374 := hF.rd l_v374 4 rfl; subst r_v374
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %ebx ; movl %eax, %ecx ; shrdl $0x1a, %ebx, %ecx ; sarl $0x1a, %ebx ; movl 0x50(%esp), %esi ; addl 0x154(%esp), %esi ; movl 0x130(%esp), %edi ; adcl 0x158(%esp), %edi -/
theorem sq_p61 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v410 v386 v404 v376 v374 v408 g411 v109 v91 v110 v92 v412 g413 v414 g415 v416 g417 v418 g419 v420 g421 : UInt32)
        (l_v109 : l.lookup 80 = some v109)
    (l_v91 : l.lookup 340 = some v91)
    (l_v110 : l.lookup 304 = some v110)
    (l_v92 : l.lookup 344 = some v92)
    (e_v412 : v412 = (addF 4 v376 0 (cfBit g411)).1)
    (e_g413 : g413 = (addF 4 v376 0 (cfBit g411)).2)
    (e_v414 : v414 = sdR false v410 v412 26)
    (e_g415 : g415 = sdF false v410 v412 26)
    (e_v416 : v416 = sarR v412 26)
    (e_g417 : g417 = sarF v412 26)
    (e_v418 : v418 = (addF 4 v109 v91 0).1)
    (e_g419 : g419 = (addF 4 v109 v91 0).2)
    (e_v420 : v420 = (addF 4 v110 v92 (cfBit g419)).1)
    (e_g421 : g421 = (addF 4 v110 v92 (cfBit g419)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v410, v386, v404, v376, fb, v374, v404, v408, 0x102aaf, efl g411, 439⟩)
      (St.m ⟨N'.get, v410, v414, v404, v416, fb, v374, v418, v420, 0x102ad4, efl g421, 447⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g421
  subst e_v420
  subst e_g419
  subst e_v418
  subst e_g417
  subst e_v416
  subst e_g415
  subst e_v414
  subst e_g413
  subst e_v412
  have r_v109 := hF.rd l_v109 80 rfl; subst r_v109
  have r_v91 := hF.rd l_v91 340 rfl; subst r_v91
  have r_v110 := hF.rd l_v110 304 rfl; subst r_v110
  have r_v92 := hF.rd l_v92 344 rfl; subst r_v92
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x17c(%esp), %esi ; adcl 0x184(%esp), %edi ; addl 0x19c(%esp), %esi ; adcl 0x1a0(%esp), %edi ; addl 0x30(%esp), %esi ; adcl 0x20(%esp), %edi ; addl %ecx, %esi ; movl %esi, %ecx -/
theorem sq_p62 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v410 v414 v404 v416 v374 v418 v420 g421 v65 v66 v37 v38 v192 v193 v422 g423 v424 g425 v426 g427 v428 g429 v430 g431 v432 g433 v434 g435 : UInt32)
        (l_v65 : l.lookup 380 = some v65)
    (l_v66 : l.lookup 388 = some v66)
    (l_v37 : l.lookup 412 = some v37)
    (l_v38 : l.lookup 416 = some v38)
    (l_v192 : l.lookup 48 = some v192)
    (l_v193 : l.lookup 32 = some v193)
    (e_v422 : v422 = (addF 4 v418 v65 0).1)
    (e_g423 : g423 = (addF 4 v418 v65 0).2)
    (e_v424 : v424 = (addF 4 v420 v66 (cfBit g423)).1)
    (e_g425 : g425 = (addF 4 v420 v66 (cfBit g423)).2)
    (e_v426 : v426 = (addF 4 v422 v37 0).1)
    (e_g427 : g427 = (addF 4 v422 v37 0).2)
    (e_v428 : v428 = (addF 4 v424 v38 (cfBit g427)).1)
    (e_g429 : g429 = (addF 4 v424 v38 (cfBit g427)).2)
    (e_v430 : v430 = (addF 4 v426 v192 0).1)
    (e_g431 : g431 = (addF 4 v426 v192 0).2)
    (e_v432 : v432 = (addF 4 v428 v193 (cfBit g431)).1)
    (e_g433 : g433 = (addF 4 v428 v193 (cfBit g431)).2)
    (e_v434 : v434 = (addF 4 v430 v414 0).1)
    (e_g435 : g435 = (addF 4 v430 v414 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v410, v414, v404, v416, fb, v374, v418, v420, 0x102ad4, efl g421, 447⟩)
      (St.m ⟨N'.get, v410, v434, v404, v416, fb, v374, v434, v432, 0x102afc, efl g435, 455⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g435
  subst e_v434
  subst e_g433
  subst e_v432
  subst e_g431
  subst e_v430
  subst e_g429
  subst e_v428
  subst e_g427
  subst e_v426
  subst e_g425
  subst e_v424
  subst e_g423
  subst e_v422
  have r_v65 := hF.rd l_v65 380 rfl; subst r_v65
  have r_v66 := hF.rd l_v66 388 rfl; subst r_v66
  have r_v37 := hF.rd l_v37 412 rfl; subst r_v37
  have r_v38 := hF.rd l_v38 416 rfl; subst r_v38
  have r_v192 := hF.rd l_v192 48 rfl; subst r_v192
  have r_v193 := hF.rd l_v193 32 rfl; subst r_v193
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl %ebx, %edi ; andl $0xfc000000, %eax -/
theorem sq_p63 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v410 v434 v404 v416 v374 v432 g435 v436 g437 v438 g439 : UInt32)
        (e_v436 : v436 = (addF 4 v432 v416 (cfBit g435)).1)
    (e_g437 : g437 = (addF 4 v432 v416 (cfBit g435)).2)
    (e_v438 : v438 = (logicF 4 (UInt32.land v410 4227858432)).1)
    (e_g439 : g439 = (logicF 4 (UInt32.land v410 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v410, v434, v404, v416, fb, v374, v434, v432, 0x102afc, efl g435, 455⟩)
      (St.m ⟨N'.get, v438, v434, v404, v416, fb, v374, v434, v436, 0x102b03, efl g439, 457⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 2) ?_, hF, hP⟩
  subst e_g439
  subst e_v438
  subst e_g437
  subst e_v436
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, %ebp ; movl %ebp, 0x4(%esp) ; movl 0x8(%esp), %esi ; movl %esi, %eax ; addl $0x1000000, %eax -/
theorem sq_p64 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v438 v434 v404 v416 v374 v436 g439 v402 v440 g441 v442 g443 : UInt32)
        (l_v402 : l.lookup 8 = some v402)
    (e_v440 : v440 = (subF 4 v374 v438 0).1)
    (e_g441 : g441 = (subF 4 v374 v438 0).2)
    (e_v442 : v442 = (addF 4 v402 16777216 0).1)
    (e_g443 : g443 = (addF 4 v402 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v438, v434, v404, v416, fb, v374, v434, v436, 0x102b03, efl g439, 457⟩)
      (St.m ⟨N'.get, v442, v434, v404, v416, fb, v440, v402, v436, 0x102b14, efl g443, 462⟩) ∧
      Frame N' fb 468 ((4, v440) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF N fb 468 4 v440 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF 4 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g443
  subst e_v442
  subst e_g441
  subst e_v440
  have r_v402 := hF.rd l_v402 8 rfl; subst r_v402
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %edx ; movl %eax, %ebx ; shrdl $0x19, %edx, %ebx ; sarl $0x19, %edx ; addl 0x10(%esp), %ebx ; movl %ebx, 0x10(%esp) ; adcl 0x28(%esp), %edx ; andl $0xfe000000, %eax -/
theorem sq_p65 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v442 v434 v404 v416 v440 v402 v436 g443 v310 v312 v444 g445 v446 g447 v448 g449 v450 g451 v452 g453 v454 g455 : UInt32)
        (l_v310 : l.lookup 16 = some v310)
    (l_v312 : l.lookup 40 = some v312)
    (e_v444 : v444 = (addF 4 v404 0 (cfBit g443)).1)
    (e_g445 : g445 = (addF 4 v404 0 (cfBit g443)).2)
    (e_v446 : v446 = sdR false v442 v444 25)
    (e_g447 : g447 = sdF false v442 v444 25)
    (e_v448 : v448 = sarR v444 25)
    (e_g449 : g449 = sarF v444 25)
    (e_v450 : v450 = (addF 4 v446 v310 0).1)
    (e_g451 : g451 = (addF 4 v446 v310 0).2)
    (e_v452 : v452 = (addF 4 v448 v312 (cfBit g451)).1)
    (e_g453 : g453 = (addF 4 v448 v312 (cfBit g451)).2)
    (e_v454 : v454 = (logicF 4 (UInt32.land v442 4261412864)).1)
    (e_g455 : g455 = (logicF 4 (UInt32.land v442 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v442, v434, v404, v416, fb, v440, v402, v436, 0x102b14, efl g443, 462⟩)
      (St.m ⟨N'.get, v454, v434, v452, v450, fb, v440, v402, v436, 0x102b31, efl g455, 470⟩) ∧
      Frame N' fb 468 ((16, v450) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF N fb 468 16 v450 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 16 rfl rfl), (hP.wrF (by decide))⟩
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
  subst e_g445
  subst e_v444
  have r_v310 := hF.rd l_v310 16 rfl; subst r_v310
  have r_v312 := hF.rd l_v312 40 rfl; subst r_v312
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
