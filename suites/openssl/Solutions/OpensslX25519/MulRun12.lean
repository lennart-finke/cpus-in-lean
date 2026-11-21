import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 66–71

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

/-- movl %edi, %ecx ; movl %edi, 0x4(%esp) ; adcl 0x1a4(%esp), %edx ; movl %edx, 0x8(%esp) ; movl 0x14(%esp), %eax ; addl 0x224(%esp), %eax ; movl %eax, 0x14(%esp) ; movl 0x44(%esp), %eax -/
theorem mul_p66 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v341 v316 v374 v24 v38 x10 v376 g377 v98 v69 v42 v70 v378 g379 v380 g381 : UInt32)
        (l_v98 : l.lookup 420 = some v98)
    (l_v69 : l.lookup 20 = some v69)
    (l_v42 : l.lookup 548 = some v42)
    (l_v70 : l.lookup 68 = some v70)
    (e_v378 : v378 = (addF 4 v374 v98 (cfBit g377)).1)
    (e_g379 : g379 = (addF 4 v374 v98 (cfBit g377)).2)
    (e_v380 : v380 = (addF 4 v69 v42 0).1)
    (e_g381 : g381 = (addF 4 v69 v42 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v341, v316, v374, v24, fb, v38, x10, v376, 0x10153f, efl g377, 533⟩)
      (St.m ⟨N'.get, v70, v376, v378, v24, fb, v38, x10, v376, 0x101563, efl g381, 541⟩) ∧
      Frame N' fb 836 ((20, v380) :: (8, v378) :: (4, v376) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 4 v376 hS (by decide)) fb 836 8 v378 stF_FB (by decide)) fb 836 20 v380 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 4 rfl rfl).wrF 8 rfl rfl).wrF 20 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g381
  subst e_v380
  subst e_g379
  subst e_v378
  have r_v98 := hF.rd l_v98 420 rfl; subst r_v98
  have r_v69 := hF.rd l_v69 20 rfl; subst r_v69
  have r_v42 := hF.rd l_v42 548 rfl; subst r_v42
  have r_v70 := hF.rd l_v70 68 rfl; subst r_v70
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl 0x234(%esp), %eax ; movl %eax, 0x44(%esp) ; movl 0x1c(%esp), %eax ; addl 0x160(%esp), %eax ; movl 0x28(%esp), %edi ; adcl 0x168(%esp), %edi ; addl 0x194(%esp), %eax ; adcl 0x19c(%esp), %edi -/
theorem mul_p67 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v70 v376 v378 v24 v38 x10 g381 v43 v161 v134 v162 v135 v106 v107 v382 g383 v384 g385 v386 g387 v388 g389 v390 g391 : UInt32)
        (l_v43 : l.lookup 564 = some v43)
    (l_v161 : l.lookup 28 = some v161)
    (l_v134 : l.lookup 352 = some v134)
    (l_v162 : l.lookup 40 = some v162)
    (l_v135 : l.lookup 360 = some v135)
    (l_v106 : l.lookup 404 = some v106)
    (l_v107 : l.lookup 412 = some v107)
    (e_v382 : v382 = (addF 4 v70 v43 (cfBit g381)).1)
    (e_g383 : g383 = (addF 4 v70 v43 (cfBit g381)).2)
    (e_v384 : v384 = (addF 4 v161 v134 0).1)
    (e_g385 : g385 = (addF 4 v161 v134 0).2)
    (e_v386 : v386 = (addF 4 v162 v135 (cfBit g385)).1)
    (e_g387 : g387 = (addF 4 v162 v135 (cfBit g385)).2)
    (e_v388 : v388 = (addF 4 v384 v106 0).1)
    (e_g389 : g389 = (addF 4 v384 v106 0).2)
    (e_v390 : v390 = (addF 4 v386 v107 (cfBit g389)).1)
    (e_g391 : g391 = (addF 4 v386 v107 (cfBit g389)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v70, v376, v378, v24, fb, v38, x10, v376, 0x101563, efl g381, 541⟩)
      (St.m ⟨N'.get, v388, v376, v378, v24, fb, v38, x10, v390, 0x101592, efl g391, 549⟩) ∧
      Frame N' fb 836 ((68, v382) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 68 v382 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 68 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g391
  subst e_v390
  subst e_g389
  subst e_v388
  subst e_g387
  subst e_v386
  subst e_g385
  subst e_v384
  subst e_g383
  subst e_v382
  have r_v43 := hF.rd l_v43 564 rfl; subst r_v43
  have r_v161 := hF.rd l_v161 28 rfl; subst r_v161
  have r_v134 := hF.rd l_v134 352 rfl; subst r_v134
  have r_v162 := hF.rd l_v162 40 rfl; subst r_v162
  have r_v135 := hF.rd l_v135 360 rfl; subst r_v135
  have r_v106 := hF.rd l_v106 404 rfl; subst r_v106
  have r_v107 := hF.rd l_v107 412 rfl; subst r_v107
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0x1d8(%esp), %eax ; adcl 0x1e0(%esp), %edi ; addl 0x220(%esp), %eax ; adcl 0x22c(%esp), %edi ; addl 0x70(%esp), %eax ; adcl 0x74(%esp), %edi ; addl 0x88(%esp), %eax ; adcl 0x8c(%esp), %edi -/
theorem mul_p68 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v388 v376 v378 v24 v38 x10 v390 g391 v79 v80 v51 v52 v329 v330 v301 v302 v392 g393 v394 g395 v396 g397 v398 g399 v400 g401 v402 g403 v404 g405 v406 g407 : UInt32)
        (l_v79 : l.lookup 472 = some v79)
    (l_v80 : l.lookup 480 = some v80)
    (l_v51 : l.lookup 544 = some v51)
    (l_v52 : l.lookup 556 = some v52)
    (l_v329 : l.lookup 112 = some v329)
    (l_v330 : l.lookup 116 = some v330)
    (l_v301 : l.lookup 136 = some v301)
    (l_v302 : l.lookup 140 = some v302)
    (e_v392 : v392 = (addF 4 v388 v79 0).1)
    (e_g393 : g393 = (addF 4 v388 v79 0).2)
    (e_v394 : v394 = (addF 4 v390 v80 (cfBit g393)).1)
    (e_g395 : g395 = (addF 4 v390 v80 (cfBit g393)).2)
    (e_v396 : v396 = (addF 4 v392 v51 0).1)
    (e_g397 : g397 = (addF 4 v392 v51 0).2)
    (e_v398 : v398 = (addF 4 v394 v52 (cfBit g397)).1)
    (e_g399 : g399 = (addF 4 v394 v52 (cfBit g397)).2)
    (e_v400 : v400 = (addF 4 v396 v329 0).1)
    (e_g401 : g401 = (addF 4 v396 v329 0).2)
    (e_v402 : v402 = (addF 4 v398 v330 (cfBit g401)).1)
    (e_g403 : g403 = (addF 4 v398 v330 (cfBit g401)).2)
    (e_v404 : v404 = (addF 4 v400 v301 0).1)
    (e_g405 : g405 = (addF 4 v400 v301 0).2)
    (e_v406 : v406 = (addF 4 v402 v302 (cfBit g405)).1)
    (e_g407 : g407 = (addF 4 v402 v302 (cfBit g405)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v388, v376, v378, v24, fb, v38, x10, v390, 0x101592, efl g391, 549⟩)
      (St.m ⟨N'.get, v404, v376, v378, v24, fb, v38, x10, v406, 0x1015c4, efl g407, 557⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g407
  subst e_v406
  subst e_g405
  subst e_v404
  subst e_g403
  subst e_v402
  subst e_g401
  subst e_v400
  subst e_g399
  subst e_v398
  subst e_g397
  subst e_v396
  subst e_g395
  subst e_v394
  subst e_g393
  subst e_v392
  have r_v79 := hF.rd l_v79 472 rfl; subst r_v79
  have r_v80 := hF.rd l_v80 480 rfl; subst r_v80
  have r_v51 := hF.rd l_v51 544 rfl; subst r_v51
  have r_v52 := hF.rd l_v52 556 rfl; subst r_v52
  have r_v329 := hF.rd l_v329 112 rfl; subst r_v329
  have r_v330 := hF.rd l_v330 116 rfl; subst r_v330
  have r_v301 := hF.rd l_v301 136 rfl; subst r_v301
  have r_v302 := hF.rd l_v302 140 rfl; subst r_v302
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0xa8(%esp), %eax ; adcl 0xac(%esp), %edi ; addl 0xd0(%esp), %eax ; adcl 0xd4(%esp), %edi ; addl 0xf8(%esp), %eax ; movl %eax, 0x1c(%esp) ; adcl 0xfc(%esp), %edi ; movl %edi, %ebp -/
theorem mul_p69 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v404 v376 v378 v24 v38 x10 v406 g407 v274 v275 v246 v247 v219 v220 v408 g409 v410 g411 v412 g413 v414 g415 v416 g417 v418 g419 : UInt32)
        (l_v274 : l.lookup 168 = some v274)
    (l_v275 : l.lookup 172 = some v275)
    (l_v246 : l.lookup 208 = some v246)
    (l_v247 : l.lookup 212 = some v247)
    (l_v219 : l.lookup 248 = some v219)
    (l_v220 : l.lookup 252 = some v220)
    (e_v408 : v408 = (addF 4 v404 v274 0).1)
    (e_g409 : g409 = (addF 4 v404 v274 0).2)
    (e_v410 : v410 = (addF 4 v406 v275 (cfBit g409)).1)
    (e_g411 : g411 = (addF 4 v406 v275 (cfBit g409)).2)
    (e_v412 : v412 = (addF 4 v408 v246 0).1)
    (e_g413 : g413 = (addF 4 v408 v246 0).2)
    (e_v414 : v414 = (addF 4 v410 v247 (cfBit g413)).1)
    (e_g415 : g415 = (addF 4 v410 v247 (cfBit g413)).2)
    (e_v416 : v416 = (addF 4 v412 v219 0).1)
    (e_g417 : g417 = (addF 4 v412 v219 0).2)
    (e_v418 : v418 = (addF 4 v414 v220 (cfBit g417)).1)
    (e_g419 : g419 = (addF 4 v414 v220 (cfBit g417)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v404, v376, v378, v24, fb, v38, x10, v406, 0x1015c4, efl g407, 557⟩)
      (St.m ⟨N'.get, v416, v376, v378, v24, fb, v418, x10, v418, 0x1015f4, efl g419, 565⟩) ∧
      Frame N' fb 836 ((28, v416) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 28 v416 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 28 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g419
  subst e_v418
  subst e_g417
  subst e_v416
  subst e_g415
  subst e_v414
  subst e_g413
  subst e_v412
  subst e_g411
  subst e_v410
  subst e_g409
  subst e_v408
  have r_v274 := hF.rd l_v274 168 rfl; subst r_v274
  have r_v275 := hF.rd l_v275 172 rfl; subst r_v275
  have r_v246 := hF.rd l_v246 208 rfl; subst r_v246
  have r_v247 := hF.rd l_v247 212 rfl; subst r_v247
  have r_v219 := hF.rd l_v219 248 rfl; subst r_v219
  have r_v220 := hF.rd l_v220 252 rfl; subst r_v220
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edi, 0x28(%esp) ; addl $0x2000000, %ecx -/
theorem mul_p70 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v416 v376 v378 v24 v418 x10 g419 v420 g421 : UInt32)
        (e_v420 : v420 = (addF 4 v376 33554432 0).1)
    (e_g421 : g421 = (addF 4 v376 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v416, v376, v378, v24, fb, v418, x10, v418, 0x1015f4, efl g419, 565⟩)
      (St.m ⟨N'.get, v416, v420, v378, v24, fb, v418, x10, v418, 0x1015fe, efl g421, 567⟩) ∧
      Frame N' fb 836 ((40, v418) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF N fb 836 40 v418 hS (by decide)), run_of_runOk (k := 2) ?_, (hF.wrF 40 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g421
  subst e_v420
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %edx ; movl %edx, %ebx ; sarl $0x1a, %ebx ; movl %ecx, %esi ; shrdl $0x1a, %edx, %esi ; movl 0x14(%esp), %eax ; addl 0x80(%esp), %eax ; movl 0x44(%esp), %edi -/
theorem mul_p71 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v416 v420 v378 v24 v418 x10 g421 v380 v320 v382 v422 g423 v424 g425 v426 g427 v428 g429 : UInt32)
        (l_v380 : l.lookup 20 = some v380)
    (l_v320 : l.lookup 128 = some v320)
    (l_v382 : l.lookup 68 = some v382)
    (e_v422 : v422 = (addF 4 v378 0 (cfBit g421)).1)
    (e_g423 : g423 = (addF 4 v378 0 (cfBit g421)).2)
    (e_v424 : v424 = sarR v422 26)
    (e_g425 : g425 = sarF v422 26)
    (e_v426 : v426 = sdR false v420 v422 26)
    (e_g427 : g427 = sdF false v420 v422 26)
    (e_v428 : v428 = (addF 4 v380 v320 0).1)
    (e_g429 : g429 = (addF 4 v380 v320 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v416, v420, v378, v24, fb, v418, x10, v418, 0x1015fe, efl g421, 567⟩)
      (St.m ⟨N'.get, v428, v420, v422, v424, fb, v418, v426, v382, 0x10161b, efl g429, 575⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g429
  subst e_v428
  subst e_g427
  subst e_v426
  subst e_g425
  subst e_v424
  subst e_g423
  subst e_v422
  have r_v380 := hF.rd l_v380 20 rfl; subst r_v380
  have r_v320 := hF.rd l_v320 128 rfl; subst r_v320
  have r_v382 := hF.rd l_v382 68 rfl; subst r_v382
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
