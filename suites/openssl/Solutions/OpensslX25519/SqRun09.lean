import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 48–53

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

/-- subl %edi, 0x10(%esp) ; sbbl %ecx, 0x28(%esp) ; movl (%esp), %esi ; movl %esi, %eax ; addl $0x1000000, %eax -/
theorem sq_p48 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v306 v282 v286 v272 v304 v284 v308 g309 v242 v244 v270 v310 g311 v312 g313 v314 g315 : UInt32)
        (l_v242 : l.lookup 16 = some v242)
    (l_v244 : l.lookup 40 = some v244)
    (l_v270 : l.lookup 0 = some v270)
    (e_v310 : v310 = (subF 4 v242 v308 0).1)
    (e_g311 : g311 = (subF 4 v242 v308 0).2)
    (e_v312 : v312 = (subF 4 v244 v282 (cfBit g311)).1)
    (e_g313 : g313 = (subF 4 v244 v282 (cfBit g311)).2)
    (e_v314 : v314 = (addF 4 v270 16777216 0).1)
    (e_g315 : g315 = (addF 4 v270 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v306, v282, v286, v272, fb, v304, v284, v308, 0x10295e, efl g309, 363⟩)
      (St.m ⟨N'.get, v314, v282, v286, v272, fb, v304, v270, v308, 0x102970, efl g315, 368⟩) ∧
      Frame N' fb 468 ((40, v312) :: (16, v310) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF N fb 468 16 v310 hS (by decide)) fb 468 40 v312 stF_FB (by decide)), run_of_runOk (k := 5) ?_, ((hF.wrF 16 rfl rfl).wrF 40 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g315
  subst e_v314
  subst e_g313
  subst e_v312
  subst e_g311
  subst e_v310
  have r_v242 := hF.rd l_v242 16 rfl; subst r_v242
  have r_v244 := hF.rd l_v244 40 rfl; subst r_v244
  have r_v270 := hF.rd0 l_v270; subst r_v270
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %ebx ; movl %eax, %ecx ; shrdl $0x19, %ebx, %ecx ; sarl $0x19, %ebx ; movl 0x1c(%esp), %edx ; addl 0x98(%esp), %edx ; movl 0x54(%esp), %ebp ; adcl 0xa0(%esp), %ebp -/
theorem sq_p49 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v314 v282 v286 v272 v304 v270 v308 g315 v218 v167 v220 v168 v316 g317 v318 g319 v320 g321 v322 g323 v324 g325 : UInt32)
        (l_v218 : l.lookup 28 = some v218)
    (l_v167 : l.lookup 152 = some v167)
    (l_v220 : l.lookup 84 = some v220)
    (l_v168 : l.lookup 160 = some v168)
    (e_v316 : v316 = (addF 4 v272 0 (cfBit g315)).1)
    (e_g317 : g317 = (addF 4 v272 0 (cfBit g315)).2)
    (e_v318 : v318 = sdR false v314 v316 25)
    (e_g319 : g319 = sdF false v314 v316 25)
    (e_v320 : v320 = sarR v316 25)
    (e_g321 : g321 = sarF v316 25)
    (e_v322 : v322 = (addF 4 v218 v167 0).1)
    (e_g323 : g323 = (addF 4 v218 v167 0).2)
    (e_v324 : v324 = (addF 4 v220 v168 (cfBit g323)).1)
    (e_g325 : g325 = (addF 4 v220 v168 (cfBit g323)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v314, v282, v286, v272, fb, v304, v270, v308, 0x102970, efl g315, 368⟩)
      (St.m ⟨N'.get, v314, v318, v322, v320, fb, v324, v270, v308, 0x102992, efl g325, 376⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g325
  subst e_v324
  subst e_g323
  subst e_v322
  subst e_g321
  subst e_v320
  subst e_g319
  subst e_v318
  subst e_g317
  subst e_v316
  have r_v218 := hF.rd l_v218 28 rfl; subst r_v218
  have r_v167 := hF.rd l_v167 152 rfl; subst r_v167
  have r_v220 := hF.rd l_v220 84 rfl; subst r_v220
  have r_v168 := hF.rd l_v168 160 rfl; subst r_v168
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl 0xb8(%esp), %edx ; adcl 0xc0(%esp), %ebp ; addl 0xc4(%esp), %edx ; adcl 0xc8(%esp), %ebp ; addl 0xe0(%esp), %edx ; adcl 0xe8(%esp), %ebp ; addl %ecx, %edx ; movl %edx, 0x1c(%esp) -/
theorem sq_p50 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v314 v318 v322 v320 v324 v270 v308 g325 v158 v159 v144 v145 v126 v127 v326 g327 v328 g329 v330 g331 v332 g333 v334 g335 v336 g337 v338 g339 : UInt32)
        (l_v158 : l.lookup 184 = some v158)
    (l_v159 : l.lookup 192 = some v159)
    (l_v144 : l.lookup 196 = some v144)
    (l_v145 : l.lookup 200 = some v145)
    (l_v126 : l.lookup 224 = some v126)
    (l_v127 : l.lookup 232 = some v127)
    (e_v326 : v326 = (addF 4 v322 v158 0).1)
    (e_g327 : g327 = (addF 4 v322 v158 0).2)
    (e_v328 : v328 = (addF 4 v324 v159 (cfBit g327)).1)
    (e_g329 : g329 = (addF 4 v324 v159 (cfBit g327)).2)
    (e_v330 : v330 = (addF 4 v326 v144 0).1)
    (e_g331 : g331 = (addF 4 v326 v144 0).2)
    (e_v332 : v332 = (addF 4 v328 v145 (cfBit g331)).1)
    (e_g333 : g333 = (addF 4 v328 v145 (cfBit g331)).2)
    (e_v334 : v334 = (addF 4 v330 v126 0).1)
    (e_g335 : g335 = (addF 4 v330 v126 0).2)
    (e_v336 : v336 = (addF 4 v332 v127 (cfBit g335)).1)
    (e_g337 : g337 = (addF 4 v332 v127 (cfBit g335)).2)
    (e_v338 : v338 = (addF 4 v334 v318 0).1)
    (e_g339 : g339 = (addF 4 v334 v318 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v314, v318, v322, v320, fb, v324, v270, v308, 0x102992, efl g325, 376⟩)
      (St.m ⟨N'.get, v314, v318, v338, v320, fb, v336, v270, v308, 0x1029c2, efl g339, 384⟩) ∧
      Frame N' fb 468 ((28, v338) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF N fb 468 28 v338 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF 28 rfl rfl), (hP.wrF (by decide))⟩
  subst e_g339
  subst e_v338
  subst e_g337
  subst e_v336
  subst e_g335
  subst e_v334
  subst e_g333
  subst e_v332
  subst e_g331
  subst e_v330
  subst e_g329
  subst e_v328
  subst e_g327
  subst e_v326
  have r_v158 := hF.rd l_v158 184 rfl; subst r_v158
  have r_v159 := hF.rd l_v159 192 rfl; subst r_v159
  have r_v144 := hF.rd l_v144 196 rfl; subst r_v144
  have r_v145 := hF.rd l_v145 200 rfl; subst r_v145
  have r_v126 := hF.rd l_v126 224 rfl; subst r_v126
  have r_v127 := hF.rd l_v127 232 rfl; subst r_v127
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl %ebx, %ebp ; andl $0xfe000000, %eax -/
theorem sq_p51 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v314 v318 v338 v320 v336 v270 v308 g339 v340 g341 v342 g343 : UInt32)
        (e_v340 : v340 = (addF 4 v336 v320 (cfBit g339)).1)
    (e_g341 : g341 = (addF 4 v336 v320 (cfBit g339)).2)
    (e_v342 : v342 = (logicF 4 (UInt32.land v314 4261412864)).1)
    (e_g343 : g343 = (logicF 4 (UInt32.land v314 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v314, v318, v338, v320, fb, v336, v270, v308, 0x1029c2, efl g339, 384⟩)
      (St.m ⟨N'.get, v342, v318, v338, v320, fb, v340, v270, v308, 0x1029c9, efl g343, 386⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 2) ?_, hF, hP⟩
  subst e_g343
  subst e_v342
  subst e_g341
  subst e_v340
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, %esi ; movl %esi, (%esp) ; movl 0x2c(%esp), %eax ; movl %eax, %ecx ; addl $0x1000000, %ecx -/
theorem sq_p52 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v342 v318 v338 v320 v340 v270 v308 g343 v304 v344 g345 v346 g347 : UInt32)
        (l_v304 : l.lookup 44 = some v304)
    (e_v344 : v344 = (subF 4 v270 v342 0).1)
    (e_g345 : g345 = (subF 4 v270 v342 0).2)
    (e_v346 : v346 = (addF 4 v304 16777216 0).1)
    (e_g347 : g347 = (addF 4 v304 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v342, v318, v338, v320, fb, v340, v270, v308, 0x1029c9, efl g343, 386⟩)
      (St.m ⟨N'.get, v304, v346, v338, v320, fb, v340, v344, v308, 0x1029da, efl g347, 391⟩) ∧
      Frame N' fb 468 ((0, v344) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF0 N fb 468 v344 hS (by decide)), run_of_runOk (k := 5) ?_, (hF.wrF0), (hP.wrF0 (by decide))⟩
  subst e_g347
  subst e_v346
  subst e_g345
  subst e_v344
  have r_v304 := hF.rd l_v304 44 rfl; subst r_v304
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x4c(%esp), %esi ; adcl $0x0, %esi ; movl %ecx, %edi ; shrdl $0x19, %esi, %edi ; sarl $0x19, %esi ; movl 0x4(%esp), %edx ; addl 0x128(%esp), %edx ; movl 0xfc(%esp), %ebx -/
theorem sq_p53 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v304 v346 v338 v320 v340 v344 v308 g347 v306 v106 v88 v107 v348 g349 v350 g351 v352 g353 v354 g355 : UInt32)
        (l_v306 : l.lookup 76 = some v306)
    (l_v106 : l.lookup 4 = some v106)
    (l_v88 : l.lookup 296 = some v88)
    (l_v107 : l.lookup 252 = some v107)
    (e_v348 : v348 = (addF 4 v306 0 (cfBit g347)).1)
    (e_g349 : g349 = (addF 4 v306 0 (cfBit g347)).2)
    (e_v350 : v350 = sdR false v346 v348 25)
    (e_g351 : g351 = sdF false v346 v348 25)
    (e_v352 : v352 = sarR v348 25)
    (e_g353 : g353 = sarF v348 25)
    (e_v354 : v354 = (addF 4 v106 v88 0).1)
    (e_g355 : g355 = (addF 4 v106 v88 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v304, v346, v338, v320, fb, v340, v344, v308, 0x1029da, efl g347, 391⟩)
      (St.m ⟨N'.get, v304, v346, v354, v107, fb, v340, v352, v350, 0x1029fc, efl g355, 399⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g355
  subst e_v354
  subst e_g353
  subst e_v352
  subst e_g351
  subst e_v350
  subst e_g349
  subst e_v348
  have r_v306 := hF.rd l_v306 76 rfl; subst r_v306
  have r_v106 := hF.rd l_v106 4 rfl; subst r_v106
  have r_v88 := hF.rd l_v88 296 rfl; subst r_v88
  have r_v107 := hF.rd l_v107 252 rfl; subst r_v107
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
