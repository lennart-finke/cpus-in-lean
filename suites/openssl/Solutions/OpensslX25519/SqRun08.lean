import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 42–47

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

/-- addl 0x134(%esp), %ebp ; adcl 0x138(%esp), %ebx ; addl 0x90(%esp), %ebp ; adcl 0x94(%esp), %ebx ; addl 0xb4(%esp), %ebp ; adcl 0xbc(%esp), %ebx ; addl 0xd0(%esp), %ebp ; adcl 0xd8(%esp), %ebx -/
theorem sq_p42 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v246 v252 v250 v156 v155 v216 v248 g253 v19 v20 v140 v141 v123 v124 v103 v104 v254 g255 v256 g257 v258 g259 v260 g261 v262 g263 v264 g265 v266 g267 v268 g269 : UInt32)
        (l_v19 : l.lookup 308 = some v19)
    (l_v20 : l.lookup 312 = some v20)
    (l_v140 : l.lookup 144 = some v140)
    (l_v141 : l.lookup 148 = some v141)
    (l_v123 : l.lookup 180 = some v123)
    (l_v124 : l.lookup 188 = some v124)
    (l_v103 : l.lookup 208 = some v103)
    (l_v104 : l.lookup 216 = some v104)
    (e_v254 : v254 = (addF 4 v155 v19 0).1)
    (e_g255 : g255 = (addF 4 v155 v19 0).2)
    (e_v256 : v256 = (addF 4 v156 v20 (cfBit g255)).1)
    (e_g257 : g257 = (addF 4 v156 v20 (cfBit g255)).2)
    (e_v258 : v258 = (addF 4 v254 v140 0).1)
    (e_g259 : g259 = (addF 4 v254 v140 0).2)
    (e_v260 : v260 = (addF 4 v256 v141 (cfBit g259)).1)
    (e_g261 : g261 = (addF 4 v256 v141 (cfBit g259)).2)
    (e_v262 : v262 = (addF 4 v258 v123 0).1)
    (e_g263 : g263 = (addF 4 v258 v123 0).2)
    (e_v264 : v264 = (addF 4 v260 v124 (cfBit g263)).1)
    (e_g265 : g265 = (addF 4 v260 v124 (cfBit g263)).2)
    (e_v266 : v266 = (addF 4 v262 v103 0).1)
    (e_g267 : g267 = (addF 4 v262 v103 0).2)
    (e_v268 : v268 = (addF 4 v264 v104 (cfBit g267)).1)
    (e_g269 : g269 = (addF 4 v264 v104 (cfBit g267)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v246, v252, v250, v156, fb, v155, v216, v248, 0x1028a8, efl g253, 325⟩)
      (St.m ⟨N'.get, v246, v252, v250, v268, fb, v266, v216, v248, 0x1028e0, efl g269, 333⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g269
  subst e_v268
  subst e_g267
  subst e_v266
  subst e_g265
  subst e_v264
  subst e_g263
  subst e_v262
  subst e_g261
  subst e_v260
  subst e_g259
  subst e_v258
  subst e_g257
  subst e_v256
  subst e_g255
  subst e_v254
  have r_v19 := hF.rd l_v19 308 rfl; subst r_v19
  have r_v20 := hF.rd l_v20 312 rfl; subst r_v20
  have r_v140 := hF.rd l_v140 144 rfl; subst r_v140
  have r_v141 := hF.rd l_v141 148 rfl; subst r_v141
  have r_v123 := hF.rd l_v123 180 rfl; subst r_v123
  have r_v124 := hF.rd l_v124 188 rfl; subst r_v124
  have r_v103 := hF.rd l_v103 208 rfl; subst r_v103
  have r_v104 := hF.rd l_v104 216 rfl; subst r_v104
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl %ecx, %ebp ; movl %ebp, (%esp) ; adcl %edx, %ebx ; andl $0xfc000000, %eax -/
theorem sq_p43 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v246 v252 v250 v268 v266 v216 v248 g269 v270 g271 v272 g273 v274 g275 : UInt32)
        (e_v270 : v270 = (addF 4 v266 v252 0).1)
    (e_g271 : g271 = (addF 4 v266 v252 0).2)
    (e_v272 : v272 = (addF 4 v268 v250 (cfBit g271)).1)
    (e_g273 : g273 = (addF 4 v268 v250 (cfBit g271)).2)
    (e_v274 : v274 = (logicF 4 (UInt32.land v246 4227858432)).1)
    (e_g275 : g275 = (logicF 4 (UInt32.land v246 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v246, v252, v250, v268, fb, v266, v216, v248, 0x1028e0, efl g269, 333⟩)
      (St.m ⟨N'.get, v274, v252, v250, v272, fb, v270, v216, v248, 0x1028ec, efl g275, 337⟩) ∧
      Frame N' fb 468 ((0, v270) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF0 N fb 468 v270 hS (by decide)), run_of_runOk (k := 4) ?_, (hF.wrF0), (hP.wrF0 (by decide))⟩
  subst e_g275
  subst e_v274
  subst e_g273
  subst e_v272
  subst e_g271
  subst e_v270
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %eax, 0xc(%esp) ; sbbl %edi, %esi ; movl %esi, 0x14(%esp) ; movl 0x10(%esp), %edi ; addl $0x2000000, %edi -/
theorem sq_p44 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v274 v252 v250 v272 v270 v216 v248 g275 v214 v242 v276 g277 v278 g279 v280 g281 : UInt32)
        (l_v214 : l.lookup 12 = some v214)
    (l_v242 : l.lookup 16 = some v242)
    (e_v276 : v276 = (subF 4 v214 v274 0).1)
    (e_g277 : g277 = (subF 4 v214 v274 0).2)
    (e_v278 : v278 = (subF 4 v216 v248 (cfBit g277)).1)
    (e_g279 : g279 = (subF 4 v216 v248 (cfBit g277)).2)
    (e_v280 : v280 = (addF 4 v242 33554432 0).1)
    (e_g281 : g281 = (addF 4 v242 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v274, v252, v250, v272, fb, v270, v216, v248, 0x1028ec, efl g275, 337⟩)
      (St.m ⟨N'.get, v274, v252, v250, v272, fb, v270, v278, v280, 0x102900, efl g281, 342⟩) ∧
      Frame N' fb 468 ((20, v278) :: (12, v276) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF N fb 468 12 v276 hS (by decide)) fb 468 20 v278 stF_FB (by decide)), run_of_runOk (k := 5) ?_, ((hF.wrF 12 rfl rfl).wrF 20 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g281
  subst e_v280
  subst e_g279
  subst e_v278
  subst e_g277
  subst e_v276
  have r_v214 := hF.rd l_v214 12 rfl; subst r_v214
  have r_v242 := hF.rd l_v242 16 rfl; subst r_v242
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x28(%esp), %ecx ; adcl $0x0, %ecx ; movl %ecx, %esi ; sarl $0x1a, %esi ; movl %edi, %edx ; shrdl $0x1a, %ecx, %edx ; movl 0x2c(%esp), %ebp ; addl 0x118(%esp), %ebp -/
theorem sq_p45 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v274 v252 v250 v272 v270 v278 v280 g281 v244 v85 v58 v282 g283 v284 g285 v286 g287 v288 g289 : UInt32)
        (l_v244 : l.lookup 40 = some v244)
    (l_v85 : l.lookup 44 = some v85)
    (l_v58 : l.lookup 280 = some v58)
    (e_v282 : v282 = (addF 4 v244 0 (cfBit g281)).1)
    (e_g283 : g283 = (addF 4 v244 0 (cfBit g281)).2)
    (e_v284 : v284 = sarR v282 26)
    (e_g285 : g285 = sarF v282 26)
    (e_v286 : v286 = sdR false v280 v282 26)
    (e_g287 : g287 = sdF false v280 v282 26)
    (e_v288 : v288 = (addF 4 v85 v58 0).1)
    (e_g289 : g289 = (addF 4 v85 v58 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v274, v252, v250, v272, fb, v270, v278, v280, 0x102900, efl g281, 342⟩)
      (St.m ⟨N'.get, v274, v282, v286, v272, fb, v288, v284, v280, 0x10291d, efl g289, 350⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g289
  subst e_v288
  subst e_g287
  subst e_v286
  subst e_g285
  subst e_v284
  subst e_g283
  subst e_v282
  have r_v244 := hF.rd l_v244 40 rfl; subst r_v244
  have r_v85 := hF.rd l_v85 44 rfl; subst r_v85
  have r_v58 := hF.rd l_v58 280 rfl; subst r_v58
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x4c(%esp), %eax ; adcl 0x124(%esp), %eax ; addl 0x144(%esp), %ebp ; adcl 0x148(%esp), %eax ; addl 0x78(%esp), %ebp ; adcl 0x7c(%esp), %eax ; addl 0x80(%esp), %ebp ; adcl 0x84(%esp), %eax -/
theorem sq_p46 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v274 v282 v286 v272 v288 v284 v280 g289 v86 v59 v31 v32 v183 v184 v177 v178 v290 g291 v292 g293 v294 g295 v296 g297 v298 g299 v300 g301 v302 g303 : UInt32)
        (l_v86 : l.lookup 76 = some v86)
    (l_v59 : l.lookup 292 = some v59)
    (l_v31 : l.lookup 324 = some v31)
    (l_v32 : l.lookup 328 = some v32)
    (l_v183 : l.lookup 120 = some v183)
    (l_v184 : l.lookup 124 = some v184)
    (l_v177 : l.lookup 128 = some v177)
    (l_v178 : l.lookup 132 = some v178)
    (e_v290 : v290 = (addF 4 v86 v59 (cfBit g289)).1)
    (e_g291 : g291 = (addF 4 v86 v59 (cfBit g289)).2)
    (e_v292 : v292 = (addF 4 v288 v31 0).1)
    (e_g293 : g293 = (addF 4 v288 v31 0).2)
    (e_v294 : v294 = (addF 4 v290 v32 (cfBit g293)).1)
    (e_g295 : g295 = (addF 4 v290 v32 (cfBit g293)).2)
    (e_v296 : v296 = (addF 4 v292 v183 0).1)
    (e_g297 : g297 = (addF 4 v292 v183 0).2)
    (e_v298 : v298 = (addF 4 v294 v184 (cfBit g297)).1)
    (e_g299 : g299 = (addF 4 v294 v184 (cfBit g297)).2)
    (e_v300 : v300 = (addF 4 v296 v177 0).1)
    (e_g301 : g301 = (addF 4 v296 v177 0).2)
    (e_v302 : v302 = (addF 4 v298 v178 (cfBit g301)).1)
    (e_g303 : g303 = (addF 4 v298 v178 (cfBit g301)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v274, v282, v286, v272, fb, v288, v284, v280, 0x10291d, efl g289, 350⟩)
      (St.m ⟨N'.get, v302, v282, v286, v272, fb, v300, v284, v280, 0x10294c, efl g303, 358⟩) ∧
      Frame N' fb 468 (l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨N, run_of_runOk (k := 8) ?_, hF, hP⟩
  subst e_g303
  subst e_v302
  subst e_g301
  subst e_v300
  subst e_g299
  subst e_v298
  subst e_g297
  subst e_v296
  subst e_g295
  subst e_v294
  subst e_g293
  subst e_v292
  subst e_g291
  subst e_v290
  have r_v86 := hF.rd l_v86 76 rfl; subst r_v86
  have r_v59 := hF.rd l_v59 292 rfl; subst r_v59
  have r_v31 := hF.rd l_v31 324 rfl; subst r_v31
  have r_v32 := hF.rd l_v32 328 rfl; subst r_v32
  have r_v183 := hF.rd l_v183 120 rfl; subst r_v183
  have r_v184 := hF.rd l_v184 124 rfl; subst r_v184
  have r_v177 := hF.rd l_v177 128 rfl; subst r_v177
  have r_v178 := hF.rd l_v178 132 rfl; subst r_v178
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- addl %edx, %ebp ; movl %ebp, 0x2c(%esp) ; adcl %esi, %eax ; movl %eax, 0x4c(%esp) ; andl $0xfc000000, %edi -/
theorem sq_p47 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v302 v282 v286 v272 v300 v284 v280 g303 v304 g305 v306 g307 v308 g309 : UInt32)
        (e_v304 : v304 = (addF 4 v300 v286 0).1)
    (e_g305 : g305 = (addF 4 v300 v286 0).2)
    (e_v306 : v306 = (addF 4 v302 v284 (cfBit g305)).1)
    (e_g307 : g307 = (addF 4 v302 v284 (cfBit g305)).2)
    (e_v308 : v308 = (logicF 4 (UInt32.land v280 4227858432)).1)
    (e_g309 : g309 = (logicF 4 (UInt32.land v280 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v302, v282, v286, v272, fb, v300, v284, v280, 0x10294c, efl g303, 358⟩)
      (St.m ⟨N'.get, v306, v282, v286, v272, fb, v304, v284, v308, 0x10295e, efl g309, 363⟩) ∧
      Frame N' fb 468 ((76, v306) :: (44, v304) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF N fb 468 44 v304 hS (by decide)) fb 468 76 v306 stF_FB (by decide)), run_of_runOk (k := 5) ?_, ((hF.wrF 44 rfl rfl).wrF 76 rfl rfl), ((hP.wrF (by decide)).wrF (by decide))⟩
  subst e_g309
  subst e_v308
  subst e_g307
  subst e_v306
  subst e_g305
  subst e_v304
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
