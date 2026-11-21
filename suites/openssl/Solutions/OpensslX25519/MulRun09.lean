import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 48–53

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

/-- movl 0x8(%esp), %eax ; imull %esi ; movl %edx, 0x1f8(%esp) ; movl %eax, 0x1f0(%esp) ; movl 0x4(%esp), %eax ; imull %ebx ; movl %edx, 0x5c(%esp) ; movl %eax, 0x244(%esp) -/
theorem mul_p48 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v252 v28 v253 x8 v36 v255 v30 g254 x12 x13 v256 v257 g258 v259 v260 g261 : UInt32)
        (l_x12 : l.lookup 8 = some x12)
    (l_x13 : l.lookup 4 = some x13)
    (e_v256 : v256 = UInt64.toUInt32 (imulCore 4 x12 v255).1)
    (e_v257 : v257 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 v255).1 32))
    (e_g258 : g258 = mixF g254 (ovfBits (imulCore 4 x12 v255).2) 2049)
    (e_v259 : v259 = UInt64.toUInt32 (imulCore 4 x13 x8).1)
    (e_v260 : v260 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x8).1 32))
    (e_g261 : g261 = mixF g258 (ovfBits (imulCore 4 x13 x8).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v252, v28, v253, x8, fb, v36, v255, v30, 0x1012ac, efl g254, 389⟩)
      (St.m ⟨N'.get, v259, v28, v260, x8, fb, v36, v255, v30, 0x1012d1, efl g261, 397⟩) ∧
      Frame N' fb 836 ((580, v259) :: (92, v260) :: (496, v256) :: (504, v257) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 504 v257 hS (by decide)) fb 836 496 v256 stF_FB (by decide)) fb 836 92 v260 stF_FB (by decide)) fb 836 580 v259 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 504 rfl rfl).wrF 496 rfl rfl).wrF 92 rfl rfl).wrF 580 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g261
  subst e_v260
  subst e_v259
  subst e_g258
  subst e_v257
  subst e_v256
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x48(%esp), %edi ; movl %edi, %eax ; imull %esi ; movl %edx, 0x94(%esp) ; movl %eax, 0x90(%esp) ; movl %ecx, %eax ; imull %ebx ; movl %edx, 0xcc(%esp) -/
theorem mul_p49 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v259 v28 v260 x8 v36 v255 v30 g261 v26 v262 v263 g264 v265 v266 g267 : UInt32)
        (l_v26 : l.lookup 72 = some v26)
    (e_v262 : v262 = UInt64.toUInt32 (imulCore 4 v26 v255).1)
    (e_v263 : v263 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v26 v255).1 32))
    (e_g264 : g264 = mixF g261 (ovfBits (imulCore 4 v26 v255).2) 2049)
    (e_v265 : v265 = UInt64.toUInt32 (imulCore 4 v28 x8).1)
    (e_v266 : v266 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v28 x8).1 32))
    (e_g267 : g267 = mixF g264 (ovfBits (imulCore 4 v28 x8).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v259, v28, v260, x8, fb, v36, v255, v30, 0x1012d1, efl g261, 397⟩)
      (St.m ⟨N'.get, v265, v28, v266, x8, fb, v36, v255, v26, 0x1012f2, efl g267, 405⟩) ∧
      Frame N' fb 836 ((204, v266) :: (144, v262) :: (148, v263) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 148 v263 hS (by decide)) fb 836 144 v262 stF_FB (by decide)) fb 836 204 v266 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 148 rfl rfl).wrF 144 rfl rfl).wrF 204 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g267
  subst e_v266
  subst e_v265
  subst e_g264
  subst e_v263
  subst e_v262
  have r_v26 := hF.rd l_v26 72 rfl; subst r_v26
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0xc8(%esp) ; movl 0x3c(%esp), %eax ; imull %esi ; movl %edx, 0x11c(%esp) ; movl %eax, 0x114(%esp) ; movl 0x38(%esp), %eax ; imull %ebx ; movl %edx, 0x164(%esp) -/
theorem mul_p50 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v265 v28 v266 x8 v36 v255 v26 g267 v30 v32 v268 v269 g270 v271 v272 g273 : UInt32)
        (l_v30 : l.lookup 60 = some v30)
    (l_v32 : l.lookup 56 = some v32)
    (e_v268 : v268 = UInt64.toUInt32 (imulCore 4 v30 v255).1)
    (e_v269 : v269 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v30 v255).1 32))
    (e_g270 : g270 = mixF g267 (ovfBits (imulCore 4 v30 v255).2) 2049)
    (e_v271 : v271 = UInt64.toUInt32 (imulCore 4 v32 x8).1)
    (e_v272 : v272 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v32 x8).1 32))
    (e_g273 : g273 = mixF g270 (ovfBits (imulCore 4 v32 x8).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v265, v28, v266, x8, fb, v36, v255, v26, 0x1012f2, efl g267, 405⟩)
      (St.m ⟨N'.get, v271, v28, v272, x8, fb, v36, v255, v26, 0x10131a, efl g273, 413⟩) ∧
      Frame N' fb 836 ((356, v272) :: (276, v268) :: (284, v269) :: (200, v265) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 200 v265 hS (by decide)) fb 836 284 v269 stF_FB (by decide)) fb 836 276 v268 stF_FB (by decide)) fb 836 356 v272 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 200 rfl rfl).wrF 284 rfl rfl).wrF 276 rfl rfl).wrF 356 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g273
  subst e_v272
  subst e_v271
  subst e_g270
  subst e_v269
  subst e_v268
  have r_v30 := hF.rd l_v30 60 rfl; subst r_v30
  have r_v32 := hF.rd l_v32 56 rfl; subst r_v32
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x15c(%esp) ; movl 0x30(%esp), %ebp ; movl %ebp, %eax ; imull %esi ; movl %edx, 0xac(%esp) ; movl %eax, 0xa8(%esp) ; movl 0x24(%esp), %eax ; imull %ebx -/
theorem mul_p51 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v271 v28 v272 x8 v36 v255 v26 g273 v34 v274 v275 g276 v277 v278 g279 : UInt32)
        (l_v34 : l.lookup 48 = some v34)
    (l_v36 : l.lookup 36 = some v36)
    (e_v274 : v274 = UInt64.toUInt32 (imulCore 4 v34 v255).1)
    (e_v275 : v275 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v34 v255).1 32))
    (e_g276 : g276 = mixF g273 (ovfBits (imulCore 4 v34 v255).2) 2049)
    (e_v277 : v277 = UInt64.toUInt32 (imulCore 4 v36 x8).1)
    (e_v278 : v278 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v36 x8).1 32))
    (e_g279 : g279 = mixF g276 (ovfBits (imulCore 4 v36 x8).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v271, v28, v272, x8, fb, v36, v255, v26, 0x10131a, efl g273, 413⟩)
      (St.m ⟨N'.get, v277, v28, v278, x8, fb, v34, v255, v26, 0x10133d, efl g279, 421⟩) ∧
      Frame N' fb 836 ((168, v274) :: (172, v275) :: (348, v271) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 348 v271 hS (by decide)) fb 836 172 v275 stF_FB (by decide)) fb 836 168 v274 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 348 rfl rfl).wrF 172 rfl rfl).wrF 168 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g279
  subst e_v278
  subst e_v277
  subst e_g276
  subst e_v275
  subst e_v274
  have r_v34 := hF.rd l_v34 48 rfl; subst r_v34
  have r_v36 := hF.rd l_v36 36 rfl; subst r_v36
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0xe8(%esp) ; movl %eax, 0xe0(%esp) ; movl 0x10(%esp), %eax ; imull %esi ; movl %edx, 0x138(%esp) ; movl %eax, 0x130(%esp) ; movl 0x2c(%esp), %esi ; movl %esi, %eax -/
theorem mul_p52 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v277 v28 v278 x8 v34 v255 v26 g279 v38 x11 v280 v281 g282 : UInt32)
        (l_v38 : l.lookup 16 = some v38)
    (l_x11 : l.lookup 44 = some x11)
    (e_v280 : v280 = UInt64.toUInt32 (imulCore 4 v38 v255).1)
    (e_v281 : v281 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v38 v255).1 32))
    (e_g282 : g282 = mixF g279 (ovfBits (imulCore 4 v38 v255).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v277, v28, v278, x8, fb, v34, v255, v26, 0x10133d, efl g279, 421⟩)
      (St.m ⟨N'.get, x11, v28, v281, x8, fb, v34, x11, v26, 0x101365, efl g282, 429⟩) ∧
      Frame N' fb 836 ((304, v280) :: (312, v281) :: (224, v277) :: (232, v278) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 232 v278 hS (by decide)) fb 836 224 v277 stF_FB (by decide)) fb 836 312 v281 stF_FB (by decide)) fb 836 304 v280 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 232 rfl rfl).wrF 224 rfl rfl).wrF 312 rfl rfl).wrF 304 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g282
  subst e_v281
  subst e_v280
  have r_v38 := hF.rd l_v38 16 rfl; subst r_v38
  have r_x11 := hF.rd l_x11 44 rfl; subst r_x11
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl 0x50(%esp), %ecx ; imull %ecx ; movl %edx, 0x1b8(%esp) ; movl %eax, 0x1b0(%esp) ; movl 0x8(%esp), %eax ; imull %ecx ; movl %edx, 0x58(%esp) ; movl %eax, 0x200(%esp) -/
theorem mul_p53 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x11 v28 v281 x8 v34 v26 g282 x9 x12 v283 v284 g285 v286 v287 g288 : UInt32)
        (l_x9 : l.lookup 80 = some x9)
    (l_x12 : l.lookup 8 = some x12)
    (e_v283 : v283 = UInt64.toUInt32 (imulCore 4 x11 x9).1)
    (e_v284 : v284 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x9).1 32))
    (e_g285 : g285 = mixF g282 (ovfBits (imulCore 4 x11 x9).2) 2049)
    (e_v286 : v286 = UInt64.toUInt32 (imulCore 4 x12 x9).1)
    (e_v287 : v287 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 x9).1 32))
    (e_g288 : g288 = mixF g285 (ovfBits (imulCore 4 x12 x9).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x11, v28, v281, x8, fb, v34, x11, v26, 0x101365, efl g282, 429⟩)
      (St.m ⟨N'.get, v286, x9, v287, x8, fb, v34, x11, v26, 0x10138a, efl g288, 437⟩) ∧
      Frame N' fb 836 ((512, v286) :: (88, v287) :: (432, v283) :: (440, v284) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 440 v284 hS (by decide)) fb 836 432 v283 stF_FB (by decide)) fb 836 88 v287 stF_FB (by decide)) fb 836 512 v286 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 440 rfl rfl).wrF 432 rfl rfl).wrF 88 rfl rfl).wrF 512 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g288
  subst e_v287
  subst e_v286
  subst e_g285
  subst e_v284
  subst e_v283
  have r_x9 := hF.rd l_x9 80 rfl; subst r_x9
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
