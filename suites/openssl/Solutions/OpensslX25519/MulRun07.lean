import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 36–41

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

/-- movl %esi, %eax ; imull %ecx ; movl %edx, 0x228(%esp) ; movl %eax, 0x21c(%esp) ; movl %ebx, %eax ; movl 0x60(%esp), %esi ; imull %esi ; movl %eax, 0xc(%esp) -/
theorem mul_p36 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v185 x5 v186 x11 v32 v38 v34 g187 x6 v188 v189 g190 v191 v192 g193 : UInt32)
        (l_x6 : l.lookup 96 = some x6)
    (e_v188 : v188 = UInt64.toUInt32 (imulCore 4 v38 x5).1)
    (e_v189 : v189 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v38 x5).1 32))
    (e_g190 : g190 = mixF g187 (ovfBits (imulCore 4 v38 x5).2) 2049)
    (e_v191 : v191 = UInt64.toUInt32 (imulCore 4 x11 x6).1)
    (e_v192 : v192 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x6).1 32))
    (e_g193 : g193 = mixF g190 (ovfBits (imulCore 4 x11 x6).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v185, x5, v186, x11, fb, v32, v38, v34, 0x1010fb, efl g187, 293⟩)
      (St.m ⟨N'.get, v191, x5, v192, x11, fb, v32, x6, v34, 0x101119, efl g193, 301⟩) ∧
      Frame N' fb 836 ((12, v191) :: (540, v188) :: (552, v189) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 552 v189 hS (by decide)) fb 836 540 v188 stF_FB (by decide)) fb 836 12 v191 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 552 rfl rfl).wrF 540 rfl rfl).wrF 12 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g193
  subst e_v192
  subst e_v191
  subst e_g190
  subst e_v189
  subst e_v188
  have r_x6 := hF.rd l_x6 96 rfl; subst r_x6
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x128(%esp) ; leal (%esi,%esi,1), %ecx ; movl 0x8(%esp), %eax ; imull %ecx ; movl %edx, 0x1c0(%esp) ; movl %eax, 0x1bc(%esp) ; movl 0x4(%esp), %eax ; imull %esi -/
theorem mul_p37 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v191 x5 v192 x11 v32 x6 v34 g193 x12 x13 v194 v195 v196 g197 v198 v199 g200 : UInt32)
        (l_x12 : l.lookup 8 = some x12)
    (l_x13 : l.lookup 4 = some x13)
    (e_v194 : v194 = UInt32.add x6 x6)
    (e_v195 : v195 = UInt64.toUInt32 (imulCore 4 x12 v194).1)
    (e_v196 : v196 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 v194).1 32))
    (e_g197 : g197 = mixF g193 (ovfBits (imulCore 4 x12 v194).2) 2049)
    (e_v198 : v198 = UInt64.toUInt32 (imulCore 4 x13 x6).1)
    (e_v199 : v199 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x6).1 32))
    (e_g200 : g200 = mixF g197 (ovfBits (imulCore 4 x13 x6).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v191, x5, v192, x11, fb, v32, x6, v34, 0x101119, efl g193, 301⟩)
      (St.m ⟨N'.get, v198, v194, v199, x11, fb, v32, x6, v34, 0x10113d, efl g200, 309⟩) ∧
      Frame N' fb 836 ((444, v195) :: (448, v196) :: (296, v192) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 296 v192 hS (by decide)) fb 836 448 v196 stF_FB (by decide)) fb 836 444 v195 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 296 rfl rfl).wrF 448 rfl rfl).wrF 444 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g200
  subst e_v199
  subst e_v198
  subst e_g197
  subst e_v196
  subst e_v195
  subst e_v194
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x238(%esp) ; movl %eax, 0x230(%esp) ; movl 0x18(%esp), %eax ; imull %ecx ; movl %edx, 0x268(%esp) ; movl %eax, 0x264(%esp) ; movl (%esp), %eax ; imull %esi -/
theorem mul_p38 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v198 v194 v199 x11 v32 x6 v34 g200 x14 x15 v201 v202 g203 v204 v205 g206 : UInt32)
        (l_x14 : l.lookup 24 = some x14)
    (l_x15 : l.lookup 0 = some x15)
    (e_v201 : v201 = UInt64.toUInt32 (imulCore 4 x14 v194).1)
    (e_v202 : v202 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x14 v194).1 32))
    (e_g203 : g203 = mixF g200 (ovfBits (imulCore 4 x14 v194).2) 2049)
    (e_v204 : v204 = UInt64.toUInt32 (imulCore 4 x15 x6).1)
    (e_v205 : v205 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x15 x6).1 32))
    (e_g206 : g206 = mixF g203 (ovfBits (imulCore 4 x15 x6).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v198, v194, v199, x11, fb, v32, x6, v34, 0x10113d, efl g200, 309⟩)
      (St.m ⟨N'.get, v204, v194, v205, x11, fb, v32, x6, v34, 0x101164, efl g206, 317⟩) ∧
      Frame N' fb 836 ((612, v201) :: (616, v202) :: (560, v198) :: (568, v199) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 568 v199 hS (by decide)) fb 836 560 v198 stF_FB (by decide)) fb 836 616 v202 stF_FB (by decide)) fb 836 612 v201 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 568 rfl rfl).wrF 560 rfl rfl).wrF 616 rfl rfl).wrF 612 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g206
  subst e_v205
  subst e_v204
  subst e_g203
  subst e_v202
  subst e_v201
  have r_x14 := hF.rd l_x14 24 rfl; subst r_x14
  have r_x15 := hF.rd0 l_x15; subst r_x15
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0x64(%esp) ; movl %eax, 0x29c(%esp) ; movl 0x3c(%esp), %edi ; movl %edi, %eax ; imull %ecx ; movl %edx, 0xdc(%esp) ; movl %eax, 0xd8(%esp) ; movl %ebp, %eax -/
theorem mul_p39 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v204 v194 v205 x11 v32 x6 v34 g206 v30 v207 v208 g209 : UInt32)
        (l_v30 : l.lookup 60 = some v30)
    (e_v207 : v207 = UInt64.toUInt32 (imulCore 4 v30 v194).1)
    (e_v208 : v208 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v30 v194).1 32))
    (e_g209 : g209 = mixF g206 (ovfBits (imulCore 4 v30 v194).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v204, v194, v205, x11, fb, v32, x6, v34, 0x101164, efl g206, 317⟩)
      (St.m ⟨N'.get, v32, v194, v208, x11, fb, v32, x6, v30, 0x101187, efl g209, 325⟩) ∧
      Frame N' fb 836 ((216, v207) :: (220, v208) :: (668, v204) :: (100, v205) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 100 v205 hS (by decide)) fb 836 668 v204 stF_FB (by decide)) fb 836 220 v208 stF_FB (by decide)) fb 836 216 v207 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 100 rfl rfl).wrF 668 rfl rfl).wrF 220 rfl rfl).wrF 216 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g209
  subst e_v208
  subst e_v207
  have r_v30 := hF.rd l_v30 60 rfl; subst r_v30
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %esi ; movl %edx, 0x120(%esp) ; movl %eax, 0x124(%esp) ; movl 0x30(%esp), %eax ; imull %ecx ; movl %edx, 0x178(%esp) ; movl %eax, 0x174(%esp) ; movl 0x24(%esp), %ebp -/
theorem mul_p40 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v32 v194 v208 x11 x6 v30 g209 v34 v36 v210 v211 g212 v213 v214 g215 : UInt32)
        (l_v34 : l.lookup 48 = some v34)
    (l_v36 : l.lookup 36 = some v36)
    (e_v210 : v210 = UInt64.toUInt32 (imulCore 4 v32 x6).1)
    (e_v211 : v211 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v32 x6).1 32))
    (e_g212 : g212 = mixF g209 (ovfBits (imulCore 4 v32 x6).2) 2049)
    (e_v213 : v213 = UInt64.toUInt32 (imulCore 4 v34 v194).1)
    (e_v214 : v214 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v34 v194).1 32))
    (e_g215 : g215 = mixF g212 (ovfBits (imulCore 4 v34 v194).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v32, v194, v208, x11, fb, v32, x6, v30, 0x101187, efl g209, 325⟩)
      (St.m ⟨N'.get, v213, v194, v214, x11, fb, v36, x6, v30, 0x1011af, efl g215, 333⟩) ∧
      Frame N' fb 836 ((372, v213) :: (376, v214) :: (292, v210) :: (288, v211) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 288 v211 hS (by decide)) fb 836 292 v210 stF_FB (by decide)) fb 836 376 v214 stF_FB (by decide)) fb 836 372 v213 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 288 rfl rfl).wrF 292 rfl rfl).wrF 376 rfl rfl).wrF 372 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g215
  subst e_v214
  subst e_v213
  subst e_g212
  subst e_v211
  subst e_v210
  have r_v34 := hF.rd l_v34 48 rfl; subst r_v34
  have r_v36 := hF.rd l_v36 36 rfl; subst r_v36
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebp, %eax ; imull %esi ; movl %edx, 0x1dc(%esp) ; movl %eax, 0x1d4(%esp) ; movl 0x10(%esp), %eax ; imull %ecx ; movl %edx, 0xfc(%esp) ; movl %eax, 0xf8(%esp) -/
theorem mul_p41 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v213 v194 v214 x11 v36 x6 v30 g215 v38 v216 v217 g218 v219 v220 g221 : UInt32)
        (l_v38 : l.lookup 16 = some v38)
    (e_v216 : v216 = UInt64.toUInt32 (imulCore 4 v36 x6).1)
    (e_v217 : v217 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v36 x6).1 32))
    (e_g218 : g218 = mixF g215 (ovfBits (imulCore 4 v36 x6).2) 2049)
    (e_v219 : v219 = UInt64.toUInt32 (imulCore 4 v38 v194).1)
    (e_v220 : v220 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v38 v194).1 32))
    (e_g221 : g221 = mixF g218 (ovfBits (imulCore 4 v38 v194).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v213, v194, v214, x11, fb, v36, x6, v30, 0x1011af, efl g215, 333⟩)
      (St.m ⟨N'.get, v219, v194, v220, x11, fb, v36, x6, v30, 0x1011d5, efl g221, 341⟩) ∧
      Frame N' fb 836 ((248, v219) :: (252, v220) :: (468, v216) :: (476, v217) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 476 v217 hS (by decide)) fb 836 468 v216 stF_FB (by decide)) fb 836 252 v220 stF_FB (by decide)) fb 836 248 v219 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 476 rfl rfl).wrF 468 rfl rfl).wrF 252 rfl rfl).wrF 248 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g221
  subst e_v220
  subst e_v219
  subst e_g218
  subst e_v217
  subst e_v216
  have r_v38 := hF.rd l_v38 16 rfl; subst r_v38
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
