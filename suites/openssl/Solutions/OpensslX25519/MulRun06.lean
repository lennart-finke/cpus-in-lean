import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 30–35

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

/-- movl %esi, %eax ; imull %ebx ; movl %edx, 0x184(%esp) ; movl %eax, 0x17c(%esp) ; movl 0x10(%esp), %esi ; movl %esi, %eax ; imull %ecx ; movl %edx, 0x1fc(%esp) -/
theorem mul_p30 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v152 v133 v153 x4 x14 v36 v34 g154 v38 v155 v156 g157 v158 v159 g160 : UInt32)
        (l_v38 : l.lookup 16 = some v38)
    (e_v155 : v155 = UInt64.toUInt32 (imulCore 4 v36 x4).1)
    (e_v156 : v156 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v36 x4).1 32))
    (e_g157 : g157 = mixF g154 (ovfBits (imulCore 4 v36 x4).2) 2049)
    (e_v158 : v158 = UInt64.toUInt32 (imulCore 4 v38 v133).1)
    (e_v159 : v159 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v38 v133).1 32))
    (e_g160 : g160 = mixF g157 (ovfBits (imulCore 4 v38 v133).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v152, v133, v153, x4, fb, x14, v36, v34, 0x101025, efl g154, 245⟩)
      (St.m ⟨N'.get, v158, v133, v159, x4, fb, x14, v38, v34, 0x101046, efl g160, 253⟩) ∧
      Frame N' fb 836 ((508, v159) :: (380, v155) :: (388, v156) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 388 v156 hS (by decide)) fb 836 380 v155 stF_FB (by decide)) fb 836 508 v159 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 388 rfl rfl).wrF 380 rfl rfl).wrF 508 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g160
  subst e_v159
  subst e_v158
  subst e_g157
  subst e_v156
  subst e_v155
  have r_v38 := hF.rd l_v38 16 rfl; subst r_v38
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %eax, 0x1f4(%esp) ; movl 0x2c(%esp), %ebx ; movl %ebx, %eax ; movl 0x64(%esp), %ecx ; imull %ecx ; movl %edx, 0x28(%esp) ; movl %eax, 0x1c(%esp) ; movl 0x8(%esp), %eax -/
theorem mul_p31 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v158 v133 v159 x4 x14 v38 v34 g160 x11 x5 x12 v161 v162 g163 : UInt32)
        (l_x11 : l.lookup 44 = some x11)
    (l_x5 : l.lookup 100 = some x5)
    (l_x12 : l.lookup 8 = some x12)
    (e_v161 : v161 = UInt64.toUInt32 (imulCore 4 x11 x5).1)
    (e_v162 : v162 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x11 x5).1 32))
    (e_g163 : g163 = mixF g160 (ovfBits (imulCore 4 x11 x5).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v158, v133, v159, x4, fb, x14, v38, v34, 0x101046, efl g160, 253⟩)
      (St.m ⟨N'.get, x12, x5, v162, x11, fb, x14, v38, v34, 0x101065, efl g163, 261⟩) ∧
      Frame N' fb 836 ((28, v161) :: (40, v162) :: (500, v158) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF N fb 836 500 v158 hS (by decide)) fb 836 40 v162 stF_FB (by decide)) fb 836 28 v161 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 500 rfl rfl).wrF 40 rfl rfl).wrF 28 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g163
  subst e_v162
  subst e_v161
  have r_x11 := hF.rd l_x11 44 rfl; subst r_x11
  have r_x5 := hF.rd l_x5 100 rfl; subst r_x5
  have r_x12 := hF.rd l_x12 8 rfl; subst r_x12
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ecx ; movl %edx, 0x18c(%esp) ; movl %eax, 0x188(%esp) ; movl 0x4(%esp), %eax ; imull %ecx ; movl %edx, 0x208(%esp) ; movl %eax, 0x204(%esp) ; movl %ebp, %eax -/
theorem mul_p32 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x12 x5 v162 x11 x14 v38 v34 g163 x13 v164 v165 g166 v167 v168 g169 : UInt32)
        (l_x13 : l.lookup 4 = some x13)
    (e_v164 : v164 = UInt64.toUInt32 (imulCore 4 x12 x5).1)
    (e_v165 : v165 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x12 x5).1 32))
    (e_g166 : g166 = mixF g163 (ovfBits (imulCore 4 x12 x5).2) 2049)
    (e_v167 : v167 = UInt64.toUInt32 (imulCore 4 x13 x5).1)
    (e_v168 : v168 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x13 x5).1 32))
    (e_g169 : g169 = mixF g166 (ovfBits (imulCore 4 x13 x5).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x12, x5, v162, x11, fb, x14, v38, v34, 0x101065, efl g163, 261⟩)
      (St.m ⟨N'.get, x14, x5, v168, x11, fb, x14, v38, v34, 0x10108b, efl g169, 269⟩) ∧
      Frame N' fb 836 ((516, v167) :: (520, v168) :: (392, v164) :: (396, v165) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 396 v165 hS (by decide)) fb 836 392 v164 stF_FB (by decide)) fb 836 520 v168 stF_FB (by decide)) fb 836 516 v167 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 396 rfl rfl).wrF 392 rfl rfl).wrF 520 rfl rfl).wrF 516 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g169
  subst e_v168
  subst e_v167
  subst e_g166
  subst e_v165
  subst e_v164
  have r_x13 := hF.rd l_x13 4 rfl; subst r_x13
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ecx ; movl %edx, 0x260(%esp) ; movl %eax, 0x25c(%esp) ; movl (%esp), %eax ; imull %ecx ; movl %edx, 0x298(%esp) ; movl %eax, 0x294(%esp) ; movl 0xc(%esp), %eax -/
theorem mul_p33 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x14 x5 v168 x11 v38 v34 g169 x15 x16 v170 v171 g172 v173 v174 g175 : UInt32)
        (l_x15 : l.lookup 0 = some x15)
    (l_x16 : l.lookup 12 = some x16)
    (e_v170 : v170 = UInt64.toUInt32 (imulCore 4 x14 x5).1)
    (e_v171 : v171 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x14 x5).1 32))
    (e_g172 : g172 = mixF g169 (ovfBits (imulCore 4 x14 x5).2) 2049)
    (e_v173 : v173 = UInt64.toUInt32 (imulCore 4 x15 x5).1)
    (e_v174 : v174 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x15 x5).1 32))
    (e_g175 : g175 = mixF g172 (ovfBits (imulCore 4 x15 x5).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x14, x5, v168, x11, fb, x14, v38, v34, 0x10108b, efl g169, 269⟩)
      (St.m ⟨N'.get, x16, x5, v174, x11, fb, x14, v38, v34, 0x1010b2, efl g175, 277⟩) ∧
      Frame N' fb 836 ((660, v173) :: (664, v174) :: (604, v170) :: (608, v171) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 608 v171 hS (by decide)) fb 836 604 v170 stF_FB (by decide)) fb 836 664 v174 stF_FB (by decide)) fb 836 660 v173 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 608 rfl rfl).wrF 604 rfl rfl).wrF 664 rfl rfl).wrF 660 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g175
  subst e_v174
  subst e_v173
  subst e_g172
  subst e_v171
  subst e_v170
  have r_x15 := hF.rd0 l_x15; subst r_x15
  have r_x16 := hF.rd l_x16 12 rfl; subst r_x16
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ecx ; movl %edx, 0x68(%esp) ; movl %eax, 0x2c8(%esp) ; movl 0x38(%esp), %ebp ; movl %ebp, %eax ; imull %ecx ; movl %edx, 0x10c(%esp) ; movl %eax, 0x108(%esp) -/
theorem mul_p34 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (x16 x5 v174 x11 x14 v38 v34 g175 v32 v176 v177 g178 v179 v180 g181 : UInt32)
        (l_v32 : l.lookup 56 = some v32)
    (e_v176 : v176 = UInt64.toUInt32 (imulCore 4 x16 x5).1)
    (e_v177 : v177 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x16 x5).1 32))
    (e_g178 : g178 = mixF g175 (ovfBits (imulCore 4 x16 x5).2) 2049)
    (e_v179 : v179 = UInt64.toUInt32 (imulCore 4 v32 x5).1)
    (e_v180 : v180 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v32 x5).1 32))
    (e_g181 : g181 = mixF g178 (ovfBits (imulCore 4 v32 x5).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, x16, x5, v174, x11, fb, x14, v38, v34, 0x1010b2, efl g175, 277⟩)
      (St.m ⟨N'.get, v179, x5, v180, x11, fb, v32, v38, v34, 0x1010d5, efl g181, 285⟩) ∧
      Frame N' fb 836 ((264, v179) :: (268, v180) :: (712, v176) :: (104, v177) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 104 v177 hS (by decide)) fb 836 712 v176 stF_FB (by decide)) fb 836 268 v180 stF_FB (by decide)) fb 836 264 v179 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 104 rfl rfl).wrF 712 rfl rfl).wrF 268 rfl rfl).wrF 264 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g181
  subst e_v180
  subst e_v179
  subst e_g178
  subst e_v177
  subst e_v176
  have r_v32 := hF.rd l_v32 56 rfl; subst r_v32
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edi, %eax ; imull %ecx ; movl %edx, 0x150(%esp) ; movl %eax, 0x14c(%esp) ; movl 0x24(%esp), %eax ; imull %ecx ; movl %edx, 0x1b4(%esp) ; movl %eax, 0x1ac(%esp) -/
theorem mul_p35 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v179 x5 v180 x11 v32 v38 v34 g181 v36 v182 v183 g184 v185 v186 g187 : UInt32)
        (l_v36 : l.lookup 36 = some v36)
    (e_v182 : v182 = UInt64.toUInt32 (imulCore 4 v34 x5).1)
    (e_v183 : v183 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v34 x5).1 32))
    (e_g184 : g184 = mixF g181 (ovfBits (imulCore 4 v34 x5).2) 2049)
    (e_v185 : v185 = UInt64.toUInt32 (imulCore 4 v36 x5).1)
    (e_v186 : v186 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v36 x5).1 32))
    (e_g187 : g187 = mixF g184 (ovfBits (imulCore 4 v36 x5).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v179, x5, v180, x11, fb, v32, v38, v34, 0x1010d5, efl g181, 285⟩)
      (St.m ⟨N'.get, v185, x5, v186, x11, fb, v32, v38, v34, 0x1010fb, efl g187, 293⟩) ∧
      Frame N' fb 836 ((428, v185) :: (436, v186) :: (332, v182) :: (336, v183) :: l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨(stF (stF (stF (stF N fb 836 336 v183 hS (by decide)) fb 836 332 v182 stF_FB (by decide)) fb 836 436 v186 stF_FB (by decide)) fb 836 428 v185 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 336 rfl rfl).wrF 332 rfl rfl).wrF 436 rfl rfl).wrF 428 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g187
  subst e_v186
  subst e_v185
  subst e_g184
  subst e_v183
  subst e_v182
  have r_v36 := hF.rd l_v36 36 rfl; subst r_v36
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
