import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_sq`, pieces 24–29

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

/-- movl %eax, 0x164(%esp) ; movl 0x38(%esp), %ebx ; movl %ebx, %eax ; leal (%ecx,%ecx,1), %edx ; imull %edx ; movl %edx, 0x74(%esp) ; movl %eax, 0x70(%esp) ; movl %edi, %eax -/
theorem sq_p24 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v133 x5 v134 v14 x6 v75 v118 g135 v12 v136 v137 v138 g139 : UInt32)
        (l_v12 : l.lookup 56 = some v12)
    (e_v136 : v136 = UInt32.add x5 x5)
    (e_v137 : v137 = UInt64.toUInt32 (imulCore 4 v12 v136).1)
    (e_v138 : v138 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v12 v136).1 32))
    (e_g139 : g139 = mixF g135 (ovfBits (imulCore 4 v12 v136).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v133, x5, v134, v14, fb, x6, v75, v118, 0x102682, efl g135, 191⟩)
      (St.m ⟨N'.get, v118, x5, v138, v12, fb, x6, v75, v118, 0x10269e, efl g139, 199⟩) ∧
      Frame N' fb 468 ((112, v137) :: (116, v138) :: (356, v133) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF N fb 468 356 v133 hS (by decide)) fb 468 116 v138 stF_FB (by decide)) fb 468 112 v137 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 356 rfl rfl).wrF 116 rfl rfl).wrF 112 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g139
  subst e_v138
  subst e_v137
  subst e_v136
  have r_v12 := hF.rd l_v12 56 rfl; subst r_v12
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- imull %ecx ; movl %edx, 0x94(%esp) ; movl %eax, 0x90(%esp) ; movl 0x20(%esp), %eax ; leal (%ecx,%ecx,1), %edx ; imull %edx ; movl %edx, 0xc8(%esp) ; movl %eax, 0xc4(%esp) -/
theorem sq_p25 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v118 x5 v138 v12 x6 v75 g139 v14 v140 v141 g142 v143 v144 v145 g146 : UInt32)
        (l_v14 : l.lookup 32 = some v14)
    (e_v140 : v140 = UInt64.toUInt32 (imulCore 4 v118 x5).1)
    (e_v141 : v141 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v118 x5).1 32))
    (e_g142 : g142 = mixF g139 (ovfBits (imulCore 4 v118 x5).2) 2049)
    (e_v143 : v143 = UInt32.add x5 x5)
    (e_v144 : v144 = UInt64.toUInt32 (imulCore 4 v14 v143).1)
    (e_v145 : v145 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v14 v143).1 32))
    (e_g146 : g146 = mixF g142 (ovfBits (imulCore 4 v14 v143).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v118, x5, v138, v12, fb, x6, v75, v118, 0x10269e, efl g139, 199⟩)
      (St.m ⟨N'.get, v144, x5, v145, v12, fb, x6, v75, v118, 0x1026c5, efl g146, 207⟩) ∧
      Frame N' fb 468 ((196, v144) :: (200, v145) :: (144, v140) :: (148, v141) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 148 v141 hS (by decide)) fb 468 144 v140 stF_FB (by decide)) fb 468 200 v145 stF_FB (by decide)) fb 468 196 v144 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 148 rfl rfl).wrF 144 rfl rfl).wrF 200 rfl rfl).wrF 196 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g146
  subst e_v145
  subst e_v144
  subst e_v143
  subst e_g142
  subst e_v141
  subst e_v140
  have r_v14 := hF.rd l_v14 32 rfl; subst r_v14
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %esi, %eax ; imull %ecx ; movl %eax, 0xf4(%esp) ; movl %edx, 0xf8(%esp) ; imull $0x26, %ebp, %eax ; imull %ebp ; movl %edx, 0x14(%esp) ; movl %eax, 0xc(%esp) -/
theorem sq_p26 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v144 x5 v145 v12 x6 v75 v118 g146 v147 v148 g149 v150 g151 v152 v153 g154 : UInt32)
        (e_v147 : v147 = UInt64.toUInt32 (imulCore 4 v75 x5).1)
    (e_v148 : v148 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v75 x5).1 32))
    (e_g149 : g149 = mixF g146 (ovfBits (imulCore 4 v75 x5).2) 2049)
    (e_v150 : v150 = UInt32.land (UInt64.toUInt32 (imulCore 4 x6 38).1) 4294967295)
    (e_g151 : g151 = mixF g149 (ovfBits (imulCore 4 x6 38).2) 2049)
    (e_v152 : v152 = UInt64.toUInt32 (imulCore 4 v150 x6).1)
    (e_v153 : v153 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v150 x6).1 32))
    (e_g154 : g154 = mixF g151 (ovfBits (imulCore 4 v150 x6).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v144, x5, v145, v12, fb, x6, v75, v118, 0x1026c5, efl g146, 207⟩)
      (St.m ⟨N'.get, v152, x5, v153, v12, fb, x6, v75, v118, 0x1026e4, efl g154, 215⟩) ∧
      Frame N' fb 468 ((12, v152) :: (20, v153) :: (248, v148) :: (244, v147) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 244 v147 hS (by decide)) fb 468 248 v148 stF_FB (by decide)) fb 468 20 v153 stF_FB (by decide)) fb 468 12 v152 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 244 rfl rfl).wrF 248 rfl rfl).wrF 20 rfl rfl).wrF 12 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g154
  subst e_v153
  subst e_v152
  subst e_g151
  subst e_v150
  subst e_g149
  subst e_v148
  subst e_v147
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %ebx, %eax ; movl 0x34(%esp), %ebp ; imull %ebp ; movl %edx, %ebx ; movl %eax, (%esp) ; movl %edi, %eax ; movl %edi, %ecx ; imull %ebp -/
theorem sq_p27 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v152 x5 v153 v12 x6 v75 v118 g154 v61 v155 v156 g157 v158 v159 g160 : UInt32)
        (l_v61 : l.lookup 52 = some v61)
    (e_v155 : v155 = UInt64.toUInt32 (imulCore 4 v12 v61).1)
    (e_v156 : v156 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v12 v61).1 32))
    (e_g157 : g157 = mixF g154 (ovfBits (imulCore 4 v12 v61).2) 2049)
    (e_v158 : v158 = UInt64.toUInt32 (imulCore 4 v118 v61).1)
    (e_v159 : v159 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v118 v61).1 32))
    (e_g160 : g160 = mixF g157 (ovfBits (imulCore 4 v118 v61).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v152, x5, v153, v12, fb, x6, v75, v118, 0x1026e4, efl g154, 215⟩)
      (St.m ⟨N'.get, v158, v118, v159, v156, fb, v61, v75, v118, 0x1026f7, efl g160, 223⟩) ∧
      Frame N' fb 468 ((0, v155) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF0 N fb 468 v155 hS (by decide)), run_of_runOk (k := 8) ?_, (hF.wrF0), (hP.wrF0 (by decide))⟩
  subst e_g160
  subst e_v159
  subst e_v158
  subst e_g157
  subst e_v156
  subst e_v155
  have r_v61 := hF.rd l_v61 52 rfl; subst r_v61
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %edx, 0xc0(%esp) ; movl %eax, 0xb8(%esp) ; movl 0x20(%esp), %edi ; movl %edi, %eax ; imull %ebp ; movl %edx, 0xe4(%esp) ; movl %eax, 0xdc(%esp) ; movl 0x44(%esp), %esi -/
theorem sq_p28 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v158 v118 v159 v156 v61 v75 g160 v14 v161 v162 g163 : UInt32)
        (l_v14 : l.lookup 32 = some v14)
    (l_v75 : l.lookup 68 = some v75)
    (e_v161 : v161 = UInt64.toUInt32 (imulCore 4 v14 v61).1)
    (e_v162 : v162 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v14 v61).1 32))
    (e_g163 : g163 = mixF g160 (ovfBits (imulCore 4 v14 v61).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v158, v118, v159, v156, fb, v61, v75, v118, 0x1026f7, efl g160, 223⟩)
      (St.m ⟨N'.get, v161, v118, v162, v156, fb, v61, v75, v14, 0x10271f, efl g163, 231⟩) ∧
      Frame N' fb 468 ((220, v161) :: (228, v162) :: (184, v158) :: (192, v159) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF (stF N fb 468 192 v159 hS (by decide)) fb 468 184 v158 stF_FB (by decide)) fb 468 228 v162 stF_FB (by decide)) fb 468 220 v161 stF_FB (by decide)), run_of_runOk (k := 8) ?_, ((((hF.wrF 192 rfl rfl).wrF 184 rfl rfl).wrF 228 rfl rfl).wrF 220 rfl rfl), ((((hP.wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g163
  subst e_v162
  subst e_v161
  have r_v14 := hF.rd l_v14 32 rfl; subst r_v14
  have r_v75 := hF.rd l_v75 68 rfl; subst r_v75
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- movl %esi, %eax ; imull %ebp ; movl %edx, 0x6c(%esp) ; movl %eax, 0x68(%esp) ; movl 0x38(%esp), %eax ; movl 0x30(%esp), %ebp ; imull %ebp ; movl %edx, 0xa0(%esp) -/
theorem sq_p29 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 468) (l : List (Nat × UInt32))
    (hF : Frame N fb 468 l) (hP : Pres G N (OutF fb 464)) (v161 v118 v162 v156 v61 v75 v14 g163 v12 x7 v164 v165 g166 v167 v168 g169 : UInt32)
        (l_v12 : l.lookup 56 = some v12)
    (l_x7 : l.lookup 48 = some x7)
    (e_v164 : v164 = UInt64.toUInt32 (imulCore 4 v75 v61).1)
    (e_v165 : v165 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v75 v61).1 32))
    (e_g166 : g166 = mixF g163 (ovfBits (imulCore 4 v75 v61).2) 2049)
    (e_v167 : v167 = UInt64.toUInt32 (imulCore 4 v12 x7).1)
    (e_v168 : v168 = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 v12 x7).1 32))
    (e_g169 : g169 = mixF g166 (ovfBits (imulCore 4 v12 x7).2) 2049) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v161, v118, v162, v156, fb, v61, v75, v14, 0x10271f, efl g163, 231⟩)
      (St.m ⟨N'.get, v167, v118, v168, v156, fb, x7, v75, v14, 0x10273c, efl g169, 239⟩) ∧
      Frame N' fb 468 ((160, v168) :: (104, v164) :: (108, v165) :: l) ∧ Pres G N' (OutF fb 464) := by
  refine ⟨(stF (stF (stF N fb 468 108 v165 hS (by decide)) fb 468 104 v164 stF_FB (by decide)) fb 468 160 v168 stF_FB (by decide)), run_of_runOk (k := 8) ?_, (((hF.wrF 108 rfl rfl).wrF 104 rfl rfl).wrF 160 rfl rfl), (((hP.wrF (by decide)).wrF (by decide)).wrF (by decide))⟩
  subst e_g169
  subst e_v168
  subst e_v167
  subst e_g166
  subst e_v165
  subst e_v164
  have r_v12 := hF.rd l_v12 56 rfl; subst r_v12
  have r_x7 := hF.rd l_x7 48 rfl; subst r_x7
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
