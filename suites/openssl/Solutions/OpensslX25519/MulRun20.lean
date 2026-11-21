import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.Frame
import Solutions.Exec.Mul
/-!
# The run of `fe_mul`, pieces 114–119

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

/-- subl %eax, %ebx ; movl %ebp, %ecx ; addl $0x1000000, %ecx -/
theorem mul_p114 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v860 v816 v818 v792 v856 v858 v806 g861 v862 g863 v864 g865 : UInt32)
        (e_v862 : v862 = (subF 4 v792 v860 0).1)
    (e_g863 : g863 = (subF 4 v792 v860 0).2)
    (e_v864 : v864 = (addF 4 v856 16777216 0).1)
    (e_g865 : g865 = (addF 4 v856 16777216 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v860, v816, v818, v792, fb, v856, v858, v806, 0x101b92, efl g861, 846⟩)
      (St.m ⟨N'.get, v860, v864, v818, v862, fb, v856, v858, v806, 0x101b9c, efl g865, 849⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 3) ?_, hF, hP⟩
  subst e_g865
  subst e_v864
  subst e_g863
  subst e_v862
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %esi ; movl %ecx, %eax ; shrdl $0x19, %esi, %eax ; sarl $0x19, %esi ; leal (%esi,%esi,8), %edx ; leal (%esi,%edx,2), %esi ; movl $0x13, %edx -/
theorem mul_p115 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v860 v864 v818 v862 v856 v858 v806 g865 v866 g867 v868 g869 v870 g871 v872 v873 : UInt32)
        (e_v866 : v866 = (addF 4 v858 0 (cfBit g865)).1)
    (e_g867 : g867 = (addF 4 v858 0 (cfBit g865)).2)
    (e_v868 : v868 = sdR false v864 v866 25)
    (e_g869 : g869 = sdF false v864 v866 25)
    (e_v870 : v870 = sarR v866 25)
    (e_g871 : g871 = sarF v866 25)
    (e_v872 : v872 = UInt32.add v870 (UInt32.shiftLeft v870 3))
    (e_v873 : v873 = UInt32.add v870 (UInt32.shiftLeft v872 1)) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v860, v864, v818, v862, fb, v856, v858, v806, 0x101b9c, efl g865, 849⟩)
      (St.m ⟨N'.get, v868, v864, 19, v862, fb, v856, v873, v806, 0x101bb3, efl g871, 856⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 7) ?_, hF, hP⟩
  subst e_v873
  subst e_v872
  subst e_g871
  subst e_v870
  subst e_g869
  subst e_v868
  subst e_g867
  subst e_v866
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- mull %edx ; addl %esi, %edx ; addl 0x4(%esp), %eax ; adcl 0x8(%esp), %edx ; andl $0xfe000000, %ecx -/
theorem mul_p116 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v868 v864 v862 v856 v873 v806 g871 v466 v468 v874 v875 g876 v877 g878 v879 g880 v881 g882 v883 g884 : UInt32)
        (l_v466 : l.lookup 4 = some v466)
    (l_v468 : l.lookup 8 = some v468)
    (e_v874 : v874 = UInt64.toUInt32 (UInt64.mul (UInt32.toUInt64 v868) 19))
    (e_v875 : v875 = UInt64.toUInt32 (UInt64.shiftRight (UInt64.mul (UInt32.toUInt64 v868) 19) 32))
    (e_g876 : g876 = mixF g871 (ovfBits (UInt64.shiftRight (UInt64.mul (UInt32.toUInt64 v868) 19) 32 != 0)) 2049)
    (e_v877 : v877 = (addF 4 v875 v873 0).1)
    (e_g878 : g878 = (addF 4 v875 v873 0).2)
    (e_v879 : v879 = (addF 4 v874 v466 0).1)
    (e_g880 : g880 = (addF 4 v874 v466 0).2)
    (e_v881 : v881 = (addF 4 v877 v468 (cfBit g880)).1)
    (e_g882 : g882 = (addF 4 v877 v468 (cfBit g880)).2)
    (e_v883 : v883 = (logicF 4 (UInt32.land v864 4261412864)).1)
    (e_g884 : g884 = (logicF 4 (UInt32.land v864 4261412864)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v868, v864, 19, v862, fb, v856, v873, v806, 0x101bb3, efl g871, 856⟩)
      (St.m ⟨N'.get, v879, v883, v881, v862, fb, v856, v873, v806, 0x101bc5, efl g884, 861⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 5) ?_, hF, hP⟩
  subst e_g884
  subst e_v883
  subst e_g882
  subst e_v881
  subst e_g880
  subst e_v879
  subst e_g878
  subst e_v877
  subst e_g876
  subst e_v875
  subst e_v874
  have r_v466 := hF.rd l_v466 4 rfl; subst r_v466
  have r_v468 := hF.rd l_v468 8 rfl; subst r_v468
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %ecx, %ebp ; movl %eax, %ecx ; addl $0x2000000, %ecx -/
theorem mul_p117 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v879 v883 v881 v862 v856 v873 v806 g884 v885 g886 v887 g888 : UInt32)
        (e_v885 : v885 = (subF 4 v856 v883 0).1)
    (e_g886 : g886 = (subF 4 v856 v883 0).2)
    (e_v887 : v887 = (addF 4 v879 33554432 0).1)
    (e_g888 : g888 = (addF 4 v879 33554432 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v879, v883, v881, v862, fb, v856, v873, v806, 0x101bc5, efl g884, 861⟩)
      (St.m ⟨N'.get, v879, v887, v881, v862, fb, v885, v873, v806, 0x101bcf, efl g888, 864⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 3) ?_, hF, hP⟩
  subst e_g888
  subst e_v887
  subst e_g886
  subst e_v885
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- adcl $0x0, %edx ; shldl $0x6, %ecx, %edx ; addl 0x14(%esp), %edx ; andl $0xfc000000, %ecx -/
theorem mul_p118 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v879 v887 v881 v862 v885 v873 v806 g888 v574 v889 g890 v891 g892 v893 g894 v895 g896 : UInt32)
        (l_v574 : l.lookup 20 = some v574)
    (e_v889 : v889 = (addF 4 v881 0 (cfBit g888)).1)
    (e_g890 : g890 = (addF 4 v881 0 (cfBit g888)).2)
    (e_v891 : v891 = sdR true v889 v887 6)
    (e_g892 : g892 = sdF true v889 v887 6)
    (e_v893 : v893 = (addF 4 v891 v574 0).1)
    (e_g894 : g894 = (addF 4 v891 v574 0).2)
    (e_v895 : v895 = (logicF 4 (UInt32.land v887 4227858432)).1)
    (e_g896 : g896 = (logicF 4 (UInt32.land v887 4227858432)).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v879, v887, v881, v862, fb, v885, v873, v806, 0x101bcf, efl g888, 864⟩)
      (St.m ⟨N'.get, v879, v895, v893, v862, fb, v885, v873, v806, 0x101be0, efl g896, 868⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 4) ?_, hF, hP⟩
  subst e_g896
  subst e_v895
  subst e_g894
  subst e_v893
  subst e_g892
  subst e_v891
  subst e_g890
  subst e_v889
  have r_v574 := hF.rd l_v574 20 rfl; subst r_v574
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

/-- subl %ecx, %eax -/
theorem mul_p119 (G N : XMem) (fb : UInt32) (hS : FB N.get.size fb 836) (l : List (Nat × UInt32))
    (hF : Frame N fb 836 l) (hP : Pres G N (OutF fb 828)) (v879 v895 v893 v862 v885 v873 v806 g896 v897 g898 : UInt32)
        (e_v897 : v897 = (subF 4 v879 v895 0).1)
    (e_g898 : g898 = (subF 4 v879 v895 0).2) :
    ∃ N' : XMem, Run img (St.m ⟨N.get, v879, v895, v893, v862, fb, v885, v873, v806, 0x101be0, efl g896, 868⟩)
      (St.m ⟨N'.get, v897, v895, v893, v862, fb, v885, v873, v806, 0x101be2, efl g898, 869⟩) ∧
      Frame N' fb 836 (l) ∧ Pres G N' (OutF fb 828) := by
  refine ⟨N, run_of_runOk (k := 1) ?_, hF, hP⟩
  subst e_g898
  subst e_v897
  
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv

end Solutions.OpensslX25519
