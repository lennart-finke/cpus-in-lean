import Solutions.OpensslSha256.X.Hyp
/-!
# The instructions of `memset` (`0x101220`)

`push %esi; mov 0x10(%esp),%ecx; mov 0x8(%esp),%eax; test %ecx,%ecx; je; mov 0xc(%esp),%edx;
mov %eax,%esi; nop×13`, the loop `movb %dl,(%esi); inc %esi; dec %ecx; jne`, then `pop %esi; ret`.
The stack pointer at the entry is `U.add 4` (the return address there, the arguments above it).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem mixF_zf (f v : UInt32) : UInt32.land (mixF f v 2260) 64 = UInt32.land v 64 := by
  show ((f &&& ~~~2260) ||| (v &&& 2260)) &&& 64 = v &&& 64
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have h64 : ∀ j, j < 32 → (UInt32.toBitVec 64).getLsbD j = decide (j = 6) := by decide
  rw [h64 i hi]
  by_cases h6 : i = 6
  · subst h6
    have : (UInt32.toBitVec 2260).getLsbD 6 = true := by decide
    simp_all
  · simp [h6]

attribute [cbv_eval] mixF_zf

theorem memset_head (H : CMem) (U dst c n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 20 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 20 ≤ 1048576)
    (hdst : rdRaw H.get (U.add 8) 4 = dst) (hc : rdRaw H.get (U.add 12) 4 = c)
    (hn : rdRaw H.get (U.add 16) 4 = n) (hn0 : n.toNat ≠ 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 20 ⟨H.get, eax, ecx, edx, ebx, U.add 4, ebp, esi, edi, 0x101220, efl f, ic⟩ =
        some ⟨H'.get, dst, n, c, ebx, U, ebp, dst, edi, 0x101240, efl f', ic + 20⟩ ∧
      H'.get = wrBytes H.get U 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memset_zero (H : CMem) (U dst c n ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 20 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 20 ≤ 1048576) (hra : rdRaw H.get (U.add 4) 4 = ra)
    (hdst : rdRaw H.get (U.add 8) 4 = dst) (hn : rdRaw H.get (U.add 16) 4 = n) (hn0 : n.toNat = 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 7 ⟨H.get, eax, ecx, edx, ebx, U.add 4, ebp, esi, edi, 0x101220, efl f, ic⟩ =
        some ⟨H'.get, dst, n, edx, ebx, U.add 8, ebp, esi, edi, ra, efl f', ic + 7⟩ ∧
      H'.get = wrBytes H.get U 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memset_cont (H : CMem) (U eax ecx edx ebx ebp p edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hp : p.toNat + 1 ≤ H.get.size)
    (hpc : 1048576 + 4944 ≤ p.toNat ∨ p.toNat + 1 ≤ 1048576) (hc : ecx.toNat ≠ 1) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, U, ebp, p, edi, 0x101240, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx.add 4294967295, edx, ebx, U, ebp, p.add 1, edi, 0x101240, efl f', ic + 4⟩ ∧
      H'.get = wrBytes H.get p 1 (edx.land 255) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memset_exit (H : CMem) (U eax ecx edx ebx ebp p edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hp : p.toNat + 1 ≤ H.get.size)
    (hpc : 1048576 + 4944 ≤ p.toNat ∨ p.toNat + 1 ≤ 1048576) (hc : ecx.toNat = 1) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, U, ebp, p, edi, 0x101240, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx.add 4294967295, edx, ebx, U, ebp, p.add 1, edi, 0x101246, efl f', ic + 4⟩ ∧
      H'.get = wrBytes H.get p 1 (edx.land 255) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memset_tail (H : CMem) (U ra sv eax ecx edx ebx ebp p edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 20 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 20 ≤ 1048576)
    (hsv : rdRaw H.get U 4 = sv) (hra : rdRaw H.get (U.add 4) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 2 ⟨H.get, eax, ecx, edx, ebx, U, ebp, p, edi, 0x101246, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, sv, edi, ra, efl f', ic + 2⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
