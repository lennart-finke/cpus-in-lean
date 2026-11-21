import Solutions.OpensslSha256.X.UpdRun1
/-!
# The instructions of `SHA256_Update`: the branch on `num + len < 64`, the copy into the buffer, the first block call
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `num + len < 64`: copy the chunk behind the buffered bytes. -/
theorem upd_as (H : CMem) (U ctx msg len num eax edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hlt : ((num.add len).lor len).toNat < 64) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, num, edx, ebx, U.add 24, len, ctx, msg, 0x100111, efl f, ic⟩ =
        some ⟨H'.get, (ctx.add num).add 40, num, edx, ebx, U.add 8, len, ctx, msg, 0x1011f0, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 20) 4 len) (U.add 16) 4 msg) (U.add 12) 4
        ((ctx.add num).add 40)) (U.add 8) 4 0x100127 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- `num + len ≥ 64`: fill the buffer to 64 bytes. -/
theorem upd_ab (H : CMem) (U ctx msg len num eax edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hlt : ¬ ((num.add len).lor len).toNat < 64) :
    ∃ (H' : CMem) (f' B : UInt32),
      exN Image.sym_halt 11 ⟨H.get, eax, num, edx, ebx, U.add 24, len, ctx, msg, 0x100111, efl f, ic⟩ =
        some ⟨H'.get, (ctx.add num).add 40, num, edx, B, U.add 8, len, ctx, msg, 0x1011f0, efl f', ic + 11⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 20) 4 B) (U.add 16) 4 msg) (U.add 12) 4
        ((ctx.add num).add 40)) (U.add 8) 4 0x10013e ∧ B = 64 - num := by
  ex_run
  refine ⟨_, _, _, rfl, rfl, ?_⟩
  first | rfl | exact Solutions.Exec.subF_fst _ _

/-- After the copy (small chunk): `num += len`, the epilogue. -/
theorem upd_se (H : CMem) (U ctx msg len num sesi sedi sebx sebp ra eax ecx edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 56 ≤ ctx.toNat)
    (s0 : rdRaw H.get (U.add 24) 4 = sesi) (s1 : rdRaw H.get (U.add 28) 4 = sedi)
    (s2 : rdRaw H.get (U.add 32) 4 = sebx) (s3 : rdRaw H.get (U.add 36) 4 = sebp) (s4 : rdRaw H.get (U.add 40) 4 = ra)
    (hn : rdRaw H.get (ctx.add 104) 4 = num) :
    ∃ (H' : CMem) (f' N : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, ebx, U.add 12, len, ctx, msg, 0x100127, efl f, ic⟩ =
        some ⟨H'.get, 1, ecx, edx, sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic + 9⟩ ∧
      H'.get = wrBytes H.get (ctx.add 104) 4 N ∧ N = num + len := by
  ex_run
  refine ⟨_, _, _, rfl, rfl, ?_⟩
  first | rfl | exact Solutions.Exec.addF_fst _ _

/-- After the copy (buffer filled): the call of the block function on the buffer. -/
theorem upd_b2 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 12, ebp, ctx, edi, 0x10013e, efl f, ic⟩ =
        some ⟨H'.get, eax, ctx, ctx.add 40, ebx, U.add 16, ebp, ctx, edi, 0x100340, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes H.get (U.add 20) 4 1) (U.add 16) 4 0x10014d := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

end Solutions.ShaX
