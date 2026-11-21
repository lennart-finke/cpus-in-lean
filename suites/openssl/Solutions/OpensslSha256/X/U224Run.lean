import Solutions.OpensslSha256.X.UpdRun1
/-!
# The instructions of `SHA224_Update` (`0x1000c0`)

`pushl 0xc(%esp)` three times (the arguments again), `call SHA256_Update`; then `addl $0xc,%esp`,
`movl $1,%eax`, `ret`. The stack pointer at the entry is `U.add 56`, so that `SHA256_Update` is entered
with it at `U.add 40`.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem u224_a (H : CMem) (U ctx msg len eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 72 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 72 ≤ 1048576)
    (h1 : rdRaw H.get (U.add 60) 4 = ctx) (h2 : rdRaw H.get (U.add 64) 4 = msg)
    (h3 : rdRaw H.get (U.add 68) 4 = len) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, U.add 56, ebp, esi, edi, 0x1000c0, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 40, ebp, esi, edi, 0x1000e0, efl f', ic + 4⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 52) 4 len) (U.add 48) 4 msg) (U.add 44) 4 ctx)
        (U.add 40) 4 0x1000d1 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem u224_b (H : CMem) (U ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 72 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 72 ≤ 1048576) (hra : rdRaw H.get (U.add 56) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 44, ebp, esi, edi, 0x1000d1, efl f, ic⟩ =
        some ⟨H.get, 1, ecx, edx, ebx, U.add 60, ebp, esi, edi, ra, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
