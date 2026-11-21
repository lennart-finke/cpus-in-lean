import Solutions.OpensslSha256.X.UpdRun1
/-!
# `SHA224_Final` (`0x1001a8`): `jmp SHA256_Final`
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem fin224_jmp (H : CMem) (esp eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) :
    ∃ f' : UInt32,
      exN Image.sym_halt 1 ⟨H.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x1001a8, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x1001b0, efl f', ic + 1⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
