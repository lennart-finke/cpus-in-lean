import Solutions.OpensslSha256.X.Bswap
import Solutions.OpensslSha256.X.UpdRun1
/-!
# The instructions of `SHA256_Final`: the length words, the last block, the wipe, the branch on `md_len`

The stack pointer at the entry is `V.add 36` (return address there, then `md`, `ctx`); after the three
pushes it is `V.add 24`.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- The bit count big-endian at the end of the block; the block function. -/
theorem fin_f (H : CMem) (U ctx D Nl Nh eax ecx edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (h4 : rdRaw H.get (ctx.add 32) 4 = Nl) (h5 : rdRaw H.get (ctx.add 36) 4 = Nh) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 11 ⟨H.get, eax, ecx, edx, ebx, U.add 12, ebp, ctx, D, 0x100206, efl f, ic⟩ =
        some ⟨H'.get, bsw Nl, ctx, D, ebx, U.add 16, ebp, ctx, D, 0x100340, efl f', ic + 11⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (ctx.add 96) 4 (bsw Nh)) (ctx.add 100) 4 (bsw Nl))
        (U.add 20) 4 1) (U.add 16) 4 0x100224 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- `num = 0`; `OPENSSL_cleanse(data, 64)`. -/
theorem fin_g (H : CMem) (U ctx D eax ecx edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, D, 0x100224, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 12, ebp, ctx, D, 0x1011d0, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (ctx.add 104) 4 0) (U.add 20) 4 64) (U.add 16) 4 D)
        (U.add 12) 4 0x100236 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- `md_len = 32`. -/
theorem fin_h32 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (hm : rdRaw H.get (ctx.add 108) 4 = 32) :
    ∃ f' : UInt32,
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, U.add 16, ebp, ctx, edi, 0x100236, efl f, ic⟩ =
        some ⟨H.get, eax, 32, edx, ebx, U.add 24, ebp, ctx, edi, 0x100253, efl f', ic + 8⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- `md_len = 28`. -/
theorem fin_h28 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (hm : rdRaw H.get (ctx.add 108) 4 = 28) :
    ∃ f' : UInt32,
      exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, U.add 16, ebp, ctx, edi, 0x100236, efl f, ic⟩ =
        some ⟨H.get, eax, 28, edx, ebx, U.add 24, ebp, ctx, edi, 0x10029a, efl f', ic + 6⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
