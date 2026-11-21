import Solutions.OpensslSha256.X.Glue
/-!
# The instructions of `SHA256_Init` (`0x100060`) and `SHA224_Init` (`0x100000`)

Before the call of `memset(ctx, 0, 0x70)` (`_a`) and after it: the eight initial hash words (`_b1`,
`_b2`) and `md_len`, then `eax = 1` and the return (`_b3`). The stack pointer at the entry is `U.add 24`.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem init256_a (H : CMem) (U ctx eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) (hctx : rdRaw H.get (U.add 28) 4 = ctx) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, 0x100060, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 4, ebp, ctx, edi, 0x101220, efl f', ic + 6⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (U.add 20) 4 esi) (U.add 16) 4 0x70) (U.add 12) 4 0) (U.add 8) 4 ctx) (U.add 4) 4 0x10006f := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init256_b1 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, ctx, edi, 0x10006f, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x10008d, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx) 4 0x6a09e667) (ctx.add 4) 4 0xbb67ae85) (ctx.add 8) 4 0x3c6ef372) (ctx.add 12) 4 0xa54ff53a := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init256_b2 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x10008d, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x1000b0, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx.add 16) 4 0x510e527f) (ctx.add 20) 4 0x9b05688c) (ctx.add 24) 4 0x1f83d9ab) (ctx.add 28) 4 0x5be0cd19) (ctx.add 108) 4 32 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init256_b3 (H : CMem) (U ctx sv ra eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) (hsv : rdRaw H.get (U.add 20) 4 = sv) (hra : rdRaw H.get (U.add 24) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x1000b0, efl f, ic⟩ =
        some ⟨H.get, 1, ecx, edx, ebx, U.add 28, ebp, sv, edi, ra, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

theorem init224_a (H : CMem) (U ctx eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) (hctx : rdRaw H.get (U.add 28) 4 = ctx) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, 0x100000, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 4, ebp, ctx, edi, 0x101220, efl f', ic + 6⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (U.add 20) 4 esi) (U.add 16) 4 0x70) (U.add 12) 4 0) (U.add 8) 4 ctx) (U.add 4) 4 0x10000f := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init224_b1 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, ctx, edi, 0x10000f, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x10002d, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx) 4 0xc1059ed8) (ctx.add 4) 4 0x367cd507) (ctx.add 8) 4 0x3070dd17) (ctx.add 12) 4 0xf70e5939 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init224_b2 (H : CMem) (U ctx eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 32 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x10002d, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x100050, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes (H.get) (ctx.add 16) 4 0xffc00b31) (ctx.add 20) 4 0x68581511) (ctx.add 24) 4 0x64f98fa7) (ctx.add 28) 4 0xbefa4fa4) (ctx.add 108) 4 28 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem init224_b3 (H : CMem) (U ctx sv ra eax ecx edx ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) (hsv : rdRaw H.get (U.add 20) 4 = sv) (hra : rdRaw H.get (U.add 24) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, ctx, edi, 0x100050, efl f, ic⟩ =
        some ⟨H.get, 1, ecx, edx, ebx, U.add 28, ebp, sv, edi, ra, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
