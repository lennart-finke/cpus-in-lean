import Solutions.OpensslSha256.X.Bswap
import Solutions.OpensslSha256.X.UpdRun1
/-!
# The instructions of `SHA256_Final`: the digest words, byte-swapped, and the return

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

/-- Words 0-2 of a 32-byte digest. -/
theorem fin_o1 (H : CMem) (U ctx out w0 w1 w2 eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 32 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 32 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 32 ≤ ctx.toNat)
    (hoU : out.toNat + 32 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g0 : rdRaw H.get ctx 4 = w0) (g1 : rdRaw H.get (ctx.add 4) 4 = w1) (g2 : rdRaw H.get (ctx.add 8) 4 = w2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x100253, efl f, ic⟩ =
        some ⟨H'.get, bsw w2, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x100269, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes H.get out 4 (bsw w0)) (out.add 4) 4 (bsw w1)) (out.add 8) 4 (bsw w2) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Words 3-5 of a 32-byte digest. -/
theorem fin_o2 (H : CMem) (U ctx out w3 w4 w5 eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 32 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 32 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 32 ≤ ctx.toNat)
    (hoU : out.toNat + 32 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g3 : rdRaw H.get (ctx.add 12) 4 = w3) (g4 : rdRaw H.get (ctx.add 16) 4 = w4) (g5 : rdRaw H.get (ctx.add 20) 4 = w5) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x100269, efl f, ic⟩ =
        some ⟨H'.get, bsw w5, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x100281, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes H.get (out.add 12) 4 (bsw w3)) (out.add 16) 4 (bsw w4)) (out.add 20) 4 (bsw w5) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Words 0-2 of a 28-byte digest. -/
theorem fin_p1 (H : CMem) (U ctx out w0 w1 w2 eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 28 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 28 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 28 ≤ ctx.toNat)
    (hoU : out.toNat + 28 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g0 : rdRaw H.get ctx 4 = w0) (g1 : rdRaw H.get (ctx.add 4) 4 = w1) (g2 : rdRaw H.get (ctx.add 8) 4 = w2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x10029a, efl f, ic⟩ =
        some ⟨H'.get, bsw w2, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x1002b0, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes H.get out 4 (bsw w0)) (out.add 4) 4 (bsw w1)) (out.add 8) 4 (bsw w2) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Words 3-5 of a 28-byte digest. -/
theorem fin_p2 (H : CMem) (U ctx out w3 w4 w5 eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 28 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 28 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 28 ≤ ctx.toNat)
    (hoU : out.toNat + 28 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g3 : rdRaw H.get (ctx.add 12) 4 = w3) (g4 : rdRaw H.get (ctx.add 16) 4 = w4) (g5 : rdRaw H.get (ctx.add 20) 4 = w5) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x1002b0, efl f, ic⟩ =
        some ⟨H'.get, bsw w5, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x1002c8, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes H.get (out.add 12) 4 (bsw w3)) (out.add 16) 4 (bsw w4)) (out.add 20) 4 (bsw w5) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Words 6, 7 of a 32-byte digest; `eax = 1`, the pops, the return. -/
theorem fin_o3 (H : CMem) (U ctx out w6 w7 sesi sedi sebx ra eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 32 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 32 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 32 ≤ ctx.toNat)
    (hoU : out.toNat + 32 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g6 : rdRaw H.get (ctx.add 24) 4 = w6) (g7 : rdRaw H.get (ctx.add 28) 4 = w7)
    (s0 : rdRaw H.get (U.add 24) 4 = sesi) (s1 : rdRaw H.get (U.add 28) 4 = sedi)
    (s2 : rdRaw H.get (U.add 32) 4 = sebx) (s3 : rdRaw H.get (U.add 36) 4 = ra) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 11 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x100281, efl f, ic⟩ =
        some ⟨H'.get, 1, ecx, edx, sebx, U.add 40, ebp, sesi, sedi, ra, efl f', ic + 11⟩ ∧
      H'.get = wrBytes (wrBytes H.get (out.add 24) 4 (bsw w6)) (out.add 28) 4 (bsw w7) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Word 6 of a 28-byte digest; `eax = 1`, the pops, the return. -/
theorem fin_p3 (H : CMem) (U ctx out w6 sesi sedi sebx ra eax ecx edx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (ho : out.toNat + 28 ≤ H.get.size) (hoc : 1048576 + 4944 ≤ out.toNat ∨ out.toNat + 28 ≤ 1048576)
    (hco : ctx.toNat + 112 ≤ out.toNat ∨ out.toNat + 28 ≤ ctx.toNat)
    (hoU : out.toNat + 28 ≤ U.toNat ∨ U.toNat + 48 ≤ out.toNat)
    (g6 : rdRaw H.get (ctx.add 24) 4 = w6)
    (s0 : rdRaw H.get (U.add 24) 4 = sesi) (s1 : rdRaw H.get (U.add 28) 4 = sedi)
    (s2 : rdRaw H.get (U.add 32) 4 = sebx) (s3 : rdRaw H.get (U.add 36) 4 = ra) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, out, U.add 24, ebp, ctx, edi, 0x1002c8, efl f, ic⟩ =
        some ⟨H'.get, 1, ecx, edx, sebx, U.add 40, ebp, sesi, sedi, ra, efl f', ic + 9⟩ ∧
      H'.get = wrBytes H.get (out.add 24) 4 (bsw w6) := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

end Solutions.ShaX
