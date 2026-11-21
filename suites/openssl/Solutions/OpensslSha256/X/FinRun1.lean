import Solutions.OpensslSha256.X.Bswap
import Solutions.OpensslSha256.X.UpdRun1
/-!
# The instructions of `SHA256_Final` (`0x1001b0`): the padding byte, the branch, the first block of a two-block padding, the length block's zeros

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

/-- The `0x80` byte; the padding fits in this block. -/
theorem fin_a1 (H : CMem) (U ctx n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (h1 : rdRaw H.get (U.add 44) 4 = ctx) (hn : rdRaw H.get (ctx.add 104) 4 = n) (hn64 : n.toNat < 64)
    (hlt : (n.add 1).toNat < 57) :
    ∃ (H' : CMem) (f' N1 D : UInt32),
      exN Image.sym_halt 10 ⟨H.get, eax, ecx, edx, ebx, U.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩ =
        some ⟨H'.get, N1, n, edx, ebx, U.add 24, ebp, ctx, D, 0x1001ef, efl f', ic + 10⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 32) 4 ebx) (U.add 28) 4 edi) (U.add 24) 4 esi)
        ((ctx.add n).add 40) 1 128 ∧ N1 = n.add 1 ∧ D = ctx.add 40 := by
  ex_run
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩

/-- The `0x80` byte; the padding needs another block. -/
theorem fin_a2 (H : CMem) (U ctx n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 48 ≤ ctx.toNat)
    (h1 : rdRaw H.get (U.add 44) 4 = ctx) (hn : rdRaw H.get (ctx.add 104) 4 = n) (hn64 : n.toNat < 64)
    (hlt : ¬ (n.add 1).toNat < 57) :
    ∃ (H' : CMem) (f' N1 D : UInt32),
      exN Image.sym_halt 10 ⟨H.get, eax, ecx, edx, ebx, U.add 36, ebp, esi, edi, 0x1001b0, efl f, ic⟩ =
        some ⟨H'.get, N1, n, edx, ebx, U.add 24, ebp, ctx, D, 0x1001ca, efl f', ic + 10⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 32) 4 ebx) (U.add 28) 4 edi) (U.add 24) 4 esi)
        ((ctx.add n).add 40) 1 128 ∧ N1 = n.add 1 ∧ D = ctx.add 40 := by
  ex_run
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩

/-- `memset(data + n + 1, 0, 63 - n)`. -/
theorem fin_b (H : CMem) (U ctx n N1 D edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576) :
    ∃ (H' : CMem) (f' A C : UInt32),
      exN Image.sym_halt 7 ⟨H.get, N1, n, edx, ebx, U.add 24, ebp, ctx, D, 0x1001ca, efl f, ic⟩ =
        some ⟨H'.get, A, n, C, ebx, U.add 8, ebp, ctx, D, 0x101220, efl f', ic + 7⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 20) 4 C) (U.add 16) 4 0) (U.add 12) 4 A)
        (U.add 8) 4 0x1001dc ∧ A = N1 + D ∧ C = 63 - n := by
  ex_run
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩
  · first | rfl | exact Solutions.Exec.addF_fst _ _
  · first | rfl | exact Solutions.Exec.subF_fst _ _

/-- The block function on the buffer. -/
theorem fin_c (H : CMem) (U ctx D eax ecx edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 12, ebp, ctx, D, 0x1001dc, efl f, ic⟩ =
        some ⟨H'.get, eax, ctx, D, ebx, U.add 16, ebp, ctx, D, 0x100340, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes H.get (U.add 20) 4 1) (U.add 16) 4 0x1001ea := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- `n = 0` for the length block. -/
theorem fin_d (H : CMem) (U eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576) :
    ∃ (f' Z : UInt32),
      exN Image.sym_halt 2 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, esi, edi, 0x1001ea, efl f, ic⟩ =
        some ⟨H.get, Z, ecx, edx, ebx, U.add 24, ebp, esi, edi, 0x1001ef, efl f', ic + 2⟩ ∧ Z = 0 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  first | rfl | exact UInt32.xor_self _ | simp

/-- `memset(data + k, 0, 56 - k)`; `ebx = md`. -/
theorem fin_e (H : CMem) (U ctx out k D ecx edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 48 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 48 ≤ 1048576)
    (ho : rdRaw H.get (U.add 40) 4 = out) :
    ∃ (H' : CMem) (f' A C : UInt32),
      exN Image.sym_halt 8 ⟨H.get, k, ecx, edx, ebx, U.add 24, ebp, ctx, D, 0x1001ef, efl f, ic⟩ =
        some ⟨H'.get, k, A, C, out, U.add 8, ebp, ctx, D, 0x101220, efl f', ic + 8⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 20) 4 C) (U.add 16) 4 0) (U.add 12) 4 A)
        (U.add 8) 4 0x100206 ∧ A = D + k ∧ C = 56 - k := by
  ex_run
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩
  · first | rfl | exact Solutions.Exec.addF_fst _ _
  · first | rfl | exact Solutions.Exec.subF_fst _ _

end Solutions.ShaX
