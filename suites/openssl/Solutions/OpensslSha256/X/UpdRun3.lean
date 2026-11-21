import Solutions.OpensslSha256.X.ShrZF
/-!
# The instructions of `SHA256_Update`: after the first block: clear the buffer; whole blocks; the tail copy; the epilogues
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- After the first block: advance past the bytes copied, `num = 0`, `memset(data, 0, 64)`. -/
theorem upd_b3 (H : CMem) (U ctx msg len B eax ecx edx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 56 ≤ ctx.toNat) :
    ∃ (H' : CMem) (f' L' P' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, B, U.add 20, len, ctx, msg, 0x10014d, efl f, ic⟩ =
        some ⟨H'.get, ctx.add 40, ecx, edx, B, U.add 8, L', ctx, P', 0x101220, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes H.get (ctx.add 104) 4 0) (U.add 20) 4 64) (U.add 16) 4 0)
        (U.add 12) 4 (ctx.add 40)) (U.add 8) 4 0x100168 ∧ L' = len - B ∧ P' = msg + B := by
  ex_run
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩
  · first | rfl | exact Solutions.Exec.subF_fst _ _
  · first | rfl | exact Solutions.Exec.addF_fst _ _

theorem upd_b4 (H : CMem) (U eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576) :
    ∃ f' : UInt32,
      exN Image.sym_halt 1 ⟨H.get, eax, ecx, edx, ebx, U.add 12, ebp, esi, edi, 0x100168, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, 0x10016b, efl f', ic + 1⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- Fewer than 64 bytes left. -/
theorem upd_c1z (H : CMem) (U L eax ecx edx ebx esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hq : (UInt32.shiftRight L 6).toNat = 0) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 24, L, esi, edi, 0x10016b, efl f, ic⟩ =
        some ⟨H.get, UInt32.shiftRight L 6, ecx, edx, ebx, U.add 24, L, esi, edi, 0x100189, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- At least 64 bytes left. -/
theorem upd_c1n (H : CMem) (U L eax ecx edx ebx esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hq : (UInt32.shiftRight L 6).toNat ≠ 0) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U.add 24, L, esi, edi, 0x10016b, efl f, ic⟩ =
        some ⟨H.get, UInt32.shiftRight L 6, ecx, edx, ebx, U.add 24, L, esi, edi, 0x100172, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- The call of the block function on the whole blocks of the chunk. -/
theorem upd_c2 (H : CMem) (U Q ctx p ecx edx ebx ebp f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, Q, ecx, edx, ebx, U.add 24, ebp, ctx, p, 0x100172, efl f, ic⟩ =
        some ⟨H'.get, Q, ctx, p, ebx, U.add 16, ebp, ctx, p, 0x100340, efl f', ic + 4⟩ ∧
      H'.get = wrBytes (wrBytes H.get (U.add 20) 4 Q) (U.add 16) 4 0x10017c := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- After the blocks: advance the pointer, keep `len % 64`. -/
theorem upd_c3 (H : CMem) (U L p eax ecx edx ebx esi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576) :
    ∃ (f' A R P' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, L, esi, p, 0x10017c, efl f, ic⟩ =
        some ⟨H.get, A, ecx, edx, ebx, U.add 24, R, esi, P', 0x100189, efl f', ic + 5⟩ ∧
      A = L &&& 4294967232 ∧ R = L &&& 63 ∧ P' = p + (L &&& 4294967232) := by
  ex_run
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · first | rfl | exact Solutions.Exec.addF_fst _ _

/-- No tail: the epilogue. -/
theorem upd_dz (H : CMem) (U r sesi sedi sebx sebp ra eax ecx edx ebx esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (s0 : rdRaw H.get (U.add 24) 4 = sesi) (s1 : rdRaw H.get (U.add 28) 4 = sedi)
    (s2 : rdRaw H.get (U.add 32) 4 = sebx) (s3 : rdRaw H.get (U.add 36) 4 = sebp) (s4 : rdRaw H.get (U.add 40) 4 = ra)
    (hr : r.toNat = 0) :
    ∃ f' : UInt32,
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, U.add 24, r, esi, edi, 0x100189, efl f, ic⟩ =
        some ⟨H.get, 1, ecx, edx, sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic + 8⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- A tail of `r` bytes: `num = r`, `memcpy(data, p, r)`. -/
theorem upd_dn (H : CMem) (U ctx r p eax ecx edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (hcU : ctx.toNat + 112 ≤ U.toNat ∨ U.toNat + 56 ≤ ctx.toNat)
    (hr : r.toNat ≠ 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, U.add 24, r, ctx, p, 0x100189, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 8, r, ctx.add 40, p, 0x1011f0, efl f', ic + 8⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes (wrBytes H.get (ctx.add 104) 4 r) (U.add 20) 4 r) (U.add 16) 4 p)
        (U.add 12) 4 (ctx.add 40)) (U.add 8) 4 0x10019b := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- After the tail copy: the epilogue. -/
theorem upd_d3 (H : CMem) (U sesi sedi sebx sebp ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (s0 : rdRaw H.get (U.add 24) 4 = sesi) (s1 : rdRaw H.get (U.add 28) 4 = sedi)
    (s2 : rdRaw H.get (U.add 32) 4 = sebx) (s3 : rdRaw H.get (U.add 36) 4 = sebp) (s4 : rdRaw H.get (U.add 40) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 7 ⟨H.get, eax, ecx, edx, ebx, U.add 12, ebp, esi, edi, 0x10019b, efl f, ic⟩ =
        some ⟨H.get, 1, ecx, edx, sebx, U.add 44, sebp, sesi, sedi, ra, efl f', ic + 7⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
