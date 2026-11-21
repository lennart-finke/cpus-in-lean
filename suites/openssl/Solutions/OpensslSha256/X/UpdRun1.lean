import Solutions.OpensslSha256.X.Arith
/-!
# The instructions of `SHA256_Update` (`0x1000e0`): entry, bit count, branch on `num`

The stack pointer at the entry is `U.add 40` (return address there, then `ctx`, `data`, `len`).
`upd_zero`: `len = 0`: the four pushes, `test`, `je` to the epilogue, `eax = 1`, the pops and the
return. `upd_p1`: `len ≠ 0`: the pushes and the argument loads. `upd_p2n`/`upd_p2z`: the bit count
(`add`/`adc` on `Nl`/`Nh`), the load of `num` and the branch on it.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem upd_zero (H : CMem) (U ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hra : rdRaw H.get (U.add 40) 4 = ra) (hl : rdRaw H.get (U.add 52) 4 = 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 13 ⟨H.get, eax, ecx, edx, ebx, U.add 40, ebp, esi, edi, 0x1000e0, efl f, ic⟩ =
        some ⟨H'.get, 1, ecx, edx, ebx, U.add 44, ebp, esi, edi, ra, efl f', ic + 13⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 36) 4 ebp) (U.add 32) 4 ebx) (U.add 28) 4 edi)
        (U.add 24) 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem upd_p1 (H : CMem) (U ctx msg len eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (h1 : rdRaw H.get (U.add 44) 4 = ctx) (h2 : rdRaw H.get (U.add 48) 4 = msg)
    (h3 : rdRaw H.get (U.add 52) 4 = len) (hl : len.toNat ≠ 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, ebx, U.add 40, ebp, esi, edi, 0x1000e0, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, ebx, U.add 24, len, ctx, msg, 0x1000f8, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 36) 4 ebp) (U.add 32) 4 ebx) (U.add 28) 4 edi)
        (U.add 24) 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem upd_p2n (H : CMem) (U ctx msg len Nl Nh num eax ecx edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (h4 : rdRaw H.get (ctx.add 32) 4 = Nl) (h5 : rdRaw H.get (ctx.add 36) 4 = Nh)
    (h6 : rdRaw H.get (ctx.add 104) 4 = num) (hn : num.toNat ≠ 0) :
    ∃ (H' : CMem) (f' eax' NL NH : UInt32),
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, U.add 24, len, ctx, msg, 0x1000f8, efl f, ic⟩ =
        some ⟨H'.get, eax', num, edx, ebx, U.add 24, len, ctx, msg, 0x100111, efl f', ic + 8⟩ ∧
      H'.get = wrBytes (wrBytes H.get (ctx.add 32) 4 NL) (ctx.add 36) 4 NH ∧
      NL.toNat = (Nl.toNat + 8 * len.toNat) % 2 ^ 32 ∧
      NH.toNat = (Nh.toNat + len.toNat / 2 ^ 29 % 2 ^ 32 +
        (if Nl.toNat % 2 ^ 32 + 8 * len.toNat % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32 := by
  ex_run
  exact ⟨_, _, _, _, _, rfl, rfl, nl_toNat Nl len, nh_toNat Nl Nh len⟩

theorem upd_p2z (H : CMem) (U ctx msg len Nl Nh num eax ecx edx ebx f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 56 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 56 ≤ 1048576)
    (hc : ctx.toNat + 112 ≤ H.get.size) (hcc : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576)
    (h4 : rdRaw H.get (ctx.add 32) 4 = Nl) (h5 : rdRaw H.get (ctx.add 36) 4 = Nh)
    (h6 : rdRaw H.get (ctx.add 104) 4 = num) (hn : num.toNat = 0) :
    ∃ (H' : CMem) (f' eax' NL NH : UInt32),
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, U.add 24, len, ctx, msg, 0x1000f8, efl f, ic⟩ =
        some ⟨H'.get, eax', num, edx, ebx, U.add 24, len, ctx, msg, 0x10016b, efl f', ic + 8⟩ ∧
      H'.get = wrBytes (wrBytes H.get (ctx.add 32) 4 NL) (ctx.add 36) 4 NH ∧
      NL.toNat = (Nl.toNat + 8 * len.toNat) % 2 ^ 32 ∧
      NH.toNat = (Nh.toNat + len.toNat / 2 ^ 29 % 2 ^ 32 +
        (if Nl.toNat % 2 ^ 32 + 8 * len.toNat % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32 := by
  ex_run
  exact ⟨_, _, _, _, _, rfl, rfl, nl_toNat Nl len, nh_toNat Nl Nh len⟩

end Solutions.ShaX
