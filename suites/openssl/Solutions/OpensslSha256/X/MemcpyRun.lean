import Solutions.OpensslSha256.X.MemsetRun
/-!
# The instructions of `memcpy` (`0x1011f0`)

`push %ebx; push %esi; mov 0x14(%esp),%ecx; mov 0xc(%esp),%eax; test %ecx,%ecx; je;
mov 0x10(%esp),%edx; xor %esi,%esi; nop×12`, the loop `movzbl (%edx,%esi),%ebx; movb %bl,(%eax,%esi);
inc %esi; cmp %esi,%ecx; jne`, then `pop %esi; pop %ebx; ret`. The stack pointer at the entry is
`U.add 8` (the return address there, the arguments above it).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem memcpy_head (H : CMem) (U dst src n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 24 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 24 ≤ 1048576)
    (hdst : rdRaw H.get (U.add 12) 4 = dst) (hsrc : rdRaw H.get (U.add 16) 4 = src)
    (hn : rdRaw H.get (U.add 20) 4 = n) (hn0 : n.toNat ≠ 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 20 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, esi, edi, 0x1011f0, efl f, ic⟩ =
        some ⟨H'.get, dst, n, src, ebx, U, ebp, 0, edi, 0x101210, efl f', ic + 20⟩ ∧
      H'.get = wrBytes (wrBytes H.get (U.add 4) 4 ebx) U 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memcpy_zero (H : CMem) (U dst n ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 24 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 24 ≤ 1048576) (hra : rdRaw H.get (U.add 8) 4 = ra)
    (hdst : rdRaw H.get (U.add 12) 4 = dst) (hn : rdRaw H.get (U.add 20) 4 = n) (hn0 : n.toNat = 0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, esi, edi, 0x1011f0, efl f, ic⟩ =
        some ⟨H'.get, dst, n, edx, ebx, U.add 12, ebp, esi, edi, ra, efl f', ic + 9⟩ ∧
      H'.get = wrBytes (wrBytes H.get (U.add 4) 4 ebx) U 4 esi := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memcpy_cont (H : CMem) (U dst src n i ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hd : dst.toNat + n.toNat ≤ H.get.size)
    (hdc : 1048576 + 4944 ≤ dst.toNat ∨ dst.toNat + n.toNat ≤ 1048576)
    (hs : src.toNat + n.toNat ≤ H.get.size)
    (hsc : 1048576 + 4944 ≤ src.toNat ∨ src.toNat + n.toNat ≤ 1048576) (hi : i.toNat + 1 < n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, dst, n, src, ebx, U, ebp, i, edi, 0x101210, efl f, ic⟩ =
        some ⟨H'.get, dst, n, src, rdRaw H.get (src.add i) 1, U, ebp, i.add 1, edi, 0x101210, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (dst.add i) 1 (UInt32.land (rdRaw H.get (src.add i) 1) 255) := by
  ex_run
  exact ⟨_, _, rfl, rfl⟩

theorem memcpy_exit (H : CMem) (U dst src n i ebx ebp edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hd : dst.toNat + n.toNat ≤ H.get.size)
    (hdc : 1048576 + 4944 ≤ dst.toNat ∨ dst.toNat + n.toNat ≤ 1048576)
    (hs : src.toNat + n.toNat ≤ H.get.size)
    (hsc : 1048576 + 4944 ≤ src.toNat ∨ src.toNat + n.toNat ≤ 1048576) (hi : i.toNat + 1 = n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, dst, n, src, ebx, U, ebp, i, edi, 0x101210, efl f, ic⟩ =
        some ⟨H'.get, dst, n, src, rdRaw H.get (src.add i) 1, U, ebp, i.add 1, edi, 0x10121c, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (dst.add i) 1 (UInt32.land (rdRaw H.get (src.add i) 1) 255) := by
  ex_run
  exact ⟨_, _, rfl, rfl⟩

theorem memcpy_tail (H : CMem) (U ra s1 s2 eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 24 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 24 ≤ 1048576)
    (h1 : rdRaw H.get U 4 = s1) (h2 : rdRaw H.get (U.add 4) 4 = s2) (hra : rdRaw H.get (U.add 8) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, ebx, U, ebp, esi, edi, 0x10121c, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, s2, U.add 12, ebp, s1, edi, ra, efl f', ic + 3⟩ := by
  ex_run
  exact ⟨_, rfl⟩

end Solutions.ShaX
