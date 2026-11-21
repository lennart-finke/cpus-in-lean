import Solutions.OpensslChacha20.Pro
/-!
# A block of `ChaCha20_ctr32`, after `chacha20_core`

`0x1000c6`: `xor %eax,%eax` and padding up to the xor loop (`xorStart_run`); `0x1000e1`: advance the
pointers, increment the block counter (the word at `C + 192`), subtract the block length and loop
(`blockEnd_more`) or leave (`blockEnd_last`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem xorStart_run (H : CMem) (C eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) :
    ∃ f' : UInt32,
      exN Image.sym_halt 9 ⟨H.get, eax, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x1000c6, efl f, ic⟩ =
        some ⟨H.get, 0, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x1000d0, efl f', ic + 9⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, rfl⟩

theorem blockEnd_more (H : CMem) (C eax ecx edx rem inp out n f ctr : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (hctr : rdRaw H.get (C.add 192) 4 = ctr) (h : rem.toNat ≠ n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, n, 0x1000e1, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, UInt32.sub rem n, C.add 144, UInt32.add inp n, UInt32.add out n, n,
          0x1000b0, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (C.add 192) 4 (UInt32.add ctr 1) := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, _, rfl, rfl⟩

theorem blockEnd_last (H : CMem) (C eax ecx edx rem inp out n f ctr : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (hctr : rdRaw H.get (C.add 192) 4 = ctr) (h : rem.toNat = n.toNat) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, n, 0x1000e1, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, UInt32.sub rem n, C.add 144, UInt32.add inp n, UInt32.add out n, n,
          0x1000ed, efl f', ic + 5⟩ ∧
      H'.get = wrBytes H.get (C.add 192) 4 (UInt32.add ctr 1) := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, _, rfl, rfl⟩

end Solutions.OpensslChacha20
