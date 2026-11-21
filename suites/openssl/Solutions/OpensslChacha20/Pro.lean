import Solutions.OpensslChacha20.Frame2
import Solutions.OpensslChacha20.Hyp
/-!
# `ChaCha20_ctr32`: entry, empty input, epilogue

Addresses are relative to `C`, the frame of `chacha20_core` in every block: the caller's stack
pointer is `C + 288`, `ChaCha20_ctr32`'s frame (the state matrix and the keystream block) is at
`C + 144`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- The stack frames `[C - 24, C + 312)` are inside memory and outside the code. -/
structure StackOk (size : Nat) (C : UInt32) : Prop where
  sz : size ≤ 4273995776
  lo : 24 ≤ C.toNat
  fit : C.toNat + 312 ≤ size
  code : 1049648 + 24 ≤ C.toNat ∨ C.toNat + 312 ≤ 1048576

/-- An empty input: `test %ebx,%ebx; je` to the epilogue. -/
theorem empty_run (H : CMem) (C eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (h0 : ebx.toNat = 0) :
    ∃ f' : UInt32,
      exN Image.sym_halt 2 ⟨H.get, eax, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x100090, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x1000ed, efl f', ic + 2⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, rfl⟩

/-- A non-empty input: the input and output pointers into `ebp` and `esi`, to the block loop. -/
theorem nonempty_run (H : CMem) (C eax ecx edx ebx ebp esi edi f out inp : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (h0 : ebx.toNat ≠ 0)
    (hout : rdRaw H.get (C.add 292) 4 = out) (hinp : rdRaw H.get (C.add 296) 4 = inp) :
    ∃ f' : UInt32,
      exN Image.sym_halt 18 ⟨H.get, eax, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x100090, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, C.add 144, inp, out, edi, 0x1000b0, efl f', ic + 18⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, rfl⟩

/-- The epilogue: restore the callee-saved registers and return. -/
theorem epilogue_run (H : CMem) (C eax ecx edx ebx ebp esi edi f sesi sedi sebx sebp : UInt32)
    (ic : UInt64) (hS : StackOk H.get.size C)
    (h1 : rdRaw H.get (C.add 272) 4 = sesi) (h2 : rdRaw H.get (C.add 276) 4 = sedi)
    (h3 : rdRaw H.get (C.add 280) 4 = sebx) (h4 : rdRaw H.get (C.add 284) 4 = sebp)
    (h5 : rdRaw H.get (C.add 288) 4 = 0x10042F) :
    ∃ f' : UInt32,
      exN Image.sym_halt 6 ⟨H.get, eax, ecx, edx, ebx, C.add 144, ebp, esi, edi, 0x1000ed, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, sebx, C.add 292, sebp, sesi, sedi, 0x10042F, efl f', ic + 6⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  exact ⟨_, rfl⟩

end Solutions.OpensslChacha20
