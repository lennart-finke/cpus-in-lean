import Solutions.OpensslChacha20.Call
/-!
# A block of `ChaCha20_ctr32`, up to the copy loop of `memcpy`, and back from it

`0x1000b0`: `n = min(64, remaining)` into EDI (`blockLen_lt`, `blockLen_ge`); `0x1000bb`: the call of
`chacha20_core(C + 208, C + 144)` and its call of `memcpy(C + 60, C + 144, 64)` up to the copy loop
(`call_run`); `0x10042c`: the return from `memcpy` (`memcpyRet_run`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem blockLen_lt (H : CMem) (C eax ecx edx rem inp out edi f : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (h : rem.toNat < 64) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, edi, 0x1000b0, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, rem, 0x1000bb, efl f', ic + 3⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  conv in exN _ _ _ => cbv
  exact ⟨_, rfl⟩

theorem blockLen_ge (H : CMem) (C eax ecx edx rem inp out edi f : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (h : 64 ≤ rem.toNat) :
    ∃ f' : UInt32,
      exN Image.sym_halt 3 ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, edi, 0x1000b0, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, 64, 0x1000bb, efl f', ic + 3⟩ := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  conv in exN _ _ _ => cbv
  exact ⟨_, rfl⟩

/-- The words the calls leave on the stack. -/
def CallFrame (M : ByteArray) (C rem inp out n : UInt32) : Prop :=
  rdRaw M (C.add 20) 4 = C.add 144 ∧ rdRaw M (C.add 36) 4 = C.add 208 ∧
  rdRaw M (C.add 124) 4 = out ∧ rdRaw M (C.add 128) 4 = n ∧ rdRaw M (C.add 132) 4 = rem ∧
  rdRaw M (C.add 136) 4 = inp ∧ rdRaw M (C.add 140) 4 = 0x1000c6 ∧
  rdRaw M (C.add 4294967276) 4 = rem ∧ rdRaw M (C.add 4294967272) 4 = out ∧
  rdRaw M (C.add 4294967280) 4 = 0x10011c

theorem addrCU {C U : UInt32} (hU : U.toNat + 24 = C.toNat) (k m : UInt32) (hkm : (k.toNat + 24) % 2 ^ 32 = m.toNat) :
    C.add k = U.add m := by
  apply UInt32.toNat_inj.1
  rw [toNat_uadd, toNat_uadd]
  have := C.toNat_lt
  have := k.toNat_lt
  omega

theorem addrCU0 {C U : UInt32} (hU : U.toNat + 24 = C.toNat) : C.add 4294967272 = U := by
  have := addrCU hU 4294967272 0 (by decide)
  rw [this]; exact UInt32.add_zero U

theorem base_U {C : UInt32} (hlo : 24 ≤ C.toNat) : ∃ U : UInt32, U.toNat + 24 = C.toNat := by
  refine ⟨C - 24, ?_⟩
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
  simp; omega

theorem call_run (H : CMem) (C eax ecx edx rem inp out n f : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 35 ⟨H.get, eax, ecx, edx, rem, C.add 144, inp, out, n, 0x1000bb, efl f, ic⟩ =
        some ⟨H'.get, C.add 60, 64, C.add 144, rem, C.add 4294967272, inp, 0, n, 0x100420, efl f', ic + 35⟩ ∧
      CallFrame H'.get C rem inp out n ∧
      AgreeOn (fun a => C.toNat - 24 ≤ a ∧ a < C.toNat + 144) H.get H'.get := by
  obtain ⟨U, hU⟩ := base_U hS.lo
  obtain ⟨H', f', e, q164, q160, q156, q152, q148, q60, q20, q44, q16, q12, q8, q4, q0, a⟩ :=
    callU_run H C f eax ecx edx rem U inp out n ic hS hU
  unfold CallFrame
  rw [addrCU hU 144 168 (by decide), addrCU hU 60 84 (by decide),
    addrCU0 hU, addrCU hU 20 44 (by decide),
    addrCU hU 36 60 (by decide), addrCU hU 208 232 (by decide),
    addrCU hU 124 148 (by decide), addrCU hU 128 152 (by decide),
    addrCU hU 132 156 (by decide), addrCU hU 136 160 (by decide),
    addrCU hU 140 164 (by decide),
    addrCU hU 4294967276 4 (by decide),
    addrCU hU 4294967280 8 (by decide)]
  exact ⟨H', f', e, ⟨q44, q60, q148, q152, q156, q160, q164, q4, q0, q8⟩,
    a.mono (fun x h => by (try simp only [] at h ⊢) <;> omega)⟩

theorem memcpyRet_run (H : CMem) (C eax ecx edx ebx ebp esi edi f rem out : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C) (h1 : rdRaw H.get (C.add 4294967272) 4 = out)
    (h2 : rdRaw H.get (C.add 4294967276) 4 = rem) (h3 : rdRaw H.get (C.add 4294967280) 4 = 0x10011c) :
    ∃ f' : UInt32,
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, C.add 4294967272, ebp, esi, edi, 0x10042c, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, rem, C, ebp, out, edi, 0x10011f, efl f', ic + 4⟩ := by
  obtain ⟨U, hU⟩ := base_U hS.lo
  rw [addrCU0 hU] at h1 ⊢
  rw [addrCU hU 4294967276 4 (by decide)] at h2
  rw [addrCU hU 4294967280 8 (by decide)] at h3
  obtain ⟨H', f', e, a⟩ := retU_run H C f eax ecx edx ebx U ebp esi edi out rem ic hS hU h1 h2 h3
  have hC : C = U.add 24 := by
    have := C.toNat_lt
    apply UInt32.toNat_inj.1; rw [toNat_uadd]; simp; omega
  have hH : H'.get = H.get := by
    apply bytes_ext a.1 (fun i hi => a.2 i (by rw [a.1] at hi; exact hi) (fun h => h))
  rw [hH] at e
  rw [hC]
  exact ⟨f', e⟩

end Solutions.OpensslChacha20
