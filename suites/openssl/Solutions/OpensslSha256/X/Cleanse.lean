import Solutions.OpensslSha256.X.MemCall
/-!
# `OPENSSL_cleanse(ptr, len)` (`0x1011d0`)

`movl 0x10134c,%eax` (the pointer `memset_func`, which holds `memset`); push `len`, `0`, `ptr`;
`call *%eax`; `addl $0xc,%esp; ret`. The stack pointer at the entry is `U.add 20`.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem cleanse_head (H : CMem) (U p len eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576)
    (hp : rdRaw H.get (U.add 24) 4 = p) (hl : rdRaw H.get (U.add 28) 4 = len)
    (hfn : rdRaw H.get 0x10134c 4 = 0x101220) (hfit : 1048576 + 4944 ≤ H.get.size) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, esi, edi, 0x1011d0, efl f, ic⟩ =
        some ⟨H'.get, 0x101220, ecx, edx, ebx, U.add 4, ebp, esi, edi, 0x101220, efl f', ic + 5⟩ ∧
      H'.get = wrBytes (wrBytes (wrBytes (wrBytes H.get (U.add 16) 4 len) (U.add 12) 4 0) (U.add 8) 4 p)
        (U.add 4) 4 0x1011e1 := by
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  rfl

theorem memset_func (H : CMem) : rdRaw H.get 0x10134c 4 = 0x101220 := by
  have hf : 1048576 + 4944 ≤ H.get.size := H.fits
  have hb : (1053516 : UInt32).toNat = 1053516 := rfl
  have e0 : H.get.get! 1053516 = Image.byte 4940 := H.ok 4940 (by decide)
  have e1 : H.get.get! (1053516 + 1) = Image.byte 4941 := H.ok 4941 (by decide)
  have e2 : H.get.get! (1053516 + 2) = Image.byte 4942 := H.ok 4942 (by decide)
  have e3 : H.get.get! (1053516 + 3) = Image.byte 4943 := H.ok 4943 (by decide)
  unfold rdRaw
  rw [rdBytes4_eq (by rw [hb]; omega), hb, e0, e1, e2, e3]
  decide

theorem cleanse_tail (H : CMem) (U ra eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size)
    (hUc : 1048576 + 4944 ≤ U.toNat ∨ U.toNat + 32 ≤ 1048576) (hra : rdRaw H.get (U.add 20) 4 = ra) :
    ∃ f' : UInt32,
      exN Image.sym_halt 2 ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, esi, edi, 0x1011e1, efl f, ic⟩ =
        some ⟨H.get, eax, ecx, edx, ebx, U.add 24, ebp, esi, edi, ra, efl f', ic + 2⟩ := by
  ex_run
  exact ⟨_, rfl⟩

/-- A call of `OPENSSL_cleanse(p, len)`: the `len` bytes at `p` become zero. -/
theorem cleanse_call (H : CMem) (U ra p len eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 32 ≤ H.get.size) (hUc : OffCode U 32)
    (hra : rdRaw H.get (U.add 20) 4 = ra) (hp : rdRaw H.get (U.add 24) 4 = p) (hl : rdRaw H.get (U.add 28) 4 = len)
    (hd : p.toNat + len.toNat ≤ H.get.size) (hdc : OffCode p len.toNat)
    (hdU : p.toNat + len.toNat ≤ U.toNat ∨ U.toNat + 32 ≤ p.toNat)
    (hic : ic.toNat + 4 * len.toNat + 40 < 2 ^ 64) :
    ∃ (H' : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 4 * len.toNat + 29 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 20, ebp, esi, edi, 0x1011d0, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, U.add 24, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 20 ∨ p.toNat ≤ a ∧ a < p.toNat + len.toNat) H.get H'.get ∧
      ∀ i, i < len.toNat → H'.get.get! (p.toNat + i) = 0 := by
  have hU' := hUc
  unfold OffCode at hUc hdc
  have hfit : 1048576 + 4944 ≤ H.get.size := H.fits
  have t4 : (U.add 4).toNat = U.toNat + 4 := toNat_add_lit (k := 4) (by omega) (by decide)
  have t8 : (U.add 8).toNat = U.toNat + 8 := toNat_add_lit (k := 8) (by omega) (by decide)
  have t12 : (U.add 12).toNat = U.toNat + 12 := toNat_add_lit (k := 12) (by omega) (by decide)
  have t16 : (U.add 16).toNat = U.toNat + 16 := toNat_add_lit (k := 16) (by omega) (by decide)
  have t20 : (U.add 20).toNat = U.toNat + 20 := toNat_add_lit (k := 20) (by omega) (by decide)
  obtain ⟨H1, f1, e1, hm1⟩ := cleanse_head H U p len eax ecx edx ebx ebp esi edi f ic hsz hU hUc hp hl
    (memset_func H) hfit
  have r1 := exN_run (img := img) 5 _ _ e1 (by show ic.toNat + 5 < _; omega)
  have s16 : (wrBytes H.get (U.add 16) 4 len).size = H.get.size := size_wrBytes4 (by rw [t16]; omega)
  have s12 : (wrBytes (wrBytes H.get (U.add 16) 4 len) (U.add 12) 4 0).size = H.get.size := by
    rw [size_wrBytes4 (by rw [s16, t12]; omega), s16]
  have s8 : (wrBytes (wrBytes (wrBytes H.get (U.add 16) 4 len) (U.add 12) 4 0) (U.add 8) 4 p).size = H.get.size := by
    rw [size_wrBytes4 (by rw [s12, t8]; omega), s12]
  have hW1 : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 20 ∨ p.toNat ≤ a ∧ a < p.toNat + len.toNat) H.get H1.get := by
    rw [hm1]
    exact agreeOn_wr4 (agreeOn_wr4 (agreeOn_wr4 (agreeOn_wr4 (AgreeOn.refl _ _) (by rw [t16]; omega)
      (fun k hk => by rw [t16]; omega)) (by rw [s16, t12]; omega) (fun k hk => by rw [t12]; omega))
      (by rw [s12, t8]; omega) (fun k hk => by rw [t8]; omega)) (by rw [s8, t4]; omega) (fun k hk => by rw [t4]; omega)
  have hS1 : H1.get.size = H.get.size := hW1.1
  have g4 : rdRaw H1.get (U.add 4) 4 = 0x1011e1 := by rw [hm1]; exact rdRaw_wr4_self (by rw [s8, t4]; omega)
  have g8 : rdRaw H1.get (U.add 8) 4 = p := by
    rw [hm1, rdRaw_wr4_other (by rw [s8, t4]; omega) (by rw [s8, t8]; omega) (by rw [t4, t8]; omega)]
    exact rdRaw_wr4_self (by rw [s12, t8]; omega)
  have g12 : rdRaw H1.get (U.add 12) 4 = 0 := by
    rw [hm1, rdRaw_wr4_other (by rw [s8, t4]; omega) (by rw [s8, t12]; omega) (by rw [t4, t12]; omega),
      rdRaw_wr4_other (by rw [s12, t8]; omega) (by rw [s12, t12]; omega) (by rw [t8, t12]; omega)]
    exact rdRaw_wr4_self (by rw [s16, t12]; omega)
  have g16 : rdRaw H1.get (U.add 16) 4 = len := by
    rw [hm1, rdRaw_wr4_other (by rw [s8, t4]; omega) (by rw [s8, t16]; omega) (by rw [t4, t16]; omega),
      rdRaw_wr4_other (by rw [s12, t8]; omega) (by rw [s12, t16]; omega) (by rw [t8, t16]; omega),
      rdRaw_wr4_other (by rw [s16, t12]; omega) (by rw [s16, t16]; omega) (by rw [t12, t16]; omega)]
    exact rdRaw_wr4_self (by rw [t16]; omega)
  have hic1 : (ic + 5).toNat = ic.toNat + 5 := by rw [u64_lit 5 (by decide), u64_toNat_add (by omega)]
  obtain ⟨H2, eax2, ecx2, edx2, f2, ic2, hic2, r2, hW2, hz⟩ := memset_call H1 U 0x1011e1 p 0 len 0x101220 ecx edx ebx
    ebp esi edi f1 (ic + 5) (by rw [hS1]; exact hsz) (by rw [hS1]; omega) (by unfold OffCode; omega) g4 g8 g12 g16
    (by rw [hS1]; exact hd) (by unfold OffCode; omega) (by omega) (by rw [hic1]; omega)
  have hra2 : rdRaw H2.get (U.add 20) 4 = ra := by
    rw [rdRaw4_agree hW2 (by rw [hS1, t20]; omega) (fun k hk => by rw [t20]; omega),
      rdRaw4_agree hW1 (by rw [t20]; omega) (fun k hk => by rw [t20]; omega), hra]
  have hS2 : H2.get.size = H.get.size := by rw [hW2.1, hS1]
  obtain ⟨f3, e3⟩ := cleanse_tail H2 U ra eax2 ecx2 edx2 ebx ebp esi edi f2 ic2 (by rw [hS2]; exact hsz)
    (by rw [hS2]; exact hU) hUc hra2
  have r3 := exN_run (img := img) 2 _ _ e3 (by show ic2.toNat + 2 < _; omega)
  refine ⟨H2, eax2, ecx2, edx2, f3, ic2 + 2, ?_, r1.trans (r2.trans r3), hW1.trans (hW2.mono fun a h => ?_),
    fun i hi => by rw [hz i hi]; rfl⟩
  · rw [u64_lit 2 (by decide), u64_toNat_add (by omega)]; omega
  · rcases h with h | h
    · exact Or.inl ⟨h.1, by omega⟩
    · exact Or.inr h

end Solutions.ShaX
