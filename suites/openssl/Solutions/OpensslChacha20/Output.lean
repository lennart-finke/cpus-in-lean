import Solutions.OpensslChacha20.OutputC
/-!
# `chacha20_core`: the output words and the return

`0x10033e`–`0x1003fc`: the sixteen words of the state after the rounds (`RS.toV r`) plus the input
words `w` (at `t + 0x90`, the caller's frame) are stored at `t + 0xd0` (the caller's keystream
buffer); the saved registers are restored and the call returns to `0x1000c6`. The run is generated
in pieces (`outC_run`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem outC_run (H : CMem) (C f eax ecx edx ebx ebp esi edi s8 w0 s10 w1 sc w2 s4 w3 w4 w5 w6 w7 s20 w8 s1c w9 s34 w10 s30 w11 s0 w12 w13 s18 w14 w15 sesi sedi sebx sebp : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hs8 : rdRaw H.get (C.add 8) 4 = s8)
    (hw0 : rdRaw H.get (C.add 144) 4 = w0)
    (hs10 : rdRaw H.get (C.add 16) 4 = s10)
    (hw1 : rdRaw H.get (C.add 148) 4 = w1)
    (hsc : rdRaw H.get (C.add 12) 4 = sc)
    (hw2 : rdRaw H.get (C.add 152) 4 = w2)
    (hs4 : rdRaw H.get (C.add 4) 4 = s4)
    (hw3 : rdRaw H.get (C.add 156) 4 = w3)
    (hw4 : rdRaw H.get (C.add 160) 4 = w4)
    (hw5 : rdRaw H.get (C.add 164) 4 = w5)
    (hw6 : rdRaw H.get (C.add 168) 4 = w6)
    (hw7 : rdRaw H.get (C.add 172) 4 = w7)
    (hs20 : rdRaw H.get (C.add 32) 4 = s20)
    (hw8 : rdRaw H.get (C.add 176) 4 = w8)
    (hs1c : rdRaw H.get (C.add 28) 4 = s1c)
    (hw9 : rdRaw H.get (C.add 180) 4 = w9)
    (hs34 : rdRaw H.get (C.add 52) 4 = s34)
    (hw10 : rdRaw H.get (C.add 184) 4 = w10)
    (hs30 : rdRaw H.get (C.add 48) 4 = s30)
    (hw11 : rdRaw H.get (C.add 188) 4 = w11)
    (hs0 : rdRaw H.get C 4 = s0)
    (hw12 : rdRaw H.get (C.add 192) 4 = w12)
    (hw13 : rdRaw H.get (C.add 196) 4 = w13)
    (hs18 : rdRaw H.get (C.add 24) 4 = s18)
    (hw14 : rdRaw H.get (C.add 200) 4 = w14)
    (hw15 : rdRaw H.get (C.add 204) 4 = w15)
    (hsesi : rdRaw H.get (C.add 124) 4 = sesi)
    (hsedi : rdRaw H.get (C.add 128) 4 = sedi)
    (hsebx : rdRaw H.get (C.add 132) 4 = sebx)
    (hsebp : rdRaw H.get (C.add 136) 4 = sebp)
    (hK0 : rdRaw H.get (C.add 20) 4 = (C.add 144))
    (hK1 : rdRaw H.get (C.add 36) 4 = (C.add 208))
    (hK2 : rdRaw H.get (C.add 140) 4 = 1048774) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 61 ⟨H.get, eax, ecx, edx, ebx, C, ebp, esi, edi, 0x10033e, efl f, ic⟩ =
        some ⟨H'.get, (UInt32.add s18 w14), (UInt32.add ecx w13), (C.add 208), sebx, (C.add 144), sebp, sesi, sedi, 0x1000c6, efl f', ic + 61⟩ ∧
      rdRaw H'.get (C.add 40) 4 = esi ∧
      rdRaw H'.get (C.add 208) 4 = (UInt32.add s8 w0) ∧
      rdRaw H'.get (C.add 212) 4 = (UInt32.add s10 w1) ∧
      rdRaw H'.get (C.add 216) 4 = (UInt32.add sc w2) ∧
      rdRaw H'.get (C.add 220) 4 = (UInt32.add s4 w3) ∧
      rdRaw H'.get (C.add 224) 4 = (UInt32.add ebp w4) ∧
      rdRaw H'.get (C.add 228) 4 = (UInt32.add edi w5) ∧
      rdRaw H'.get (C.add 232) 4 = (UInt32.add esi w6) ∧
      rdRaw H'.get (C.add 236) 4 = (UInt32.add eax w7) ∧
      rdRaw H'.get (C.add 240) 4 = (UInt32.add s20 w8) ∧
      rdRaw H'.get (C.add 244) 4 = (UInt32.add s1c w9) ∧
      rdRaw H'.get (C.add 248) 4 = (UInt32.add s34 w10) ∧
      rdRaw H'.get (C.add 252) 4 = (UInt32.add s30 w11) ∧
      rdRaw H'.get (C.add 256) 4 = (UInt32.add s0 w12) ∧
      rdRaw H'.get (C.add 260) 4 = (UInt32.add ecx w13) ∧
      rdRaw H'.get (C.add 264) 4 = (UInt32.add s18 w14) ∧
      rdRaw H'.get (C.add 268) 4 = (UInt32.add ebx w15) ∧
      AgreeOn (fun a => (C.toNat ≤ a ∧ a < C.toNat + 60) ∨ (C.toNat + 208 ≤ a ∧ a < C.toNat + 272)) H.get H'.get := by
  have hS0 := hS
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  have hz0 : H.get.size = H.get.size := rfl
  obtain ⟨H1, f1, e1, p1_0, p1_1, p1_2, a1⟩ := outC_run_0 H C f (eax) (ecx) (edx) (ebx) (ebp) (esi) (edi) (s8) (w0) (s10) (w1) (ic) hS0 hs8 hw0 hs10 hw1 hK0 hK1
  have hS1 : StackOk H1.get.size C := by rw [a1.1]; exact hS0
  have hz1 : H1.get.size = H.get.size := a1.1.trans hz0
  have t1_3 : rdRaw H1.get (C.add 8) 4 = s8 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs8
  have t1_4 : rdRaw H1.get (C.add 144) 4 = w0 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw0
  have t1_5 : rdRaw H1.get (C.add 16) 4 = s10 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs10
  have t1_6 : rdRaw H1.get (C.add 148) 4 = w1 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw1
  have t1_7 : rdRaw H1.get (C.add 12) 4 = sc :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hsc
  have t1_8 : rdRaw H1.get (C.add 152) 4 = w2 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw2
  have t1_9 : rdRaw H1.get (C.add 4) 4 = s4 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs4
  have t1_10 : rdRaw H1.get (C.add 156) 4 = w3 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw3
  have t1_11 : rdRaw H1.get (C.add 160) 4 = w4 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw4
  have t1_12 : rdRaw H1.get (C.add 164) 4 = w5 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw5
  have t1_13 : rdRaw H1.get (C.add 168) 4 = w6 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw6
  have t1_14 : rdRaw H1.get (C.add 172) 4 = w7 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw7
  have t1_15 : rdRaw H1.get (C.add 32) 4 = s20 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs20
  have t1_16 : rdRaw H1.get (C.add 176) 4 = w8 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw8
  have t1_17 : rdRaw H1.get (C.add 28) 4 = s1c :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs1c
  have t1_18 : rdRaw H1.get (C.add 180) 4 = w9 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw9
  have t1_19 : rdRaw H1.get (C.add 52) 4 = s34 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs34
  have t1_20 : rdRaw H1.get (C.add 184) 4 = w10 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw10
  have t1_21 : rdRaw H1.get (C.add 48) 4 = s30 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs30
  have t1_22 : rdRaw H1.get (C.add 188) 4 = w11 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw11
  have t1_23 : rdRaw H1.get C 4 = s0 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs0
  have t1_24 : rdRaw H1.get (C.add 192) 4 = w12 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw12
  have t1_25 : rdRaw H1.get (C.add 196) 4 = w13 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw13
  have t1_26 : rdRaw H1.get (C.add 24) 4 = s18 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs18
  have t1_27 : rdRaw H1.get (C.add 200) 4 = w14 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw14
  have t1_28 : rdRaw H1.get (C.add 204) 4 = w15 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw15
  have t1_29 : rdRaw H1.get (C.add 124) 4 = sesi :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hsesi
  have t1_30 : rdRaw H1.get (C.add 128) 4 = sedi :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hsedi
  have t1_31 : rdRaw H1.get (C.add 132) 4 = sebx :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hsebx
  have t1_32 : rdRaw H1.get (C.add 136) 4 = sebp :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hsebp
  have t1_33 : rdRaw H1.get (C.add 20) 4 = (C.add 144) :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hK0
  have t1_34 : rdRaw H1.get (C.add 36) 4 = (C.add 208) :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hK1
  have t1_35 : rdRaw H1.get (C.add 140) 4 = 1048774 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hK2
  obtain ⟨H2, f2, e2, p2_0, p2_1, a2⟩ := outC_run_1 H1 C f1 (eax) (ecx) ((UInt32.add s10 w1)) (ebx) (ebp) (edi) (sc) (w2) (s4) (w3) (ic + 11) hS1 t1_7 t1_8 t1_9 t1_10 t1_33 t1_34
  have hS2 : StackOk H2.get.size C := by rw [a2.1]; exact hS1
  have hz2 : H2.get.size = H.get.size := a2.1.trans hz1
  have t2_2 : rdRaw H2.get (C.add 40) 4 = esi :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_0
  have t2_3 : rdRaw H2.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_1
  have t2_4 : rdRaw H2.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_2
  have t2_5 : rdRaw H2.get (C.add 8) 4 = s8 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_3
  have t2_6 : rdRaw H2.get (C.add 144) 4 = w0 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_4
  have t2_7 : rdRaw H2.get (C.add 16) 4 = s10 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_5
  have t2_8 : rdRaw H2.get (C.add 148) 4 = w1 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_6
  have t2_9 : rdRaw H2.get (C.add 12) 4 = sc :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_7
  have t2_10 : rdRaw H2.get (C.add 152) 4 = w2 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_8
  have t2_11 : rdRaw H2.get (C.add 4) 4 = s4 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_9
  have t2_12 : rdRaw H2.get (C.add 156) 4 = w3 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_10
  have t2_13 : rdRaw H2.get (C.add 160) 4 = w4 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_11
  have t2_14 : rdRaw H2.get (C.add 164) 4 = w5 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_12
  have t2_15 : rdRaw H2.get (C.add 168) 4 = w6 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_13
  have t2_16 : rdRaw H2.get (C.add 172) 4 = w7 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_14
  have t2_17 : rdRaw H2.get (C.add 32) 4 = s20 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_15
  have t2_18 : rdRaw H2.get (C.add 176) 4 = w8 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_16
  have t2_19 : rdRaw H2.get (C.add 28) 4 = s1c :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_17
  have t2_20 : rdRaw H2.get (C.add 180) 4 = w9 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_18
  have t2_21 : rdRaw H2.get (C.add 52) 4 = s34 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_19
  have t2_22 : rdRaw H2.get (C.add 184) 4 = w10 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_20
  have t2_23 : rdRaw H2.get (C.add 48) 4 = s30 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_21
  have t2_24 : rdRaw H2.get (C.add 188) 4 = w11 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_22
  have t2_25 : rdRaw H2.get C 4 = s0 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_23
  have t2_26 : rdRaw H2.get (C.add 192) 4 = w12 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_24
  have t2_27 : rdRaw H2.get (C.add 196) 4 = w13 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_25
  have t2_28 : rdRaw H2.get (C.add 24) 4 = s18 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_26
  have t2_29 : rdRaw H2.get (C.add 200) 4 = w14 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_27
  have t2_30 : rdRaw H2.get (C.add 204) 4 = w15 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_28
  have t2_31 : rdRaw H2.get (C.add 124) 4 = sesi :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_29
  have t2_32 : rdRaw H2.get (C.add 128) 4 = sedi :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_30
  have t2_33 : rdRaw H2.get (C.add 132) 4 = sebx :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_31
  have t2_34 : rdRaw H2.get (C.add 136) 4 = sebp :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_32
  have t2_35 : rdRaw H2.get (C.add 20) 4 = (C.add 144) :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_33
  have t2_36 : rdRaw H2.get (C.add 36) 4 = (C.add 208) :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_34
  have t2_37 : rdRaw H2.get (C.add 140) 4 = 1048774 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_35
  obtain ⟨H3, f3, e3, p3_0, p3_1, p3_2, a3⟩ := outC_run_2 H2 C f2 (eax) (ecx) ((UInt32.add s4 w3)) (ebx) (ebp) (edi) (w4) (w5) (esi) (w6) (ic + 11 + 10) hS2 t2_13 t2_14 t2_2 t2_15 t2_35
  have hS3 : StackOk H3.get.size C := by rw [a3.1]; exact hS2
  have hz3 : H3.get.size = H.get.size := a3.1.trans hz2
  have t3_3 : rdRaw H3.get (C.add 216) 4 = (UInt32.add sc w2) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_0
  have t3_4 : rdRaw H3.get (C.add 220) 4 = (UInt32.add s4 w3) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_1
  have t3_5 : rdRaw H3.get (C.add 40) 4 = esi :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_2
  have t3_6 : rdRaw H3.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_3
  have t3_7 : rdRaw H3.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_4
  have t3_8 : rdRaw H3.get (C.add 8) 4 = s8 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_5
  have t3_9 : rdRaw H3.get (C.add 144) 4 = w0 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_6
  have t3_10 : rdRaw H3.get (C.add 16) 4 = s10 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_7
  have t3_11 : rdRaw H3.get (C.add 148) 4 = w1 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_8
  have t3_12 : rdRaw H3.get (C.add 12) 4 = sc :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_9
  have t3_13 : rdRaw H3.get (C.add 152) 4 = w2 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_10
  have t3_14 : rdRaw H3.get (C.add 4) 4 = s4 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_11
  have t3_15 : rdRaw H3.get (C.add 156) 4 = w3 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_12
  have t3_16 : rdRaw H3.get (C.add 160) 4 = w4 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_13
  have t3_17 : rdRaw H3.get (C.add 164) 4 = w5 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_14
  have t3_18 : rdRaw H3.get (C.add 168) 4 = w6 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_15
  have t3_19 : rdRaw H3.get (C.add 172) 4 = w7 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_16
  have t3_20 : rdRaw H3.get (C.add 32) 4 = s20 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_17
  have t3_21 : rdRaw H3.get (C.add 176) 4 = w8 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_18
  have t3_22 : rdRaw H3.get (C.add 28) 4 = s1c :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_19
  have t3_23 : rdRaw H3.get (C.add 180) 4 = w9 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_20
  have t3_24 : rdRaw H3.get (C.add 52) 4 = s34 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_21
  have t3_25 : rdRaw H3.get (C.add 184) 4 = w10 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_22
  have t3_26 : rdRaw H3.get (C.add 48) 4 = s30 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_23
  have t3_27 : rdRaw H3.get (C.add 188) 4 = w11 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_24
  have t3_28 : rdRaw H3.get C 4 = s0 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_25
  have t3_29 : rdRaw H3.get (C.add 192) 4 = w12 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_26
  have t3_30 : rdRaw H3.get (C.add 196) 4 = w13 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_27
  have t3_31 : rdRaw H3.get (C.add 24) 4 = s18 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_28
  have t3_32 : rdRaw H3.get (C.add 200) 4 = w14 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_29
  have t3_33 : rdRaw H3.get (C.add 204) 4 = w15 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_30
  have t3_34 : rdRaw H3.get (C.add 124) 4 = sesi :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_31
  have t3_35 : rdRaw H3.get (C.add 128) 4 = sedi :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_32
  have t3_36 : rdRaw H3.get (C.add 132) 4 = sebx :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_33
  have t3_37 : rdRaw H3.get (C.add 136) 4 = sebp :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_34
  have t3_38 : rdRaw H3.get (C.add 20) 4 = (C.add 144) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_35
  have t3_39 : rdRaw H3.get (C.add 36) 4 = (C.add 208) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_36
  have t3_40 : rdRaw H3.get (C.add 140) 4 = 1048774 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_37
  obtain ⟨H4, f4, e4, p4_0, p4_1, p4_2, a4⟩ := outC_run_3 H3 C f3 (eax) (ecx) (ebx) ((UInt32.add esi w6)) ((UInt32.add edi w5)) (w7) (s20) (w8) (s1c) (w9) (ic + 11 + 10 + 10) hS3 t3_19 t3_20 t3_21 t3_22 t3_23
  have hS4 : StackOk H4.get.size C := by rw [a4.1]; exact hS3
  have hz4 : H4.get.size = H.get.size := a4.1.trans hz3
  have t4_3 : rdRaw H4.get (C.add 224) 4 = (UInt32.add ebp w4) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_0
  have t4_4 : rdRaw H4.get (C.add 228) 4 = (UInt32.add edi w5) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_1
  have t4_5 : rdRaw H4.get (C.add 232) 4 = (UInt32.add esi w6) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_2
  have t4_6 : rdRaw H4.get (C.add 216) 4 = (UInt32.add sc w2) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_3
  have t4_7 : rdRaw H4.get (C.add 220) 4 = (UInt32.add s4 w3) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_4
  have t4_8 : rdRaw H4.get (C.add 40) 4 = esi :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_5
  have t4_9 : rdRaw H4.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_6
  have t4_10 : rdRaw H4.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_7
  have t4_11 : rdRaw H4.get (C.add 8) 4 = s8 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_8
  have t4_12 : rdRaw H4.get (C.add 144) 4 = w0 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_9
  have t4_13 : rdRaw H4.get (C.add 16) 4 = s10 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_10
  have t4_14 : rdRaw H4.get (C.add 148) 4 = w1 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_11
  have t4_15 : rdRaw H4.get (C.add 12) 4 = sc :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_12
  have t4_16 : rdRaw H4.get (C.add 152) 4 = w2 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_13
  have t4_17 : rdRaw H4.get (C.add 4) 4 = s4 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_14
  have t4_18 : rdRaw H4.get (C.add 156) 4 = w3 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_15
  have t4_19 : rdRaw H4.get (C.add 160) 4 = w4 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_16
  have t4_20 : rdRaw H4.get (C.add 164) 4 = w5 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_17
  have t4_21 : rdRaw H4.get (C.add 168) 4 = w6 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_18
  have t4_22 : rdRaw H4.get (C.add 172) 4 = w7 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_19
  have t4_23 : rdRaw H4.get (C.add 32) 4 = s20 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_20
  have t4_24 : rdRaw H4.get (C.add 176) 4 = w8 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_21
  have t4_25 : rdRaw H4.get (C.add 28) 4 = s1c :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_22
  have t4_26 : rdRaw H4.get (C.add 180) 4 = w9 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_23
  have t4_27 : rdRaw H4.get (C.add 52) 4 = s34 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_24
  have t4_28 : rdRaw H4.get (C.add 184) 4 = w10 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_25
  have t4_29 : rdRaw H4.get (C.add 48) 4 = s30 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_26
  have t4_30 : rdRaw H4.get (C.add 188) 4 = w11 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_27
  have t4_31 : rdRaw H4.get C 4 = s0 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_28
  have t4_32 : rdRaw H4.get (C.add 192) 4 = w12 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_29
  have t4_33 : rdRaw H4.get (C.add 196) 4 = w13 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_30
  have t4_34 : rdRaw H4.get (C.add 24) 4 = s18 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_31
  have t4_35 : rdRaw H4.get (C.add 200) 4 = w14 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_32
  have t4_36 : rdRaw H4.get (C.add 204) 4 = w15 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_33
  have t4_37 : rdRaw H4.get (C.add 124) 4 = sesi :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_34
  have t4_38 : rdRaw H4.get (C.add 128) 4 = sedi :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_35
  have t4_39 : rdRaw H4.get (C.add 132) 4 = sebx :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_36
  have t4_40 : rdRaw H4.get (C.add 136) 4 = sebp :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_37
  have t4_41 : rdRaw H4.get (C.add 20) 4 = (C.add 144) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_38
  have t4_42 : rdRaw H4.get (C.add 36) 4 = (C.add 208) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_39
  have t4_43 : rdRaw H4.get (C.add 140) 4 = 1048774 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_40
  obtain ⟨H5, f5, e5, p5_0, p5_1, a5⟩ := outC_run_4 H4 C f4 ((UInt32.add s1c w9)) (ecx) (ebx) ((UInt32.add esi w6)) ((UInt32.add edi w5)) (s34) (w10) (s30) (w11) (s0) (w12) (ic + 11 + 10 + 10 + 8) hS4 t4_27 t4_28 t4_29 t4_30 t4_31 t4_32
  have hS5 : StackOk H5.get.size C := by rw [a5.1]; exact hS4
  have hz5 : H5.get.size = H.get.size := a5.1.trans hz4
  have t5_2 : rdRaw H5.get (C.add 236) 4 = (UInt32.add eax w7) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_0
  have t5_3 : rdRaw H5.get (C.add 240) 4 = (UInt32.add s20 w8) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_1
  have t5_4 : rdRaw H5.get (C.add 244) 4 = (UInt32.add s1c w9) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_2
  have t5_5 : rdRaw H5.get (C.add 224) 4 = (UInt32.add ebp w4) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_3
  have t5_6 : rdRaw H5.get (C.add 228) 4 = (UInt32.add edi w5) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_4
  have t5_7 : rdRaw H5.get (C.add 232) 4 = (UInt32.add esi w6) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_5
  have t5_8 : rdRaw H5.get (C.add 216) 4 = (UInt32.add sc w2) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_6
  have t5_9 : rdRaw H5.get (C.add 220) 4 = (UInt32.add s4 w3) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_7
  have t5_10 : rdRaw H5.get (C.add 40) 4 = esi :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_8
  have t5_11 : rdRaw H5.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_9
  have t5_12 : rdRaw H5.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_10
  have t5_13 : rdRaw H5.get (C.add 8) 4 = s8 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_11
  have t5_14 : rdRaw H5.get (C.add 144) 4 = w0 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_12
  have t5_15 : rdRaw H5.get (C.add 16) 4 = s10 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_13
  have t5_16 : rdRaw H5.get (C.add 148) 4 = w1 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_14
  have t5_17 : rdRaw H5.get (C.add 12) 4 = sc :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_15
  have t5_18 : rdRaw H5.get (C.add 152) 4 = w2 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_16
  have t5_19 : rdRaw H5.get (C.add 4) 4 = s4 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_17
  have t5_20 : rdRaw H5.get (C.add 156) 4 = w3 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_18
  have t5_21 : rdRaw H5.get (C.add 160) 4 = w4 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_19
  have t5_22 : rdRaw H5.get (C.add 164) 4 = w5 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_20
  have t5_23 : rdRaw H5.get (C.add 168) 4 = w6 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_21
  have t5_24 : rdRaw H5.get (C.add 172) 4 = w7 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_22
  have t5_25 : rdRaw H5.get (C.add 32) 4 = s20 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_23
  have t5_26 : rdRaw H5.get (C.add 176) 4 = w8 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_24
  have t5_27 : rdRaw H5.get (C.add 28) 4 = s1c :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_25
  have t5_28 : rdRaw H5.get (C.add 180) 4 = w9 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_26
  have t5_29 : rdRaw H5.get (C.add 52) 4 = s34 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_27
  have t5_30 : rdRaw H5.get (C.add 184) 4 = w10 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_28
  have t5_31 : rdRaw H5.get (C.add 48) 4 = s30 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_29
  have t5_32 : rdRaw H5.get (C.add 188) 4 = w11 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_30
  have t5_33 : rdRaw H5.get C 4 = s0 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_31
  have t5_34 : rdRaw H5.get (C.add 192) 4 = w12 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_32
  have t5_35 : rdRaw H5.get (C.add 196) 4 = w13 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_33
  have t5_36 : rdRaw H5.get (C.add 24) 4 = s18 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_34
  have t5_37 : rdRaw H5.get (C.add 200) 4 = w14 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_35
  have t5_38 : rdRaw H5.get (C.add 204) 4 = w15 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_36
  have t5_39 : rdRaw H5.get (C.add 124) 4 = sesi :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_37
  have t5_40 : rdRaw H5.get (C.add 128) 4 = sedi :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_38
  have t5_41 : rdRaw H5.get (C.add 132) 4 = sebx :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_39
  have t5_42 : rdRaw H5.get (C.add 136) 4 = sebp :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_40
  have t5_43 : rdRaw H5.get (C.add 20) 4 = (C.add 144) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_41
  have t5_44 : rdRaw H5.get (C.add 36) 4 = (C.add 208) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_42
  have t5_45 : rdRaw H5.get (C.add 140) 4 = 1048774 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_43
  obtain ⟨H6, f6, e6, p6_0, p6_1, p6_2, p6_3, a6⟩ := outC_run_5 H5 C f5 ((UInt32.add s0 w12)) (ecx) (ebx) ((UInt32.add esi w6)) ((UInt32.add edi w5)) (w13) (s18) (w14) (w15) (ic + 11 + 10 + 10 + 8 + 8) hS5 t5_35 t5_36 t5_37 t5_38
  have hS6 : StackOk H6.get.size C := by rw [a6.1]; exact hS5
  have hz6 : H6.get.size = H.get.size := a6.1.trans hz5
  have t6_4 : rdRaw H6.get (C.add 248) 4 = (UInt32.add s34 w10) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p5_0
  have t6_5 : rdRaw H6.get (C.add 252) 4 = (UInt32.add s30 w11) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p5_1
  have t6_6 : rdRaw H6.get (C.add 236) 4 = (UInt32.add eax w7) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_2
  have t6_7 : rdRaw H6.get (C.add 240) 4 = (UInt32.add s20 w8) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_3
  have t6_8 : rdRaw H6.get (C.add 244) 4 = (UInt32.add s1c w9) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_4
  have t6_9 : rdRaw H6.get (C.add 224) 4 = (UInt32.add ebp w4) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_5
  have t6_10 : rdRaw H6.get (C.add 228) 4 = (UInt32.add edi w5) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_6
  have t6_11 : rdRaw H6.get (C.add 232) 4 = (UInt32.add esi w6) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_7
  have t6_12 : rdRaw H6.get (C.add 216) 4 = (UInt32.add sc w2) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_8
  have t6_13 : rdRaw H6.get (C.add 220) 4 = (UInt32.add s4 w3) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_9
  have t6_14 : rdRaw H6.get (C.add 40) 4 = esi :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_10
  have t6_15 : rdRaw H6.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_11
  have t6_16 : rdRaw H6.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_12
  have t6_17 : rdRaw H6.get (C.add 8) 4 = s8 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_13
  have t6_18 : rdRaw H6.get (C.add 144) 4 = w0 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_14
  have t6_19 : rdRaw H6.get (C.add 16) 4 = s10 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_15
  have t6_20 : rdRaw H6.get (C.add 148) 4 = w1 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_16
  have t6_21 : rdRaw H6.get (C.add 12) 4 = sc :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_17
  have t6_22 : rdRaw H6.get (C.add 152) 4 = w2 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_18
  have t6_23 : rdRaw H6.get (C.add 4) 4 = s4 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_19
  have t6_24 : rdRaw H6.get (C.add 156) 4 = w3 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_20
  have t6_25 : rdRaw H6.get (C.add 160) 4 = w4 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_21
  have t6_26 : rdRaw H6.get (C.add 164) 4 = w5 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_22
  have t6_27 : rdRaw H6.get (C.add 168) 4 = w6 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_23
  have t6_28 : rdRaw H6.get (C.add 172) 4 = w7 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_24
  have t6_29 : rdRaw H6.get (C.add 32) 4 = s20 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_25
  have t6_30 : rdRaw H6.get (C.add 176) 4 = w8 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_26
  have t6_31 : rdRaw H6.get (C.add 28) 4 = s1c :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_27
  have t6_32 : rdRaw H6.get (C.add 180) 4 = w9 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_28
  have t6_33 : rdRaw H6.get (C.add 52) 4 = s34 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_29
  have t6_34 : rdRaw H6.get (C.add 184) 4 = w10 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_30
  have t6_35 : rdRaw H6.get (C.add 48) 4 = s30 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_31
  have t6_36 : rdRaw H6.get (C.add 188) 4 = w11 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_32
  have t6_37 : rdRaw H6.get C 4 = s0 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_33
  have t6_38 : rdRaw H6.get (C.add 192) 4 = w12 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_34
  have t6_39 : rdRaw H6.get (C.add 196) 4 = w13 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_35
  have t6_40 : rdRaw H6.get (C.add 24) 4 = s18 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_36
  have t6_41 : rdRaw H6.get (C.add 200) 4 = w14 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_37
  have t6_42 : rdRaw H6.get (C.add 204) 4 = w15 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_38
  have t6_43 : rdRaw H6.get (C.add 124) 4 = sesi :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_39
  have t6_44 : rdRaw H6.get (C.add 128) 4 = sedi :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_40
  have t6_45 : rdRaw H6.get (C.add 132) 4 = sebx :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_41
  have t6_46 : rdRaw H6.get (C.add 136) 4 = sebp :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_42
  have t6_47 : rdRaw H6.get (C.add 20) 4 = (C.add 144) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_43
  have t6_48 : rdRaw H6.get (C.add 36) 4 = (C.add 208) :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_44
  have t6_49 : rdRaw H6.get (C.add 140) 4 = 1048774 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_45
  obtain ⟨H7, f7, e7, a7⟩ := outC_run_6 H6 C f6 ((UInt32.add s18 w14)) ((UInt32.add ecx w13)) ((UInt32.add ebx w15)) ((UInt32.add esi w6)) ((UInt32.add edi w5)) (sesi) (sedi) (sebx) (sebp) (ic + 11 + 10 + 10 + 8 + 8 + 8) hS6 t6_43 t6_44 t6_45 t6_46 t6_49
  have hS7 : StackOk H7.get.size C := by rw [a7.1]; exact hS6
  have hz7 : H7.get.size = H.get.size := a7.1.trans hz6
  have t7_0 : rdRaw H7.get (C.add 256) 4 = (UInt32.add s0 w12) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p6_0
  have t7_1 : rdRaw H7.get (C.add 260) 4 = (UInt32.add ecx w13) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p6_1
  have t7_2 : rdRaw H7.get (C.add 264) 4 = (UInt32.add s18 w14) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p6_2
  have t7_3 : rdRaw H7.get (C.add 268) 4 = (UInt32.add ebx w15) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p6_3
  have t7_4 : rdRaw H7.get (C.add 248) 4 = (UInt32.add s34 w10) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_4
  have t7_5 : rdRaw H7.get (C.add 252) 4 = (UInt32.add s30 w11) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_5
  have t7_6 : rdRaw H7.get (C.add 236) 4 = (UInt32.add eax w7) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_6
  have t7_7 : rdRaw H7.get (C.add 240) 4 = (UInt32.add s20 w8) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_7
  have t7_8 : rdRaw H7.get (C.add 244) 4 = (UInt32.add s1c w9) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_8
  have t7_9 : rdRaw H7.get (C.add 224) 4 = (UInt32.add ebp w4) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_9
  have t7_10 : rdRaw H7.get (C.add 228) 4 = (UInt32.add edi w5) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_10
  have t7_11 : rdRaw H7.get (C.add 232) 4 = (UInt32.add esi w6) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_11
  have t7_12 : rdRaw H7.get (C.add 216) 4 = (UInt32.add sc w2) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_12
  have t7_13 : rdRaw H7.get (C.add 220) 4 = (UInt32.add s4 w3) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_13
  have t7_14 : rdRaw H7.get (C.add 40) 4 = esi :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_14
  have t7_15 : rdRaw H7.get (C.add 208) 4 = (UInt32.add s8 w0) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_15
  have t7_16 : rdRaw H7.get (C.add 212) 4 = (UInt32.add s10 w1) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_16
  have t7_17 : rdRaw H7.get (C.add 8) 4 = s8 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_17
  have t7_18 : rdRaw H7.get (C.add 144) 4 = w0 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_18
  have t7_19 : rdRaw H7.get (C.add 16) 4 = s10 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_19
  have t7_20 : rdRaw H7.get (C.add 148) 4 = w1 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_20
  have t7_21 : rdRaw H7.get (C.add 12) 4 = sc :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_21
  have t7_22 : rdRaw H7.get (C.add 152) 4 = w2 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_22
  have t7_23 : rdRaw H7.get (C.add 4) 4 = s4 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_23
  have t7_24 : rdRaw H7.get (C.add 156) 4 = w3 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_24
  have t7_25 : rdRaw H7.get (C.add 160) 4 = w4 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_25
  have t7_26 : rdRaw H7.get (C.add 164) 4 = w5 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_26
  have t7_27 : rdRaw H7.get (C.add 168) 4 = w6 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_27
  have t7_28 : rdRaw H7.get (C.add 172) 4 = w7 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_28
  have t7_29 : rdRaw H7.get (C.add 32) 4 = s20 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_29
  have t7_30 : rdRaw H7.get (C.add 176) 4 = w8 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_30
  have t7_31 : rdRaw H7.get (C.add 28) 4 = s1c :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_31
  have t7_32 : rdRaw H7.get (C.add 180) 4 = w9 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_32
  have t7_33 : rdRaw H7.get (C.add 52) 4 = s34 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_33
  have t7_34 : rdRaw H7.get (C.add 184) 4 = w10 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_34
  have t7_35 : rdRaw H7.get (C.add 48) 4 = s30 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_35
  have t7_36 : rdRaw H7.get (C.add 188) 4 = w11 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_36
  have t7_37 : rdRaw H7.get C 4 = s0 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_37
  have t7_38 : rdRaw H7.get (C.add 192) 4 = w12 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_38
  have t7_39 : rdRaw H7.get (C.add 196) 4 = w13 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_39
  have t7_40 : rdRaw H7.get (C.add 24) 4 = s18 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_40
  have t7_41 : rdRaw H7.get (C.add 200) 4 = w14 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_41
  have t7_42 : rdRaw H7.get (C.add 204) 4 = w15 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_42
  have t7_43 : rdRaw H7.get (C.add 124) 4 = sesi :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_43
  have t7_44 : rdRaw H7.get (C.add 128) 4 = sedi :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_44
  have t7_45 : rdRaw H7.get (C.add 132) 4 = sebx :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_45
  have t7_46 : rdRaw H7.get (C.add 136) 4 = sebp :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_46
  have t7_47 : rdRaw H7.get (C.add 20) 4 = (C.add 144) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_47
  have t7_48 : rdRaw H7.get (C.add 36) 4 = (C.add 208) :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_48
  have t7_49 : rdRaw H7.get (C.add 140) 4 = 1048774 :=
    (a7.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t6_49
  have hrun := exN_trans (exN_trans (exN_trans (exN_trans (exN_trans (exN_trans (e1) e2) e3) e4) e5) e6) e7
  rw [show ic + 11 + 10 + 10 + 8 + 8 + 8 + 6 = ic + 61 from by simp only [UInt64.add_assoc] <;> rfl] at hrun
  exact ⟨H7, f7, hrun, t7_14, t7_15, t7_16, t7_12, t7_13, t7_9, t7_10, t7_11, t7_6, t7_7, t7_8, t7_4, t7_5, t7_0, t7_1, t7_2, t7_3, (((((((a1.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)).trans (a2.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a3.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a4.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a5.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a6.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a7.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)))⟩

/-- The input words at `t + 0x90`. -/
def InAt (M : ByteArray) (t : UInt32) (w : V16) : Prop :=
  rdRaw M (t.add 144) 4 = w.x0 ∧
  rdRaw M (t.add 148) 4 = w.x1 ∧
  rdRaw M (t.add 152) 4 = w.x2 ∧
  rdRaw M (t.add 156) 4 = w.x3 ∧
  rdRaw M (t.add 160) 4 = w.x4 ∧
  rdRaw M (t.add 164) 4 = w.x5 ∧
  rdRaw M (t.add 168) 4 = w.x6 ∧
  rdRaw M (t.add 172) 4 = w.x7 ∧
  rdRaw M (t.add 176) 4 = w.x8 ∧
  rdRaw M (t.add 180) 4 = w.x9 ∧
  rdRaw M (t.add 184) 4 = w.x10 ∧
  rdRaw M (t.add 188) 4 = w.x11 ∧
  rdRaw M (t.add 192) 4 = w.x12 ∧
  rdRaw M (t.add 196) 4 = w.x13 ∧
  rdRaw M (t.add 200) 4 = w.x14 ∧
  rdRaw M (t.add 204) 4 = w.x15

/-- Memory outside the slots `[t, t + 60)` and the output words `[t + 0xd0, t + 0x110)`. -/
def OutRegion (t : UInt32) (a : Nat) : Prop :=
  (t.toNat ≤ a ∧ a < t.toNat + 60) ∨ (t.toNat + 208 ≤ a ∧ a < t.toNat + 272)

theorem output_run (H : CMem) (t f : UInt32) (r : RS) (w : V16) (sesi sedi sebx sebp : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size t)
    (hr : Corr H.get t r) (h14 : r.s14 = t.add 144) (h24 : r.s24 = t.add 208) (hw : InAt H.get t w)
    (hsv : rdRaw H.get (t.add 124) 4 = sesi ∧ rdRaw H.get (t.add 128) 4 = sedi ∧
      rdRaw H.get (t.add 132) 4 = sebx ∧ rdRaw H.get (t.add 136) 4 = sebp ∧
      rdRaw H.get (t.add 140) 4 = 0x1000c6) :
    ∃ (H' : CMem) (f' a c d : UInt32),
      exN Image.sym_halt 61 (stRS H.get t r 0x10033e (efl f) ic) =
        some ⟨H'.get, a, c, d, sebx, t.add 144, sebp, sesi, sedi, 0x1000c6, efl f', ic + 61⟩ ∧
      rdRaw H'.get (t.add 208) 4 = UInt32.add (RS.toV r).x0 w.x0 ∧
      rdRaw H'.get (t.add 212) 4 = UInt32.add (RS.toV r).x1 w.x1 ∧
      rdRaw H'.get (t.add 216) 4 = UInt32.add (RS.toV r).x2 w.x2 ∧
      rdRaw H'.get (t.add 220) 4 = UInt32.add (RS.toV r).x3 w.x3 ∧
      rdRaw H'.get (t.add 224) 4 = UInt32.add (RS.toV r).x4 w.x4 ∧
      rdRaw H'.get (t.add 228) 4 = UInt32.add (RS.toV r).x5 w.x5 ∧
      rdRaw H'.get (t.add 232) 4 = UInt32.add (RS.toV r).x6 w.x6 ∧
      rdRaw H'.get (t.add 236) 4 = UInt32.add (RS.toV r).x7 w.x7 ∧
      rdRaw H'.get (t.add 240) 4 = UInt32.add (RS.toV r).x8 w.x8 ∧
      rdRaw H'.get (t.add 244) 4 = UInt32.add (RS.toV r).x9 w.x9 ∧
      rdRaw H'.get (t.add 248) 4 = UInt32.add (RS.toV r).x10 w.x10 ∧
      rdRaw H'.get (t.add 252) 4 = UInt32.add (RS.toV r).x11 w.x11 ∧
      rdRaw H'.get (t.add 256) 4 = UInt32.add (RS.toV r).x12 w.x12 ∧
      rdRaw H'.get (t.add 260) 4 = UInt32.add (RS.toV r).x13 w.x13 ∧
      rdRaw H'.get (t.add 264) 4 = UInt32.add (RS.toV r).x14 w.x14 ∧
      rdRaw H'.get (t.add 268) 4 = UInt32.add (RS.toV r).x15 w.x15 ∧
      AgreeOn (OutRegion t) H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  rcases w with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15⟩ := hw
  obtain ⟨hv0, hv1, hv2, hv3, hv4⟩ := hsv
  simp only at h14 h24
  subst h14 h24
  obtain ⟨H', f', e, q40, q208, q212, q216, q220, q224, q228, q232, q236, q240, q244, q248, q252, q256, q260, q264, q268, ag⟩ :=
    outC_run H t f eax ecx edx ebx ebp esi edi s8 w0 s10 w1 sc w2 s4 w3 w4 w5 w6 w7 s20 w8 s1c w9 s34 w10 s30 w11 s0 w12 w13 s18 w14 w15 sesi sedi sebx sebp ic hS hs8 hw0 hs10 hw1 hsc hw2 hs4 hw3 hw4 hw5 hw6 hw7 hs20 hw8 hs1c hw9 hs34 hw10 hs30 hw11 hs0 hw12 hw13 hs18 hw14 hw15 hv0 hv1 hv2 hv3 hs14 hs24 hv4
  exact ⟨H', f', _, _, _, e, q208, q212, q216, q220, q224, q228, q232, q236, q240, q244, q248, q252, q256, q260, q264, q268, ag⟩

end Solutions.OpensslChacha20
