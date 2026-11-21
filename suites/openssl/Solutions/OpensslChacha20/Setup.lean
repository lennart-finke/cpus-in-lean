import Solutions.OpensslChacha20.SetupC
/-!
# `chacha20_core`: from the copy of the input to the loop head

`0x10011f`–`0x100190`: the sixteen words `w` of the local copy at `t + 0x3c` are loaded into the
registers and slots of the round loop, and the counter slot is set to 22. The run is generated in
pieces (`setupC_run`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem setupC_run (H : CMem) (C f eax ecx edx ebx ebp esi edi w4 w0 w1 w12 w8 w5 w13 w9 w6 w2 w14 w10 w7 w3 w15 w11 s14 s24 s2c s38 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hw4 : rdRaw H.get (C.add 76) 4 = w4)
    (hw0 : rdRaw H.get (C.add 60) 4 = w0)
    (hw1 : rdRaw H.get (C.add 64) 4 = w1)
    (hw12 : rdRaw H.get (C.add 108) 4 = w12)
    (hw8 : rdRaw H.get (C.add 92) 4 = w8)
    (hw5 : rdRaw H.get (C.add 80) 4 = w5)
    (hw13 : rdRaw H.get (C.add 112) 4 = w13)
    (hw9 : rdRaw H.get (C.add 96) 4 = w9)
    (hw6 : rdRaw H.get (C.add 84) 4 = w6)
    (hw2 : rdRaw H.get (C.add 68) 4 = w2)
    (hw14 : rdRaw H.get (C.add 116) 4 = w14)
    (hw10 : rdRaw H.get (C.add 100) 4 = w10)
    (hw7 : rdRaw H.get (C.add 88) 4 = w7)
    (hw3 : rdRaw H.get (C.add 72) 4 = w3)
    (hw15 : rdRaw H.get (C.add 120) 4 = w15)
    (hw11 : rdRaw H.get (C.add 104) 4 = w11)
    (hs14 : rdRaw H.get (C.add 20) 4 = s14)
    (hs24 : rdRaw H.get (C.add 36) 4 = s24)
    (hs2c : rdRaw H.get (C.add 44) 4 = s2c)
    (hs38 : rdRaw H.get (C.add 56) 4 = s38) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 29 ⟨H.get, eax, ecx, edx, ebx, C, ebp, esi, edi, 0x10011f, efl f, ic⟩ =
        some ⟨H'.get, w7, w13, w11, w15, C, w4, w6, w5, 0x100190, efl f', ic + 29⟩ ∧
      rdRaw H'.get (C.add 8) 4 = w0 ∧
      rdRaw H'.get (C.add 16) 4 = w1 ∧
      rdRaw H'.get C 4 = w12 ∧
      rdRaw H'.get (C.add 32) 4 = w8 ∧
      rdRaw H'.get (C.add 28) 4 = w9 ∧
      rdRaw H'.get (C.add 12) 4 = w2 ∧
      rdRaw H'.get (C.add 24) 4 = w14 ∧
      rdRaw H'.get (C.add 52) 4 = w10 ∧
      rdRaw H'.get (C.add 4) 4 = w3 ∧
      rdRaw H'.get (C.add 40) 4 = 22 ∧
      rdRaw H'.get (C.add 48) 4 = w11 ∧
      rdRaw H'.get (C.add 20) 4 = s14 ∧
      rdRaw H'.get (C.add 36) 4 = s24 ∧
      rdRaw H'.get (C.add 44) 4 = s2c ∧
      rdRaw H'.get (C.add 56) 4 = s38 ∧
      AgreeOn (fun a => C.toNat ≤ a ∧ a < C.toNat + 60) H.get H'.get := by
  have hS0 := hS
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  have hz0 : H.get.size = H.get.size := rfl
  obtain ⟨H1, f1, e1, p1_0, p1_1, a1⟩ := setupC_run_0 H C f (eax) (ecx) (edx) (ebx) (ebp) (esi) (edi) (w4) (w0) (w1) (ic) hS0 hw4 hw0 hw1
  have hS1 : StackOk H1.get.size C := by rw [a1.1]; exact hS0
  have hz1 : H1.get.size = H.get.size := a1.1.trans hz0
  have t1_2 : rdRaw H1.get (C.add 76) 4 = w4 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw4
  have t1_3 : rdRaw H1.get (C.add 60) 4 = w0 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw0
  have t1_4 : rdRaw H1.get (C.add 64) 4 = w1 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw1
  have t1_5 : rdRaw H1.get (C.add 108) 4 = w12 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw12
  have t1_6 : rdRaw H1.get (C.add 92) 4 = w8 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw8
  have t1_7 : rdRaw H1.get (C.add 80) 4 = w5 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw5
  have t1_8 : rdRaw H1.get (C.add 112) 4 = w13 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw13
  have t1_9 : rdRaw H1.get (C.add 96) 4 = w9 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw9
  have t1_10 : rdRaw H1.get (C.add 84) 4 = w6 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw6
  have t1_11 : rdRaw H1.get (C.add 68) 4 = w2 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw2
  have t1_12 : rdRaw H1.get (C.add 116) 4 = w14 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw14
  have t1_13 : rdRaw H1.get (C.add 100) 4 = w10 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw10
  have t1_14 : rdRaw H1.get (C.add 88) 4 = w7 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw7
  have t1_15 : rdRaw H1.get (C.add 72) 4 = w3 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw3
  have t1_16 : rdRaw H1.get (C.add 120) 4 = w15 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw15
  have t1_17 : rdRaw H1.get (C.add 104) 4 = w11 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hw11
  have t1_18 : rdRaw H1.get (C.add 20) 4 = s14 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs14
  have t1_19 : rdRaw H1.get (C.add 36) 4 = s24 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs24
  have t1_20 : rdRaw H1.get (C.add 44) 4 = s2c :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs2c
  have t1_21 : rdRaw H1.get (C.add 56) 4 = s38 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hs38
  obtain ⟨H2, f2, e2, p2_0, p2_1, a2⟩ := setupC_run_1 H1 C f1 (w1) (ecx) (edx) (ebx) (w4) (esi) (edi) (w12) (w8) (w5) (w13) (ic + 5) hS1 t1_5 t1_6 t1_7 t1_8
  have hS2 : StackOk H2.get.size C := by rw [a2.1]; exact hS1
  have hz2 : H2.get.size = H.get.size := a2.1.trans hz1
  have t2_2 : rdRaw H2.get (C.add 8) 4 = w0 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_0
  have t2_3 : rdRaw H2.get (C.add 16) 4 = w1 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_1
  have t2_4 : rdRaw H2.get (C.add 76) 4 = w4 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_2
  have t2_5 : rdRaw H2.get (C.add 60) 4 = w0 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_3
  have t2_6 : rdRaw H2.get (C.add 64) 4 = w1 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_4
  have t2_7 : rdRaw H2.get (C.add 108) 4 = w12 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_5
  have t2_8 : rdRaw H2.get (C.add 92) 4 = w8 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_6
  have t2_9 : rdRaw H2.get (C.add 80) 4 = w5 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_7
  have t2_10 : rdRaw H2.get (C.add 112) 4 = w13 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_8
  have t2_11 : rdRaw H2.get (C.add 96) 4 = w9 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_9
  have t2_12 : rdRaw H2.get (C.add 84) 4 = w6 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_10
  have t2_13 : rdRaw H2.get (C.add 68) 4 = w2 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_11
  have t2_14 : rdRaw H2.get (C.add 116) 4 = w14 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_12
  have t2_15 : rdRaw H2.get (C.add 100) 4 = w10 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_13
  have t2_16 : rdRaw H2.get (C.add 88) 4 = w7 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_14
  have t2_17 : rdRaw H2.get (C.add 72) 4 = w3 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_15
  have t2_18 : rdRaw H2.get (C.add 120) 4 = w15 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_16
  have t2_19 : rdRaw H2.get (C.add 104) 4 = w11 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_17
  have t2_20 : rdRaw H2.get (C.add 20) 4 = s14 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_18
  have t2_21 : rdRaw H2.get (C.add 36) 4 = s24 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_19
  have t2_22 : rdRaw H2.get (C.add 44) 4 = s2c :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_20
  have t2_23 : rdRaw H2.get (C.add 56) 4 = s38 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t1_21
  obtain ⟨H3, f3, e3, p3_0, p3_1, a3⟩ := setupC_run_2 H2 C f2 (w8) (w13) (edx) (ebx) (w4) (esi) (w5) (w9) (w6) (w2) (ic + 5 + 6) hS2 t2_11 t2_12 t2_13
  have hS3 : StackOk H3.get.size C := by rw [a3.1]; exact hS2
  have hz3 : H3.get.size = H.get.size := a3.1.trans hz2
  have t3_2 : rdRaw H3.get C 4 = w12 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_0
  have t3_3 : rdRaw H3.get (C.add 32) 4 = w8 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_1
  have t3_4 : rdRaw H3.get (C.add 8) 4 = w0 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_2
  have t3_5 : rdRaw H3.get (C.add 16) 4 = w1 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_3
  have t3_6 : rdRaw H3.get (C.add 76) 4 = w4 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_4
  have t3_7 : rdRaw H3.get (C.add 60) 4 = w0 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_5
  have t3_8 : rdRaw H3.get (C.add 64) 4 = w1 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_6
  have t3_9 : rdRaw H3.get (C.add 108) 4 = w12 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_7
  have t3_10 : rdRaw H3.get (C.add 92) 4 = w8 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_8
  have t3_11 : rdRaw H3.get (C.add 80) 4 = w5 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_9
  have t3_12 : rdRaw H3.get (C.add 112) 4 = w13 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_10
  have t3_13 : rdRaw H3.get (C.add 96) 4 = w9 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_11
  have t3_14 : rdRaw H3.get (C.add 84) 4 = w6 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_12
  have t3_15 : rdRaw H3.get (C.add 68) 4 = w2 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_13
  have t3_16 : rdRaw H3.get (C.add 116) 4 = w14 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_14
  have t3_17 : rdRaw H3.get (C.add 100) 4 = w10 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_15
  have t3_18 : rdRaw H3.get (C.add 88) 4 = w7 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_16
  have t3_19 : rdRaw H3.get (C.add 72) 4 = w3 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_17
  have t3_20 : rdRaw H3.get (C.add 120) 4 = w15 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_18
  have t3_21 : rdRaw H3.get (C.add 104) 4 = w11 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_19
  have t3_22 : rdRaw H3.get (C.add 20) 4 = s14 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_20
  have t3_23 : rdRaw H3.get (C.add 36) 4 = s24 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_21
  have t3_24 : rdRaw H3.get (C.add 44) 4 = s2c :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_22
  have t3_25 : rdRaw H3.get (C.add 56) 4 = s38 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_23
  obtain ⟨H4, f4, e4, p4_0, p4_1, a4⟩ := setupC_run_3 H3 C f3 (w2) (w13) (edx) (ebx) (w4) (w6) (w5) (w14) (w10) (w7) (ic + 5 + 6 + 5) hS3 t3_16 t3_17 t3_18
  have hS4 : StackOk H4.get.size C := by rw [a4.1]; exact hS3
  have hz4 : H4.get.size = H.get.size := a4.1.trans hz3
  have t4_2 : rdRaw H4.get (C.add 28) 4 = w9 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_0
  have t4_3 : rdRaw H4.get (C.add 12) 4 = w2 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_1
  have t4_4 : rdRaw H4.get C 4 = w12 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_2
  have t4_5 : rdRaw H4.get (C.add 32) 4 = w8 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_3
  have t4_6 : rdRaw H4.get (C.add 8) 4 = w0 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_4
  have t4_7 : rdRaw H4.get (C.add 16) 4 = w1 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_5
  have t4_8 : rdRaw H4.get (C.add 76) 4 = w4 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_6
  have t4_9 : rdRaw H4.get (C.add 60) 4 = w0 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_7
  have t4_10 : rdRaw H4.get (C.add 64) 4 = w1 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_8
  have t4_11 : rdRaw H4.get (C.add 108) 4 = w12 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_9
  have t4_12 : rdRaw H4.get (C.add 92) 4 = w8 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_10
  have t4_13 : rdRaw H4.get (C.add 80) 4 = w5 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_11
  have t4_14 : rdRaw H4.get (C.add 112) 4 = w13 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_12
  have t4_15 : rdRaw H4.get (C.add 96) 4 = w9 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_13
  have t4_16 : rdRaw H4.get (C.add 84) 4 = w6 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_14
  have t4_17 : rdRaw H4.get (C.add 68) 4 = w2 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_15
  have t4_18 : rdRaw H4.get (C.add 116) 4 = w14 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_16
  have t4_19 : rdRaw H4.get (C.add 100) 4 = w10 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_17
  have t4_20 : rdRaw H4.get (C.add 88) 4 = w7 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_18
  have t4_21 : rdRaw H4.get (C.add 72) 4 = w3 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_19
  have t4_22 : rdRaw H4.get (C.add 120) 4 = w15 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_20
  have t4_23 : rdRaw H4.get (C.add 104) 4 = w11 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_21
  have t4_24 : rdRaw H4.get (C.add 20) 4 = s14 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_22
  have t4_25 : rdRaw H4.get (C.add 36) 4 = s24 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_23
  have t4_26 : rdRaw H4.get (C.add 44) 4 = s2c :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_24
  have t4_27 : rdRaw H4.get (C.add 56) 4 = s38 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_25
  obtain ⟨H5, f5, e5, p5_0, p5_1, a5⟩ := setupC_run_4 H4 C f4 (w7) (w13) (edx) (ebx) (w4) (w6) (w5) (w3) (w15) (ic + 5 + 6 + 5 + 5) hS4 t4_21 t4_22
  have hS5 : StackOk H5.get.size C := by rw [a5.1]; exact hS4
  have hz5 : H5.get.size = H.get.size := a5.1.trans hz4
  have t5_2 : rdRaw H5.get (C.add 24) 4 = w14 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_0
  have t5_3 : rdRaw H5.get (C.add 52) 4 = w10 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_1
  have t5_4 : rdRaw H5.get (C.add 28) 4 = w9 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_2
  have t5_5 : rdRaw H5.get (C.add 12) 4 = w2 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_3
  have t5_6 : rdRaw H5.get C 4 = w12 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_4
  have t5_7 : rdRaw H5.get (C.add 32) 4 = w8 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_5
  have t5_8 : rdRaw H5.get (C.add 8) 4 = w0 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_6
  have t5_9 : rdRaw H5.get (C.add 16) 4 = w1 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_7
  have t5_10 : rdRaw H5.get (C.add 76) 4 = w4 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_8
  have t5_11 : rdRaw H5.get (C.add 60) 4 = w0 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_9
  have t5_12 : rdRaw H5.get (C.add 64) 4 = w1 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_10
  have t5_13 : rdRaw H5.get (C.add 108) 4 = w12 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_11
  have t5_14 : rdRaw H5.get (C.add 92) 4 = w8 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_12
  have t5_15 : rdRaw H5.get (C.add 80) 4 = w5 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_13
  have t5_16 : rdRaw H5.get (C.add 112) 4 = w13 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_14
  have t5_17 : rdRaw H5.get (C.add 96) 4 = w9 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_15
  have t5_18 : rdRaw H5.get (C.add 84) 4 = w6 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_16
  have t5_19 : rdRaw H5.get (C.add 68) 4 = w2 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_17
  have t5_20 : rdRaw H5.get (C.add 116) 4 = w14 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_18
  have t5_21 : rdRaw H5.get (C.add 100) 4 = w10 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_19
  have t5_22 : rdRaw H5.get (C.add 88) 4 = w7 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_20
  have t5_23 : rdRaw H5.get (C.add 72) 4 = w3 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_21
  have t5_24 : rdRaw H5.get (C.add 120) 4 = w15 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_22
  have t5_25 : rdRaw H5.get (C.add 104) 4 = w11 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_23
  have t5_26 : rdRaw H5.get (C.add 20) 4 = s14 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_24
  have t5_27 : rdRaw H5.get (C.add 36) 4 = s24 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_25
  have t5_28 : rdRaw H5.get (C.add 44) 4 = s2c :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_26
  have t5_29 : rdRaw H5.get (C.add 56) 4 = s38 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_27
  obtain ⟨H6, f6, e6, p6_0, a6⟩ := setupC_run_5 H5 C f5 (w7) (w13) (w3) (w15) (w4) (w6) (w5) (w11) (ic + 5 + 6 + 5 + 5 + 4) hS5 t5_25
  have hS6 : StackOk H6.get.size C := by rw [a6.1]; exact hS5
  have hz6 : H6.get.size = H.get.size := a6.1.trans hz5
  have t6_1 : rdRaw H6.get (C.add 4) 4 = w3 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p5_0
  have t6_2 : rdRaw H6.get (C.add 40) 4 = 22 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p5_1
  have t6_3 : rdRaw H6.get (C.add 24) 4 = w14 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_2
  have t6_4 : rdRaw H6.get (C.add 52) 4 = w10 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_3
  have t6_5 : rdRaw H6.get (C.add 28) 4 = w9 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_4
  have t6_6 : rdRaw H6.get (C.add 12) 4 = w2 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_5
  have t6_7 : rdRaw H6.get C 4 = w12 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_6
  have t6_8 : rdRaw H6.get (C.add 32) 4 = w8 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_7
  have t6_9 : rdRaw H6.get (C.add 8) 4 = w0 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_8
  have t6_10 : rdRaw H6.get (C.add 16) 4 = w1 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_9
  have t6_11 : rdRaw H6.get (C.add 76) 4 = w4 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_10
  have t6_12 : rdRaw H6.get (C.add 60) 4 = w0 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_11
  have t6_13 : rdRaw H6.get (C.add 64) 4 = w1 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_12
  have t6_14 : rdRaw H6.get (C.add 108) 4 = w12 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_13
  have t6_15 : rdRaw H6.get (C.add 92) 4 = w8 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_14
  have t6_16 : rdRaw H6.get (C.add 80) 4 = w5 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_15
  have t6_17 : rdRaw H6.get (C.add 112) 4 = w13 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_16
  have t6_18 : rdRaw H6.get (C.add 96) 4 = w9 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_17
  have t6_19 : rdRaw H6.get (C.add 84) 4 = w6 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_18
  have t6_20 : rdRaw H6.get (C.add 68) 4 = w2 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_19
  have t6_21 : rdRaw H6.get (C.add 116) 4 = w14 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_20
  have t6_22 : rdRaw H6.get (C.add 100) 4 = w10 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_21
  have t6_23 : rdRaw H6.get (C.add 88) 4 = w7 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_22
  have t6_24 : rdRaw H6.get (C.add 72) 4 = w3 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_23
  have t6_25 : rdRaw H6.get (C.add 120) 4 = w15 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_24
  have t6_26 : rdRaw H6.get (C.add 104) 4 = w11 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_25
  have t6_27 : rdRaw H6.get (C.add 20) 4 = s14 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_26
  have t6_28 : rdRaw H6.get (C.add 36) 4 = s24 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_27
  have t6_29 : rdRaw H6.get (C.add 44) 4 = s2c :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_28
  have t6_30 : rdRaw H6.get (C.add 56) 4 = s38 :=
    (a6.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t5_29
  have hrun := exN_trans (exN_trans (exN_trans (exN_trans (exN_trans (e1) e2) e3) e4) e5) e6
  rw [show ic + 5 + 6 + 5 + 5 + 4 + 4 = ic + 29 from by simp only [UInt64.add_assoc] <;> rfl] at hrun
  exact ⟨H6, f6, hrun, t6_9, t6_10, t6_7, t6_8, t6_5, t6_6, t6_3, t6_4, t6_1, t6_2, p6_0, t6_27, t6_28, t6_29, t6_30, ((((((a1.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)).trans (a2.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a3.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a4.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a5.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a6.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)))⟩

/-- The round state at the loop head, from the copied words `w`. -/
def setupRS (r : RS) (w : V16) : RS :=
  { r with eax := w.x7, ecx := w.x13, edx := w.x11, ebx := w.x15, ebp := w.x4, esi := w.x6, edi := w.x5,
           s0 := w.x12, s4 := w.x3, s8 := w.x0, sc := w.x2, s10 := w.x1, s18 := w.x14, s1c := w.x9,
           s20 := w.x8, s28 := 22, s30 := w.x11, s34 := w.x10 }

/-- The copy at `t + 0x3c` holds the words `w`. -/
def CopyAt (M : ByteArray) (t : UInt32) (w : V16) : Prop :=
  rdRaw M (t.add 60) 4 = w.x0 ∧ rdRaw M (t.add 64) 4 = w.x1 ∧ rdRaw M (t.add 68) 4 = w.x2 ∧
  rdRaw M (t.add 72) 4 = w.x3 ∧ rdRaw M (t.add 76) 4 = w.x4 ∧ rdRaw M (t.add 80) 4 = w.x5 ∧
  rdRaw M (t.add 84) 4 = w.x6 ∧ rdRaw M (t.add 88) 4 = w.x7 ∧ rdRaw M (t.add 92) 4 = w.x8 ∧
  rdRaw M (t.add 96) 4 = w.x9 ∧ rdRaw M (t.add 100) 4 = w.x10 ∧ rdRaw M (t.add 104) 4 = w.x11 ∧
  rdRaw M (t.add 108) 4 = w.x12 ∧ rdRaw M (t.add 112) 4 = w.x13 ∧ rdRaw M (t.add 116) 4 = w.x14 ∧
  rdRaw M (t.add 120) 4 = w.x15

theorem Agree.of_agreeOn {lo n : Nat} {A B : ByteArray} (h : AgreeOn (fun a => lo ≤ a ∧ a < lo + n) A B) :
    Agree lo n A B :=
  ⟨h.1, fun a ha hd => h.2 a ha (by omega)⟩

theorem setup_run (H : CMem) (t f : UInt32) (r : RS) (w : V16) (ic : UInt64) (hS : StackOk H.get.size t)
    (hr : Corr H.get t r) (hw : CopyAt H.get t w) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 29 (stRS H.get t r 0x10011f (efl f) ic) =
        some (stRS H'.get t (setupRS r w) 0x100190 (efl f') (ic + 29)) ∧
      Corr H'.get t (setupRS r w) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  rcases w with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15⟩ := hw
  obtain ⟨H', f', e, q8, q10, q0, q20, q1c, qc, q18, q34, q4, q28, q30, q14, q24, q2c, q38, a⟩ :=
    setupC_run H t f eax ecx edx ebx ebp esi edi w4 w0 w1 w12 w8 w5 w13 w9 w6 w2 w14 w10 w7 w3 w15 w11 s14 s24 s2c s38 ic hS hw4 hw0 hw1 hw12 hw8 hw5 hw13 hw9 hw6 hw2 hw14 hw10 hw7 hw3 hw15 hw11 hs14 hs24 hs2c hs38
  exact ⟨H', f', e, ⟨q0, q4, q8, qc, q10, q14, q18, q1c, q20, q24, q28, q2c, q30, q34, q38⟩, Agree.of_agreeOn a⟩

end Solutions.OpensslChacha20
