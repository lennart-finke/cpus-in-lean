import Solutions.OpensslChacha20.CallC
/-!
# A block of `ChaCha20_ctr32`: the calls of `chacha20_core` and `memcpy`, in pieces

Generated: each piece is a few instructions on a memory given by the facts it reads. Addresses are
relative to `U = C - 24`, the lowest stack word, so that every offset is a small positive literal.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem callU_run (H : CMem) (C f eax ecx edx rem U inp out n : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
     :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 35 ⟨H.get, eax, ecx, edx, rem, (U.add 168), inp, out, n, 0x1000bb, efl f, ic⟩ =
        some ⟨H'.get, (U.add 84), 64, (U.add 168), rem, U, inp, 0, n, 0x100420, efl f', ic + 35⟩ ∧
      rdRaw H'.get (U.add 164) 4 = 1048774 ∧
      rdRaw H'.get (U.add 160) 4 = inp ∧
      rdRaw H'.get (U.add 156) 4 = rem ∧
      rdRaw H'.get (U.add 152) 4 = n ∧
      rdRaw H'.get (U.add 148) 4 = out ∧
      rdRaw H'.get (U.add 60) 4 = (U.add 232) ∧
      rdRaw H'.get (U.add 20) 4 = 64 ∧
      rdRaw H'.get (U.add 44) 4 = (U.add 168) ∧
      rdRaw H'.get (U.add 16) 4 = (U.add 168) ∧
      rdRaw H'.get (U.add 12) 4 = (U.add 84) ∧
      rdRaw H'.get (U.add 8) 4 = 1048860 ∧
      rdRaw H'.get (U.add 4) 4 = rem ∧
      rdRaw H'.get U 4 = out ∧
      AgreeOn (fun a => (U.toNat + 0 ≤ a ∧ a < U.toNat + 168)) H.get H'.get := by
  have hS0 := hS
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  have hz0 : H.get.size = H.get.size := rfl
  obtain ⟨H1, f1, e1, p1_0, p1_1, p1_2, a1⟩ := callU_run_0 H C f (eax) (ecx) (edx) (rem) (U) (inp) (out) (n) (ic) hS0 hU 
  have hS1 : StackOk H1.get.size C := by rw [a1.1]; exact hS0
  have hz1 : H1.get.size = H.get.size := a1.1.trans hz0
  obtain ⟨H2, f2, e2, p2_0, p2_1, p2_2, a2⟩ := callU_run_1 H1 C f1 (eax) (U) (rem) (inp) (out) (n) (ic + 5) hS1 hU 
  have hS2 : StackOk H2.get.size C := by rw [a2.1]; exact hS1
  have hz2 : H2.get.size = H.get.size := a2.1.trans hz1
  have t2_3 : rdRaw H2.get (U.add 164) 4 = 1048774 :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_0
  have t2_4 : rdRaw H2.get (U.add 160) 4 = inp :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_1
  have t2_5 : rdRaw H2.get (U.add 156) 4 = rem :=
    (a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p1_2
  obtain ⟨H3, f3, e3, p3_0, p3_1, p3_2, p3_3, p3_4, a3⟩ := callU_run_2 H2 C f2 (U) (rem) (inp) (out) (n) (ic + 5 + 5) hS2 hU 
  have hS3 : StackOk H3.get.size C := by rw [a3.1]; exact hS2
  have hz3 : H3.get.size = H.get.size := a3.1.trans hz2
  have t3_5 : rdRaw H3.get (U.add 152) 4 = n :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_0
  have t3_6 : rdRaw H3.get (U.add 148) 4 = out :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_1
  have t3_7 : rdRaw H3.get (U.add 60) 4 = (U.add 232) :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p2_2
  have t3_8 : rdRaw H3.get (U.add 164) 4 = 1048774 :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_3
  have t3_9 : rdRaw H3.get (U.add 160) 4 = inp :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_4
  have t3_10 : rdRaw H3.get (U.add 156) 4 = rem :=
    (a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t2_5
  obtain ⟨H4, f4, e4, p4_0, p4_1, a4⟩ := callU_run_3 H3 C f3 (U) (rem) (inp) (out) (n) ((U.add 84)) (ic + 5 + 5 + 5) hS3 hU p3_3 p3_0
  have hS4 : StackOk H4.get.size C := by rw [a4.1]; exact hS3
  have hz4 : H4.get.size = H.get.size := a4.1.trans hz3
  have t4_2 : rdRaw H4.get (U.add 20) 4 = 64 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_0
  have t4_3 : rdRaw H4.get (U.add 44) 4 = (U.add 168) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_1
  have t4_4 : rdRaw H4.get (U.add 16) 4 = (U.add 168) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_2
  have t4_5 : rdRaw H4.get (U.add 12) 4 = (U.add 84) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_3
  have t4_6 : rdRaw H4.get (U.add 8) 4 = 1048860 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p3_4
  have t4_7 : rdRaw H4.get (U.add 152) 4 = n :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_5
  have t4_8 : rdRaw H4.get (U.add 148) 4 = out :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_6
  have t4_9 : rdRaw H4.get (U.add 60) 4 = (U.add 232) :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_7
  have t4_10 : rdRaw H4.get (U.add 164) 4 = 1048774 :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_8
  have t4_11 : rdRaw H4.get (U.add 160) 4 = inp :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_9
  have t4_12 : rdRaw H4.get (U.add 156) 4 = rem :=
    (a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t3_10
  obtain ⟨H5, f5, e5, a5⟩ := callU_run_4 H4 C f4 (U) (rem) (inp) (out) (n) ((U.add 168)) (ic + 5 + 5 + 5 + 6) hS4 hU t4_4
  have hS5 : StackOk H5.get.size C := by rw [a5.1]; exact hS4
  have hz5 : H5.get.size = H.get.size := a5.1.trans hz4
  have t5_0 : rdRaw H5.get (U.add 4) 4 = rem :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_0
  have t5_1 : rdRaw H5.get U 4 = out :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans p4_1
  have t5_2 : rdRaw H5.get (U.add 20) 4 = 64 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_2
  have t5_3 : rdRaw H5.get (U.add 44) 4 = (U.add 168) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_3
  have t5_4 : rdRaw H5.get (U.add 16) 4 = (U.add 168) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_4
  have t5_5 : rdRaw H5.get (U.add 12) 4 = (U.add 84) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_5
  have t5_6 : rdRaw H5.get (U.add 8) 4 = 1048860 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_6
  have t5_7 : rdRaw H5.get (U.add 152) 4 = n :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_7
  have t5_8 : rdRaw H5.get (U.add 148) 4 = out :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_8
  have t5_9 : rdRaw H5.get (U.add 60) 4 = (U.add 232) :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_9
  have t5_10 : rdRaw H5.get (U.add 164) 4 = 1048774 :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_10
  have t5_11 : rdRaw H5.get (U.add 160) 4 = inp :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_11
  have t5_12 : rdRaw H5.get (U.add 156) 4 = rem :=
    (a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans t4_12
  have hrun := exN_trans (exN_trans (exN_trans (exN_trans (e1) e2) e3) e4) e5
  rw [show ic + 5 + 5 + 5 + 6 + 14 = ic + 35 from by simp only [UInt64.add_assoc] <;> rfl] at hrun
  exact ⟨H5, f5, hrun, t5_10, t5_11, t5_12, t5_7, t5_8, t5_9, t5_2, t5_3, t5_4, t5_5, t5_6, t5_0, t5_1, (((((a1.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)).trans (a2.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a3.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a4.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))).trans (a5.mono (fun a h => by (try simp only [] at h ⊢) <;> omega)))⟩

theorem retU_run (H : CMem) (C f eax ecx edx ebx U ebp esi edi out rem : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
    (hout : rdRaw H.get U 4 = out)
    (hrem : rdRaw H.get (U.add 4) 4 = rem)
    (hK0 : rdRaw H.get (U.add 8) 4 = 1048860) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, U, ebp, esi, edi, 0x10042c, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, rem, (U.add 24), ebp, out, edi, 0x10011f, efl f', ic + 4⟩ ∧
      AgreeOn (fun a => False) H.get H'.get := by
  have hS0 := hS
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  have hz0 : H.get.size = H.get.size := rfl
  obtain ⟨H1, f1, e1, a1⟩ := retU_run_0 H C f (eax) (ecx) (edx) (ebx) (U) (ebp) (esi) (edi) (out) (rem) (ic) hS0 hU hout hrem hK0
  have hS1 : StackOk H1.get.size C := by rw [a1.1]; exact hS0
  have hz1 : H1.get.size = H.get.size := a1.1.trans hz0
  have t1_0 : rdRaw H1.get U 4 = out :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hout
  have t1_1 : rdRaw H1.get (U.add 4) 4 = rem :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hrem
  have t1_2 : rdRaw H1.get (U.add 8) 4 = 1048860 :=
    (a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h) <;> sym_omega)).trans hK0
  have hrun := e1
  rw [show ic + 4 = ic + 4 from by simp only [UInt64.add_assoc] <;> rfl] at hrun
  exact ⟨H1, f1, hrun, (a1.mono (fun a h => by (try simp only [] at h ⊢) <;> omega))⟩

end Solutions.OpensslChacha20
