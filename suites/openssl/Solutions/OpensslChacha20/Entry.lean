import Solutions.OpensslChacha20.EntryC
/-!
# `ChaCha20_ctr32`: the entry, in pieces

Generated: each piece is a few instructions on a memory given by the facts it reads.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

theorem entry_run (H : CMem) (C f eax ecx edx ebx ebp esi edi len ctrp keyp k0 k1 k2 k3 k4 k5 k6 k7 c0 c1 c2 c3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hkp : keyp.toNat + 32 ≤ H.get.size) (hks : keyp.toNat + 32 ≤ C.toNat ∨ C.toNat + 312 ≤ keyp.toNat)
    (hcp : ctrp.toNat + 16 ≤ H.get.size) (hcs : ctrp.toNat + 16 ≤ C.toNat ∨ C.toNat + 312 ≤ ctrp.toNat)
    (hlen : rdRaw H.get (C.add 300) 4 = len)
    (hctrp : rdRaw H.get (C.add 308) 4 = ctrp)
    (hkeyp : rdRaw H.get (C.add 304) 4 = keyp)
    (hk0 : rdRaw H.get keyp 4 = k0)
    (hk1 : rdRaw H.get (keyp.add 4) 4 = k1)
    (hk2 : rdRaw H.get (keyp.add 8) 4 = k2)
    (hk3 : rdRaw H.get (keyp.add 12) 4 = k3)
    (hk4 : rdRaw H.get (keyp.add 16) 4 = k4)
    (hk5 : rdRaw H.get (keyp.add 20) 4 = k5)
    (hk6 : rdRaw H.get (keyp.add 24) 4 = k6)
    (hk7 : rdRaw H.get (keyp.add 28) 4 = k7)
    (hc0 : rdRaw H.get ctrp 4 = c0)
    (hc1 : rdRaw H.get (ctrp.add 4) 4 = c1)
    (hc2 : rdRaw H.get (ctrp.add 8) 4 = c2)
    (hc3 : rdRaw H.get (ctrp.add 12) 4 = c3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 36 ⟨H.get, eax, ecx, edx, ebx, (C.add 288), ebp, esi, edi, 0x100000, efl f, ic⟩ =
        some ⟨H'.get, c3, c2, k6, len, (C.add 144), ebp, esi, edi, 0x100090, efl f', ic + 36⟩ ∧
      rdRaw H'.get (C.add 284) 4 = ebp ∧
      rdRaw H'.get (C.add 280) 4 = ebx ∧
      rdRaw H'.get (C.add 276) 4 = edi ∧
      rdRaw H'.get (C.add 272) 4 = esi ∧
      rdRaw H'.get (C.add 144) 4 = 1634760805 ∧
      rdRaw H'.get (C.add 148) 4 = 857760878 ∧
      rdRaw H'.get (C.add 152) 4 = 2036477234 ∧
      rdRaw H'.get (C.add 156) 4 = 1797285236 ∧
      rdRaw H'.get (C.add 160) 4 = k0 ∧
      rdRaw H'.get (C.add 164) 4 = k1 ∧
      rdRaw H'.get (C.add 168) 4 = k2 ∧
      rdRaw H'.get (C.add 172) 4 = k3 ∧
      rdRaw H'.get (C.add 176) 4 = k4 ∧
      rdRaw H'.get (C.add 180) 4 = k5 ∧
      rdRaw H'.get (C.add 184) 4 = k6 ∧
      rdRaw H'.get (C.add 188) 4 = k7 ∧
      rdRaw H'.get (C.add 192) 4 = c0 ∧
      rdRaw H'.get (C.add 196) 4 = c1 ∧
      rdRaw H'.get (C.add 200) 4 = c2 ∧
      rdRaw H'.get (C.add 204) 4 = c3 ∧
      AgreeOn (fun a => (C.toNat + 144 ≤ a ∧ a < C.toNat + 288)) H.get H'.get := by
  have hS0 := hS
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  have hz0 : H.get.size = H.get.size := rfl
  obtain ⟨H1, f1, e1, p1_0, p1_1, p1_2, p1_3, a1⟩ := entry_run_0 H C f (eax) (ecx) (edx) (ebx) (ebp) (esi) (edi) (len) (ctrp) (keyp) (ic) hS0 hlen hctrp hkeyp
  have hS1 : StackOk H1.get.size C := by rw [a1.1]; exact hS0
  have hz1 : H1.get.size = H.get.size := a1.1.trans hz0
  have t1_4 : rdRaw H1.get (C.add 300) 4 = len := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hlen
  have t1_5 : rdRaw H1.get (C.add 308) 4 = ctrp := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hctrp
  have t1_6 : rdRaw H1.get (C.add 304) 4 = keyp := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hkeyp
  have t1_7 : rdRaw H1.get keyp 4 = k0 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk0
  have t1_8 : rdRaw H1.get (keyp.add 4) 4 = k1 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk1
  have t1_9 : rdRaw H1.get (keyp.add 8) 4 = k2 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk2
  have t1_10 : rdRaw H1.get (keyp.add 12) 4 = k3 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk3
  have t1_11 : rdRaw H1.get (keyp.add 16) 4 = k4 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk4
  have t1_12 : rdRaw H1.get (keyp.add 20) 4 = k5 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk5
  have t1_13 : rdRaw H1.get (keyp.add 24) 4 = k6 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk6
  have t1_14 : rdRaw H1.get (keyp.add 28) 4 = k7 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hk7
  have t1_15 : rdRaw H1.get ctrp 4 = c0 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hc0
  have t1_16 : rdRaw H1.get (ctrp.add 4) 4 = c1 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hc1
  have t1_17 : rdRaw H1.get (ctrp.add 8) 4 = c2 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hc2
  have t1_18 : rdRaw H1.get (ctrp.add 12) 4 = c3 := by
    rw [a1.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact hc3
  obtain ⟨H2, f2, e2, p2_0, p2_1, p2_2, p2_3, a2⟩ := entry_run_1 H1 C f1 (ctrp) (keyp) (edx) (len) (ebp) (esi) (edi) (ic + 8) hS1 
  have hS2 : StackOk H2.get.size C := by rw [a2.1]; exact hS1
  have hz2 : H2.get.size = H.get.size := a2.1.trans hz1
  have t2_4 : rdRaw H2.get (C.add 284) 4 = ebp := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p1_0
  have t2_5 : rdRaw H2.get (C.add 280) 4 = ebx := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p1_1
  have t2_6 : rdRaw H2.get (C.add 276) 4 = edi := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p1_2
  have t2_7 : rdRaw H2.get (C.add 272) 4 = esi := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p1_3
  have t2_8 : rdRaw H2.get (C.add 300) 4 = len := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_4
  have t2_9 : rdRaw H2.get (C.add 308) 4 = ctrp := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_5
  have t2_10 : rdRaw H2.get (C.add 304) 4 = keyp := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_6
  have t2_11 : rdRaw H2.get keyp 4 = k0 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_7
  have t2_12 : rdRaw H2.get (keyp.add 4) 4 = k1 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_8
  have t2_13 : rdRaw H2.get (keyp.add 8) 4 = k2 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_9
  have t2_14 : rdRaw H2.get (keyp.add 12) 4 = k3 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_10
  have t2_15 : rdRaw H2.get (keyp.add 16) 4 = k4 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_11
  have t2_16 : rdRaw H2.get (keyp.add 20) 4 = k5 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_12
  have t2_17 : rdRaw H2.get (keyp.add 24) 4 = k6 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_13
  have t2_18 : rdRaw H2.get (keyp.add 28) 4 = k7 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_14
  have t2_19 : rdRaw H2.get ctrp 4 = c0 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_15
  have t2_20 : rdRaw H2.get (ctrp.add 4) 4 = c1 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_16
  have t2_21 : rdRaw H2.get (ctrp.add 8) 4 = c2 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_17
  have t2_22 : rdRaw H2.get (ctrp.add 12) 4 = c3 := by
    rw [a2.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t1_18
  obtain ⟨H3, f3, e3, p3_0, p3_1, p3_2, p3_3, a3⟩ := entry_run_2 H2 C f2 (ctrp) (keyp) (edx) (len) (ebp) (esi) (edi) (k0) (k1) (k2) (k3) (ic + 8 + 4) hS2 (by rw [hz2]; exact hkp) hks t2_11 t2_12 t2_13 t2_14
  have hS3 : StackOk H3.get.size C := by rw [a3.1]; exact hS2
  have hz3 : H3.get.size = H.get.size := a3.1.trans hz2
  have t3_4 : rdRaw H3.get (C.add 144) 4 = 1634760805 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p2_0
  have t3_5 : rdRaw H3.get (C.add 148) 4 = 857760878 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p2_1
  have t3_6 : rdRaw H3.get (C.add 152) 4 = 2036477234 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p2_2
  have t3_7 : rdRaw H3.get (C.add 156) 4 = 1797285236 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p2_3
  have t3_8 : rdRaw H3.get (C.add 284) 4 = ebp := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_4
  have t3_9 : rdRaw H3.get (C.add 280) 4 = ebx := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_5
  have t3_10 : rdRaw H3.get (C.add 276) 4 = edi := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_6
  have t3_11 : rdRaw H3.get (C.add 272) 4 = esi := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_7
  have t3_12 : rdRaw H3.get (C.add 300) 4 = len := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_8
  have t3_13 : rdRaw H3.get (C.add 308) 4 = ctrp := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_9
  have t3_14 : rdRaw H3.get (C.add 304) 4 = keyp := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_10
  have t3_15 : rdRaw H3.get keyp 4 = k0 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_11
  have t3_16 : rdRaw H3.get (keyp.add 4) 4 = k1 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_12
  have t3_17 : rdRaw H3.get (keyp.add 8) 4 = k2 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_13
  have t3_18 : rdRaw H3.get (keyp.add 12) 4 = k3 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_14
  have t3_19 : rdRaw H3.get (keyp.add 16) 4 = k4 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_15
  have t3_20 : rdRaw H3.get (keyp.add 20) 4 = k5 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_16
  have t3_21 : rdRaw H3.get (keyp.add 24) 4 = k6 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_17
  have t3_22 : rdRaw H3.get (keyp.add 28) 4 = k7 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_18
  have t3_23 : rdRaw H3.get ctrp 4 = c0 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_19
  have t3_24 : rdRaw H3.get (ctrp.add 4) 4 = c1 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_20
  have t3_25 : rdRaw H3.get (ctrp.add 8) 4 = c2 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_21
  have t3_26 : rdRaw H3.get (ctrp.add 12) 4 = c3 := by
    rw [a3.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t2_22
  obtain ⟨H4, f4, e4, p4_0, p4_1, p4_2, p4_3, a4⟩ := entry_run_3 H3 C f3 (ctrp) (keyp) (k3) (len) (ebp) (esi) (edi) (k4) (k5) (k6) (k7) (ic + 8 + 4 + 8) hS3 (by rw [hz3]; exact hkp) hks t3_19 t3_20 t3_21 t3_22
  have hS4 : StackOk H4.get.size C := by rw [a4.1]; exact hS3
  have hz4 : H4.get.size = H.get.size := a4.1.trans hz3
  have t4_4 : rdRaw H4.get (C.add 160) 4 = k0 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p3_0
  have t4_5 : rdRaw H4.get (C.add 164) 4 = k1 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p3_1
  have t4_6 : rdRaw H4.get (C.add 168) 4 = k2 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p3_2
  have t4_7 : rdRaw H4.get (C.add 172) 4 = k3 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p3_3
  have t4_8 : rdRaw H4.get (C.add 144) 4 = 1634760805 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_4
  have t4_9 : rdRaw H4.get (C.add 148) 4 = 857760878 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_5
  have t4_10 : rdRaw H4.get (C.add 152) 4 = 2036477234 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_6
  have t4_11 : rdRaw H4.get (C.add 156) 4 = 1797285236 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_7
  have t4_12 : rdRaw H4.get (C.add 284) 4 = ebp := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_8
  have t4_13 : rdRaw H4.get (C.add 280) 4 = ebx := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_9
  have t4_14 : rdRaw H4.get (C.add 276) 4 = edi := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_10
  have t4_15 : rdRaw H4.get (C.add 272) 4 = esi := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_11
  have t4_16 : rdRaw H4.get (C.add 300) 4 = len := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_12
  have t4_17 : rdRaw H4.get (C.add 308) 4 = ctrp := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_13
  have t4_18 : rdRaw H4.get (C.add 304) 4 = keyp := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_14
  have t4_19 : rdRaw H4.get keyp 4 = k0 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_15
  have t4_20 : rdRaw H4.get (keyp.add 4) 4 = k1 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_16
  have t4_21 : rdRaw H4.get (keyp.add 8) 4 = k2 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_17
  have t4_22 : rdRaw H4.get (keyp.add 12) 4 = k3 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_18
  have t4_23 : rdRaw H4.get (keyp.add 16) 4 = k4 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_19
  have t4_24 : rdRaw H4.get (keyp.add 20) 4 = k5 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_20
  have t4_25 : rdRaw H4.get (keyp.add 24) 4 = k6 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_21
  have t4_26 : rdRaw H4.get (keyp.add 28) 4 = k7 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_22
  have t4_27 : rdRaw H4.get ctrp 4 = c0 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_23
  have t4_28 : rdRaw H4.get (ctrp.add 4) 4 = c1 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_24
  have t4_29 : rdRaw H4.get (ctrp.add 8) 4 = c2 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_25
  have t4_30 : rdRaw H4.get (ctrp.add 12) 4 = c3 := by
    rw [a4.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t3_26
  obtain ⟨H5, f5, e5, p5_0, p5_1, p5_2, p5_3, a5⟩ := entry_run_4 H4 C f4 (ctrp) (k7) (k6) (len) (ebp) (esi) (edi) (c0) (c1) (c2) (c3) (ic + 8 + 4 + 8 + 8) hS4 (by rw [hz4]; exact hcp) hcs t4_27 t4_28 t4_29 t4_30
  have hS5 : StackOk H5.get.size C := by rw [a5.1]; exact hS4
  have hz5 : H5.get.size = H.get.size := a5.1.trans hz4
  have t5_4 : rdRaw H5.get (C.add 176) 4 = k4 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p4_0
  have t5_5 : rdRaw H5.get (C.add 180) 4 = k5 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p4_1
  have t5_6 : rdRaw H5.get (C.add 184) 4 = k6 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p4_2
  have t5_7 : rdRaw H5.get (C.add 188) 4 = k7 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact p4_3
  have t5_8 : rdRaw H5.get (C.add 160) 4 = k0 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_4
  have t5_9 : rdRaw H5.get (C.add 164) 4 = k1 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_5
  have t5_10 : rdRaw H5.get (C.add 168) 4 = k2 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_6
  have t5_11 : rdRaw H5.get (C.add 172) 4 = k3 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_7
  have t5_12 : rdRaw H5.get (C.add 144) 4 = 1634760805 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_8
  have t5_13 : rdRaw H5.get (C.add 148) 4 = 857760878 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_9
  have t5_14 : rdRaw H5.get (C.add 152) 4 = 2036477234 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_10
  have t5_15 : rdRaw H5.get (C.add 156) 4 = 1797285236 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_11
  have t5_16 : rdRaw H5.get (C.add 284) 4 = ebp := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_12
  have t5_17 : rdRaw H5.get (C.add 280) 4 = ebx := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_13
  have t5_18 : rdRaw H5.get (C.add 276) 4 = edi := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_14
  have t5_19 : rdRaw H5.get (C.add 272) 4 = esi := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_15
  have t5_20 : rdRaw H5.get (C.add 300) 4 = len := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_16
  have t5_21 : rdRaw H5.get (C.add 308) 4 = ctrp := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_17
  have t5_22 : rdRaw H5.get (C.add 304) 4 = keyp := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_18
  have t5_23 : rdRaw H5.get keyp 4 = k0 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_19
  have t5_24 : rdRaw H5.get (keyp.add 4) 4 = k1 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_20
  have t5_25 : rdRaw H5.get (keyp.add 8) 4 = k2 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_21
  have t5_26 : rdRaw H5.get (keyp.add 12) 4 = k3 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_22
  have t5_27 : rdRaw H5.get (keyp.add 16) 4 = k4 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_23
  have t5_28 : rdRaw H5.get (keyp.add 20) 4 = k5 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_24
  have t5_29 : rdRaw H5.get (keyp.add 24) 4 = k6 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_25
  have t5_30 : rdRaw H5.get (keyp.add 28) 4 = k7 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_26
  have t5_31 : rdRaw H5.get ctrp 4 = c0 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_27
  have t5_32 : rdRaw H5.get (ctrp.add 4) 4 = c1 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_28
  have t5_33 : rdRaw H5.get (ctrp.add 8) 4 = c2 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_29
  have t5_34 : rdRaw H5.get (ctrp.add 12) 4 = c3 := by
    rw [a5.rdRaw4 (by sym_omega) (fun k hk h => by (try simp only [] at h); sym_omega)]; exact t4_30
  have hrun := exN_trans (exN_trans (exN_trans (exN_trans (e1) e2) e3) e4) e5
  rw [show ic + 8 + 4 + 8 + 8 + 8 = ic + 36 from by simp only [UInt64.add_assoc]; rfl] at hrun
  exact ⟨H5, f5, hrun, t5_16, t5_17, t5_18, t5_19, t5_12, t5_13, t5_14, t5_15, t5_8, t5_9, t5_10, t5_11, t5_4, t5_5, t5_6, t5_7, p5_0, p5_1, p5_2, p5_3, (((((a1.mono (fun a h => by (try simp only [] at h ⊢); omega)).trans (a2.mono (fun a h => by (try simp only [] at h ⊢); omega))).trans (a3.mono (fun a h => by (try simp only [] at h ⊢); omega))).trans (a4.mono (fun a h => by (try simp only [] at h ⊢); omega))).trans (a5.mono (fun a h => by (try simp only [] at h ⊢); omega)))⟩

end Solutions.OpensslChacha20
