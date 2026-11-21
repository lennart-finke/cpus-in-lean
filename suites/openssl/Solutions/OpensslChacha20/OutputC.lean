import Solutions.OpensslChacha20.RoundLoop
import Solutions.OpensslChacha20.Frame2
import Solutions.OpensslChacha20.Pro
/-! Generated pieces of `outC_run`. -/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


theorem outC_run_0 (H : CMem) (C f eax ecx edx ebx ebp esi edi m0_0 m0_1 m0_2 m0_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm0_0 : rdRaw H.get (C.add 8) 4 = m0_0)
    (hm0_1 : rdRaw H.get (C.add 144) 4 = m0_1)
    (hm0_2 : rdRaw H.get (C.add 16) 4 = m0_2)
    (hm0_3 : rdRaw H.get (C.add 148) 4 = m0_3)
    (hfix0 : rdRaw H.get (C.add 20) 4 = (C.add 144))
    (hfix1 : rdRaw H.get (C.add 36) 4 = (C.add 208)) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 11 ⟨H.get, eax, ecx, edx, ebx, C, ebp, esi, edi, 0x10033e, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, (UInt32.add m0_2 m0_3), ebx, C, ebp, (C.add 208), edi, 0x100364, efl f', ic + 11⟩ ∧
      rdRaw H'.get (C.add 40) 4 = esi ∧
      rdRaw H'.get (C.add 208) 4 = (UInt32.add m0_0 m0_1) ∧
      rdRaw H'.get (C.add 212) 4 = (UInt32.add m0_2 m0_3) ∧
      AgreeOn (fun a => (C.toNat + 40 ≤ a ∧ a < C.toNat + 44) ∨ (C.toNat + 208 ≤ a ∧ a < C.toNat + 212) ∨ (C.toNat + 212 ≤ a ∧ a < C.toNat + 216)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_1 (H : CMem) (C f eax ecx r1_edx ebx ebp edi m1_0 m1_1 m1_2 m1_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm1_0 : rdRaw H.get (C.add 12) 4 = m1_0)
    (hm1_1 : rdRaw H.get (C.add 152) 4 = m1_1)
    (hm1_2 : rdRaw H.get (C.add 4) 4 = m1_2)
    (hm1_3 : rdRaw H.get (C.add 156) 4 = m1_3)
    (hfix0 : rdRaw H.get (C.add 20) 4 = (C.add 144))
    (hfix1 : rdRaw H.get (C.add 36) 4 = (C.add 208)) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 10 ⟨H.get, eax, ecx, r1_edx, ebx, C, ebp, (C.add 208), edi, 0x100364, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, (UInt32.add m1_2 m1_3), ebx, C, ebp, (C.add 208), edi, 0x100388, efl f', ic + 10⟩ ∧
      rdRaw H'.get (C.add 216) 4 = (UInt32.add m1_0 m1_1) ∧
      rdRaw H'.get (C.add 220) 4 = (UInt32.add m1_2 m1_3) ∧
      AgreeOn (fun a => (C.toNat + 216 ≤ a ∧ a < C.toNat + 220) ∨ (C.toNat + 220 ≤ a ∧ a < C.toNat + 224)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_2 (H : CMem) (C f eax ecx r2_edx ebx ebp edi m2_0 m2_1 m2_2 m2_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm2_0 : rdRaw H.get (C.add 160) 4 = m2_0)
    (hm2_1 : rdRaw H.get (C.add 164) 4 = m2_1)
    (hm2_2 : rdRaw H.get (C.add 40) 4 = m2_2)
    (hm2_3 : rdRaw H.get (C.add 168) 4 = m2_3)
    (hfix0 : rdRaw H.get (C.add 20) 4 = (C.add 144)) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 10 ⟨H.get, eax, ecx, r2_edx, ebx, C, ebp, (C.add 208), edi, 0x100388, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, (C.add 208), ebx, C, (C.add 144), (UInt32.add m2_2 m2_3), (UInt32.add edi m2_1), 0x1003a8, efl f', ic + 10⟩ ∧
      rdRaw H'.get (C.add 224) 4 = (UInt32.add ebp m2_0) ∧
      rdRaw H'.get (C.add 228) 4 = (UInt32.add edi m2_1) ∧
      rdRaw H'.get (C.add 232) 4 = (UInt32.add m2_2 m2_3) ∧
      AgreeOn (fun a => (C.toNat + 224 ≤ a ∧ a < C.toNat + 228) ∨ (C.toNat + 228 ≤ a ∧ a < C.toNat + 232) ∨ (C.toNat + 232 ≤ a ∧ a < C.toNat + 236)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_3 (H : CMem) (C f eax ecx ebx r3_esi r3_edi m3_0 m3_1 m3_2 m3_3 m3_4 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm3_0 : rdRaw H.get (C.add 172) 4 = m3_0)
    (hm3_1 : rdRaw H.get (C.add 32) 4 = m3_1)
    (hm3_2 : rdRaw H.get (C.add 176) 4 = m3_2)
    (hm3_3 : rdRaw H.get (C.add 28) 4 = m3_3)
    (hm3_4 : rdRaw H.get (C.add 180) 4 = m3_4) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, (C.add 208), ebx, C, (C.add 144), r3_esi, r3_edi, 0x1003a8, efl f, ic⟩ =
        some ⟨H'.get, (UInt32.add m3_3 m3_4), ecx, (C.add 208), ebx, C, (C.add 144), r3_esi, r3_edi, 0x1003c2, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 236) 4 = (UInt32.add eax m3_0) ∧
      rdRaw H'.get (C.add 240) 4 = (UInt32.add m3_1 m3_2) ∧
      rdRaw H'.get (C.add 244) 4 = (UInt32.add m3_3 m3_4) ∧
      AgreeOn (fun a => (C.toNat + 236 ≤ a ∧ a < C.toNat + 240) ∨ (C.toNat + 240 ≤ a ∧ a < C.toNat + 244) ∨ (C.toNat + 244 ≤ a ∧ a < C.toNat + 248)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_4 (H : CMem) (C f r4_eax ecx ebx r4_esi r4_edi m4_0 m4_1 m4_2 m4_3 m4_4 m4_5 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm4_0 : rdRaw H.get (C.add 52) 4 = m4_0)
    (hm4_1 : rdRaw H.get (C.add 184) 4 = m4_1)
    (hm4_2 : rdRaw H.get (C.add 48) 4 = m4_2)
    (hm4_3 : rdRaw H.get (C.add 188) 4 = m4_3)
    (hm4_4 : rdRaw H.get C 4 = m4_4)
    (hm4_5 : rdRaw H.get (C.add 192) 4 = m4_5) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, r4_eax, ecx, (C.add 208), ebx, C, (C.add 144), r4_esi, r4_edi, 0x1003c2, efl f, ic⟩ =
        some ⟨H'.get, (UInt32.add m4_4 m4_5), ecx, (C.add 208), ebx, C, (C.add 144), r4_esi, r4_edi, 0x1003dc, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 248) 4 = (UInt32.add m4_0 m4_1) ∧
      rdRaw H'.get (C.add 252) 4 = (UInt32.add m4_2 m4_3) ∧
      AgreeOn (fun a => (C.toNat + 248 ≤ a ∧ a < C.toNat + 252) ∨ (C.toNat + 252 ≤ a ∧ a < C.toNat + 256)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_5 (H : CMem) (C f r5_eax ecx ebx r5_esi r5_edi m5_0 m5_1 m5_2 m5_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm5_0 : rdRaw H.get (C.add 196) 4 = m5_0)
    (hm5_1 : rdRaw H.get (C.add 24) 4 = m5_1)
    (hm5_2 : rdRaw H.get (C.add 200) 4 = m5_2)
    (hm5_3 : rdRaw H.get (C.add 204) 4 = m5_3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, r5_eax, ecx, (C.add 208), ebx, C, (C.add 144), r5_esi, r5_edi, 0x1003dc, efl f, ic⟩ =
        some ⟨H'.get, (UInt32.add m5_1 m5_2), (UInt32.add ecx m5_0), (C.add 208), (UInt32.add ebx m5_3), C, (C.add 144), r5_esi, r5_edi, 0x1003f5, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 256) 4 = r5_eax ∧
      rdRaw H'.get (C.add 260) 4 = (UInt32.add ecx m5_0) ∧
      rdRaw H'.get (C.add 264) 4 = (UInt32.add m5_1 m5_2) ∧
      rdRaw H'.get (C.add 268) 4 = (UInt32.add ebx m5_3) ∧
      AgreeOn (fun a => (C.toNat + 256 ≤ a ∧ a < C.toNat + 260) ∨ (C.toNat + 260 ≤ a ∧ a < C.toNat + 264) ∨ (C.toNat + 264 ≤ a ∧ a < C.toNat + 268) ∨ (C.toNat + 268 ≤ a ∧ a < C.toNat + 272)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem outC_run_6 (H : CMem) (C f r6_eax r6_ecx r6_ebx r6_esi r6_edi m6_0 m6_1 m6_2 m6_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm6_0 : rdRaw H.get (C.add 124) 4 = m6_0)
    (hm6_1 : rdRaw H.get (C.add 128) 4 = m6_1)
    (hm6_2 : rdRaw H.get (C.add 132) 4 = m6_2)
    (hm6_3 : rdRaw H.get (C.add 136) 4 = m6_3)
    (hfix0 : rdRaw H.get (C.add 140) 4 = 1048774) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, r6_eax, r6_ecx, (C.add 208), r6_ebx, C, (C.add 144), r6_esi, r6_edi, 0x1003f5, efl f, ic⟩ =
        some ⟨H'.get, r6_eax, r6_ecx, (C.add 208), m6_2, (C.add 144), m6_3, m6_0, m6_1, 0x1000c6, efl f', ic + 6⟩ ∧
      AgreeOn (fun a => False) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  skip
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

end Solutions.OpensslChacha20
