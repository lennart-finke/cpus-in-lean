import Solutions.OpensslChacha20.RoundRun
import Solutions.OpensslChacha20.Frame2
import Solutions.OpensslChacha20.Pro
/-! Generated pieces of `setupC_run`. -/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


theorem setupC_run_0 (H : CMem) (C f eax ecx edx ebx ebp esi edi m0_0 m0_1 m0_2 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm0_0 : rdRaw H.get (C.add 76) 4 = m0_0)
    (hm0_1 : rdRaw H.get (C.add 60) 4 = m0_1)
    (hm0_2 : rdRaw H.get (C.add 64) 4 = m0_2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, ebx, C, ebp, esi, edi, 0x10011f, efl f, ic⟩ =
        some ⟨H'.get, m0_2, ecx, edx, ebx, C, m0_0, esi, edi, 0x100133, efl f', ic + 5⟩ ∧
      rdRaw H'.get (C.add 8) 4 = m0_1 ∧
      rdRaw H'.get (C.add 16) 4 = m0_2 ∧
      AgreeOn (fun a => (C.toNat + 8 ≤ a ∧ a < C.toNat + 12) ∨ (C.toNat + 16 ≤ a ∧ a < C.toNat + 20)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem setupC_run_1 (H : CMem) (C f w1 ecx edx ebx w4 esi edi m1_0 m1_1 m1_2 m1_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm1_0 : rdRaw H.get (C.add 108) 4 = m1_0)
    (hm1_1 : rdRaw H.get (C.add 92) 4 = m1_1)
    (hm1_2 : rdRaw H.get (C.add 80) 4 = m1_2)
    (hm1_3 : rdRaw H.get (C.add 112) 4 = m1_3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, w1, ecx, edx, ebx, C, w4, esi, edi, 0x100133, efl f, ic⟩ =
        some ⟨H'.get, m1_1, m1_3, edx, ebx, C, w4, esi, m1_2, 0x10014a, efl f', ic + 6⟩ ∧
      rdRaw H'.get C 4 = m1_0 ∧
      rdRaw H'.get (C.add 32) 4 = m1_1 ∧
      AgreeOn (fun a => (C.toNat + 0 ≤ a ∧ a < C.toNat + 4) ∨ (C.toNat + 32 ≤ a ∧ a < C.toNat + 36)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem setupC_run_2 (H : CMem) (C f w8 w13 edx ebx w4 esi w5 m2_0 m2_1 m2_2 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm2_0 : rdRaw H.get (C.add 96) 4 = m2_0)
    (hm2_1 : rdRaw H.get (C.add 84) 4 = m2_1)
    (hm2_2 : rdRaw H.get (C.add 68) 4 = m2_2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, w8, w13, edx, ebx, C, w4, esi, w5, 0x10014a, efl f, ic⟩ =
        some ⟨H'.get, m2_2, w13, edx, ebx, C, w4, m2_1, w5, 0x10015e, efl f', ic + 5⟩ ∧
      rdRaw H'.get (C.add 28) 4 = m2_0 ∧
      rdRaw H'.get (C.add 12) 4 = m2_2 ∧
      AgreeOn (fun a => (C.toNat + 28 ≤ a ∧ a < C.toNat + 32) ∨ (C.toNat + 12 ≤ a ∧ a < C.toNat + 16)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem setupC_run_3 (H : CMem) (C f w2 w13 edx ebx w4 w6 w5 m3_0 m3_1 m3_2 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm3_0 : rdRaw H.get (C.add 116) 4 = m3_0)
    (hm3_1 : rdRaw H.get (C.add 100) 4 = m3_1)
    (hm3_2 : rdRaw H.get (C.add 88) 4 = m3_2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, w2, w13, edx, ebx, C, w4, w6, w5, 0x10015e, efl f, ic⟩ =
        some ⟨H'.get, m3_2, w13, edx, ebx, C, w4, w6, w5, 0x100172, efl f', ic + 5⟩ ∧
      rdRaw H'.get (C.add 24) 4 = m3_0 ∧
      rdRaw H'.get (C.add 52) 4 = m3_1 ∧
      AgreeOn (fun a => (C.toNat + 24 ≤ a ∧ a < C.toNat + 28) ∨ (C.toNat + 52 ≤ a ∧ a < C.toNat + 56)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem setupC_run_4 (H : CMem) (C f w7 w13 edx ebx w4 w6 w5 m4_0 m4_1 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm4_0 : rdRaw H.get (C.add 72) 4 = m4_0)
    (hm4_1 : rdRaw H.get (C.add 120) 4 = m4_1) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, w7, w13, edx, ebx, C, w4, w6, w5, 0x100172, efl f, ic⟩ =
        some ⟨H'.get, w7, w13, m4_0, m4_1, C, w4, w6, w5, 0x100186, efl f', ic + 4⟩ ∧
      rdRaw H'.get (C.add 4) 4 = m4_0 ∧
      rdRaw H'.get (C.add 40) 4 = 22 ∧
      AgreeOn (fun a => (C.toNat + 4 ≤ a ∧ a < C.toNat + 8) ∨ (C.toNat + 40 ≤ a ∧ a < C.toNat + 44)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem setupC_run_5 (H : CMem) (C f w7 w13 w3 w15 w4 w6 w5 m5_0 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm5_0 : rdRaw H.get (C.add 104) 4 = m5_0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, w7, w13, w3, w15, C, w4, w6, w5, 0x100186, efl f, ic⟩ =
        some ⟨H'.get, w7, w13, m5_0, w15, C, w4, w6, w5, 0x100190, efl f', ic + 4⟩ ∧
      rdRaw H'.get (C.add 48) 4 = m5_0 ∧
      AgreeOn (fun a => (C.toNat + 48 ≤ a ∧ a < C.toNat + 52)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

end Solutions.OpensslChacha20
