import Solutions.OpensslChacha20.Pro
/-! Generated pieces of `entry_run`. -/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


theorem entry_run_0 (H : CMem) (C f eax ecx edx ebx ebp esi edi m0_0 m0_1 m0_2 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hm0_0 : rdRaw H.get (C.add 300) 4 = m0_0)
    (hm0_1 : rdRaw H.get (C.add 308) 4 = m0_1)
    (hm0_2 : rdRaw H.get (C.add 304) 4 = m0_2) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, eax, ecx, edx, ebx, (C.add 288), ebp, esi, edi, 0x100000, efl f, ic⟩ =
        some ⟨H'.get, m0_1, m0_2, edx, m0_0, (C.add 144), ebp, esi, edi, 0x10001f, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 284) 4 = ebp ∧
      rdRaw H'.get (C.add 280) 4 = ebx ∧
      rdRaw H'.get (C.add 276) 4 = edi ∧
      rdRaw H'.get (C.add 272) 4 = esi ∧
      AgreeOn (fun a => (C.toNat + 284 ≤ a ∧ a < C.toNat + 288) ∨ (C.toNat + 280 ≤ a ∧ a < C.toNat + 284) ∨ (C.toNat + 276 ≤ a ∧ a < C.toNat + 280) ∨ (C.toNat + 272 ≤ a ∧ a < C.toNat + 276)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem entry_run_1 (H : CMem) (C f ctrp keyp edx len ebp esi edi : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
     :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, ctrp, keyp, edx, len, (C.add 144), ebp, esi, edi, 0x10001f, efl f, ic⟩ =
        some ⟨H'.get, ctrp, keyp, edx, len, (C.add 144), ebp, esi, edi, 0x10003e, efl f', ic + 4⟩ ∧
      rdRaw H'.get (C.add 144) 4 = 1634760805 ∧
      rdRaw H'.get (C.add 148) 4 = 857760878 ∧
      rdRaw H'.get (C.add 152) 4 = 2036477234 ∧
      rdRaw H'.get (C.add 156) 4 = 1797285236 ∧
      AgreeOn (fun a => (C.toNat + 144 ≤ a ∧ a < C.toNat + 148) ∨ (C.toNat + 148 ≤ a ∧ a < C.toNat + 152) ∨ (C.toNat + 152 ≤ a ∧ a < C.toNat + 156) ∨ (C.toNat + 156 ≤ a ∧ a < C.toNat + 160)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem entry_run_2 (H : CMem) (C f ctrp keyp edx len ebp esi edi m2_0 m2_1 m2_2 m2_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hkp : keyp.toNat + 32 ≤ H.get.size) (hks : keyp.toNat + 32 ≤ C.toNat ∨ C.toNat + 312 ≤ keyp.toNat)
    (hm2_0 : rdRaw H.get keyp 4 = m2_0)
    (hm2_1 : rdRaw H.get (keyp.add 4) 4 = m2_1)
    (hm2_2 : rdRaw H.get (keyp.add 8) 4 = m2_2)
    (hm2_3 : rdRaw H.get (keyp.add 12) 4 = m2_3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, ctrp, keyp, edx, len, (C.add 144), ebp, esi, edi, 0x10003e, efl f, ic⟩ =
        some ⟨H'.get, ctrp, keyp, m2_3, len, (C.add 144), ebp, esi, edi, 0x100059, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 160) 4 = m2_0 ∧
      rdRaw H'.get (C.add 164) 4 = m2_1 ∧
      rdRaw H'.get (C.add 168) 4 = m2_2 ∧
      rdRaw H'.get (C.add 172) 4 = m2_3 ∧
      AgreeOn (fun a => (C.toNat + 160 ≤ a ∧ a < C.toNat + 164) ∨ (C.toNat + 164 ≤ a ∧ a < C.toNat + 168) ∨ (C.toNat + 168 ≤ a ∧ a < C.toNat + 172) ∨ (C.toNat + 172 ≤ a ∧ a < C.toNat + 176)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem entry_run_3 (H : CMem) (C f ctrp keyp k3 len ebp esi edi m3_0 m3_1 m3_2 m3_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hkp : keyp.toNat + 32 ≤ H.get.size) (hks : keyp.toNat + 32 ≤ C.toNat ∨ C.toNat + 312 ≤ keyp.toNat)
    (hm3_0 : rdRaw H.get (keyp.add 16) 4 = m3_0)
    (hm3_1 : rdRaw H.get (keyp.add 20) 4 = m3_1)
    (hm3_2 : rdRaw H.get (keyp.add 24) 4 = m3_2)
    (hm3_3 : rdRaw H.get (keyp.add 28) 4 = m3_3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, ctrp, keyp, k3, len, (C.add 144), ebp, esi, edi, 0x100059, efl f, ic⟩ =
        some ⟨H'.get, ctrp, m3_3, m3_2, len, (C.add 144), ebp, esi, edi, 0x100075, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 176) 4 = m3_0 ∧
      rdRaw H'.get (C.add 180) 4 = m3_1 ∧
      rdRaw H'.get (C.add 184) 4 = m3_2 ∧
      rdRaw H'.get (C.add 188) 4 = m3_3 ∧
      AgreeOn (fun a => (C.toNat + 176 ≤ a ∧ a < C.toNat + 180) ∨ (C.toNat + 180 ≤ a ∧ a < C.toNat + 184) ∨ (C.toNat + 184 ≤ a ∧ a < C.toNat + 188) ∨ (C.toNat + 188 ≤ a ∧ a < C.toNat + 192)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem entry_run_4 (H : CMem) (C f ctrp k7 k6 len ebp esi edi m4_0 m4_1 m4_2 m4_3 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hcp : ctrp.toNat + 16 ≤ H.get.size) (hcs : ctrp.toNat + 16 ≤ C.toNat ∨ C.toNat + 312 ≤ ctrp.toNat)
    (hm4_0 : rdRaw H.get ctrp 4 = m4_0)
    (hm4_1 : rdRaw H.get (ctrp.add 4) 4 = m4_1)
    (hm4_2 : rdRaw H.get (ctrp.add 8) 4 = m4_2)
    (hm4_3 : rdRaw H.get (ctrp.add 12) 4 = m4_3) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 8 ⟨H.get, ctrp, k7, k6, len, (C.add 144), ebp, esi, edi, 0x100075, efl f, ic⟩ =
        some ⟨H'.get, m4_3, m4_2, k6, len, (C.add 144), ebp, esi, edi, 0x100090, efl f', ic + 8⟩ ∧
      rdRaw H'.get (C.add 192) 4 = m4_0 ∧
      rdRaw H'.get (C.add 196) 4 = m4_1 ∧
      rdRaw H'.get (C.add 200) 4 = m4_2 ∧
      rdRaw H'.get (C.add 204) 4 = m4_3 ∧
      AgreeOn (fun a => (C.toNat + 192 ≤ a ∧ a < C.toNat + 196) ∨ (C.toNat + 196 ≤ a ∧ a < C.toNat + 200) ∨ (C.toNat + 200 ≤ a ∧ a < C.toNat + 204) ∨ (C.toNat + 204 ≤ a ∧ a < C.toNat + 208)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

end Solutions.OpensslChacha20
