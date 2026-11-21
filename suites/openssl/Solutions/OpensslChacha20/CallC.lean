import Solutions.OpensslChacha20.Pro
/-! Generated pieces of `callU_run` and `retU_run`. -/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000


theorem callU_run_0 (H : CMem) (C f eax ecx edx rem U inp out n : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
     :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, ecx, edx, rem, (U.add 168), inp, out, n, 0x1000bb, efl f, ic⟩ =
        some ⟨H'.get, eax, (U.add 232), (U.add 168), rem, (U.add 156), inp, out, n, 0x100102, efl f', ic + 5⟩ ∧
      rdRaw H'.get (U.add 164) 4 = 1048774 ∧
      rdRaw H'.get (U.add 160) 4 = inp ∧
      rdRaw H'.get (U.add 156) 4 = rem ∧
      AgreeOn (fun a => (U.toNat + 164 ≤ a ∧ a < U.toNat + 168) ∨ (U.toNat + 160 ≤ a ∧ a < U.toNat + 164) ∨ (U.toNat + 156 ≤ a ∧ a < U.toNat + 160)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem callU_run_1 (H : CMem) (C f eax U rem inp out n : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
     :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, eax, (U.add 232), (U.add 168), rem, (U.add 156), inp, out, n, 0x100102, efl f, ic⟩ =
        some ⟨H'.get, (U.add 84), (U.add 232), (U.add 168), rem, (U.add 24), inp, out, n, 0x10010f, efl f', ic + 5⟩ ∧
      rdRaw H'.get (U.add 152) 4 = n ∧
      rdRaw H'.get (U.add 148) 4 = out ∧
      rdRaw H'.get (U.add 60) 4 = (U.add 232) ∧
      AgreeOn (fun a => (U.toNat + 152 ≤ a ∧ a < U.toNat + 156) ∨ (U.toNat + 148 ≤ a ∧ a < U.toNat + 152) ∨ (U.toNat + 60 ≤ a ∧ a < U.toNat + 64)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem callU_run_2 (H : CMem) (C f U rem inp out n : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
     :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 5 ⟨H.get, (U.add 84), (U.add 232), (U.add 168), rem, (U.add 24), inp, out, n, 0x10010f, efl f, ic⟩ =
        some ⟨H'.get, (U.add 84), (U.add 232), (U.add 168), rem, (U.add 8), inp, out, n, 0x100400, efl f', ic + 5⟩ ∧
      rdRaw H'.get (U.add 20) 4 = 64 ∧
      rdRaw H'.get (U.add 44) 4 = (U.add 168) ∧
      rdRaw H'.get (U.add 16) 4 = (U.add 168) ∧
      rdRaw H'.get (U.add 12) 4 = (U.add 84) ∧
      rdRaw H'.get (U.add 8) 4 = 1048860 ∧
      AgreeOn (fun a => (U.toNat + 20 ≤ a ∧ a < U.toNat + 24) ∨ (U.toNat + 44 ≤ a ∧ a < U.toNat + 48) ∨ (U.toNat + 16 ≤ a ∧ a < U.toNat + 20) ∨ (U.toNat + 12 ≤ a ∧ a < U.toNat + 16) ∨ (U.toNat + 8 ≤ a ∧ a < U.toNat + 12)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem callU_run_3 (H : CMem) (C f U rem inp out n m3_0 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
    (hm3_0 : rdRaw H.get (U.add 12) 4 = m3_0)
    (hfix0 : rdRaw H.get (U.add 20) 4 = 64) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 ⟨H.get, (U.add 84), (U.add 232), (U.add 168), rem, (U.add 8), inp, out, n, 0x100400, efl f, ic⟩ =
        some ⟨H'.get, m3_0, 64, (U.add 168), rem, U, inp, out, n, 0x10040e, efl f', ic + 6⟩ ∧
      rdRaw H'.get (U.add 4) 4 = rem ∧
      rdRaw H'.get U 4 = out ∧
      AgreeOn (fun a => (U.toNat + 4 ≤ a ∧ a < U.toNat + 8) ∨ (U.toNat + 0 ≤ a ∧ a < U.toNat + 4)) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem callU_run_4 (H : CMem) (C f U rem inp out n m4_0 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
    (hm4_0 : rdRaw H.get (U.add 16) 4 = m4_0) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 14 ⟨H.get, (U.add 84), 64, (U.add 168), rem, U, inp, out, n, 0x10040e, efl f, ic⟩ =
        some ⟨H'.get, (U.add 84), 64, m4_0, rem, U, inp, 0, n, 0x100420, efl f', ic + 14⟩ ∧
      AgreeOn (fun a => False) H.get H'.get := by
  obtain ⟨hsz, hlo, hfit, hcode⟩ := hS
  ex_run
  refine ⟨_, _, rfl, ?_⟩
  skip
  all_goals first
    | ((conv => lhs; cbv) <;> rfl)
    | (repeat (first | exact AgreeOn.refl _ _ |
        (refine agreeOn_wr4 ?_ _ (fun k hk => ?_) <;> try ((try simp only []) <;> sym_omega))))

theorem retU_run_0 (H : CMem) (C f eax ecx edx ebx U ebp esi edi m0_0 m0_1 : UInt32) (ic : UInt64)
    (hS : StackOk H.get.size C)
    (hU : U.toNat + 24 = C.toNat)
    (hm0_0 : rdRaw H.get U 4 = m0_0)
    (hm0_1 : rdRaw H.get (U.add 4) 4 = m0_1)
    (hfix0 : rdRaw H.get (U.add 8) 4 = 1048860) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 4 ⟨H.get, eax, ecx, edx, ebx, U, ebp, esi, edi, 0x10042c, efl f, ic⟩ =
        some ⟨H'.get, eax, ecx, edx, m0_1, (U.add 24), ebp, m0_0, edi, 0x10011f, efl f', ic + 4⟩ ∧
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
