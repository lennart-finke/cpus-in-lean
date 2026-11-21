import Solutions.OpensslChacha20.RoundState
/-!
# The double round of `chacha20_core`, part 3

Generated: each `rbN` is a few instructions of the loop body, on the round state `RS`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `0x100271`–`0x100285`. -/
def rb12 (r : RS) : RS := { r with ebx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s8 (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi r.ecx) 12))) 8), edi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi r.ecx) 12), s8 := (UInt32.add r.s8 (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi r.ecx) 12)), s38 := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s8 (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi r.ecx) 12))) 8) }

theorem rb12_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100271 (efl f) ic) =
        some (stRS H'.get t (rb12 r) 0x100285 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb12 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100285`–`0x100298`. -/
def rb13 (r : RS) : RS := { r with ecx := r.s2c, ebx := r.s10, edi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi (UInt32.add r.ecx r.ebx)) 7), s34 := (UInt32.add r.ecx r.ebx) }

theorem rb13_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100285 (efl f) ic) =
        some (stRS H'.get t (rb13 r) 0x100298 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb13 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100298`–`0x1002a9`. -/
def rb14 (r : RS) : RS := { r with edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 16)), ebx := (UInt32.add r.ebx r.esi), esi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 16))) 12), s0 := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 16) }

theorem rb14_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100298 (efl f) ic) =
        some (stRS H'.get t (rb14 r) 0x1002a9 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb14 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1002a9`–`0x1002bd`. -/
def rb15 (r : RS) : RS := { r with edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 8)), ebx := (UInt32.add r.ebx r.esi), s0 := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 8), s10 := (UInt32.add r.ebx r.esi), s30 := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.ebx r.esi)) 8)) }

theorem rb15_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1002a9 (efl f) ic) =
        some (stRS H'.get t (rb15 r) 0x1002bd (efl f') (ic + 6)) ∧
      Corr H'.get t (rb15 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1002bd`–`0x1002cd`. -/
def rb16 (r : RS) : RS := { r with ecx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx (UInt32.add r.sc r.eax)) 16), ebx := (UInt32.add r.sc r.eax), esi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi r.edx) 7) }

theorem rb16_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1002bd (efl f) ic) =
        some (stRS H'.get t (rb16 r) 0x1002cd (efl f') (ic + 6)) ∧
      Corr H'.get t (rb16 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1002cd`–`0x1002de`. -/
def rb17 (r : RS) : RS := { r with eax := (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax (UInt32.add r.s20 r.ecx)) 12), edx := (UInt32.add r.s20 r.ecx), ebx := (UInt32.add r.ebx (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax (UInt32.add r.s20 r.ecx)) 12)), sc := (UInt32.add r.ebx (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax (UInt32.add r.s20 r.ecx)) 12)) }

theorem rb17_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1002cd (efl f) ic) =
        some (stRS H'.get t (rb17 r) 0x1002de (efl f') (ic + 6)) ∧
      Corr H'.get t (rb17 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

end Solutions.OpensslChacha20
