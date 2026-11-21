import Solutions.OpensslChacha20.RoundState
/-!
# The double round of `chacha20_core`, part 4

Generated: each `rbN` is a few instructions of the loop body, on the round state `RS`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `0x1002de`–`0x1002ee`. -/
def rb18 (r : RS) : RS := { r with eax := (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx r.ebx) 8))) 7), ecx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx r.ebx) 8), edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx r.ebx) 8)), s20 := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx r.ebx) 8)) }

theorem rb18_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1002de (efl f) ic) =
        some (stRS H'.get t (rb18 r) 0x1002ee (efl f') (ic + 6)) ∧
      Corr H'.get t (rb18 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1002ee`–`0x100301`. -/
def rb19 (r : RS) : RS := { r with edx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s18 (UInt32.add r.s4 r.ebp)) 16), ebx := (UInt32.add r.s4 r.ebp), s4 := (UInt32.add r.s4 r.ebp) }

theorem rb19_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1002ee (efl f) ic) =
        some (stRS H'.get t (rb19 r) 0x100301 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb19 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100301`–`0x100314`. -/
def rb20 (r : RS) : RS := { r with edx := (UInt32.xor r.edx (UInt32.add r.s4 (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.s1c r.edx)) 12))), ebx := (UInt32.add r.s1c r.edx), ebp := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.s1c r.edx)) 12), s4 := (UInt32.add r.s4 (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.s1c r.edx)) 12)) }

theorem rb20_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100301 (efl f) ic) =
        some (stRS H'.get t (rb20 r) 0x100314 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb20 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100314`–`0x100327`. -/
def rb21 (r : RS) : RS := { r with edx := (Ssl.Spec.Chacha.rotl r.edx 8), ebx := r.s38, ebp := (UInt32.xor r.ebp (UInt32.add r.ebx (Ssl.Spec.Chacha.rotl r.edx 8))), s18 := (Ssl.Spec.Chacha.rotl r.edx 8), s1c := (UInt32.add r.ebx (Ssl.Spec.Chacha.rotl r.edx 8)) }

theorem rb21_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100314 (efl f) ic) =
        some (stRS H'.get t (rb21 r) 0x100327 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb21 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100327`–`0x10032a`. -/
def rb22 (r : RS) : RS := { r with ebp := (Ssl.Spec.Chacha.rotl r.ebp 7) }

theorem rb22_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 1 (stRS H.get t r 0x100327 (efl f) ic) =
        some (stRS H'.get t (rb22 r) 0x10032a (efl f') (ic + 1)) ∧
      Corr H'.get t (rb22 r) ∧ Agree t.toNat 60 H.get H'.get := by
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
