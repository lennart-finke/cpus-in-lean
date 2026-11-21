import Solutions.OpensslChacha20.RoundState
/-!
# The double round of `chacha20_core`, part 1

Generated: each `rbN` is a few instructions of the loop body, on the round state `RS`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `0x100190`–`0x1001a5`. -/
def rb0 (r : RS) : RS := { r with edx := r.s20, s0 := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 (UInt32.add r.s8 r.ebp)) 16), s8 := (UInt32.add r.s8 r.ebp) }

theorem rb0_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100190 (efl f) ic) =
        some (stRS H'.get t (rb0 r) 0x1001a5 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb0 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1001a5`–`0x1001b9`. -/
def rb1 (r : RS) : RS := { r with edx := (UInt32.add r.edx r.s0), ebp := (UInt32.add r.s8 (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.edx r.s0)) 12)), s8 := (UInt32.add r.s8 (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.edx r.s0)) 12)), s2c := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebp (UInt32.add r.edx r.s0)) 12) }

theorem rb1_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1001a5 (efl f) ic) =
        some (stRS H'.get t (rb1 r) 0x1001b9 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb1 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1001b9`–`0x1001cd`. -/
def rb2 (r : RS) : RS := { r with edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 r.ebp) 8)), ebp := (UInt32.xor r.s2c (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 r.ebp) 8))), s0 := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 r.ebp) 8), s20 := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.s0 r.ebp) 8)) }

theorem rb2_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1001b9 (efl f) ic) =
        some (stRS H'.get t (rb2 r) 0x1001cd (efl f') (ic + 6)) ∧
      Corr H'.get t (rb2 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1001cd`–`0x1001df`. -/
def rb3 (r : RS) : RS := { r with ecx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ecx (UInt32.add r.s10 r.edi)) 16), edx := (UInt32.add r.s10 r.edi), ebp := (Ssl.Spec.Chacha.rotl r.ebp 7), s10 := (UInt32.add r.s10 r.edi) }

theorem rb3_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1001cd (efl f) ic) =
        some (stRS H'.get t (rb3 r) 0x1001df (efl f') (ic + 6)) ∧
      Corr H'.get t (rb3 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1001df`–`0x1001f2`. -/
def rb4 (r : RS) : RS := { r with ecx := (UInt32.xor r.ecx (UInt32.add r.s10 (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi (UInt32.add r.s1c r.ecx)) 12))), edx := (UInt32.add r.s1c r.ecx), edi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi (UInt32.add r.s1c r.ecx)) 12), s10 := (UInt32.add r.s10 (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi (UInt32.add r.s1c r.ecx)) 12)) }

theorem rb4_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1001df (efl f) ic) =
        some (stRS H'.get t (rb4 r) 0x1001f2 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb4 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x1001f2`–`0x100204`. -/
def rb5 (r : RS) : RS := { r with ecx := (Ssl.Spec.Chacha.rotl r.ecx 8), edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl r.ecx 8)), edi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.edi (UInt32.add r.edx (Ssl.Spec.Chacha.rotl r.ecx 8))) 7), s1c := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl r.ecx 8)), s2c := (Ssl.Spec.Chacha.rotl r.ecx 8) }

theorem rb5_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x1001f2 (efl f) ic) =
        some (stRS H'.get t (rb5 r) 0x100204 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb5 r) ∧ Agree t.toNat 60 H.get H'.get := by
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
