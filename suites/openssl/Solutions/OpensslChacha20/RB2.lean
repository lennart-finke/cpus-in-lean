import Solutions.OpensslChacha20.RoundState
/-!
# The double round of `chacha20_core`, part 2

Generated: each `rbN` is a few instructions of the loop body, on the round state `RS`.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- `0x100204`–`0x100217`. -/
def rb6 (r : RS) : RS := { r with ecx := (UInt32.add r.sc r.esi), edx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.s18 (UInt32.add r.sc r.esi)) 16), sc := (UInt32.add r.sc r.esi) }

theorem rb6_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100204 (efl f) ic) =
        some (stRS H'.get t (rb6 r) 0x100217 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb6 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x100217`–`0x10022a`. -/
def rb7 (r : RS) : RS := { r with ecx := (UInt32.add r.s34 r.edx), edx := (UInt32.xor r.edx (UInt32.add r.sc (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi (UInt32.add r.s34 r.edx)) 12))), esi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi (UInt32.add r.s34 r.edx)) 12), sc := (UInt32.add r.sc (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi (UInt32.add r.s34 r.edx)) 12)) }

theorem rb7_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x100217 (efl f) ic) =
        some (stRS H'.get t (rb7 r) 0x10022a (efl f') (ic + 6)) ∧
      Corr H'.get t (rb7 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x10022a`–`0x10023c`. -/
def rb8 (r : RS) : RS := { r with ecx := (UInt32.add r.ecx (Ssl.Spec.Chacha.rotl r.edx 8)), edx := r.s4, esi := (Ssl.Spec.Chacha.rotl (UInt32.xor r.esi (UInt32.add r.ecx (Ssl.Spec.Chacha.rotl r.edx 8))) 7), s18 := (Ssl.Spec.Chacha.rotl r.edx 8) }

theorem rb8_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x10022a (efl f) ic) =
        some (stRS H'.get t (rb8 r) 0x10023c (efl f') (ic + 6)) ∧
      Corr H'.get t (rb8 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x10023c`–`0x10024d`. -/
def rb9 (r : RS) : RS := { r with edx := (UInt32.add r.s30 (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.edx r.eax)) 16)), ebx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.edx r.eax)) 16), s4 := (UInt32.add r.edx r.eax) }

theorem rb9_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x10023c (efl f) ic) =
        some (stRS H'.get t (rb9 r) 0x10024d (efl f') (ic + 6)) ∧
      Corr H'.get t (rb9 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x10024d`–`0x10025f`. -/
def rb10 (r : RS) : RS := { r with eax := (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax r.edx) 12), edx := (UInt32.add r.edx (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s4 (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax r.edx) 12))) 8)), ebx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s4 (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax r.edx) 12))) 8), s4 := (UInt32.add r.s4 (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax r.edx) 12)) }

theorem rb10_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x10024d (efl f) ic) =
        some (stRS H'.get t (rb10 r) 0x10025f (efl f') (ic + 6)) ∧
      Corr H'.get t (rb10 r) ∧ Agree t.toNat 60 H.get H'.get := by
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30, s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;>
      (try simp only [hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38]) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

/-- `0x10025f`–`0x100271`. -/
def rb11 (r : RS) : RS := { r with eax := (Ssl.Spec.Chacha.rotl (UInt32.xor r.eax r.edx) 7), ecx := (UInt32.add r.ecx (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s8 r.edi)) 16)), ebx := (Ssl.Spec.Chacha.rotl (UInt32.xor r.ebx (UInt32.add r.s8 r.edi)) 16), s8 := (UInt32.add r.s8 r.edi) }

theorem rb11_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (ht : t.toNat + 128 ≤ H.get.size)
    (hc : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576) (hr : Corr H.get t r) :
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt 6 (stRS H.get t r 0x10025f (efl f) ic) =
        some (stRS H'.get t (rb11 r) 0x100271 (efl f') (ic + 6)) ∧
      Corr H'.get t (rb11 r) ∧ Agree t.toNat 60 H.get H'.get := by
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
