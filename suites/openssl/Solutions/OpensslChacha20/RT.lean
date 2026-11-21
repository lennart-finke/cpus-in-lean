import Solutions.OpensslChacha20.RoundRun
/-!
# The counter update at the end of the round loop

`0x10032a: mov 0x28(%esp),%edx; add $-2,%edx; mov %edx,0x28(%esp)` (`rtA_run`), then
`cmp $2,%edx; ja 0x100190` (`rtB_cont`, `rtB_exit`, on a counter value given as a variable).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

/-- The round state with the counter (and EDX) replaced by `c`. -/
def rtailV (r : RS) (c : UInt32) : RS := { r with edx := c, s28 := c }

/-- The round state after the counter update. -/
def rtail (r : RS) : RS := rtailV r (UInt32.add r.s28 4294967294)

theorem rtA_run (t : UInt32) : RunR t 3 0x10032a 0x100335 (fun _ => True) rtail := by
  intro H f r ic hF hr _
  have hsz := hF.sz; have ht := hF.fit; have hc := hF.code
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  obtain ⟨hs0, hs4, hs8, hsc, hs10, hs14, hs18, hs1c, hs20, hs24, hs28, hs2c, hs30, hs34, hs38⟩ := hr
  simp only [stRS] at *
  ex_run
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (conv => lhs; cbv) <;> (try rfl)
  · repeat (first | exact Agree.refl _ _ _ | (refine agree_wr4 ?_ _ ?_ ?_ <;> try sym_omega))

theorem rtB_cont (t : UInt32) : RunR t 2 0x100335 0x100190 (fun r => 2 < r.edx.toNat ∧ r.edx.toNat ≤ 20) id := by
  intro H f r ic hF hr hP
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  simp only [stRS] at *
  ex_run
  exact ⟨_, _, rfl, hr, Agree.refl _ _ _⟩

theorem rtB_exit (t : UInt32) : RunR t 2 0x100335 0x10033e (fun r => r.edx.toNat = 2) id := by
  intro H f r ic hF hr hP
  rcases r with ⟨eax, ecx, edx, ebx, ebp, esi, edi, s0, s4, s8, sc, s10, s14, s18, s1c, s20, s24, s28, s2c, s30,
    s34, s38⟩
  simp only [stRS] at *
  ex_run
  exact ⟨_, _, rfl, hr, Agree.refl _ _ _⟩

end Solutions.OpensslChacha20
