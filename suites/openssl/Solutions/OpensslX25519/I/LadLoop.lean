import Solutions.OpensslX25519.I.LadIter
/-!
# The ladder loop of `x25519_scalar_mult_generic`

`for (pos = 254; pos >= 0; --pos) …`, compiled with `esi = pos` counting down to the `addl $-1 ; jb` exit:
from the loop head with `esi = r - 1`, the run reaches the exit at `0x103afd` after `r` iterations, and the
buffers represent `ladFrom x₁ k r st` (`lad_loop`, by induction on `r` from `lad_iter`).
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Ssl.Spec.X25519

set_option maxRecDepth 100000

theorem ladderStep_kt (x₁ : Nat) (st : Nat × Nat × Nat × Nat × Nat) (kt : Nat) : (ladderStep x₁ st kt).2.2.2.2 = kt := by
  obtain ⟨a, b, c, d, e⟩ := st
  rw [ladderStep_eq]

theorem and_one_mod (x : Nat) : x &&& 1 = x % 2 := Nat.and_two_pow_sub_one_eq_mod x 1

theorem toUInt32_pred (r : Nat) (h1 : 1 ≤ r) (h2 : r < 2 ^ 32) :
    UInt32.add r.toUInt32 4294967295 = (r - 1).toUInt32 := by
  apply UInt32.toNat_inj.1
  rw [toNat_uadd]
  simp only [Nat.toUInt32, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

theorem lad_loop (G : XMem) (L : UInt32) (hS : FB G.get.size L 344) (out s0 s1 s2 s3 : UInt32) (w : Nat → UInt32)
    (eb : List UInt8) (heb : EB w eb) (hlen : eb.length = 32) (vx1 : Array UInt32) (mx1 : MulIn vx1) (X1 : Nat)
    (rx1 : Rep vx1 X1) (ic0 : UInt64) (s00 : Machine) :
    ∀ (r : Nat) (N : XMem) (b0 : UInt32) (vz3 vx2 vx3 vt0 vz2 vt1 : Array UInt32) (X2 Z2 X3 Z3 : Nat) (sw : UInt32)
      (c : Nat) (eax ecx edx ebx ebp fl : UInt32),
      1 ≤ r → r ≤ 255 →
      CSt G N L 344 1012 (ladSl out b0 w s0 s1 s2 s3)
        [(48, vz3), (88, vx2), (128, vx3), (168, vt0), (208, vz2), (248, vx1), (288, vt1)] →
      MulOut vz3 → MulOut vx2 → MulOut vx3 → MulOut vz2 → Rep vz3 Z3 → Rep vx2 X2 → Rep vx3 X3 → Rep vz2 Z2 →
      (sw = 0 ∨ sw = 1) → ic0.toNat + c + ladK * r < 2 ^ 62 →
      Run img s00 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, (r - 1).toUInt32, sw, 0x103990, efl fl,
        icAdd ic0 c⟩) →
      ∃ (N' : XMem) (bitv : UInt32) (vz3' vx2' vx3' vt0' vz2' vt1' : Array UInt32) (eax' ecx' edx' ebx' ebp' esi' fl' : UInt32),
        Run img s00 (St.m ⟨N'.get, eax', ecx', edx', ebx', UInt32.add L 8, ebp', esi', bitv, 0x103afd, efl fl',
          icAdd ic0 (c + ladK * r)⟩) ∧
        CSt G N' L 344 1012 (ladSl out bitv w s0 s1 s2 s3)
          [(48, vz3'), (88, vx2'), (128, vx3'), (168, vt0'), (208, vz2'), (248, vx1), (288, vt1')] ∧
        MulOut vz3' ∧ MulOut vx2' ∧ MulOut vx3' ∧ MulOut vz2' ∧
        bitv.toNat = (ladFrom X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat)).2.2.2.2 ∧
        Rep vx2' (ladFrom X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat)).1 ∧
        Rep vz2' (ladFrom X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat)).2.1 ∧
        Rep vx3' (ladFrom X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat)).2.2.1 ∧
        Rep vz3' (ladFrom X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat)).2.2.2.1 := by
  intro r
  induction r with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
  | succ r ih =>
    intro N b0 vz3 vx2 vx3 vt0 vz2 vt1 X2 Z2 X3 Z3 sw c eax ecx edx ebx ebp fl _ hr C mz3 mx2 mx3 mz2 rz3 rx2 rx3 rz2
      hsw hic R0
    have hr' : r + 1 - 1 = r := by omega
    rw [hr'] at R0
    have hpos : r.toUInt32.toNat = r := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    obtain ⟨N1, bitv, vz3', vx2', vx3', vt0', vz2', vt1', eax', ecx', edx', ebx', ebp', fl', eip, R1, he1, he2, C1, hb,
      hbit, mz3', mx2', mx3', mz2', rx2', rz2', rx3', rz3'⟩ := lad_iter G N L hS out b0 s0 s1 s2 s3 w eb heb hlen
      vz3 vx2 vx3 vt0 vz2 vx1 vt1 C mz3 mx2 mx3 mz2 mx1 X1 X2 Z2 X3 Z3 rz3 rx2 rx3 rz2 rx1 r.toUInt32 sw
      (by rw [hpos]; omega) hsw eax ecx edx ebx ebp fl ic0 c (by rw [Nat.mul_succ] at hic; unfold ladK at hic; omega)
      s00 R0
    rw [hpos] at hbit rx2' rz2' rx3' rz3' he1 he2
    rw [← hbit] at rx2' rz2' rx3' rz3'
    -- the state after the step, as `ladS`
    have hS1 : ladS X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat) =
        ((ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat).1,
          (ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat).2.1,
          (ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat).2.2.1,
          (ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat).2.2.2.1, bitv.toNat) := by
      have e1 : ladS X1 (leNat eb) r (X2, Z2, X3, Z3, sw.toNat) = ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat := by
        unfold ladS; congr 1; exact (and_one_mod _).trans hbit.symm
      rw [e1]
      have hk := ladderStep_kt X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat
      generalize ladderStep X1 (X2, Z2, X3, Z3, sw.toNat) bitv.toNat = q at hk ⊢
      obtain ⟨q1, q2, q3, q4, q5⟩ := q
      simp only at hk
      rw [hk]
    by_cases h0 : r = 0
    · subst h0
      have he := he2 rfl
      subst he
      refine ⟨N1, bitv, vz3', vx2', vx3', vt0', vz2', vt1', eax', ecx', edx', ebx', ebp',
        UInt32.add (Nat.toUInt32 0) 4294967295, fl', ?_, C1, mz3', mx2', mx3',
        mz2', ?_, ?_, ?_, ?_, ?_⟩
      · rw [show c + ladK * (0 + 1) = c + ladK by omega]; exact R1
      all_goals rw [ladFrom_succ, hS1]
      all_goals simp only [ladFrom, List.range_zero, List.reverse_nil, List.foldl_nil]
      all_goals assumption
    · have he := he1 h0
      subst he
      rw [toUInt32_pred r (by omega) (by omega)] at R1
      obtain ⟨N2, bitv2, vz3'', vx2'', vx3'', vt0'', vz2'', vt1'', eax'', ecx'', edx'', ebx'', ebp'', esi'', fl'', R2, C2,
        mz3'', mx2'', mx3'', mz2'', hbit2, rx2'', rz2'', rx3'', rz3''⟩ := ih N1 bitv vz3' vx2' vx3' vt0' vz2' vt1' _ _ _ _
        bitv (c + ladK) eax' ecx' edx' ebx' ebp' fl' (by omega) (by omega) C1 mz3' mx2' mx3' mz2' rz3' rx2' rx3' rz2' hb
        (by rw [Nat.mul_succ] at hic; omega) R1
      refine ⟨N2, bitv2, vz3'', vx2'', vx3'', vt0'', vz2'', vt1'', eax'', ecx'', edx'', ebx'', ebp'', esi'', fl'', ?_, C2,
        mz3'', mx2'', mx3'', mz2'', ?_, ?_, ?_, ?_, ?_⟩
      · rw [show c + ladK * (r + 1) = c + ladK + ladK * r by rw [Nat.mul_succ]; omega]; exact R2
      all_goals rw [ladFrom_succ, hS1]
      all_goals assumption

end Solutions.OpensslX25519.I
