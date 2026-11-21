import Solutions.OpensslX25519.I.InvRun1
import Solutions.OpensslX25519.I.CSt
import Solutions.OpensslX25519.I.MemCall
import Solutions.OpensslX25519.I.SpecMath
import Solutions.OpensslX25519.I.M121Math
/-!
# The loop of `fe_invert`

`for (i = 1; i < 100; ++i) fe_sq(t3, t3);`, compiled as a counter in `edi` from 99 down: after `r`
iterations the buffer `t3` (at `L + 12`) holds the `2^r`-th power of what it held (`inv_loop`).
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000

theorem upd_upd {α : Type} (l : List (Nat × α)) (j : Nat) (a b : α) : upd (upd l j a) j b = upd l j b := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    simp only [upd]
    by_cases h : k = j
    · simp [h, upd]
    · simp [h, upd, ih]

theorem lookup_append_some {α : Type} {l1 l2 : List (Nat × α)} {k : Nat} {v : α} (h : l1.lookup k = some v) :
    (l1 ++ l2).lookup k = some v := by
  induction l1 with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k', w⟩ := p
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h ⊢; exact h
    · have e : (k == k') = false := by simp [hk]
      simp only [List.lookup, List.cons_append, e] at h ⊢
      exact ih h

theorem inv_loop (G : XMem) (L ebx ebp : UInt32) (hS : FB G.get.size L 192) (sl : List (Nat × UInt32)) (Z : Int) (ic0 : UInt64)
    (s0 : Machine) :
    ∀ (r : Nat) (N : XMem) (bf : List (Nat × Array UInt32)) (v : Array UInt32) (e c : Nat)
      (eax ecx edx edi fl : UInt32),
      1 ≤ r → edi.toNat = r → CSt G N L 188 828 sl bf → bf.lookup 12 = some v → MulOut v →
      feValI v % pI = Z ^ e % pI → ic0.toNat + c + 579 * r < 2 ^ 63 →
      Run img s0 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, UInt32.add L 12, edi, 0x1009e0, efl fl,
        icAdd ic0 c⟩) →
      ∃ (N' : XMem) (eax' ecx' edx' edi' fl' : UInt32),
        Run img s0 (St.m ⟨N'.get, eax', ecx', edx', ebx, UInt32.add L 8, ebp, UInt32.add L 12, edi', 0x1009ec,
          efl fl', icAdd ic0 (c + 579 * r)⟩) ∧
        CSt G N' L 188 828 sl (upd bf 12 (memWords N'.get (UInt32.add L (12 : Nat).toUInt32) 10)) ∧
        MulOut (memWords N'.get (UInt32.add L (12 : Nat).toUInt32) 10) ∧
        feValI (memWords N'.get (UInt32.add L (12 : Nat).toUInt32) 10) % pI = Z ^ (e * 2 ^ r) % pI := by
  intro r
  induction r with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; omega
  | succ r ih =>
    intro N bf v e c eax ecx edx edi fl _ hedi C hl hmo hex hic R0
    have hk := mem_of_lookup hl
    have R1 := inv_lb (icAdd ic0 c) (icB' (k := 3) (by omega)) N L (hS.size_eq C.pres.1) eax ecx edx ebx ebp (UInt32.add L 12) edi fl
    simp only [icAdd_add, Nat.add_zero] at R1
    obtain ⟨N1, a1, c1, d1, f1, R2, C1, M1, V1⟩ := C.sq (by decide) (by decide) 12 12 hk hl (mulIn_of_mulOut hmo)
      0x1009e9 eax ebx ebp (UInt32.add L 12) edi fl ic0 (c + 3) (by omega) s0 (by decide) (R0.trans R1)
    have E1 := pow_sq_emod hex V1
    by_cases hr : r = 0
    · subst hr
      have R3 := inv_lx (icAdd ic0 (c + 3 + 574)) (icB' (k := 2) (by omega)) N1 L (hS.size_eq C1.pres.1) a1 c1 d1 ebx ebp
        (UInt32.add L 12) edi f1 (by omega)
      simp only [icAdd_add, Nat.add_zero] at R3
      refine ⟨N1, _, _, _, _, _, R2.trans R3, C1, M1, ?_⟩
      rw [E1]; congr 2; rw [Nat.zero_add, Nat.pow_one, Nat.mul_comm]
    · have R3 := inv_lj (icAdd ic0 (c + 3 + 574)) (icB' (k := 2) (by omega)) N1 L (hS.size_eq C1.pres.1) a1 c1 d1 ebx ebp
        (UInt32.add L 12) edi f1 (by omega)
      simp only [icAdd_add, Nat.add_zero] at R3
      have hk1 : 12 ∈ (upd bf 12 (memWords N1.get (UInt32.add L (12 : Nat).toUInt32) 10)).map Prod.fst := by
        rw [keys_upd]; exact hk
      have hedi' : (subF 4 edi 1 0).1.toNat = r := by
        rw [subF_fst, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
      obtain ⟨N', a', c', d', e', f', R4, C', M', V'⟩ := ih N1 _ _ (2 * e) (c + 3 + 574 + 2) _ _ _ _ _ (by omega)
        hedi' C1 (lookup_upd_self _ _ _ hk) M1 E1 (by omega) (R2.trans R3)
      rw [upd_upd] at C'
      refine ⟨N', a', c', d', e', f', ?_, C', M', ?_⟩
      · rw [show c + 579 * (r + 1) = c + 3 + 574 + 2 + 579 * r by omega]; exact R4
      · rw [V']; congr 2; rw [Nat.pow_succ]; rw [Nat.mul_comm 2 e, Nat.mul_assoc, Nat.mul_comm 2]

end Solutions.OpensslX25519.I
