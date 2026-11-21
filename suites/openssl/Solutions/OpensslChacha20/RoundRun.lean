import Solutions.OpensslChacha20.RoundState
/-!
# Runs on the round state

`RunR t n A B P g`: from every machine state at `A` with frame `t` whose round state `r` satisfies
`P`, `n` instructions reach `B` with round state `g r`, changing memory only in the slots
`[t, t + 60)`. Such runs compose (`RunR.trans`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

/-- The facts about the frame `t` every step needs. -/
structure FrameOk (H : CMem) (t : UInt32) : Prop where
  sz : H.get.size ≤ 4273995776
  fit : t.toNat + 128 ≤ H.get.size
  code : 1049648 ≤ t.toNat ∨ t.toNat + 128 ≤ 1048576

def RunR (t : UInt32) (n : Nat) (A B : UInt32) (P : RS → Prop) (g : RS → RS) : Prop :=
  ∀ (H : CMem) (f : UInt32) (r : RS) (ic : UInt64), FrameOk H t → Corr H.get t r → P r →
    ∃ (H' : CMem) (f' : UInt32),
      exN Image.sym_halt n (stRS H.get t r A (efl f) ic) =
        some (stRS H'.get t (g r) B (efl f') (ic + n.toUInt64)) ∧
      Corr H'.get t (g r) ∧ Agree t.toNat 60 H.get H'.get

theorem FrameOk.of_agree {H H' : CMem} {t : UInt32} (h : FrameOk H t) (ha : Agree t.toNat 60 H.get H'.get) :
    FrameOk H' t :=
  ⟨by rw [ha.1]; exact h.sz, by rw [ha.1]; exact h.fit, h.code⟩

theorem toUInt64_add (a b : Nat) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by
  apply UInt64.toNat_inj.1
  simp only [Nat.toUInt64_eq, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

theorem RunR.trans {t : UInt32} {n m : Nat} {A B C : UInt32} {P Q : RS → Prop} {g h : RS → RS}
    (h1 : RunR t n A B P g) (hPQ : ∀ r, P r → Q (g r)) (h2 : RunR t m B C Q h) :
    RunR t (n + m) A C P (fun r => h (g r)) := by
  intro H f r ic hF hC hP
  obtain ⟨H1, f1, e1, c1, a1⟩ := h1 H f r ic hF hC hP
  obtain ⟨H2, f2, e2, c2, a2⟩ := h2 H1 f1 (g r) (ic + n.toUInt64) (hF.of_agree a1) c1 (hPQ r hP)
  refine ⟨H2, f2, ?_, c2, a1.trans a2⟩
  rw [exN_trans e1 e2, toUInt64_add, UInt64.add_assoc]

theorem RunR.mono {t : UInt32} {n : Nat} {A B : UInt32} {P P' : RS → Prop} {g : RS → RS}
    (h : RunR t n A B P g) (hP : ∀ r, P' r → P r) : RunR t n A B P' g :=
  fun H f r ic hF hC hP' => h H f r ic hF hC (hP r hP')

end Solutions.OpensslChacha20
