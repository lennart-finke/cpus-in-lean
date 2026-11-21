import Solutions.OpensslChacha20.RoundLoop
import Solutions.OpensslChacha20.RunUtil
/-!
# Ten double rounds

The round loop runs from the loop head with counter 22 to the exit at `0x10033e`, ten times the
double round (`rounds_run`, `rfin_toV`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20

set_option maxRecDepth 100000

/-- `j` iterations of the loop body with the counter update. -/
def rIter : Nat → RS → RS
  | 0, r => r
  | j + 1, r => rIter j (rtail (rbAll r))

/-- The round state at the loop exit. -/
def rfin (r : RS) : RS := rtail (rbAll (rIter 9 r))

theorem RunR.cast {t : UInt32} {n n' : Nat} {A B : UInt32} {P : RS → Prop} {g g' : RS → RS}
    (h : RunR t n A B P g) (hn : n = n') (hg : ∀ r, g r = g' r) : RunR t n' A B P g' := by
  subst hn
  have : g = g' := funext hg
  subst this; exact h

theorem RunR.zero (t A : UInt32) (P : RS → Prop) : RunR t 0 A A P id := by
  intro H f r ic _ hC _
  refine ⟨H, f, ?_, hC, Agree.refl _ _ _⟩
  rw [exN_zero]
  congr
  show ic = ic + 0
  exact (UInt64.add_zero ic).symm

theorem rtailV_s28 (r : RS) (c : UInt32) : (rtailV r c).s28 = c := rfl
theorem rtailV_edx (r : RS) (c : UInt32) : (rtailV r c).edx = c := rfl
theorem rtailV_toV (r : RS) (c : UInt32) : (rtailV r c).toV = r.toV := rfl
theorem rtailV_s14 (r : RS) (c : UInt32) : (rtailV r c).s14 = r.s14 := rfl
theorem rtailV_s24 (r : RS) (c : UInt32) : (rtailV r c).s24 = r.s24 := rfl

theorem dec2_toNat (x : UInt32) (h : 2 ≤ x.toNat) : (UInt32.add x 4294967294).toNat = x.toNat - 2 := by
  have := x.toNat_lt
  rw [toNat_uadd]
  simp only [UInt32.reduceToNat]
  omega

theorem rtail_s28 (r : RS) (h : 2 ≤ r.s28.toNat) : (rtail r).s28.toNat = r.s28.toNat - 2 := by
  unfold rtail; rw [rtailV_s28]; exact dec2_toNat _ h

theorem rtail_edx (r : RS) (h : 2 ≤ r.s28.toNat) : (rtail r).edx.toNat = r.s28.toNat - 2 := by
  unfold rtail; rw [rtailV_edx]; exact dec2_toNat _ h

theorem iter_cont (t : UInt32) :
    RunR t 138 0x100190 0x100190 (fun r => 6 ≤ r.s28.toNat ∧ r.s28.toNat ≤ 22) (fun r => rtail (rbAll r)) :=
  ((((rbAll_run t).mono (fun _ _ => trivial)).trans (fun _ _ => trivial) (rtA_run t)).trans
    (fun r h => by
      show 2 < (rtail (rbAll r)).edx.toNat ∧ (rtail (rbAll r)).edx.toNat ≤ 20
      rw [rtail_edx _ (by rw [rbAll_s28]; omega), rbAll_s28]; omega) (rtB_cont t)).cast rfl (fun _ => rfl)

theorem iter_exit (t : UInt32) :
    RunR t 138 0x100190 0x10033e (fun r => r.s28.toNat = 4) (fun r => rtail (rbAll r)) :=
  ((((rbAll_run t).mono (fun _ _ => trivial)).trans (fun _ _ => trivial) (rtA_run t)).trans
    (fun r h => by
      show (rtail (rbAll r)).edx.toNat = 2
      rw [rtail_edx _ (by rw [rbAll_s28]; omega), rbAll_s28]; omega) (rtB_exit t)).cast rfl (fun _ => rfl)

theorem iters_run (t : UInt32) : ∀ j : Nat, j ≤ 9 →
    RunR t (138 * j) 0x100190 0x100190 (fun r => r.s28.toNat = 2 * j + 4) (rIter j)
  | 0, _ => (RunR.zero t 0x100190 _).cast (by rfl) (fun _ => rfl)
  | j + 1, hj => by
    have ih := iters_run t j (by omega)
    refine ((iter_cont t).mono (fun r (h : r.s28.toNat = 2 * (j + 1) + 4) => by omega)).trans ?_ ih |>.cast
      (by omega) (fun _ => rfl)
    intro r h
    show (rtail (rbAll r)).s28.toNat = 2 * j + 4
    rw [rtail_s28 _ (by rw [rbAll_s28]; omega), rbAll_s28]
    omega

theorem rounds_runR (t : UInt32) :
    RunR t 1380 0x100190 0x10033e (fun r => r.s28.toNat = 22) rfin := by
  have h9 := iters_run t 9 (by omega)
  have key : ∀ r : RS, r.s28.toNat = 2 * 9 + 4 → (rIter 9 r).s28.toNat = 4 := by
    intro r hr
    have : ∀ j, j ≤ 9 → ∀ r : RS, r.s28.toNat = 2 * j + 4 → (rIter j r).s28.toNat = 4 := by
      intro j
      induction j with
      | zero => intro _ r hr; exact hr
      | succ j ih =>
        intro hj r hr
        show (rIter j (rtail (rbAll r))).s28.toNat = 4
        apply ih (by omega)
        rw [rtail_s28 _ (by rw [rbAll_s28]; omega), rbAll_s28]
        omega
    exact this 9 (by omega) r hr
  exact (h9.trans (fun r hr => key r hr) (iter_exit t)).mono (fun r hr => by omega) |>.cast (by rfl) (fun _ => rfl)

theorem rtail_toV (r : RS) : (rtail r).toV = r.toV := by unfold rtail; exact rtailV_toV _ _

theorem repeat_comm (f : V16 → V16) : ∀ (j : Nat) (v : V16), Nat.repeat f j (f v) = f (Nat.repeat f j v)
  | 0, _ => rfl
  | j + 1, v => by simp only [Nat.repeat]; rw [repeat_comm f j v]

theorem rIter_toV : ∀ (j : Nat) (r : RS), (rIter j r).toV = Nat.repeat dround j r.toV
  | 0, _ => rfl
  | j + 1, r => by
    simp only [rIter, Nat.repeat]
    rw [rIter_toV j, rtail_toV, rbAll_toV, repeat_comm]

theorem rfin_toV (r : RS) : (rfin r).toV = Nat.repeat dround 10 r.toV := by
  simp only [rfin, rtail_toV, rbAll_toV, rIter_toV]
  rfl

theorem rIter_keep : ∀ (j : Nat) (r : RS), (rIter j r).s14 = r.s14 ∧ (rIter j r).s24 = r.s24
  | 0, _ => ⟨rfl, rfl⟩
  | j + 1, r => by
    simp only [rIter]
    obtain ⟨h1, h2⟩ := rIter_keep j (rtail (rbAll r))
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · unfold rtail; rw [rtailV_s14]; exact rbAll_s14 r
    · unfold rtail; rw [rtailV_s24]; exact rbAll_s24 r

theorem rfin_s14 (r : RS) : (rfin r).s14 = r.s14 := by
  unfold rfin rtail; rw [rtailV_s14]; exact (rbAll_s14 (rIter 9 r)).trans (rIter_keep 9 r).1
theorem rfin_s24 (r : RS) : (rfin r).s24 = r.s24 := by
  unfold rfin rtail; rw [rtailV_s24]; exact (rbAll_s24 (rIter 9 r)).trans (rIter_keep 9 r).2

/-- The round loop as a run of the image. -/
theorem rounds_run (H : CMem) (t f : UInt32) (r : RS) (ic : UInt64) (hF : FrameOk H t) (hC : Corr H.get t r)
    (h28 : r.s28.toNat = 22) (hic : ic.toNat + 1380 < 2 ^ 64) :
    ∃ (H' : CMem) (f' : UInt32),
      Run img (stRS H.get t r 0x100190 (efl f) ic).m
        (stRS H'.get t (rfin r) 0x10033e (efl f') (ic + (1380 : Nat).toUInt64)).m ∧
      Corr H'.get t (rfin r) ∧ Agree t.toNat 60 H.get H'.get := by
  obtain ⟨H', f', e, hc, ha⟩ := rounds_runR t H f r ic hF hC h28
  exact ⟨H', f', run_of_exN e hic, hc, ha⟩

end Solutions.OpensslChacha20
