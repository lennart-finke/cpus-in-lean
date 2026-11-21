import Solutions.OpensslX25519.I.SpecMath
/-!
# The ladder of RFC 7748 as the code runs it

`stepOf x₁ x₂ z₂ x₃ z₃`: one ladder step after the conditional swap (`ladderStep_eq`); `ladFrom x₁ k r st`:
the steps for the bits `r - 1, …, 0` of `k`, which is the fold of `Spec.X25519.ladder` for `r = 255`
(`ladder_fold`); `Rep_ite`.
-/
namespace Solutions.OpensslX25519.I
open Ssl Ssl.Spec.X25519 Ssl.OpensslX25519

/-- One ladder step on the swapped values. -/
def stepOf (x₁ x₂ z₂ x₃ z₃ : Nat) : Nat × Nat × Nat × Nat :=
  let A := addp x₂ z₂
  let AA := mulp A A
  let B := subp x₂ z₂
  let BB := mulp B B
  let E := subp AA BB
  let C := addp x₃ z₃
  let D := subp x₃ z₃
  let DA := mulp D A
  let CB := mulp C B
  (mulp AA BB, mulp E (addp AA (mulp a24 E)), mulp (addp DA CB) (addp DA CB),
    mulp x₁ (mulp (subp DA CB) (subp DA CB)))

theorem ladderStep_eq (x₁ x₂ z₂ x₃ z₃ s kt : Nat) : ladderStep x₁ (x₂, z₂, x₃, z₃, s) kt =
    ((stepOf x₁ (if s ^^^ kt = 1 then x₃ else x₂) (if s ^^^ kt = 1 then z₃ else z₂)
        (if s ^^^ kt = 1 then x₂ else x₃) (if s ^^^ kt = 1 then z₂ else z₃)).1,
      (stepOf x₁ (if s ^^^ kt = 1 then x₃ else x₂) (if s ^^^ kt = 1 then z₃ else z₂)
        (if s ^^^ kt = 1 then x₂ else x₃) (if s ^^^ kt = 1 then z₂ else z₃)).2.1,
      (stepOf x₁ (if s ^^^ kt = 1 then x₃ else x₂) (if s ^^^ kt = 1 then z₃ else z₂)
        (if s ^^^ kt = 1 then x₂ else x₃) (if s ^^^ kt = 1 then z₂ else z₃)).2.2.1,
      (stepOf x₁ (if s ^^^ kt = 1 then x₃ else x₂) (if s ^^^ kt = 1 then z₃ else z₂)
        (if s ^^^ kt = 1 then x₂ else x₃) (if s ^^^ kt = 1 then z₂ else z₃)).2.2.2, kt) := by
  unfold ladderStep
  by_cases h : s ^^^ kt = 1
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]; rfl

/-- The ladder step for bit `r` of `k` (irreducible, so that the equations of `ladFrom` stay small). -/
@[irreducible] def ladS (x₁ k r : Nat) (st : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  ladderStep x₁ st ((k >>> r) &&& 1)

/-- The steps for the bits `r - 1, …, 0` of `k`. -/
def ladFrom (x₁ k : Nat) (r : Nat) (st : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  (List.range r).reverse.foldl (fun st i => ladS x₁ k i st) st

theorem ladFrom_succ (x₁ k r : Nat) (st : Nat × Nat × Nat × Nat × Nat) :
    ladFrom x₁ k (r + 1) st = ladFrom x₁ k r (ladS x₁ k r st) := by
  unfold ladFrom
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]

/-- The fold body of `Spec.X25519.ladder`. -/
def ladF (x₁ k : Nat) (st : Nat × Nat × Nat × Nat × Nat) (i : Nat) : Nat × Nat × Nat × Nat × Nat :=
  ladderStep x₁ st ((k >>> (254 - i)) &&& 1)

theorem fold_ladFrom (x₁ k : Nat) : ∀ m, m ≤ 255 → ∀ st,
    (List.range' (255 - m) m).foldl (ladF x₁ k) st = ladFrom x₁ k m st := by
  intro m
  induction m with
  | zero => intro _ st; simp [ladFrom]
  | succ m ih =>
    intro hm st
    have e : List.range' (255 - (m + 1)) (m + 1) = (254 - m) :: List.range' (255 - m) m := by
      rw [show 255 - (m + 1) = 254 - m by omega, show 255 - m = 254 - m + 1 by omega]; rfl
    have h1 := ih (by omega) (ladS x₁ k m st)
    have h2 : ladF x₁ k st (254 - m) = ladS x₁ k m st := by
      unfold ladF ladS; rw [show 254 - (254 - m) = m by omega]
    have h3 : (List.range' (255 - (m + 1)) (m + 1)).foldl (ladF x₁ k) st =
        (List.range' (255 - m) m).foldl (ladF x₁ k) (ladF x₁ k st (254 - m)) := by
      rw [e, List.foldl_cons]
    exact h3.trans ((congrArg (fun s => List.foldl (ladF x₁ k) s (List.range' (255 - m) m)) h2).trans
      (h1.trans (ladFrom_succ x₁ k m st).symm))

theorem ladder_fold (x₁ k : Nat) (st : Nat × Nat × Nat × Nat × Nat) :
    (List.range 255).foldl (fun st i => ladderStep x₁ st ((k >>> (254 - i)) &&& 1)) st = ladFrom x₁ k 255 st := by
  have h := fold_ladFrom x₁ k 255 (Nat.le_refl _) st
  have e : List.range 255 = List.range' (255 - 255) 255 := List.range_eq_range'
  exact (congrArg (fun l => List.foldl (ladF x₁ k) st l) e).trans h

theorem Rep_ite {v w : Array UInt32} {x y : Nat} (P : Prop) [Decidable P] (Q : Prop) [Decidable Q] (hPQ : P ↔ Q)
    (hv : Rep v x) (hw : Rep w y) : Rep (if P then w else v) (if Q then y else x) := by
  by_cases h : Q
  · rw [if_pos (hPQ.2 h), if_pos h]; exact hw
  · rw [if_neg (fun h' => h (hPQ.1 h')), if_neg h]; exact hv

theorem bound_ite {v w : Array UInt32} (B : Array UInt32 → Prop) (P : Prop) [Decidable P] (hv : B v) (hw : B w) :
    B (if P then w else v) := by
  by_cases h : P
  · rw [if_pos h]; exact hw
  · rw [if_neg h]; exact hv

/-- The last bit of a clamped scalar is 0, so the swap after the last step is 0. -/
theorem ladFrom_swap (x₁ k : Nat) (r : Nat) (st : Nat × Nat × Nat × Nat × Nat) :
    (ladFrom x₁ k (r + 1) st).2.2.2.2 = (k >>> 0) &&& 1 := by
  induction r generalizing st with
  | zero =>
    obtain ⟨a, b, c, d, e⟩ := st
    rw [ladFrom_succ]
    unfold ladS
    simp only [ladFrom, List.range_zero, List.reverse_nil, List.foldl_nil, ladderStep_eq]
  | succ r ih => rw [ladFrom_succ, ih]

end Solutions.OpensslX25519.I
