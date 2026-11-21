import Ssl.Spec.Poly1305
/-!
# Poly1305 as a fold over blocks

`Spec.Poly1305.poly r bl` is the sum `Σ (m_i + pad_i) · r^(q-i+1)`; here it is Horner's fold
(`poly_eq_accF`), reduced modulo `p` at each step (`accM`), and the blocks of a message split at any
multiple of 16 (`blocks_append`). This is the shape of `Poly1305_Update` (whole blocks, any chunking)
and `Poly1305_Final` (the padded tail).
-/
namespace Solutions.OpensslPoly1305
open Ssl.Spec.Poly1305

/-- A block's value with its pad bit. -/
def mval (b : List UInt8) : Nat := leNat b + 2 ^ (8 * b.length)

/-- Horner's fold from `a`. -/
def accF (r a : Nat) (bl : List (List UInt8)) : Nat := bl.foldl (fun a b => (a + mval b) * r) a

/-- Horner's fold from `a`, modulo `p` at each step. -/
def accMa (r a : Nat) (bl : List (List UInt8)) : Nat := bl.foldl (fun a b => (a + mval b) * r % p) a

/-- The accumulator after the blocks `bl` (modulo `p`). -/
def accM (r : Nat) (bl : List (List UInt8)) : Nat := accMa r 0 bl

def sumR (f : Nat → Nat) (n : Nat) : Nat := (List.range n).foldl (fun acc i => acc + f i) 0

theorem foldl_add_shift (f : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun acc i => acc + f i) a = a + l.foldl (fun acc i => acc + f i) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih, ih (0 + f x)]; omega

theorem sumR_succ (f : Nat → Nat) (n : Nat) : sumR f (n + 1) = sumR f n + f n := by
  unfold sumR; rw [List.range_succ, List.foldl_append]; simp

theorem sumR_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i, i < n → f i = g i) → sumR f n = sumR g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumR_succ, sumR_succ, sumR_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem sumR_mul (f : Nat → Nat) (r : Nat) : ∀ n, sumR (fun i => f i * r) n = sumR f n * r
  | 0 => by simp [sumR]
  | n + 1 => by rw [sumR_succ, sumR_succ, sumR_mul f r n, Nat.add_mul]

theorem poly_def (r : Nat) (bl : List (List UInt8)) :
    poly r bl = sumR (fun i => mval bl[i]! * r ^ (bl.length - i)) bl.length := rfl

theorem poly_snoc (r : Nat) (bl : List (List UInt8)) (b : List UInt8) :
    poly r (bl ++ [b]) = (poly r bl + mval b) * r := by
  rw [poly_def, poly_def, List.length_append, List.length_singleton, sumR_succ, Nat.add_mul,
    ← sumR_mul]
  congr 1
  · apply sumR_congr
    intro i hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi,
      show bl.length + 1 - i = (bl.length - i) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simp

theorem snoc_ind {α : Type} {P : List α → Prop} (h0 : P []) (hs : ∀ l a, P l → P (l ++ [a])) :
    ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  generalize l.reverse = t
  induction t with
  | nil => exact h0
  | cons a t ih => rw [List.reverse_cons]; exact hs _ _ ih

theorem poly_eq_accF (r : Nat) (bl : List (List UInt8)) : poly r bl = accF r 0 bl := by
  induction bl using snoc_ind with
  | h0 => rfl
  | hs bl b ih => rw [poly_snoc, ih, accF, accF, List.foldl_append]; rfl

theorem accF_mod (r : Nat) (bl : List (List UInt8)) (a : Nat) : accF r a bl % p = accMa r (a % p) bl := by
  induction bl generalizing a with
  | nil => simp [accF, accMa]
  | cons b bl ih =>
    simp only [accF, accMa, List.foldl_cons] at *
    rw [ih]
    congr 1
    simp [Nat.mul_mod, Nat.add_mod]

theorem poly_mod (r : Nat) (bl : List (List UInt8)) : poly r bl % p = accM r bl := by
  rw [poly_eq_accF, accF_mod]; rfl

theorem accMa_append (r a : Nat) (b1 b2 : List (List UInt8)) :
    accMa r a (b1 ++ b2) = accMa r (accMa r a b1) b2 := by
  simp [accMa, List.foldl_append]

theorem accM_append (r : Nat) (b1 b2 : List (List UInt8)) : accM r (b1 ++ b2) = accMa r (accM r b1) b2 :=
  accMa_append r 0 b1 b2

theorem accM_lt (r : Nat) (bl : List (List UInt8)) (h : bl ≠ []) : accM r bl < p := by
  induction bl using snoc_ind with
  | h0 => exact absurd rfl h
  | hs bl b _ =>
    rw [accM_append]; simp only [accMa, List.foldl_cons, List.foldl_nil]
    exact Nat.mod_lt _ (by decide)

/-! ## Blocks -/

theorem blocksAux_fuel : ∀ (n m : Nat) (bs : List UInt8), bs.length ≤ n → bs.length ≤ m →
    blocksAux n bs = blocksAux m bs
  | 0, m, bs, h, _ => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases m <;> rfl
  | n + 1, 0, bs, _, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | n + 1, m + 1, [], _, _ => rfl
  | n + 1, m + 1, b :: bs, h1, h2 => by
    simp only [blocksAux]
    congr 1
    apply blocksAux_fuel <;> simp at * <;> omega

theorem blocks_nil : blocks [] = [] := rfl

theorem blocks_cons16 (A B : List UInt8) (hA : A.length = 16) : blocks (A ++ B) = A :: blocks B := by
  unfold blocks
  obtain ⟨a, A', rfl⟩ : ∃ a A', A = a :: A' := by
    cases A with
    | nil => simp at hA
    | cons a A' => exact ⟨a, A', rfl⟩
  rw [List.length_append, show (a :: A').length + B.length = (A'.length + B.length) + 1 by simp; omega]
  simp only [blocksAux, List.cons_append]
  rw [show (a :: (A' ++ B)).take 16 = a :: A' by
        rw [← List.cons_append, List.take_append_of_le_length (by rw [hA]; omega), List.take_of_length_le (by rw [hA]; omega)],
      show (a :: (A' ++ B)).drop 16 = B by
        rw [← List.cons_append, List.drop_append_of_le_length (by rw [hA]; omega), List.drop_of_length_le (by rw [hA]; omega)]; rfl]
  congr 1
  apply blocksAux_fuel <;> simp at hA ⊢ <;> omega

theorem blocks_short (T : List UInt8) (h : T.length ≤ 16) (h0 : T ≠ []) : blocks T = [T] := by
  unfold blocks
  obtain ⟨a, T', rfl⟩ : ∃ a T', T = a :: T' := by
    cases T with
    | nil => exact absurd rfl h0
    | cons a T' => exact ⟨a, T', rfl⟩
  simp only [List.length_cons, blocksAux]
  rw [List.take_of_length_le (by simpa using h), List.drop_of_length_le (by simpa using h)]
  cases T'.length <;> rfl

theorem blocks_append : ∀ (k : Nat) (A B : List UInt8), A.length = 16 * k →
    blocks (A ++ B) = blocks A ++ blocks B
  | 0, A, B, h => by
    have : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | k + 1, A, B, h => by
    have e : A = A.take 16 ++ A.drop 16 := (List.take_append_drop 16 A).symm
    have h1 : (A.take 16).length = 16 := by simp; omega
    have h2 : (A.drop 16).length = 16 * k := by simp; omega
    rw [e, List.append_assoc, blocks_cons16 _ _ h1, blocks_cons16 _ _ h1,
      blocks_append k _ _ h2]
    rfl

/-! ## The state of a message: whole blocks and the buffered tail -/

/-- The number of bytes in whole blocks. -/
def fullLen (msg : List UInt8) : Nat := 16 * (msg.length / 16)

/-- The accumulator of the whole blocks of a message (what the context's `h` holds modulo `p`). -/
def accOf (r : Nat) (msg : List UInt8) : Nat := accM r (blocks (msg.take (fullLen msg)))

theorem fullLen_le (msg : List UInt8) : fullLen msg ≤ msg.length := by
  unfold fullLen; omega

theorem take_fullLen_length (msg : List UInt8) : (msg.take (fullLen msg)).length = fullLen msg := by
  simp [fullLen_le]

theorem drop_fullLen_length (msg : List UInt8) : (msg.drop (fullLen msg)).length = msg.length % 16 := by
  simp [fullLen]; omega

/-- The tag from the accumulator of all blocks. -/
theorem tagNat_eq (key msg : List UInt8) :
    tagNat key msg = (accM (r key) (blocks msg) + s key) % 2 ^ 128 := by
  unfold tagNat; rw [poly_mod]

/-- The blocks of a message: its whole blocks, then the tail if it is not empty. -/
theorem blocks_split (msg : List UInt8) :
    blocks msg = blocks (msg.take (fullLen msg)) ++ blocks (msg.drop (fullLen msg)) := by
  conv => lhs; rw [← List.take_append_drop (fullLen msg) msg]
  exact blocks_append (msg.length / 16) _ _ (by rw [take_fullLen_length]; rfl)

end Solutions.OpensslPoly1305
