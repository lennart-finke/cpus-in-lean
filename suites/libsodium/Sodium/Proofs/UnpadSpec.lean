import Sodium.Spec.Utils
/-!
# The arithmetic of `sodium_unpad`'s loop

The loop of `sodium_unpad` scans the last `block` bytes `c 0, c 1, …` of the buffer from the end,
keeping the `or` of the bytes seen (`acc`), a validity bit (`v`) and the padding length (`pl`):

```
b   = ((((c ^ 0x80) - 1) & ((pl - 1) & (acc - 1))) >> 8) & 1
acc = acc | c;  v = v | b;  pl = pl | (i & -b)
```

`b` is 1 exactly when every byte seen so far is zero and `c` is `0x80` (`barrier_zero`,
`barrier_ne`). `run` is the loop as a function, and `run_spec` what it computes in terms of the number
`z` of zero bytes at the end of the buffer. `unpad_spec` puts `Sodium.Spec.unpad` in the same terms.
-/
namespace Sodium.Proofs.Unpad

/-- The barrier bit of one iteration. -/
def barrier (acc pl c : UInt32) : UInt32 :=
  ((((c ^^^ 0x80) - 1) &&& ((pl - 1) &&& (acc - 1))) >>> 8) &&& 1

theorem toNat_shr8 (x : UInt32) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [UInt32.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem shr8_and1_of_lt (x : UInt32) (h : x.toNat < 256) : (x >>> 8) &&& 1 = 0 := by
  have : x >>> 8 = 0 := by
    apply UInt32.toNat_inj.1
    rw [toNat_shr8]; simp; omega
  rw [this]; rfl

theorem barrier_ne (acc pl c : UInt32) (h : acc ≠ 0) (hacc : acc.toNat < 256) : barrier acc pl c = 0 := by
  unfold barrier
  apply shr8_and1_of_lt
  have h1 : (acc - 1).toNat = acc.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]
      have : acc.toNat ≠ 0 := fun e => h (UInt32.toNat_inj.1 (by rw [e]; rfl))
      show 1 ≤ acc.toNat; omega
  have hne : acc.toNat ≠ 0 := fun e => h (UInt32.toNat_inj.1 (by rw [e]; rfl))
  rw [UInt32.toNat_and, UInt32.toNat_and]
  have h2 := Nat.and_le_right (n := ((c ^^^ 128) - 1).toNat) (m := (pl - 1).toNat &&& (acc - 1).toNat)
  have h3 := Nat.and_le_right (n := (pl - 1).toNat) (m := (acc - 1).toNat)
  omega

set_option maxRecDepth 100000 in
theorem barrier_table : ∀ n : Nat, n < 256 →
    (((((n.toUInt32 ^^^ 0x80) - 1) &&& 0xFFFFFFFF) >>> 8) &&& 1 : UInt32) = if n = 0x80 then (1 : UInt32) else 0 := by
  decide

theorem barrier_zero (c : UInt32) (hc : c.toNat < 256) :
    barrier 0 0 c = if c = 0x80 then 1 else 0 := by
  have e : c = c.toNat.toUInt32 := by simp
  have := barrier_table c.toNat hc
  rw [← e] at this
  unfold barrier
  rw [show ((0 : UInt32) - 1 &&& (0 : UInt32) - 1) = 0xFFFFFFFF from rfl, this]
  by_cases h : c = 0x80
  · subst h; rfl
  · rw [if_neg h, if_neg]
    intro e'; apply h; rw [e, e']; rfl

/-- One iteration on the state `(acc, v, pl)`. -/
def step (cb : Nat → UInt32) (s : UInt32 × UInt32 × UInt32) (i : Nat) : UInt32 × UInt32 × UInt32 :=
  let b := barrier s.1 s.2.2 (cb i)
  (s.1 ||| cb i, s.2.1 ||| b, s.2.2 ||| (i.toUInt32 &&& (0 - b)))

/-- The first `i` iterations. -/
def run (cb : Nat → UInt32) : Nat → UInt32 × UInt32 × UInt32
  | 0 => (0, 0, 0)
  | i + 1 => step cb (run cb i) i

theorem or_lt256 (a b : UInt32) (ha : a.toNat < 256) (hb : b.toNat < 256) : (a ||| b).toNat < 256 := by
  rw [UInt32.toNat_or]
  exact Nat.or_lt_two_pow (n := 8) ha hb

theorem toNat_ne_zero {a : UInt32} (h : a ≠ 0) : a.toNat ≠ 0 :=
  fun e => h (UInt32.toNat_inj.1 (by rw [e]; rfl))

theorem or_ne_zero_left (a b : UInt32) (h : a ≠ 0) : a ||| b ≠ 0 := by
  intro e
  have := congrArg UInt32.toNat e
  rw [UInt32.toNat_or] at this
  have h1 := Nat.left_le_or (n := a.toNat) (m := b.toNat)
  have h2 := toNat_ne_zero h
  simp at this; omega

theorem or_ne_zero_right (a b : UInt32) (h : b ≠ 0) : a ||| b ≠ 0 := by
  rw [UInt32.or_comm]; exact or_ne_zero_left b a h

/-- What the loop computes after `i` of its `n` iterations, `z` being the number of zero bytes before
the first non-zero one. -/
def Inv (cb : Nat → UInt32) (z i : Nat) (s : UInt32 × UInt32 × UInt32) : Prop :=
  if i ≤ z then s = (0, 0, 0)
  else s.1 ≠ 0 ∧ s.1.toNat < 256 ∧ s.2.1 = (if cb z = 0x80 then 1 else 0) ∧
    s.2.2 = (if cb z = 0x80 then z.toUInt32 else 0)

theorem run_inv (cb : Nat → UInt32) (n z : Nat) (hc : ∀ j, j < n → (cb j).toNat < 256)
    (hz0 : ∀ j, j < z → j < n → cb j = 0) (hz1 : z < n → cb z ≠ 0) :
    ∀ i, i ≤ n → Inv cb z i (run cb i) := by
  intro i
  induction i with
  | zero => intro _; simp [Inv, run]
  | succ i ih =>
    intro hi
    have ih := ih (by omega)
    simp only [run, step]
    unfold Inv at ih ⊢
    by_cases h1 : i + 1 ≤ z
    · rw [if_pos (by omega)] at ih
      rw [if_pos h1, ih]
      have hci : cb i = 0 := hz0 i (by omega) (by omega)
      simp only [hci]
      rw [barrier_zero 0 (by decide), if_neg (by decide)]
      simp
    · rw [if_neg h1]
      by_cases h2 : i = z
      · subst h2
        rw [if_pos (Nat.le_refl _)] at ih
        rw [ih]
        have hcz := hz1 (by omega)
        have hlt := hc i (by omega)
        simp only
        rw [barrier_zero (cb i) hlt]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [UInt32.zero_or]; exact hcz
        · rw [UInt32.zero_or]; exact hlt
        · by_cases h : cb i = 0x80 <;> simp [h]
        · by_cases h : cb i = 0x80 <;> simp [h]
      · rw [if_neg (by omega)] at ih
        obtain ⟨ha, hal, hv, hp⟩ := ih
        simp only
        rw [barrier_ne _ _ _ ha hal]
        refine ⟨or_ne_zero_left _ _ ha, or_lt256 _ _ hal (hc i (by omega)), ?_, ?_⟩
        · rw [UInt32.or_zero]; exact hv
        · rw [show (0 : UInt32) - 0 = 0 from rfl, UInt32.and_zero, UInt32.or_zero]; exact hp

/-! ## The specification in the same terms -/

theorem tw_zero {α : Type} (p : α → Bool) : ∀ (l : List α) (j : Nat) (hj : j < (l.takeWhile p).length),
    p (l[j]'(Nat.lt_of_lt_of_le hj (List.takeWhile_sublist p).length_le)) = true
  | [], j, hj => by simp at hj
  | a :: l, j, hj => by
    by_cases hp : p a = true
    · rw [List.takeWhile_cons_of_pos hp] at hj
      cases j with
      | zero => simpa using hp
      | succ j => simpa using tw_zero p l j (by simpa using hj)
    · rw [List.takeWhile_cons_of_neg hp] at hj
      simp at hj

theorem tw_stop {α : Type} (p : α → Bool) : ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p (l[(l.takeWhile p).length]'h) = false
  | [], h => by simp at h
  | a :: l, h => by
    by_cases hp : p a = true
    · have e : (List.takeWhile p (a :: l)).length = (l.takeWhile p).length + 1 := by
        rw [List.takeWhile_cons_of_pos hp]; simp
      have h' : (l.takeWhile p).length < l.length := by rw [e] at h; simpa using h
      have := tw_stop p l h'
      simp only [e, List.getElem_cons_succ]
      exact this
    · have e : (List.takeWhile p (a :: l)).length = 0 := by
        rw [List.takeWhile_cons_of_neg hp]; simp
      simp only [e, List.getElem_cons_zero]
      simpa using hp

/-- The number of zero bytes at the end of `buf`. -/
def zeros (buf : List UInt8) : Nat := (buf.reverse.takeWhile (· == 0)).length

theorem zeros_le (buf : List UInt8) : zeros buf ≤ buf.length := by
  unfold zeros
  have := (List.takeWhile_sublist (· == (0 : UInt8)) (l := buf.reverse)).length_le
  simpa using this

theorem getElem_rev (buf : List UInt8) (j : Nat) (hj : j < buf.length) :
    buf.reverse[j]'(by simpa using hj) = buf[buf.length - 1 - j]'(by omega) := by
  rw [List.getElem_reverse]

theorem zeros_zero (buf : List UInt8) (j : Nat) (hj : j < zeros buf) :
    buf[buf.length - 1 - j]'(by have := zeros_le buf; omega) = 0 := by
  have hl := zeros_le buf
  have := tw_zero (· == (0 : UInt8)) buf.reverse j hj
  rw [getElem_rev buf j (by omega)] at this
  simpa using this

theorem zeros_stop (buf : List UInt8) (h : zeros buf < buf.length) :
    buf[buf.length - 1 - zeros buf]'(by omega) ≠ 0 := by
  have := tw_stop (· == (0 : UInt8)) buf.reverse (by simpa [zeros] using h)
  have e := getElem_rev buf (zeros buf) h
  unfold zeros at e
  rw [e] at this
  simpa [zeros] using this

theorem unpad_spec (buf : List UInt8) (block : Nat) (hbl : block ≤ buf.length) :
    Sodium.Spec.unpad buf block =
      if h : zeros buf < block then
        (if buf[buf.length - 1 - zeros buf]'(by omega) = 0x80 then some (buf.length - 1 - zeros buf) else none)
      else none := by
  unfold Sodium.Spec.unpad
  simp only
  have hz : (buf.reverse.takeWhile (· == 0)).length = zeros buf := rfl
  rw [hz]
  by_cases h : zeros buf < block
  · rw [dif_pos h]
    have h2 : zeros buf < buf.length := by omega
    have hget : buf[buf.length - 1 - zeros buf]? = some (buf[buf.length - 1 - zeros buf]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [hget]
    by_cases h3 : buf[buf.length - 1 - zeros buf]'(by omega) = 0x80
    · rw [if_pos h3, if_pos]; simp [h, h2, h3]
    · rw [if_neg h3, if_neg]; simp [h3]
  · rw [dif_neg h, if_neg]; simp [h]

end Sodium.Proofs.Unpad
