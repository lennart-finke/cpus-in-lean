import Ssl.Spec.Chacha
/-!
# ChaCha20 encryption byte by byte

`crypt_getElem`: byte `i` of `Spec.Chacha.crypt n s src` is `src[i]` xor byte `i % 64` of the block
of the state advanced by `i / 64` blocks.
-/
namespace Solutions.OpensslChacha20
open Ssl Ssl.Spec.Chacha

theorem le32_length (v : UInt32) : (le32 v).length = 4 := rfl

theorem block_length (n : Nat) (s : Array UInt32) : (block n s).length = 64 := by
  simp [block, List.length_flatMap, le32_length]
  decide

theorem keystream_length (n : Nat) (s : Array UInt32) (k : Nat) : (keystream n s k).length = 64 * k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [keystream, List.length_append, block_length, ih]; omega

theorem advance_size (s : Array UInt32) (n : Nat) : (advance s n).size = s.size := by
  simp [advance]

theorem toUInt32_add (a b : Nat) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := by
  apply UInt32.toNat_inj.1
  simp only [Nat.toUInt32_eq, UInt32.toNat_add, UInt32.toNat_ofNat']
  omega

theorem getElem!_twelve (s : Array UInt32) (h : 12 < s.size) : s[12]! = s[12] := by
  simp [getElem!_pos, h]

theorem advance_zero (s : Array UInt32) (h : 12 < s.size) : advance s 0 = s := by
  apply Array.ext (advance_size s 0)
  intro i h1 h2
  simp only [advance, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds h2]
  split
  · subst_vars; rw [getElem!_twelve s h]; exact UInt32.add_zero _
  · rfl

theorem advance_advance (s : Array UInt32) (a b : Nat) (h : 12 < s.size) :
    advance (advance s a) b = advance s (a + b) := by
  simp only [advance, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  congr 1
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_setIfInBounds_self, toUInt32_add, UInt32.add_assoc]

theorem keystream_getElem (n : Nat) (s : Array UInt32) (hs : 12 < s.size) (k i : Nat)
    (h : i < (keystream n s k).length) :
    (keystream n s k)[i] = (block n (advance s (i / 64)))[i % 64]'(by
      rw [block_length]; exact Nat.mod_lt _ (by decide)) := by
  induction k generalizing s i with
  | zero => simp [keystream] at h
  | succ k ih =>
    simp only [keystream]
    by_cases hi : i < 64
    · rw [List.getElem_append_left (by rw [block_length]; exact hi)]
      simp only [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, advance_zero s hs]
    · have hl := keystream_length n s (k + 1)
      rw [List.getElem_append_right (by rw [block_length]; omega)]
      simp only [block_length]
      have hs' : 12 < (advance s 1).size := by rw [advance_size]; exact hs
      rw [ih (advance s 1) hs' (i - 64) (by rw [keystream_length]; rw [hl] at h; omega)]
      have e1 : (i - 64) / 64 = i / 64 - 1 := by omega
      have e2 : (i - 64) % 64 = i % 64 := by omega
      have e3 : 1 + (i / 64 - 1) = i / 64 := by omega
      simp only [e1, e2, advance_advance s 1 _ hs, e3]

theorem crypt_length (n : Nat) (s : Array UInt32) (src : List UInt8) : (crypt n s src).length = src.length := by
  simp only [crypt, List.length_zipWith, keystream_length]
  omega

theorem crypt_getElem (n : Nat) (s : Array UInt32) (hs : 12 < s.size) (src : List UInt8) (i : Nat)
    (h : i < (crypt n s src).length) :
    (crypt n s src)[i] = src[i]'(by rw [crypt_length] at h; exact h) ^^^
      (block n (advance s (i / 64)))[i % 64]'(by rw [block_length]; exact Nat.mod_lt _ (by decide)) := by
  simp only [crypt, List.getElem_zipWith]
  rw [keystream_getElem n s hs]

theorem length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) (hk : ∀ a, (f a).length = k)
    (l : List α) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, hk, ih, List.length_cons, Nat.succ_mul]; omega

theorem getElem_flatMap_const {α β : Type} (f : α → List β) (k : Nat) (hk : ∀ a, (f a).length = k) :
    ∀ (l : List α) (i : Nat) (h : i < l.length * k),
      (l.flatMap f)[i]'(by rw [length_flatMap_const f k hk]; exact h) =
        (f (l[i / k]'(Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h))))[i % k]'(by
          rw [hk]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at h)))
  | [], i, h => by simp at h
  | a :: l, i, h => by
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at h)
    have hka := hk a
    simp only [List.flatMap_cons]
    by_cases hi : i < k
    · rw [List.getElem_append_left (by rw [hk]; exact hi)]
      simp only [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getElem_cons_zero]
    · rw [List.getElem_append_right (by rw [hk]; omega)]
      have h2 : i - k < l.length * k := by
        simp only [List.length_cons, Nat.succ_mul] at h; omega
      have e0 : i - (f a).length = i - k := by rw [hk]
      simp only [e0]
      rw [getElem_flatMap_const f k hk l (i - k) h2]
      have e1 : i / k = (i - k) / k + 1 := Nat.div_eq_sub_div hk0 (by omega)
      have e2 : (i - k) % k = i % k := (Nat.mod_eq_sub_mod (show k ≤ i by omega)).symm
      simp only [e2]
      congr 2
      simp only [e1, List.getElem_cons_succ]

end Solutions.OpensslChacha20
