import Ssl.Spec.Sha256
/-!
# The padded message block by block

`blocks` of a concatenation whose first part is whole blocks is the concatenation of the blocks
(`blocks_append`); so the hash of a message is the compression over its whole blocks followed by
the compression over the padded tail (`hashWords_split`). This is the form the streaming calls
compute: `Update` compresses whole blocks as they fill, `Final` pads the buffered tail.
-/
namespace Solutions.OpensslSha256
open Ssl Ssl.Spec.Sha256

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
    exact blocksAux_fuel n m _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)

theorem blocksAux_eq (n : Nat) (bs : List UInt8) (h : bs.length ≤ n) :
    blocksAux n bs = blocksAux bs.length bs := blocksAux_fuel n _ bs h (Nat.le_refl _)

theorem blocks_cons64 (bs : List UInt8) (h : 64 ≤ bs.length) :
    blocks bs = bs.take 64 :: blocks (bs.drop 64) := by
  unfold blocks
  obtain ⟨n, hn⟩ : ∃ n, bs.length = n + 1 := ⟨bs.length - 1, by omega⟩
  rw [hn]
  cases bs with
  | nil => simp at hn
  | cons b bs' =>
    simp only [blocksAux]
    congr 1
    exact blocksAux_eq n _ (by simp at hn ⊢; omega)

theorem blocks_append (X Y : List UInt8) (k : Nat) (hX : X.length = 64 * k) :
    blocks (X ++ Y) = blocks X ++ blocks Y := by
  induction k generalizing X with
  | zero =>
    have : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ k ih =>
    rw [blocks_cons64 (X ++ Y) (by simp; omega), blocks_cons64 X (by omega)]
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    rw [ih (X.drop 64) (by simp; omega)]
    rfl

/-- The hash words: the compression over the whole blocks of a prefix, then over the padded rest. -/
theorem hashWords_split (H0 : Array UInt32) (B T : List UInt8) (k : Nat) (hB : B.length = 64 * k) :
    hashWords H0 (B ++ T) =
      (blocks (T ++ [0x80] ++ List.replicate ((119 - (B ++ T).length % 64) % 64) 0 ++
        be64 (8 * (B ++ T).length).toUInt64)).foldl compress ((blocks B).foldl compress H0) := by
  unfold hashWords pad
  rw [show B ++ T ++ [0x80] ++ List.replicate ((119 - (B ++ T).length % 64) % 64) 0 ++
      be64 (8 * (B ++ T).length).toUInt64 =
    B ++ (T ++ [0x80] ++ List.replicate ((119 - (B ++ T).length % 64) % 64) 0 ++
      be64 (8 * (B ++ T).length).toUInt64) by simp [List.append_assoc]]
  rw [blocks_append B _ k hB, List.foldl_append]

end Solutions.OpensslSha256
