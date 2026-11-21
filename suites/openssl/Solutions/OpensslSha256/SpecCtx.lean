import Solutions.OpensslSha256.SpecStream
/-!
# The context of a streaming computation, as a specification

After the bytes `msg` the context holds the hash words compressed over the whole blocks of `msg`
(`hOf`), the bit count `8 |msg|` in two words, the bytes of the incomplete last block (`tailOf`) at
the start of the buffer, their number, and the digest length (`Good`). `hOf_small` and `hOf_big` are
the two ways an `Update` changes the whole blocks and the tail.
-/
namespace Solutions.OpensslSha256
open Ssl Ssl.Spec.Sha256

/-- The little-endian word at byte offset `k` of a byte list. -/
def lw (st : List UInt8) (k : Nat) : UInt32 :=
  st[k]!.toUInt32 ||| (st[k + 1]!.toUInt32 <<< 8) ||| (st[k + 2]!.toUInt32 <<< 16) ||| (st[k + 3]!.toUInt32 <<< 24)

/-- The hash words after the whole blocks of `msg`. -/
def hOf (H0 : Array UInt32) (msg : List UInt8) : Array UInt32 :=
  (blocks (msg.take (64 * (msg.length / 64)))).foldl compress H0

/-- The bytes after the whole blocks. -/
def tailOf (msg : List UInt8) : List UInt8 := msg.drop (64 * (msg.length / 64))

/-- The 112 context bytes `st` after the bytes `msg`, from the initial value `H0` and digest length `md`. -/
structure Good (H0 : Array UInt32) (md : Nat) (msg : List UInt8) (st : List UInt8) : Prop where
  len : st.length = 112
  lt : msg.length < lenBound
  h : ∀ k, k < 8 → lw st (4 * k) = (hOf H0 msg)[k]!
  nl : lw st 32 = (8 * msg.length).toUInt32
  nh : lw st 36 = (8 * msg.length / 2 ^ 32).toUInt32
  num : lw st 104 = (msg.length % 64).toUInt32
  data : ∀ i, i < msg.length % 64 → st[40 + i]! = (tailOf msg)[i]!
  md : lw st 108 = md.toUInt32

theorem tailOf_length (msg : List UInt8) : (tailOf msg).length = msg.length % 64 := by
  unfold tailOf; rw [List.length_drop]; omega

theorem take_append_tail (msg : List UInt8) : msg.take (64 * (msg.length / 64)) ++ tailOf msg = msg :=
  List.take_append_drop _ _

theorem foldl_blocks_append (H : Array UInt32) (X Y : List UInt8) (k : Nat) (hX : X.length = 64 * k) :
    (blocks (X ++ Y)).foldl compress H = (blocks Y).foldl compress ((blocks X).foldl compress H) := by
  rw [blocks_append X Y k hX, List.foldl_append]

theorem blocks_one (B : List UInt8) (h : B.length = 64) : blocks B = [B] := by
  rw [blocks_cons64 B (by omega)]
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
  rfl

/-- An `Update` that stays inside the incomplete block. -/
theorem hOf_small (H0 : Array UInt32) (msg chunk : List UInt8) (h : msg.length % 64 + chunk.length < 64) :
    hOf H0 (msg ++ chunk) = hOf H0 msg ∧ tailOf (msg ++ chunk) = tailOf msg ++ chunk := by
  have e : (msg ++ chunk).length / 64 = msg.length / 64 := by simp; omega
  have hW : (msg.take (64 * (msg.length / 64))).length = 64 * (msg.length / 64) := by
    rw [List.length_take]; omega
  constructor
  · unfold hOf
    rw [e, List.take_append_of_le_length (by omega)]
  · unfold tailOf
    rw [e, List.drop_append_of_le_length (by omega)]

/-- An `Update` that completes blocks: the incomplete block `T` with the first `j` bytes of the chunk
(if `T` is not empty), then the whole blocks of the rest, then the new tail. -/
theorem hOf_big (H0 : Array UInt32) (msg chunk : List UInt8) (j : Nat)
    (hj : (msg.length % 64 = 0 ∧ j = 0) ∨ (msg.length % 64 ≠ 0 ∧ j = 64 - msg.length % 64 ∧ j ≤ chunk.length)) :
    hOf H0 (msg ++ chunk) =
      (blocks ((chunk.drop j).take (64 * ((chunk.length - j) / 64)))).foldl compress
        ((blocks (tailOf msg ++ chunk.take j)).foldl compress (hOf H0 msg)) ∧
    tailOf (msg ++ chunk) = (chunk.drop j).drop (64 * ((chunk.length - j) / 64)) := by
  have hT := tailOf_length msg
  obtain ⟨e, he⟩ : ∃ e, (tailOf msg ++ chunk.take j).length = 64 * e := by
    rw [List.length_append, List.length_take, hT]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
  have hW : (msg.take (64 * (msg.length / 64))).length = 64 * (msg.length / 64) := by
    rw [List.length_take]; omega
  have hR : ((chunk.drop j).take (64 * ((chunk.length - j) / 64))).length = 64 * ((chunk.length - j) / 64) := by
    rw [List.length_take, List.length_drop]; omega
  have hsplit : msg ++ chunk = (msg.take (64 * (msg.length / 64)) ++ (tailOf msg ++ chunk.take j) ++
      (chunk.drop j).take (64 * ((chunk.length - j) / 64))) ++ (chunk.drop j).drop (64 * ((chunk.length - j) / 64)) := by
    conv => lhs; rw [← take_append_tail msg, ← List.take_append_drop j chunk,
      ← List.take_append_drop (64 * ((chunk.length - j) / 64)) (chunk.drop j)]
    simp only [List.append_assoc]
  have hPlen : (msg.take (64 * (msg.length / 64)) ++ (tailOf msg ++ chunk.take j) ++
      (chunk.drop j).take (64 * ((chunk.length - j) / 64))).length =
      64 * (msg.length / 64 + e + (chunk.length - j) / 64) := by
    have he' : (tailOf msg).length + (chunk.take j).length = 64 * e := by rw [← List.length_append]; exact he
    simp only [List.length_append]; rw [hW, hR]; omega
  have hRlen : ((chunk.drop j).drop (64 * ((chunk.length - j) / 64))).length < 64 := by
    rw [List.length_drop, List.length_drop]; omega
  have hK : (msg ++ chunk).length / 64 = msg.length / 64 + e + (chunk.length - j) / 64 := by
    rw [hsplit, List.length_append, hPlen]; omega
  constructor
  · unfold hOf
    rw [hK, hsplit, List.take_left' hPlen,
      foldl_blocks_append H0 _ _ (msg.length / 64 + e) (by
        have he' : (tailOf msg).length + (chunk.take j).length = 64 * e := by rw [← List.length_append]; exact he
        simp only [List.length_append]; rw [hW]; omega),
      foldl_blocks_append H0 _ _ (msg.length / 64) hW]
  · unfold tailOf
    rw [hK, hsplit, List.drop_left' hPlen]

/-! ## The padded tail -/

theorem be64_split (v : Nat) (h : v < 2 ^ 64) :
    be64 v.toUInt64 = be32 (v / 2 ^ 32).toUInt32 ++ be32 v.toUInt32 := by
  unfold be64 le64 be32
  rw [List.reverse_append]
  have e1 : v.toUInt64.toUInt32 = v.toUInt32 := by
    apply UInt32.toNat_inj.1
    simp only [UInt64.toNat_toUInt32, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat']
    omega
  have e2 : (v.toUInt64 >>> 32).toUInt32 = (v / 2 ^ 32).toUInt32 := by
    apply UInt32.toNat_inj.1
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    show v % 2 ^ 64 / 2 ^ (32 % 64) % 2 ^ 32 = v / 2 ^ 32 % 2 ^ 32
    rw [Nat.mod_eq_of_lt h]
  rw [e1, e2]

theorem hashWords_tail (H0 : Array UInt32) (msg : List UInt8) :
    hashWords H0 msg = (blocks (tailOf msg ++ [0x80] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++
      be64 (8 * msg.length).toUInt64)).foldl compress (hOf H0 msg) := by
  have := hashWords_split H0 (msg.take (64 * (msg.length / 64))) (tailOf msg) (msg.length / 64)
    (by rw [List.length_take]; omega)
  rw [take_append_tail] at this
  rw [this]; rfl

/-- The padded tail in one block. -/
theorem hashWords_one (H0 : Array UInt32) (msg : List UInt8) (hr : msg.length % 64 ≤ 55) (hm : msg.length < lenBound) :
    hashWords H0 msg = compress (hOf H0 msg) (tailOf msg ++ [0x80] ++ List.replicate (55 - msg.length % 64) 0 ++
      be32 (8 * msg.length / 2 ^ 32).toUInt32 ++ be32 (8 * msg.length).toUInt32) := by
  rw [hashWords_tail, show (119 - msg.length % 64) % 64 = 55 - msg.length % 64 by omega,
    be64_split _ (by unfold lenBound at hm; omega), ← List.append_assoc, blocks_one]
  · rfl
  · simp only [List.length_append, List.length_replicate, tailOf_length, be32, le32, List.length_reverse]
    simp; omega

/-- The padded tail in two blocks. -/
theorem hashWords_two (H0 : Array UInt32) (msg : List UInt8) (hr : 56 ≤ msg.length % 64) (hm : msg.length < lenBound) :
    hashWords H0 msg = compress (compress (hOf H0 msg) (tailOf msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0))
      (List.replicate 56 0 ++ be32 (8 * msg.length / 2 ^ 32).toUInt32 ++ be32 (8 * msg.length).toUInt32) := by
  have hT := tailOf_length msg
  have hl32 : ∀ v : UInt32, (be32 v).length = 4 := fun v => by simp [be32, le32]
  rw [hashWords_tail, show (119 - msg.length % 64) % 64 = (63 - msg.length % 64) + 56 by omega,
    be64_split _ (by unfold lenBound at hm; omega), ← List.replicate_append_replicate]
  have hA : (tailOf msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0).length = 64 := by
    simp only [List.length_append, List.length_replicate, hT, List.length_singleton]; omega
  have e : tailOf msg ++ [0x80] ++ (List.replicate (63 - msg.length % 64) 0 ++ List.replicate 56 0) ++
      (be32 (8 * msg.length / 2 ^ 32).toUInt32 ++ be32 (8 * msg.length).toUInt32) =
      (tailOf msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0) ++
        (List.replicate 56 0 ++ be32 (8 * msg.length / 2 ^ 32).toUInt32 ++ be32 (8 * msg.length).toUInt32) := by
    simp only [List.append_assoc]
  rw [e, blocks_append _ _ 1 hA, blocks_one _ hA, blocks_one]
  · rfl
  · simp only [List.length_append, List.length_replicate, hl32]

/-! ## The bit count -/

/-- `Update` adds `8 len` to the 64-bit bit count kept in two words. -/
theorem bitcount_add (m len : Nat) (hm : m + len < lenBound) :
    ((8 * (m + len)) % 2 ^ 32 = ((8 * m) % 2 ^ 32 + (8 * len) % 2 ^ 32) % 2 ^ 32) ∧
    ((8 * (m + len)) / 2 ^ 32 % 2 ^ 32 =
      ((8 * m) / 2 ^ 32 % 2 ^ 32 + len / 2 ^ 29 % 2 ^ 32 +
        (if (8 * m) % 2 ^ 32 + (8 * len) % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32) := by
  unfold lenBound at hm
  constructor
  · omega
  · split <;> omega

end Solutions.OpensslSha256
