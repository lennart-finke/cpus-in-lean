import Solutions.OpensslChacha20.Spec
import Solutions.OpensslChacha20.Rounds
import Solutions.OpensslChacha20.RunUtil
/-!
# Keystream bytes from words

The bytes of a word in memory are its little-endian bytes (`get!_of_rdRaw4`); the keystream block of
a state is the 16 words `permute + state`, byte by byte (`block_getElem`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Ssl.Spec.Chacha Solutions.Logic

theorem join_split (b0 b1 b2 b3 : UInt8) :
    let B : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    B.toUInt8 = b0 ∧ (B >>> 8).toUInt8 = b1 ∧ (B >>> 16).toUInt8 = b2 ∧ (B >>> 24).toUInt8 = b3 := by
  intro B
  have hge : ∀ (b : UInt8) (j : Nat), 8 ≤ j → b.toBitVec.getLsbD j = false :=
    fun b j hj => BitVec.getLsbD_of_ge _ _ hj
  have h8 : (UInt32.toBitVec 8 % 32).toNat = 8 := rfl
  have h16 : (UInt32.toBitVec 16 % 32).toNat = 16 := rfl
  have h24 : (UInt32.toBitVec 24 % 32).toNat = 24 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [B, shr32, shl32, UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_shiftRight,
      UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, UInt8.toBitVec_toUInt32, hi, decide_true, Bool.true_and, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', h8, h16, h24]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hge]

/-- The bytes of a word in memory are its little-endian bytes. -/
theorem get!_of_rdRaw4 {M : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ M.size) (hv : rdRaw M a 4 = v)
    (j : Nat) (hj : j < 4) : M.get! (a.toNat + j) = (le32 v)[j]'(by rw [le32_length]; exact hj) := by
  unfold rdRaw at hv
  rw [rdBytes4_eq h] at hv
  obtain ⟨e0, e1, e2, e3⟩ := join_split (M.get! a.toNat) (M.get! (a.toNat + 1)) (M.get! (a.toNat + 2))
    (M.get! (a.toNat + 3))
  subst hv
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm

/-- The `i`-th field of sixteen words. -/
def V16.get (v : V16) (i : Nat) : UInt32 := v.toArr[i]!

theorem repeat_toArr : ∀ (j : Nat) (v : V16), Nat.repeat doubleRound j v.toArr = (Nat.repeat dround j v).toArr
  | 0, _ => rfl
  | j + 1, v => by simp only [Nat.repeat]; rw [repeat_toArr j v, doubleRound_toArr]

/-- Byte `i` of the keystream block of the state `w`: byte `i % 4` of word `i / 4` of
`permute + state`. -/
theorem block_getElem (w : V16) (i : Nat) (hi : i < 64) :
    (block 20 w.toArr)[i]'(by rw [block_length]; exact hi) =
      (le32 (((Nat.repeat dround 10 w).get (i / 4)) + w.get (i / 4)))[i % 4]'(by
        rw [le32_length]; exact Nat.mod_lt _ (by decide)) := by
  unfold block
  simp only []
  rw [getElem_flatMap_const _ 4 (fun _ => le32_length _) _ i (by simpa using hi)]
  simp only [List.getElem_range, permute, repeat_toArr, V16.get]

end Solutions.OpensslChacha20
