import Solutions.OpensslSha256.X.Bswap
import Solutions.OpensslSha256.X.UpdContract
/-!
# Bytes of words, and the digest in memory

`get!_of_rdRaw4'`: the bytes of a word in memory are its little-endian bytes (as in the ChaCha20
proof); `le32_bsw`: those of `bsw w` are the big-endian bytes of `w`; `digest_of_words`: words
`bsw H[i]` at `out + 4 i` make the bytes at `out` the big-endian digest of `H`.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem le32_length' (v : UInt32) : (le32 v).length = 4 := rfl

theorem length_flatMap_const' {α β : Type} (f : α → List β) (k : Nat) (hk : ∀ a, (f a).length = k)
    (l : List α) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, hk, ih, List.length_cons, Nat.succ_mul]; omega

theorem getElem_flatMap_const' {α β : Type} (f : α → List β) (k : Nat) (hk : ∀ a, (f a).length = k) :
    ∀ (l : List α) (i : Nat) (h : i < l.length * k),
      (l.flatMap f)[i]'(by rw [length_flatMap_const' f k hk]; exact h) =
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
      rw [getElem_flatMap_const' f k hk l (i - k) h2]
      have e1 : i / k = (i - k) / k + 1 := Nat.div_eq_sub_div hk0 (by omega)
      have e2 : (i - k) % k = i % k := (Nat.mod_eq_sub_mod (show k ≤ i by omega)).symm
      simp only [e2]
      congr 2
      simp only [e1, List.getElem_cons_succ]

theorem join_split' (b0 b1 b2 b3 : UInt8) :
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
theorem get!_of_rdRaw4' {M : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ M.size) (hv : rdRaw M a 4 = v)
    (j : Nat) (hj : j < 4) : M.get! (a.toNat + j) = (le32 v)[j]'(by rw [le32_length']; exact hj) := by
  unfold rdRaw at hv
  rw [rdBytes4_eq h] at hv
  obtain ⟨e0, e1, e2, e3⟩ := join_split' (M.get! a.toNat) (M.get! (a.toNat + 1)) (M.get! (a.toNat + 2))
    (M.get! (a.toNat + 3))
  subst hv
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm

theorem le32_bsw (w : UInt32) : le32 (bsw w) = be32 w := by
  unfold be32 le32
  rw [bsw_b0, bsw_b1, bsw_b2, bsw_b3]
  rfl

/-- Words `bsw H[i]` at `out + 4 i` are the big-endian digest. -/
theorem digest_of_words (M : ByteArray) (out : UInt32) (Hf : Array UInt32) (m : Nat)
    (hfit : out.toNat + 4 * m ≤ M.size) (hM : M.size < 2 ^ 32)
    (hw : ∀ i : Nat, i < m → rdRaw M (out + (4 * i).toUInt32) 4 = bsw Hf[i]!) :
    memBytes M out (4 * m) = (List.range m).flatMap (fun i : Nat => be32 Hf[i]!) := by
  have hk : ∀ i : Nat, (be32 Hf[i]!).length = 4 := fun i => by rw [← le32_bsw]; rfl
  rw [memBytes_eq_iff]
  refine ⟨by rw [length_flatMap_const' _ 4 hk, List.length_range]; omega, fun p hp => ?_⟩
  have hp' : p < (List.range m).length * 4 := by rw [← length_flatMap_const' _ 4 hk]; exact hp
  rw [getElem_flatMap_const' _ 4 hk _ p hp']
  have hq : p / 4 < m := by rw [List.length_range] at hp'; omega
  have ea : (out + (4 * (p / 4)).toUInt32).toNat = out.toNat + 4 * (p / 4) := by
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have eb : (out + p.toUInt32).toNat = out.toNat + p := by
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have := get!_of_rdRaw4' (by rw [ea]; omega) (hw (p / 4) hq) (p % 4) (Nat.mod_lt _ (by decide))
  rw [ea, show out.toNat + 4 * (p / 4) + p % 4 = out.toNat + p by omega] at this
  rw [memByte_def (by rw [eb]; omega), eb, this]
  simp only [List.getElem_range, le32_bsw]

theorem sub8_add (V : UInt32) (k : UInt32) (hV : 8 ≤ V.toNat) (hk : 8 ≤ k.toNat) : (V - 8).add k = V.add (k - 8) := by
  apply UInt32.toNat_inj.1
  have := V.toNat_lt; have := k.toNat_lt
  rw [uadd_toNat, uadd_toNat, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hV),
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hk)]
  simp only [UInt32.reduceToNat]
  omega

/-- `OPENSSL_cleanse(p, len)` called with the stack pointer at `V.add 12`. -/
theorem cleanse_V (H : CMem) (V ra p len eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hV8 : 8 ≤ V.toNat) (hU : V.toNat + 24 ≤ H.get.size) (hUc : OffCode (V - 8) 32)
    (hra : rdRaw H.get (V.add 12) 4 = ra) (hp : rdRaw H.get (V.add 16) 4 = p) (hl : rdRaw H.get (V.add 20) 4 = len)
    (hd : p.toNat + len.toNat ≤ H.get.size) (hdc : OffCode p len.toNat)
    (hdU : p.toNat + len.toNat + 8 ≤ V.toNat ∨ V.toNat + 24 ≤ p.toNat)
    (hic : ic.toNat + 4 * len.toNat + 40 < 2 ^ 64) :
    ∃ (H' : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 4 * len.toNat + 29 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, V.add 12, ebp, esi, edi, 0x1011d0, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, V.add 16, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => V.toNat - 8 ≤ a ∧ a < V.toNat + 12 ∨ p.toNat ≤ a ∧ a < p.toNat + len.toNat) H.get H'.get ∧
      ∀ i, i < len.toNat → H'.get.get! (p.toNat + i) = 0 := by
  have tW : (V - 8).toNat = V.toNat - 8 := tS (y := 8) 8 rfl hV8
  have e : ∀ k : UInt32, 8 ≤ k.toNat → (V - 8).add k = V.add (k - 8) := fun k hk => sub8_add V k hV8 hk
  obtain ⟨H', eax', ecx', edx', f', ic', hic', hr, ha, hz⟩ := cleanse_call H (V - 8) ra p len eax ecx edx ebx ebp esi
    edi f ic hsz (by omega) hUc (by rw [e 20 (by decide)]; exact hra) (by rw [e 24 (by decide)]; exact hp)
    (by rw [e 28 (by decide)]; exact hl) hd hdc (by omega) hic
  rw [e 20 (by decide), e 24 (by decide)] at hr
  exact ⟨H', eax', ecx', edx', f', ic', hic', hr, ha.mono fun a h => by omega, hz⟩

/-- Zero bytes in memory. -/
theorem zeros_of (M : ByteArray) (a : UInt32) (n : Nat) (hfit : a.toNat + n ≤ M.size) (hM : M.size < 2 ^ 32)
    (hz : ∀ i, i < n → M.get! (a.toNat + i) = 0) : memBytes M a n = List.replicate n 0 := by
  rw [memBytes_eq_iff]
  refine ⟨List.length_replicate, fun i hi => ?_⟩
  rw [List.length_replicate] at hi
  have eb : (a + i.toUInt32).toNat = a.toNat + i := by
    rw [UInt32.toNat_add, toUInt32_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  rw [memByte_def (by rw [eb]; omega), eb, hz i hi, List.getElem_replicate]

end Solutions.ShaX
