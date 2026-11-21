import Solutions.OpensslPoly1305.UpdTail
/-!
# The specification side of `Poly1305_Update`

The accumulator after a chunk (`accOf` of the longer message) from the blocks the code folds in
(`accB` over memory = `accMa` over the message's blocks, `accB_bytes`), and `goodB_mk`: the context
words and data bytes after a run give `GoodB` of the longer message.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

theorem toUInt32_add (k i : Nat) : (k + i).toUInt32 = k.toUInt32 + i.toUInt32 := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']
  omega

theorem memBytes_add (mem : ByteArray) (a : UInt32) (k m : Nat) :
    memBytes mem a (k + m) = memBytes mem a k ++ memBytes mem (a + k.toUInt32) m := by
  unfold memBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [toUInt32_add, UInt32.add_assoc]

theorem memBytes_length (mem : ByteArray) (a : UInt32) (n : Nat) : (memBytes mem a n).length = n := by
  simp [memBytes]

theorem bval_memBytes {G : PMem} {a : UInt32} (h : a.toNat + 16 ≤ G.get.size) (htop : G.get.size ≤ ramTop) :
    bval G a = leNat (memBytes G.get a 16) := by
  have ht : memBytes G.get a 16 = (memBytes G.get a 16).take 16 := by
    rw [List.take_of_length_le (by simp [memBytes_length])]
  rw [ht, leNat_take16 _ (by simp [memBytes_length])]
  unfold wd4 bval val4
  simp only [Nat.zero_add]
  rw [wd_memBytes h htop 0 (by decide) 0 rfl, uadd_zero, wd_memBytes h htop 4 (by decide) 4 rfl,
    wd_memBytes h htop 8 (by decide) 8 rfl, wd_memBytes h htop 12 (by decide) 12 rfl]

theorem accMa_cons (R x : Nat) (b : List UInt8) (bl : List (List UInt8)) :
    accMa R x (b :: bl) = accMa R ((x + mval b) * R % p) bl := rfl

theorem accB_succ (G : PMem) (R padv : Nat) (a : UInt32) (n x : Nat) :
    accB G R padv a (n + 1) x = accB G R padv (UInt32.add a 16) n ((x + bval G a + 2 ^ 128 * padv) * R % p) := rfl

/-- The blocks `poly1305_blocks` folds in with pad bit 1 are the message's blocks. -/
theorem accB_bytes {G : PMem} (R : Nat) (htop : G.get.size ≤ ramTop) :
    ∀ (n : Nat) (a : UInt32) (x : Nat), a.toNat + 16 * n ≤ G.get.size →
      accB G R 1 a n x = accMa R x (blocks (memBytes G.get a (16 * n)))
  | 0, a, x, _ => rfl
  | n + 1, a, x, h => by
    rw [show 16 * (n + 1) = 16 + 16 * n by omega, memBytes_add, blocks_cons16 _ _ (memBytes_length _ _ _),
      accMa_cons]
    have hb := bval_memBytes (G := G) (a := a) (by omega) htop
    have ih := accB_bytes R htop n (UInt32.add a 16) ((x + mval (memBytes G.get a 16)) * R % p) (by
      rw [uadd_sem]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega)
    rw [accB_succ, show a + Nat.toUInt32 16 = UInt32.add a 16 from rfl]
    rw [hb, show x + leNat (memBytes G.get a 16) + 2 ^ 128 * 1 = x + mval (memBytes G.get a 16) by
      unfold mval; rw [memBytes_length]; omega, ih]

theorem fullLen_of_mod0 {l : List UInt8} (h : l.length % 16 = 0) : fullLen l = l.length := by
  unfold fullLen; omega

/-- A message of whole blocks followed by `B`: the whole blocks of `B` are folded in. -/
theorem accOf_append0 (R : Nat) (msg B : List UInt8) (h : msg.length % 16 = 0) :
    accOf R (msg ++ B) = accMa R (accOf R msg) (blocks (B.take (16 * (B.length / 16)))) := by
  unfold accOf
  have e1 : fullLen (msg ++ B) = msg.length + 16 * (B.length / 16) := by
    unfold fullLen; simp only [List.length_append]; omega
  rw [e1, List.take_length_add_append, fullLen_of_mod0 h, List.take_length,
    blocks_append (msg.length / 16) msg _ (by omega), accM_append]

/-- A short addition to the buffered tail does not change the whole blocks. -/
theorem accOf_append_short (R : Nat) (msg B : List UInt8) (h : msg.length % 16 + B.length < 16) :
    accOf R (msg ++ B) = accOf R msg := by
  unfold accOf
  have e1 : fullLen (msg ++ B) = fullLen msg := by
    unfold fullLen; simp only [List.length_append]; omega
  rw [e1, List.take_append_of_le_length (fullLen_le msg)]

/-- Filling the buffered tail to a block. -/
theorem accOf_fill (R : Nat) (msg B : List UInt8) (h0 : msg.length % 16 ≠ 0)
    (h : 16 - msg.length % 16 ≤ B.length) :
    accOf R (msg ++ B.take (16 - msg.length % 16)) =
      accMa R (accOf R msg) [msg.drop (fullLen msg) ++ B.take (16 - msg.length % 16)] := by
  have hl : (msg.drop (fullLen msg) ++ B.take (16 - msg.length % 16)).length = 16 := by
    simp only [List.length_append, drop_fullLen_length, List.length_take]; omega
  have e : msg ++ B.take (16 - msg.length % 16) =
      msg.take (fullLen msg) ++ (msg.drop (fullLen msg) ++ B.take (16 - msg.length % 16)) := by
    rw [← List.append_assoc, List.take_append_drop]
  have hm : (msg ++ B.take (16 - msg.length % 16)).length % 16 = 0 := by
    simp only [List.length_append, List.length_take]; omega
  unfold accOf
  rw [fullLen_of_mod0 hm, List.take_length, e,
    blocks_append (msg.length / 16) _ _ (by rw [take_fullLen_length]; rfl), accM_append]
  congr 1
  rw [← List.append_nil (msg.drop (fullLen msg) ++ B.take (16 - msg.length % 16)), blocks_cons16 _ _ hl,
    blocks_nil, List.append_nil]

/-! ## The context after a run -/

/-- The context word at `k` in memory `G`. -/
def cw (G : PMem) (C k : UInt32) : UInt32 := rdRaw G.get (UInt32.add C k) 4

theorem getElem!_memBytes {mem : ByteArray} {a : UInt32} {n k : Nat} (hk : k < n) :
    (memBytes mem a n)[k]! = memByte mem (a + k.toUInt32) := memBytes_get hk

set_option maxHeartbeats 1000000 in
/-- The context words and data bytes after a run give `GoodB` of the new message. -/
theorem goodB_mk (key msg msg' : List UInt8) {G N' : PMem} {U C : UInt32} {lU lC : List (Nat × UInt32)}
    {P : Nat → Prop} (hg : GoodB key msg (memBytes G.get C 236)) (hM : MemOK G N' U 272 lU C 236 236 lC P)
    (o0 o1 o2 o3 o4 t : UInt32)
    (hlC : LK lC (W13 o0 o1 o2 o3 o4 (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) (cw G C 192) (cw G C 196)
      (cw G C 200) (cw G C 204)))
    (hlt : LK lC [(224, t)])
    (ho4 : o4.toNat ≤ 4) (hacc : val5 o0 o1 o2 o3 o4 % p = accOf (r key) msg') (ht : t.toNat = msg'.length % 16)
    (hd : ∀ j, j < msg'.length % 16 → memByte N'.get (C + (208 + j).toUInt32) = msg'[fullLen msg' + j]!) :
    GoodB key msg' (memBytes N'.get C 236) := by
  have hf := hM.fC
  have hs := hM.size
  have hfG : C.toNat + 236 ≤ G.get.size := by rw [← hs]; exact hf.fit
  have htG : G.get.size ≤ ramTop := by rw [← hs]; exact hf.top
  have hw : ∀ (k : Nat) (j : UInt32), j.toNat = k → k + 4 ≤ 236 →
      wd (memBytes N'.get C 236) k = (rdRaw N'.get (UInt32.add C j) 4).toNat :=
    fun k j hj hk4 => wd_memBytes hf.fit hf.top k hk4 j hj
  have hwG : ∀ (k : Nat) (j : UInt32), j.toNat = k → k + 4 ≤ 236 →
      wd (memBytes G.get C 236) k = (cw G C j).toNat :=
    fun k j hj hk4 => wd_memBytes hfG htG k hk4 j hj
  obtain ⟨_, _, _, hr, hcl, hsk, _, _⟩ := hg
  have z0 := hw 0 0 rfl (by decide); rw [hM.rdC (k := 0) hlC.1 0 rfl] at z0
  have z4 := hw 4 4 rfl (by decide); rw [hM.rdC (k := 4) hlC.2.1 4 rfl] at z4
  have z8 := hw 8 8 rfl (by decide); rw [hM.rdC (k := 8) hlC.2.2.1 8 rfl] at z8
  have z12 := hw 12 12 rfl (by decide); rw [hM.rdC (k := 12) hlC.2.2.2.1 12 rfl] at z12
  have z16 := hw 16 16 rfl (by decide); rw [hM.rdC (k := 16) hlC.2.2.2.2.1 16 rfl] at z16
  have w20 := hw 20 20 rfl (by decide); rw [hM.rdC (k := 20) hlC.2.2.2.2.2.1 20 rfl, ← hwG 20 20 rfl (by decide)] at w20
  have w24 := hw 24 24 rfl (by decide)
  rw [hM.rdC (k := 24) hlC.2.2.2.2.2.2.1 24 rfl, ← hwG 24 24 rfl (by decide)] at w24
  have w28 := hw 28 28 rfl (by decide)
  rw [hM.rdC (k := 28) hlC.2.2.2.2.2.2.2.1 28 rfl, ← hwG 28 28 rfl (by decide)] at w28
  have w32 := hw 32 32 rfl (by decide)
  rw [hM.rdC (k := 32) hlC.2.2.2.2.2.2.2.2.1 32 rfl, ← hwG 32 32 rfl (by decide)] at w32
  have s0 := hw 192 192 rfl (by decide)
  rw [hM.rdC (k := 192) hlC.2.2.2.2.2.2.2.2.2.1 192 rfl, ← hwG 192 192 rfl (by decide)] at s0
  have s4 := hw 196 196 rfl (by decide)
  rw [hM.rdC (k := 196) hlC.2.2.2.2.2.2.2.2.2.2.1 196 rfl, ← hwG 196 196 rfl (by decide)] at s4
  have s8 := hw 200 200 rfl (by decide)
  rw [hM.rdC (k := 200) hlC.2.2.2.2.2.2.2.2.2.2.2.1 200 rfl, ← hwG 200 200 rfl (by decide)] at s8
  have s12 := hw 204 204 rfl (by decide)
  rw [hM.rdC (k := 204) hlC.2.2.2.2.2.2.2.2.2.2.2.2.1 204 rfl, ← hwG 204 204 rfl (by decide)] at s12
  have n0 := hw 224 224 rfl (by decide); rw [hM.rdC (k := 224) hlt.1 224 rfl] at n0
  refine ⟨by simp [memBytes], by rw [z16]; exact ho4, ?_, ?_, ?_, ?_, by rw [n0, ht], fun j hj => ?_⟩
  · unfold wd4; rw [z0, z4, z8, z12, z16]; exact hacc
  · unfold wd4 at hr ⊢; simp only [Nat.reduceAdd] at hr ⊢; rw [w20, w24, w28, w32]; exact hr
  · rw [w20, w24, w28, w32]; exact hcl
  · unfold wd4 at hsk ⊢; simp only [Nat.reduceAdd] at hsk ⊢; rw [s0, s4, s8, s12]; exact hsk
  · rw [getElem!_memBytes (by omega), ← hd j hj]

end Solutions.OpensslPoly1305
