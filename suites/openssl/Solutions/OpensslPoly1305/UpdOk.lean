import Solutions.OpensslPoly1305.UpdMath
import Solutions.OpensslPoly1305.Correct
/-!
# `Poly1305_Update` from its entry: the four paths

The context words of the entry memory `G` (`cw G C k`) are the known words `lC0 G C`. The paths:
`num = 0` and `len < 16` (`upd_pA0`), `num = 0` and `len ≥ 16` (`upd_pA1`), `num ≠ 0` and the chunk
does not fill the buffered block (`upd_pB0`), `num ≠ 0` and it does (`upd_pB1`). Each returns with
`GoodB key (msg ++ chunk)`.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

theorem icAdd_le (x : UInt64) (n : Nat) : (icAdd x n).toNat ≤ x.toNat + n := by
  rw [icAdd_eq, UInt64.toNat_add]; simp [Nat.toUInt64]; omega

/-- The context words of `G` the run needs: `num`, the data words, `h`, `r`, `s`. -/
def lC0 (G : PMem) (C : UInt32) : List (Nat × UInt32) :=
  (224, cw G C 224) :: (208, cw G C 208) :: (212, cw G C 212) :: (216, cw G C 216) :: (220, cw G C 220) ::
    W13 (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32)
      (cw G C 192) (cw G C 196) (cw G C 200) (cw G C 204)

/-- `h`, `r`, `s` of `G`. -/
abbrev WG (G : PMem) (C : UInt32) : List (Nat × UInt32) :=
  W13 (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32)
    (cw G C 192) (cw G C 196) (cw G C 200) (cw G C 204)

theorem frame_lC0 (G : PMem) (C : UInt32) : Frame G C 236 (lC0 G C) := by
  refine Frame.ofMem _ (fun k v hm => ?_)
  simp only [lC0, W13, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, by decide, rfl⟩

/-- `LK` of the words `e` survives five stores at offsets ≥ 208. -/
theorem lk_skip5 {l e : List (Nat × UInt32)} (h : LK l e) (he : ∀ k v, (k, v) ∈ e → k + 4 ≤ 208)
    (j1 j2 j3 j4 j5 : Nat) (w1 w2 w3 w4 w5 : UInt32) (h1 : 208 ≤ j1) (h2 : 208 ≤ j2) (h3 : 208 ≤ j3)
    (h4 : 208 ≤ j4) (h5 : 208 ≤ j5) :
    LK ((j1, w1) :: (j2, w2) :: (j3, w3) :: (j4, w4) :: (j5, w5) :: l) e := by
  have hk : ∀ (j : Nat), 208 ≤ j → ∀ k v, (k, v) ∈ e → k ≠ j := fun j hj k v hm => by have := he k v hm; omega
  exact ((((h.skip (hk j5 h5)).skip (hk j4 h4)).skip (hk j3 h3)).skip (hk j2 h2)).skip (hk j1 h1)

theorem lk_lC0_W (G : PMem) (C : UInt32) : LK (lC0 G C) (WG G C) :=
  lk_skip5 (lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _) (fun k v hm => W13_keys hm) _ _ _ _ _ _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The data bytes of a memory whose data words are those of `N0`. -/
theorem data_lk {G N' N0 : PMem} {U C : UInt32} {nU : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}
    (hM : MemOK G N' U nU lU C 236 236 lC P) (hs : N0.get.size = N'.get.size)
    (hl : LK lC [(208, rdRaw N0.get (UInt32.add C 208) 4), (212, rdRaw N0.get (UInt32.add C 212) 4),
      (216, rdRaw N0.get (UInt32.add C 216) 4), (220, rdRaw N0.get (UInt32.add C 220) 4)])
    (j : Nat) (hj : j < 16) : memByte N'.get (C + (208 + j).toUInt32) = memByte N0.get (C + (208 + j).toUInt32) := by
  refine data_bytes (hM.fC.size_eq hs) hs.symm (fun i hi => ?_) j hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · show rdRaw N'.get (UInt32.add C 208) 4 = rdRaw N0.get (UInt32.add C 208) 4
    exact hM.rdC (k := 208) hl.1 208 rfl
  · show rdRaw N'.get (UInt32.add C 212) 4 = rdRaw N0.get (UInt32.add C 212) 4
    exact hM.rdC (k := 212) hl.2.1 212 rfl
  · show rdRaw N'.get (UInt32.add C 216) 4 = rdRaw N0.get (UInt32.add C 216) 4
    exact hM.rdC (k := 216) hl.2.2.1 216 rfl
  · show rdRaw N'.get (UInt32.add C 220) 4 = rdRaw N0.get (UInt32.add C 220) 4
    exact hM.rdC (k := 220) hl.2.2.2.1 220 rfl

/-- What `GoodB` says about the entry memory's context words. -/
theorem goodB_cw {key msg : List UInt8} {G : PMem} {C : UInt32} (hg : GoodB key msg (memBytes G.get C 236))
    (hfit : C.toNat + 236 ≤ G.get.size) (htop : G.get.size ≤ ramTop) :
    (cw G C 16).toNat ≤ 4 ∧
    val5 (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) % p = accOf (r key) msg ∧
    r key = val4 (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) ∧
    ((cw G C 20).toNat < 2 ^ 28 ∧ (cw G C 24).toNat < 2 ^ 28 ∧ (cw G C 28).toNat < 2 ^ 28 ∧
      (cw G C 32).toNat < 2 ^ 28 ∧ (cw G C 24).toNat % 4 = 0 ∧ (cw G C 28).toNat % 4 = 0 ∧
      (cw G C 32).toNat % 4 = 0) ∧
    (cw G C 224).toNat = msg.length % 16 ∧
    ∀ j, j < msg.length % 16 → memByte G.get (C + (208 + j).toUInt32) = msg[fullLen msg + j]! := by
  have hw : ∀ (k : Nat) (j : UInt32), j.toNat = k → k + 4 ≤ 236 →
      wd (memBytes G.get C 236) k = (cw G C j).toNat :=
    fun k j hj hk4 => wd_memBytes hfit htop k hk4 j hj
  obtain ⟨_, h4, hacc, hr, hcl, _, hn, hd⟩ := hg
  unfold wd4 at hacc hr
  simp only [Nat.reduceAdd] at hacc hr
  rw [hw 0 0 rfl (by decide), hw 4 4 rfl (by decide), hw 8 8 rfl (by decide), hw 12 12 rfl (by decide),
    hw 16 16 rfl (by decide)] at hacc
  rw [hw 20 20 rfl (by decide), hw 24 24 rfl (by decide), hw 28 28 rfl (by decide),
    hw 32 32 rfl (by decide)] at hr hcl
  rw [hw 16 16 rfl (by decide)] at h4
  rw [hw 224 224 rfl (by decide)] at hn
  exact ⟨h4, hacc, hr, hcl, hn, fun j hj => by rw [← getElem!_memBytes (n := 236) (k := 208 + j) (by omega)]; exact hd j hj⟩

theorem memBytes_take (mem : ByteArray) (a : UInt32) (k n : Nat) (h : k ≤ n) :
    (memBytes mem a n).take k = memBytes mem a k := by
  rw [show n = k + (n - k) by omega, memBytes_add, List.take_left' (memBytes_length _ _ _)]

theorem memBytes_drop (mem : ByteArray) (a : UInt32) (k n : Nat) (h : k ≤ n) :
    (memBytes mem a n).drop k = memBytes mem (a + k.toUInt32) (n - k) := by
  conv => lhs; rw [show n = k + (n - k) by omega]
  rw [memBytes_add, List.drop_left' (memBytes_length _ _ _)]

theorem getElem!_app_r (l1 l2 : List UInt8) (i : Nat) : (l1 ++ l2)[l1.length + i]! = l2[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getElem!_app_l (l1 l2 : List UInt8) (i : Nat) (h : i < l1.length) : (l1 ++ l2)[i]! = l1[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

/-- The whole blocks of `B` (bytes at `ip`) folded into the accumulator of a message of whole blocks. -/
theorem acc_rest (R : Nat) (msg1 B : List UInt8) {G : PMem} {ip : UInt32} (h16 : msg1.length % 16 = 0)
    (hB : memBytes G.get ip B.length = B) (hfit : ip.toNat + B.length ≤ G.get.size)
    (htop : G.get.size ≤ ramTop) :
    accB G R 1 ip (B.length / 16) (accOf R msg1) = accOf R (msg1 ++ B) := by
  rw [accB_bytes R htop _ _ _ (by omega), accOf_append0 R msg1 B h16,
    ← memBytes_take _ _ (16 * (B.length / 16)) B.length (by omega), hB]

/-- The tail bytes of `B` (at `ip`) are the buffered tail of `msg1 ++ B`. -/
theorem bytes_rest (msg1 B : List UInt8) {G : PMem} {ip : UInt32} (h16 : msg1.length % 16 = 0)
    (hB : memBytes G.get ip B.length = B) :
    ∀ j, j < B.length % 16 →
      memByte G.get (ip + (16 * (B.length / 16) + j).toUInt32) = (msg1 ++ B)[fullLen (msg1 ++ B) + j]! := by
  intro j hj
  have e1 : fullLen (msg1 ++ B) = msg1.length + 16 * (B.length / 16) := by
    unfold fullLen; simp only [List.length_append]; omega
  rw [← getElem!_memBytes (mem := G.get) (a := ip) (n := B.length) (k := 16 * (B.length / 16) + j) (by omega), hB,
    e1, Nat.add_assoc, getElem!_app_r]

set_option maxHeartbeats 2000000 in
/-- `num = 0`, `len < 16`: only the tail copy. -/
theorem upd_pA0 (key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])
    (hn0 : msg.length % 16 = 0) (hl : chunk.length < 16) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      GoodB key (msg ++ chunk) (memBytes N'.get C 236) := by
  have hf := hM.fC; have hfit := hf.fit; have htop := hf.top
  obtain ⟨g4, gacc, gr, gcl, gnum, gdat⟩ := goodB_cw hg hfit htop
  obtain ⟨N1, lU1, g1, R1, M1, LU1, -⟩ := upd_a0 0 (by decide) G G U C lU (lC0 G C) P hM a0 c0 d0 ebx0 ebp0
    esi0 edi0 g0 ret inp len (cw G C 224) hlU ⟨lk_here, trivial⟩ (by rw [gnum, hn0])
  obtain ⟨N2, lU2, v1, g3, R2, M2, LU2, -, ev1⟩ := upd_b0 (icAdd 0 11) (by decide) G N1 U C _ _ P M1 a0 c0 len
    (cw G C 224) ebp0 inp g1 a0 esi0 edi0 ebx0 ebp0 ret LU1 trivial (by omega)
  have hv1 : v1.toNat = chunk.length := by rw [ev1, land15_sem]; omega
  obtain ⟨N3, lU3, lC3, eax, ecx, edx, gf, ic, R3, M3, LU3, LC3, LT3, Hb⟩ := upd_tail (icAdd (icAdd 0 11) 5)
    (by decide) M2 a0 c0 len v1 len inp g3 a0 esi0 edi0 ebx0 ebp0 ret inp len (cw G C 0) (cw G C 4) (cw G C 8)
    (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) (cw G C 192) (cw G C 196) (cw G C 200)
    (cw G C 204) LU2 (lk_lC0_W G C) (by omega) (fun h => by rw [hv1] at h ⊢; exact E h)
  refine ⟨N3, lU3, lC3, eax, ecx, edx, gf, ic, R1.trans (R2.trans R3), M3, LU3, ?_⟩
  refine goodB_mk key msg (msg ++ chunk) hg M3 _ _ _ _ _ v1 LC3 LT3 g4 ?_ ?_ ?_
  · rw [gacc, accOf_append_short _ _ _ (by omega)]
  · rw [hv1]; simp only [List.length_append]; omega
  · intro j hj
    simp only [List.length_append] at hj
    rw [Hb j (by omega)]
    have := bytes_rest msg chunk hn0 hch j (by omega)
    rw [show chunk.length / 16 = 0 by omega, Nat.mul_zero, Nat.zero_add] at this
    exact this

set_option maxHeartbeats 2000000 in
/-- `num = 0`, `len ≥ 16`: the whole blocks, then the tail. -/
theorem upd_pA1 (key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])
    (hn0 : msg.length % 16 = 0) (hl : 16 ≤ chunk.length) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      GoodB key (msg ++ chunk) (memBytes N'.get C 236) := by
  have hf := hM.fC; have hfit := hf.fit; have htop := hf.top
  obtain ⟨g4, gacc, gr, gcl, gnum, gdat⟩ := goodB_cw hg hfit htop
  obtain ⟨N1, lU1, g1, R1, M1, LU1, -⟩ := upd_a0 0 (by decide) G G U C lU (lC0 G C) P hM a0 c0 d0 ebx0 ebp0
    esi0 edi0 g0 ret inp len (cw G C 224) hlU ⟨lk_here, trivial⟩ (by rw [gnum, hn0])
  obtain ⟨N2, lU2, v1, g3, R2, M2, LU2, -, ev1⟩ := upd_b1 (icAdd 0 11) (by decide) G N1 U C _ _ P M1 a0 c0 len
    (cw G C 224) ebp0 inp g1 a0 esi0 edi0 ebx0 ebp0 ret LU1 trivial (by omega)
  subst ev1
  have E' := E (by omega)
  rw [← hlen] at E'
  obtain ⟨N3, lU3, lC3, eax, ecx, edx, gf, o0, o1, o2, o3, o4, ic, R3, M3, LU3, LC3, LT3, ho4, hv, Hb⟩ :=
    upd_full (icAdd (icAdd 0 11) 5) (by decide) M2 a0 c0 len len inp g3 a0 esi0 edi0 ebx0 ebp0 ret inp len
      (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32)
      (cw G C 192) (cw G C 196) (cw G C 200) (cw G C 204) LU2 (lk_lC0_W G C) (by omega) E'
      gcl.1 gcl.2.1 gcl.2.2.1 gcl.2.2.2.1 gcl.2.2.2.2.1 gcl.2.2.2.2.2.1 gcl.2.2.2.2.2.2 g4
  refine ⟨N3, lU3, lC3, eax, ecx, edx, gf, ic, R1.trans (R2.trans R3), M3, LU3, ?_⟩
  refine goodB_mk key msg (msg ++ chunk) hg M3 _ _ _ _ _ _ LC3 LT3 ho4 ?_ ?_ ?_
  · rw [hv, gacc, ← gr, hlen]
    exact acc_rest _ msg chunk hn0 hch (by rw [← hlen]; exact E'.fit) E'.top
  · rw [land15_sem]; simp only [List.length_append]; omega
  · intro j hj
    simp only [List.length_append] at hj
    rw [Hb j (by omega), hlen]
    exact bytes_rest msg chunk hn0 hch j (by omega)


theorem accB_zero (G : PMem) (R padv : Nat) (a : UInt32) (x : Nat) : accB G R padv a 0 x = x := rfl

theorem accMa_nil (R x : Nat) : accMa R x [] = x := rfl

theorem list_ext! {l1 l2 : List UInt8} (h : l1.length = l2.length) (h2 : ∀ j, j < l1.length → l1[j]! = l2[j]!) :
    l1 = l2 := by
  apply List.ext_getElem h
  intro n h1 h2'
  have := h2 n h1
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2',
    Option.getD_some] at this
  exact this

theorem getElem!_drop' (l : List UInt8) (k j : Nat) : (l.drop k)[j]! = l[k + j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

theorem getElem!_take' (l : List UInt8) (k j : Nat) (h : j < k) : (l.take k)[j]! = l[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem lk_skip4 {l e : List (Nat × UInt32)} (h : LK l e) (he : ∀ k v, (k, v) ∈ e → k + 4 ≤ 208)
    (j1 j2 j3 j4 : Nat) (w1 w2 w3 w4 : UInt32) (h1 : 208 ≤ j1) (h2 : 208 ≤ j2) (h3 : 208 ≤ j3)
    (h4 : 208 ≤ j4) : LK ((j1, w1) :: (j2, w2) :: (j3, w3) :: (j4, w4) :: l) e := by
  have hk : ∀ (j : Nat), 208 ≤ j → ∀ k v, (k, v) ∈ e → k ≠ j := fun j hj k v hm => by have := he k v hm; omega
  exact (((h.skip (hk j4 h4)).skip (hk j3 h3)).skip (hk j2 h2)).skip (hk j1 h1)

theorem addr208 {C : UInt32} (hC : C.toNat + 236 ≤ ramTop) (j : Nat) (hj : j < 28) :
    (C + (208 + j).toUInt32).toNat = C.toNat + 208 + j := by
  rw [UInt32.toNat_add]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at hC; omega

set_option maxHeartbeats 2000000 in
/-- `num ≠ 0`, the chunk does not fill the block: copy it after the buffered bytes. -/
theorem upd_pB0 (key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])
    (hn : msg.length % 16 ≠ 0) (hl : msg.length % 16 + chunk.length < 16) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      GoodB key (msg ++ chunk) (memBytes N'.get C 236) := by
  have hf := hM.fC; have hfit := hf.fit; have htop := hf.top
  have hCt : C.toNat + 236 ≤ ramTop := Nat.le_trans hfit htop
  obtain ⟨g4, gacc, gr, gcl, gnum, gdat⟩ := goodB_cw hg hfit htop
  obtain ⟨N1, lU1, g1, R1, M1, LU1, -⟩ := upd_a1 0 (by decide) G G U C lU (lC0 G C) P hM a0 c0 d0 ebx0 ebp0
    esi0 edi0 g0 ret inp len (cw G C 224) hlU ⟨lk_here, trivial⟩ (by rw [gnum]; exact hn)
  obtain ⟨N2, lU2, v5, v3, g5, R2, M2, LU2, -, ev5, -⟩ := upd_g0 (icAdd 0 11) (by decide) G N1 U C _ _ P M1 a0 c0
    len (cw G C 224) ebp0 inp g1 a0 esi0 edi0 ebx0 ebp0 ret LU1 trivial ⟨by omega, by omega⟩
  have e5 : v5.toNat = C.toNat + msg.length % 16 + 208 := by
    rw [ev5, uadd_sem, uadd_sem, gnum]; simp only [UInt32.reduceToNat]; unfold ramTop at hCt; omega
  obtain ⟨N3, eax, ecx, edx, gf, R3, M3, Hpre, Hb⟩ := upd_mc (icAdd (icAdd 0 11) 13) (by decide) M2 v5 C len
    (cw G C 224) C len v3 g5 1048861 v5 inp len a0 esi0 edi0 ebx0 ebp0 ret C inp len LU2 (WG G C) (lk_lC0_W G C)
    (fun k v hm => W13_keys hm) (by omega) (by omega) (by omega) (fun h => by rw [hlen] at h ⊢; exact E h)
  have M3' := (((M3.addC 208 208 rfl rfl (by decide)).addC 212 212 rfl rfl (by decide)).addC 216 216 rfl rfl
    (by decide)).addC 220 220 rfl rfl (by decide)
  have hmk : mcK len.toNat ≤ 103 := by unfold mcK; split <;> omega
  obtain ⟨N4, lU4, g6, v2, R4, M4, LU4, -, ev2⟩ := upd_h (icAdd (icAdd (icAdd 0 11) 13) (mcK len.toNat))
    (by
      have := icAdd_le (icAdd (icAdd 0 11) 13) (mcK len.toNat)
      have : (icAdd (icAdd 0 11) 13).toNat = 24 := by decide
      omega)
    G N3 U C _ _ P M3' eax ecx edx (cw G C 224) v3 len gf a0 esi0 edi0 ebx0 ebp0 ret inp (lk_W9 _ _ _ _ _ _ _ _ _)
    trivial
  refine ⟨N4, lU4, _, eax, ecx, edx, g6, _, R1.trans (R2.trans (R3.trans R4)), M4, ⟨LU4.2.2.2.2.2.1,
    LU4.2.2.2.2.2.2.1, LU4.2.2.2.2.2.2.2.1, LU4.2.2.2.2.2.2.2.2.1, trivial⟩, ?_⟩
  refine goodB_mk key msg (msg ++ chunk) hg M4 _ _ _ _ _ v2
    (lk_skip5 (lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _) (fun k v hm => W13_keys hm) _ _ _ _ _ _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide)) ⟨lk_here, trivial⟩ g4 ?_ ?_ ?_
  · rw [gacc, accOf_append_short _ _ _ (by omega)]
  · rw [ev2, add_lo, gnum, hlen]; simp only [List.length_append, UInt32.reduceToNat]; omega
  · intro j hj
    simp only [List.length_append] at hj
    have hfl : fullLen (msg ++ chunk) = fullLen msg := by unfold fullLen; simp only [List.length_append]; omega
    rw [data_lk M4 (M3.size.trans M4.size.symm) ⟨lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl,
      lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip lk_here rfl,
      trivial⟩ j (by omega), hfl]
    have ea := addr208 hCt j (by omega)
    by_cases hjn : j < msg.length % 16
    · rw [Hpre _ (by rw [ea]; omega) (by rw [ea]; omega)]
      rw [data_lk M2 M2.size.symm ⟨lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl,
        lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl,
        trivial⟩ j (by omega), gdat j hjn, getElem!_app_l _ _ _ (by unfold fullLen; omega)]
    · have e : C + (208 + j).toUInt32 = v5 + (j - msg.length % 16).toUInt32 := by
        apply UInt32.toNat_inj.1
        rw [ea, UInt32.toNat_add, e5]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at hCt; omega
      rw [e, Hb _ (by omega), ← getElem!_memBytes (n := chunk.length) (k := j - msg.length % 16) (by omega), hch,
        show fullLen msg + j = msg.length + (j - msg.length % 16) by unfold fullLen; omega, getElem!_app_r]

set_option maxHeartbeats 4000000 in
/-- `num ≠ 0`, the chunk fills the block: copy `rem` bytes and fold in the block. -/
theorem upd_pB1a (key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])
    (hn : msg.length % 16 ≠ 0) (hl : 16 ≤ msg.length % 16 + chunk.length) :
    ∃ (N' : PMem) (eax ecx edx gf o0 o1 o2 o3 o4 v1 v3 : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, C, UInt32.add U 228, v3, v1, inp, 0x10017f, efl gf, ic⟩) ∧
      ic.toNat < 2 ^ 20 ∧
      MemOK G N' U 272 (W9 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret C inp len) C 236 236
        (W13 o0 o1 o2 o3 o4 (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) (cw G C 192) (cw G C 196)
          (cw G C 200) (cw G C 204)) P ∧
      v1.toNat = 16 - msg.length % 16 ∧ v3.toNat = chunk.length - (16 - msg.length % 16) ∧ o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = accOf (r key) (msg ++ chunk.take (16 - msg.length % 16)) := by
  have hf := hM.fC; have hfit := hf.fit; have htop := hf.top
  have hCt : C.toNat + 236 ≤ ramTop := Nat.le_trans hfit htop
  obtain ⟨g4, gacc, gr, gcl, gnum, gdat⟩ := goodB_cw hg hfit htop
  have E' := E (by omega)
  obtain ⟨N1, lU1, g1, R1, M1, LU1, -⟩ := upd_a1 0 (by decide) G G U C lU (lC0 G C) P hM a0 c0 d0 ebx0 ebp0
    esi0 edi0 g0 ret inp len (cw G C 224) hlU ⟨lk_here, trivial⟩ (by rw [gnum]; exact hn)
  obtain ⟨N2, lU2, v5, v3, v1, g5, R2, M2, LU2, -, ev5, ev3, ev1⟩ := upd_g1 (icAdd 0 11) (by decide) G N1 U C _ _
    P M1 a0 c0 len (cw G C 224) ebp0 inp g1 a0 esi0 edi0 ebx0 ebp0 ret LU1 trivial ⟨by omega, by omega⟩
  have e5 : v5.toNat = C.toNat + msg.length % 16 + 208 := by
    rw [ev5, uadd_sem, uadd_sem, gnum]; simp only [UInt32.reduceToNat]; unfold ramTop at hCt; omega
  have h16 : (16 : UInt32).toNat = 16 := rfl
  have hle : cw G C 224 ≤ 16 := by rw [UInt32.le_iff_toNat_le, gnum, h16]; omega
  have e1 : v1.toNat = 16 - msg.length % 16 := by
    rw [ev1, subF_fst, UInt32.toNat_sub_of_le _ _ hle, h16, gnum]
  have e3 : v3.toNat = chunk.length - (16 - msg.length % 16) := by
    rw [ev3, subF_fst, ← ev1, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e1]; omega), e1, hlen]
  obtain ⟨N3, eax, ecx, edx, gf, R3, M3, Hpre, Hb⟩ := upd_mc (icAdd (icAdd 0 11) 14) (by decide) M2 v5 C
    (UInt32.add C 208) C v1 inp v3 g5 1048942 v5 inp v1 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret C inp len LU2
    (WG G C) (lk_lC0_W G C) (fun k v hm => W13_keys hm) (by omega) (by omega) (by omega)
    (fun _ => E'.mono (by omega))
  have M3' := (((M3.addC 208 208 rfl rfl (by decide)).addC 212 212 rfl rfl (by decide)).addC 216 216 rfl rfl
    (by decide)).addC 220 220 rfl rfl (by decide)
  have hmk : mcK v1.toNat ≤ 103 := by unfold mcK; split <;> omega
  have ic3 : (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)).toNat ≤ 128 := by
    have := icAdd_le (icAdd (icAdd 0 11) 14) (mcK v1.toNat)
    have : (icAdd (icAdd 0 11) 14).toNat = 25 := by decide
    omega
  obtain ⟨N4, lU4, g7, R4, M4, LU4, -⟩ := upd_i (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)) (by omega) G N3 U C
    _ _ P M3' eax ecx edx v3 v1 inp gf (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret len (lk_W9 _ _ _ _ _ _ _ _ _)
    trivial
  have hdUC := hM.dUC
  have e120 := hM.fU.add_toNat (j := 120) (by decide)
  have e208 := hf.add_toNat (j := 208) (by decide)
  have Eb : ExtR N4 (BQ U C) (UInt32.add C 208) (16 * 1) :=
    ⟨by rw [e208, M4.size]; simp only [UInt32.reduceToNat]; omega, by rw [M4.size]; exact htop,
      fun x h1 h2 => by
        rw [e208] at h1 h2; simp only [UInt32.reduceToNat] at h1 h2
        exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩⟩
  have hW := lk_skip4 (lk_W13 (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24)
    (cw G C 28) (cw G C 32) (cw G C 192) (cw G C 196) (cw G C 200) (cw G C 204)) (fun k v hm => W13_keys hm)
    220 216 212 208 (rdRaw N3.get (UInt32.add C 220) 4) (rdRaw N3.get (UInt32.add C 216) 4)
    (rdRaw N3.get (UInt32.add C 212) 4) (rdRaw N3.get (UInt32.add C 208) 4)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨N5, eax5, ecx5, edx5, gf5, o0, o1, o2, o3, o4, R5, M5, ho4, hv⟩ :=
    upd_blk (icAdd (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)) 6) M4 1 (Nat.le_refl _)
      (by have := icAdd_le (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)) 6; omega)
      eax (UInt32.add C 208) C v3 v1 inp g7 1048959 16 1 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret C inp len
      (cw G C 0) (cw G C 4) (cw G C 8) (cw G C 12) (cw G C 16) (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) LU4
      ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1, hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.1,
        hW.2.2.2.2.2.2.2.2.1, trivial⟩
      [(192, cw G C 192), (196, cw G C 196), (200, cw G C 200), (204, cw G C 204)]
      ⟨hW.2.2.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2.2.2.2.2.1,
        trivial⟩
      (fun k v hm => by have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega)
      (by decide) Eb gcl.1 gcl.2.1 gcl.2.2.1 gcl.2.2.2.1 gcl.2.2.2.2.1 gcl.2.2.2.2.2.1 gcl.2.2.2.2.2.2 g4 (by decide)
  -- the block in the context's data: the buffered bytes, then the first `rem` bytes of the chunk
  have hblk : memBytes N4.get (UInt32.add C 208) 16 =
      msg.drop (fullLen msg) ++ chunk.take (16 - msg.length % 16) := by
    have hTl := drop_fullLen_length msg
    apply list_ext! (by rw [memBytes_length]; simp only [List.length_append, List.length_take, hTl]; omega)
    intro j hj
    rw [memBytes_length] at hj
    have ea := addr208 hCt j (by omega)
    rw [getElem!_memBytes hj, show UInt32.add C 208 + j.toUInt32 = C + (208 + j).toUInt32 by
      apply UInt32.toNat_inj.1; rw [ea, UInt32.toNat_add, e208]
      simp only [Nat.toUInt32, UInt32.toNat_ofNat', UInt32.reduceToNat]; unfold ramTop at hCt; omega]
    rw [data_lk M4 (M3.size.trans M4.size.symm) ⟨lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl,
      lk_skip (lk_skip lk_here rfl) rfl, lk_skip lk_here rfl, lk_here, trivial⟩ j hj]
    by_cases hjn : j < msg.length % 16
    · rw [Hpre _ (by rw [ea]; omega) (by rw [ea]; omega)]
      rw [data_lk M2 M2.size.symm ⟨lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl,
        lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl,
        trivial⟩ j (by omega), gdat j hjn, getElem!_app_l _ _ _ (by rw [hTl]; exact hjn), getElem!_drop']
    · obtain ⟨i, rfl⟩ : ∃ i, j = msg.length % 16 + i := ⟨j - msg.length % 16, by omega⟩
      have e : C + (208 + (msg.length % 16 + i)).toUInt32 = v5 + i.toUInt32 := by
        apply UInt32.toNat_inj.1
        rw [ea, UInt32.toNat_add, e5]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at hCt; omega
      rw [e, Hb i (by omega), ← getElem!_memBytes (n := chunk.length) (k := i) (by omega), hch, ← hTl,
        getElem!_app_r, getElem!_take' _ _ _ (by omega)]
  have hb1 := bval_memBytes (G := N4) (a := UInt32.add C 208) (by rw [e208, M4.size]; simp only [UInt32.reduceToNat]; omega)
    (by rw [M4.size]; exact htop)
  rw [hblk] at hb1
  have hBl : (msg.drop (fullLen msg) ++ chunk.take (16 - msg.length % 16)).length = 16 := by
    simp only [List.length_append, drop_fullLen_length, List.length_take]; omega
  refine ⟨N5, eax5, ecx5, edx5, gf5, o0, o1, o2, o3, o4, v1, v3, _, R1.trans (R2.trans (R3.trans (R4.trans R5))),
    ?_, M5, e1, e3, ho4, ?_⟩
  · have := icAdd_le (icAdd (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)) 6) (61 + 184 * 1)
    have := icAdd_le (icAdd (icAdd (icAdd 0 11) 14) (mcK v1.toNat)) 6
    omega
  · have hm : mval (msg.drop (fullLen msg) ++ chunk.take (16 - msg.length % 16)) =
        leNat (msg.drop (fullLen msg) ++ chunk.take (16 - msg.length % 16)) + 2 ^ 128 := by
      unfold mval; rw [hBl]
    have h1 : (1 : UInt32).toNat = 1 := rfl
    rw [hv, accB_succ, accB_zero, accOf_fill _ _ _ hn (by omega), accMa_cons, accMa_nil, hb1, gacc, ← gr, hm, h1,
      Nat.mul_one, Nat.add_assoc]


set_option maxHeartbeats 4000000 in
/-- `num ≠ 0`, the chunk fills the block: after the block, the rest as for `num = 0`. -/
theorem upd_pB1 (key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])
    (hn : msg.length % 16 ≠ 0) (hl : 16 ≤ msg.length % 16 + chunk.length) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      GoodB key (msg ++ chunk) (memBytes N'.get C 236) := by
  have hf := hM.fC; have hfit := hf.fit; have htop := hf.top
  obtain ⟨g4, gacc, gr, gcl, gnum, gdat⟩ := goodB_cw hg hfit htop
  have E' := E (by omega)
  obtain ⟨N5, eax5, ecx5, edx5, gf5, o0, o1, o2, o3, o4, v1, v3, ic5, R5, hic5, M5, e1, e3, ho4, hacc1⟩ :=
    upd_pB1a key msg chunk G U C inp len lU P hM hg hlen hch E ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 hlU hn hl
  have hm1 : (msg ++ chunk.take (16 - msg.length % 16)).length % 16 = 0 := by
    simp only [List.length_append, List.length_take]; omega
  have happ : msg ++ chunk.take (16 - msg.length % 16) ++ chunk.drop (16 - msg.length % 16) = msg ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  have hBl : (chunk.drop (16 - msg.length % 16)).length = v3.toNat := by rw [List.length_drop, e3]
  have ev1 : (16 - msg.length % 16).toUInt32 = v1 := toUInt32_of_toNat e1
  have hB : memBytes G.get (inp + v1) (chunk.drop (16 - msg.length % 16)).length =
      chunk.drop (16 - msg.length % 16) := by
    rw [List.length_drop, ← hch, memBytes_drop G.get inp (16 - msg.length % 16) chunk.length (by omega), ev1,
      memBytes_length]
  by_cases hl2 : 16 ≤ v3.toNat
  · obtain ⟨N6, lU6, v4, v2, g8, R6, M6, LU6, -, ev2, ev4⟩ := upd_j0 ic5 (by omega) G N5 U C _ _ P M5 eax5 ecx5
      edx5 v3 v1 inp gf5 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret len (lk_W9 _ _ _ _ _ _ _ _ _) trivial hl2
    subst ev4
    have e2 : v2 = inp + v1 := by rw [ev2, addF_fst]
    have E2 : ExtR G P v2 v3.toNat := by rw [e2]; exact E'.drop v1 _ (by rw [e1, e3]; omega)
    obtain ⟨N7, lU7, lC7, eax7, ecx7, edx7, gf7, p0, p1, p2, p3, p4, ic, R7, M7, LU7, LC7, LT7, hp4, hv7, Hb7⟩ :=
      upd_full (icAdd ic5 7) (by have := icAdd_le ic5 7; omega) M6 eax5 ecx5 edx5 v3 v2 g8 (UInt32.add C 208)
        esi0 edi0 ebx0 ebp0 ret inp len o0 o1 o2 o3 o4 (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32)
        (cw G C 192) (cw G C 196) (cw G C 200) (cw G C 204) LU6 (lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _) hl2 E2
        gcl.1 gcl.2.1 gcl.2.2.1 gcl.2.2.2.1 gcl.2.2.2.2.1 gcl.2.2.2.2.2.1 gcl.2.2.2.2.2.2 ho4
    refine ⟨N7, lU7, lC7, eax7, ecx7, edx7, gf7, ic, R5.trans (R6.trans R7), M7, LU7, ?_⟩
    refine goodB_mk key msg (msg ++ chunk) hg M7 _ _ _ _ _ _ LC7 LT7 hp4 ?_ ?_ ?_
    · rw [hv7, hacc1, ← gr, ← happ, ← hBl, e2]
      exact acc_rest _ _ _ hm1 hB (by rw [hBl, ← e2]; exact E2.fit) htop
    · rw [land15_sem, e3]; simp only [List.length_append]; omega
    · intro j hj
      simp only [List.length_append] at hj
      rw [Hb7 j (by rw [e3]; omega), e2, ← hBl, ← happ]
      exact bytes_rest _ _ hm1 hB j (by rw [hBl, e3]; omega)
  · obtain ⟨N6, lU6, v4, v2, g8, R6, M6, LU6, -, ev2, ev4⟩ := upd_j1 ic5 (by omega) G N5 U C _ _ P M5 eax5 ecx5
      edx5 v3 v1 inp gf5 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret len (lk_W9 _ _ _ _ _ _ _ _ _) trivial
      (by omega)
    have e2 : v2 = inp + v1 := by rw [ev2, addF_fst]
    have hv4 : v4.toNat = v3.toNat := by rw [ev4, land15_sem]; omega
    obtain ⟨N7, lU7, lC7, eax7, ecx7, edx7, gf7, ic, R7, M7, LU7, LC7, LT7, Hb7⟩ := upd_tail (icAdd ic5 8)
      (by have := icAdd_le ic5 8; omega) M6 eax5 ecx5 edx5 v4 v3 v2 g8 (UInt32.add C 208) esi0 edi0 ebx0 ebp0 ret
      inp len o0 o1 o2 o3 o4 (cw G C 20) (cw G C 24) (cw G C 28) (cw G C 32) (cw G C 192) (cw G C 196) (cw G C 200)
      (cw G C 204) LU6 (lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _) (by omega)
      (fun _ => by rw [hv4, e2]; exact E'.drop v1 _ (by rw [e1, e3]; omega))
    refine ⟨N7, lU7, lC7, eax7, ecx7, edx7, gf7, ic, R5.trans (R6.trans R7), M7, LU7, ?_⟩
    refine goodB_mk key msg (msg ++ chunk) hg M7 _ _ _ _ _ v4 LC7 LT7 ho4 ?_ ?_ ?_
    · rw [hacc1, ← happ, accOf_append_short (r key) (msg ++ chunk.take (16 - msg.length % 16))
        (chunk.drop (16 - msg.length % 16)) (by rw [hm1, hBl]; omega)]
    · rw [hv4, e3]; simp only [List.length_append]; omega
    · intro j hj
      simp only [List.length_append] at hj
      rw [Hb7 j (by rw [hv4, e3]; omega), e2, ← happ]
      have := bytes_rest _ _ hm1 hB j (by rw [hBl, e3]; omega)
      rw [show (chunk.drop (16 - msg.length % 16)).length / 16 = 0 by rw [hBl]; omega, Nat.mul_zero,
        Nat.zero_add] at this
      exact this

set_option maxHeartbeats 4000000 in
/-- `Poly1305_Update` extends the message of a good context by its chunk. -/
theorem update_ok : UpdSpec := by
  intro key msg st chunk c ctx msgp hk hg hpre
  obtain ⟨hc, hbc, hbm, hap, hst, hch⟩ := hpre
  have hf := calls_facts hc
  have bc := buffer_facts hc hbc (by decide)
  have hsp := stk_toNat hf.2.2.1
  simp only [List.length, ctxSize] at hf bc hst
  have hlen32 : chunk.length < 2 ^ 32 := by have := hbm.2.1; unfold maxObject at this; omega
  have hlen : chunk.length.toUInt32.toNat = chunk.length := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  let P : Nat → Prop := fun x => OutF (stk c) 272 x ∧ OutF ctx 236 x
  have hl : Frame (pmem hc) (stk c) 272
      [(256, Image.sym_halt), (260, ctx), (264, msgp), (268, chunk.length.toUInt32)] :=
    frame_cons (frame_cons (frame_cons (frame_cons (Frame.nil (pmem hc) (stk c) 272) 268 _ 268 rfl rfl (by decide)
      (word_arg hc 2 (by simp) 268 rfl)) 264 msgp 264 rfl rfl (by decide) (word_arg hc 1 (by simp) 264 rfl))
      260 ctx 260 rfl rfl (by decide) (word_arg hc 0 (by simp) 260 rfl)) 256 _ 256 rfl rfl (by decide) (word_ret hc)
  have hM0 := entry_memok hc ctx 236 236 bc.1 bc.2.1 (by simp only [List.length]; omega) _ hl P
    (fun x h => h.1) (fun x h => h.2)
  have hM : MemOK (pmem hc) (pmem hc) (stk c) 272
      [(256, Image.sym_halt), (260, ctx), (264, msgp), (268, chunk.length.toUInt32)] ctx 236 236
      (lC0 (pmem hc) ctx) P :=
    ⟨hM0.fU, hM0.fC, hM0.dUC, hM0.wU, frame_lC0 _ _, hM0.pres, hM0.pU, hM0.pC⟩
  have hg' : GoodB key msg (memBytes (pmem hc).get ctx 236) := by rw [pmem_get, hst]; exact hg
  have hch' : memBytes (pmem hc).get msgp chunk.length = chunk := by rw [pmem_get]; exact hch
  have E : chunk.length ≠ 0 → ExtR (pmem hc) P msgp chunk.length := fun h => by
    have bm := buffer_facts hc hbm h
    have ha := apart_nat hap (by decide) h
    simp only [List.length, ctxSize] at bm ha
    exact ⟨by rw [pmem_get]; exact bm.1, by rw [pmem_get]; exact hf.1,
      fun x h1 h2 => ⟨by unfold OutF; rw [hsp]; omega, by unfold OutF; omega⟩⟩
  have hlU : LK [(256, Image.sym_halt), (260, ctx), (264, msgp), (268, chunk.length.toUInt32)]
      [(256, Image.sym_halt), (260, ctx), (264, msgp), (268, chunk.length.toUInt32)] :=
    ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl,
      trivial⟩
  obtain ⟨N', lU', lC', eax, ecx, edx, gf, ic, R, M, LU, hgood⟩ :
      ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
        Run img (St.m ⟨(pmem hc).get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, UInt32.add (stk c) 256,
            c.regs.ebp, c.regs.esi, c.regs.edi, 0x1000e0, efl c.regs.flags, icAdd 0 0⟩)
          (St.m ⟨N'.get, eax, ecx, edx, c.regs.ebx, UInt32.add (stk c) 260, c.regs.ebp, c.regs.esi, c.regs.edi,
            Image.sym_halt, efl gf, ic⟩) ∧
        MemOK (pmem hc) N' (stk c) 272 lU' ctx 236 236 lC' P ∧
        LK lU' [(256, Image.sym_halt), (260, ctx), (264, msgp), (268, chunk.length.toUInt32)] ∧
        GoodB key (msg ++ chunk) (memBytes N'.get ctx 236) := by
    by_cases h0 : msg.length % 16 = 0
    · by_cases h1 : chunk.length < 16
      · exact upd_pA0 key msg chunk (pmem hc) (stk c) ctx msgp chunk.length.toUInt32 _ P hM hg' hlen hch' E
          Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags
          hlU h0 h1
      · exact upd_pA1 key msg chunk (pmem hc) (stk c) ctx msgp chunk.length.toUInt32 _ P hM hg' hlen hch' E
          Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags
          hlU h0 (by omega)
    · by_cases h1 : msg.length % 16 + chunk.length < 16
      · exact upd_pB0 key msg chunk (pmem hc) (stk c) ctx msgp chunk.length.toUInt32 _ P hM hg' hlen hch' E
          Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags
          hlU h0 h1
      · exact upd_pB1 key msg chunk (pmem hc) (stk c) ctx msgp chunk.length.toUInt32 _ P hM hg' hlen hch' E
          Image.sym_halt c.regs.eax c.regs.ecx c.regs.edx c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags
          hlU h0 (by omega)
  have hsz : N'.get.size = c.mem.size := M.size
  have R' : Run img (c.enter Image.sym_Poly1305_Update) (St.m ⟨N'.get, eax, ecx, edx, c.regs.ebx,
      UInt32.add (stk c) 260, c.regs.ebp, c.regs.esi, c.regs.edi, Image.sym_halt, efl gf, ic⟩) := by
    rw [enter_eq c _ hf.2.2.1]; exact R
  refine returns_of hc _ M ?_ ?_ R' ?_
  · intro a hW ha
    refine ⟨by unfold OutF; rw [hsp]; simp only [List.length] at ha; omega, ?_⟩
    unfold OutF
    simp only [InRange, ctxSize, UInt32.le_iff_toNat_le] at hW
    omega
  · refine arg_bytes hc hsz (fun i hi => ?_)
    simp only [List.length] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact (M.rdU (k := 256) LU.1 _ rfl).trans (word_ret hc).symm
    · exact (M.rdU (k := 260) LU.2.1 _ rfl).trans (word_arg hc 0 (by simp) _ rfl).symm
    · exact (M.rdU (k := 264) LU.2.2.1 _ rfl).trans (word_arg hc 1 (by simp) _ rfl).symm
    · exact (M.rdU (k := 268) LU.2.2.2.1 _ rfl).trans (word_arg hc 2 (by simp) _ rfl).symm
  · exact hgood

end Solutions.OpensslPoly1305
