import Solutions.OpensslPoly1305.UpdCall
/-!
# The ends of `Poly1305_Update`

`upd_tail`: from `0x100144` (the `rem = len % 16` tail bytes at `p`) to the return: copies the tail
into the context's data (`memcpy`) when it is not empty and stores it as `num`.
`upd_full`: from `0x100130` (`len ≥ 16` bytes at `p`): `poly1305_blocks` over the whole blocks
(pad bit 1), then `upd_tail` for the rest.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

variable {G N : PMem} {U C : UInt32} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

/-- The saved registers and the arguments on the `Update` frame. -/
def W9 (a b c d e f g h i : UInt32) : List (Nat × UInt32) :=
  [(236, a), (240, b), (244, c), (248, d), (252, e), (256, f), (260, g), (264, h), (268, i)]

/-- The context words that matter between the calls: `h`, `r`, `s`. -/
def W13 (h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 : UInt32) : List (Nat × UInt32) :=
  [(0, h0), (4, h1), (8, h2), (12, h3), (16, h4), (20, r0), (24, r1), (28, r2), (32, r3), (192, s0), (196, s1),
    (200, s2), (204, s3)]

theorem lk_W9 (a b c d e f g h i : UInt32) : LK (W9 a b c d e f g h i) (W9 a b c d e f g h i) :=
  ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, trivial⟩

theorem lk_W13 (h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 : UInt32) :
    LK (W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3) (W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3) :=
  ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl, trivial⟩

theorem W13_keys {h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 : UInt32} {k : Nat} {v : UInt32}
    (hm : (k, v) ∈ W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3) : k + 4 ≤ 208 := by
  have := List.mem_map_of_mem (f := Prod.fst) hm; simp [W13] at this; omega

theorem LK.skip {l e : List (Nat × UInt32)} {j : Nat} {w : UInt32} (h : LK l e)
    (hk : ∀ k v, (k, v) ∈ e → k ≠ j) : LK ((j, w) :: l) e := by
  induction e with
  | nil => trivial
  | cons a e ih =>
    obtain ⟨k, v⟩ := a
    exact ⟨lk_skip h.1 (by simp [hk k v List.mem_cons_self]),
      ih h.2 (fun k' v' hm => hk k' v' (List.mem_cons_of_mem _ hm))⟩

theorem ExtR.drop {p : UInt32} {L : Nat} (E : ExtR G P p L) (k : UInt32) (L' : Nat) (h : k.toNat + L' ≤ L) :
    ExtR G P (UInt32.add p k) L' := by
  have e := E.add_toNat (j := k) (by omega)
  refine ⟨?_, E.top, ?_⟩
  · rw [e]; have := E.fit; omega
  · intro x h1 h2; rw [e] at h1 h2; exact E.cov x (by omega) (by omega)

theorem MemOK.bq (h : MemOK G N U 272 lU C 236 236 lC P) (x : Nat) (hx : P x) : BQ U C x := by
  have e120 := h.fU.add_toNat (j := 120) (by decide)
  have h1 := h.pU x hx; have h2 := h.pC x hx
  unfold OutF at h1 h2
  exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩

theorem land15_sem (a : UInt32) : (UInt32.land a 15).toNat = a.toNat % 16 := by
  show (a &&& 15).toNat = _
  rw [UInt32.toNat_and, show (15 : UInt32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem nat_and_m16 (x : Nat) (hx : x < 2 ^ 32) : x &&& 4294967280 = 16 * (x / 16) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ex : x = 2 ^ 4 * (x / 16) + x % 16 := by omega
  rw [Nat.testBit_and, show 16 * (x / 16) = 2 ^ 4 * (x / 16) + 0 by omega, Nat.testBit_two_pow_mul_add _ (by decide),
    show (4294967280 : Nat) = 2 ^ 4 * (2 ^ 28 - 1) + 0 by decide, Nat.testBit_two_pow_mul_add _ (by decide)]
  rw [ex, Nat.testBit_two_pow_mul_add _ (by omega)]
  have hq : x / 16 < 2 ^ 28 := by omega
  rw [show (2 ^ 4 * (x / 16) + x % 16) / 16 = x / 16 by omega]
  split
  · simp [Nat.zero_testBit]
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases h : i - 4 < 28
    · simp [h]
    · have := Nat.testBit_lt_two_pow (i := i - 4) (Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h, this]

theorem landm16_sem (a : UInt32) : (UInt32.land a 4294967280).toNat = 16 * (a.toNat / 16) := by
  show (a &&& 4294967280).toNat = _
  rw [UInt32.toNat_and, show (4294967280 : UInt32).toNat = 4294967280 from rfl, nat_and_m16 _ a.toNat_lt]

/-- Equal data words, equal data bytes. -/
theorem data_bytes {N1 N2 : PMem} (hf : FB N1.get.size C 236) (hs : N2.get.size = N1.get.size)
    (hw : ∀ i, i < 4 → rdRaw N2.get (UInt32.add C (208 + 4 * i).toUInt32) 4 =
      rdRaw N1.get (UInt32.add C (208 + 4 * i).toUInt32) 4)
    (j : Nat) (hj : j < 16) : memByte N2.get (C + (208 + j).toUInt32) = memByte N1.get (C + (208 + j).toUInt32) := by
  have htop := hf.top; have hfit := hf.fit
  have ea := Frame.add_toNat hf (k := 208 + 4 * (j / 4)) (by omega)
  have e : C + (208 + j).toUInt32 = UInt32.add C (208 + 4 * (j / 4)).toUInt32 + (j % 4).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, UInt32.toNat_add, ea]
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    unfold ramTop at htop; omega
  rw [e]
  exact bytes_of_word (by rw [ea, hs]; omega) (by rw [ea]; omega) (by rw [hs]; exact htop)
    (hw (j / 4) (by omega)) (j % 4) (by omega)

set_option maxHeartbeats 2000000 in
/-- From `0x100144` (`t = len % 16` bytes left at `p`) to the return. -/
theorem upd_tail (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 62) (hM : MemOK G N U 272 lU C 236 236 lC P)
    (a1 c1 d1 t p1 p g0 a0 esi0 edi0 ebx0 ebp0 ret inp len h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 : UInt32)
    (hlU : LK lU (W9 a0 esi0 edi0 ebx0 ebp0 ret C inp len))
    (hlC : LK lC (W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3))
    (ht : t.toNat < 16) (E : t.toNat ≠ 0 → ExtR G P p t.toNat) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨N.get, a1, c1, d1, t, UInt32.add U 236, p1, C, p, 0x100144, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      LK lC' (W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3) ∧ LK lC' [(224, t)] ∧
      ∀ j, j < t.toNat → memByte N'.get (C + (208 + j).toUInt32) = memByte G.get (p + j.toUInt32) := by
  by_cases hz : t.toNat = 0
  · obtain ⟨N1, lU1, g3, R1, M1, LU1, -⟩ := upd_e0 ic0 (by omega) G N U C lU lC P hM a1 c1 d1 t p1 p g0 a0 esi0
      edi0 ebx0 ebp0 ret inp len hlU trivial hz
    have et : t = 0 := UInt32.toNat_inj.1 hz
    subst et
    exact ⟨N1, lU1, _, a1, c1, d1, g3, _, R1, M1, ⟨LU1.2.2.2.2.2.1, LU1.2.2.2.2.2.2.1, LU1.2.2.2.2.2.2.2.1,
      LU1.2.2.2.2.2.2.2.2.1, trivial⟩, hlC.skip (fun k v hm => by have := W13_keys hm; omega), ⟨lk_here, trivial⟩,
      fun j hj => absurd hj (by omega)⟩
  · obtain ⟨N1, lU1, g1, R1, M1, LU1, -⟩ := upd_e1 ic0 (by omega) G N U C lU lC P hM a1 c1 d1 t p1 p g0 a0 esi0
      edi0 ebx0 ebp0 ret inp len hlU trivial hz
    have e208 := hM.fC.add_toNat (j := 208) (by decide)
    obtain ⟨N2, eax, ecx, edx, gf, R2, M2, -, Hb⟩ := upd_mc (icAdd ic0 7)
      (by rw [icAdd_toNat _ _ (by omega)]; omega) M1
      (UInt32.add C 208) c1 d1 t C p p1 g1 1048918 (UInt32.add C 208) p t a0 esi0 edi0 ebx0 ebp0 ret C inp len LU1
      _ hlC (fun k v hm => W13_keys hm)
      (by rw [e208]; simp only [UInt32.reduceToNat]; omega) (by rw [e208]; simp only [UInt32.reduceToNat]; omega)
      (by omega) E
    have M3 := (((M2.addC 208 208 rfl rfl (by decide)).addC 212 212 rfl rfl (by decide)).addC 216 216 rfl rfl
      (by decide)).addC 220 220 rfl rfl (by decide)
    have hmk : mcK t.toNat ≤ 103 := by unfold mcK; split <;> omega
    obtain ⟨N4, lU4, g2, R4, M4, LU4, -⟩ := upd_f (icAdd (icAdd ic0 7) (mcK t.toNat))
      (by rw [icAdd_toNat _ _ (by rw [icAdd_toNat _ _ (by omega)]; omega), icAdd_toNat _ _ (by omega)]; omega)
      G N2 U C _ _ P M3 eax ecx edx t p1 p gf a0 esi0 edi0 ebx0 ebp0 ret inp len (lk_W9 _ _ _ _ _ _ _ _ _) trivial
    refine ⟨N4, lU4, _, eax, ecx, edx, g2, _, R1.trans (R2.trans R4), M4, ⟨LU4.2.2.2.2.2.1, LU4.2.2.2.2.2.2.1,
      LU4.2.2.2.2.2.2.2.1, LU4.2.2.2.2.2.2.2.2.1, trivial⟩, ?_, ⟨lk_here, trivial⟩, fun j hj => ?_⟩
    · have hk : ∀ (j : Nat), 208 ≤ j → ∀ k v, (k, v) ∈ W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 → k ≠ j :=
        fun j hj k v hm => by have := W13_keys hm; omega
      exact ((((((lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _).skip (hk 208 (by omega))).skip (hk 212 (by omega))).skip
        (hk 216 (by omega))).skip (hk 220 (by omega))).skip (hk 224 (by omega)))
    · have hw : ∀ i, i < 4 → rdRaw N4.get (UInt32.add C (208 + 4 * i).toUInt32) 4 =
          rdRaw N2.get (UInt32.add C (208 + 4 * i).toUInt32) 4 := by
        intro i hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
        · show rdRaw N4.get (UInt32.add C 208) 4 = rdRaw N2.get (UInt32.add C 208) 4
          exact M4.rdC (k := 208) (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) 208 rfl
        · show rdRaw N4.get (UInt32.add C 212) 4 = rdRaw N2.get (UInt32.add C 212) 4
          exact M4.rdC (k := 212) (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) 212 rfl
        · show rdRaw N4.get (UInt32.add C 216) 4 = rdRaw N2.get (UInt32.add C 216) 4
          exact M4.rdC (k := 216) (lk_skip (lk_skip lk_here rfl) rfl) 216 rfl
        · show rdRaw N4.get (UInt32.add C 220) 4 = rdRaw N2.get (UInt32.add C 220) 4
          exact M4.rdC (k := 220) (lk_skip lk_here rfl) 220 rfl
      rw [data_bytes M2.fC (M4.size.trans M2.size.symm) hw j (by omega)]
      have htop := hM.fC.top; have hfit := hM.fC.fit
      rw [show C + (208 + j).toUInt32 = UInt32.add C 208 + j.toUInt32 by
        apply UInt32.toNat_inj.1
        rw [UInt32.toNat_add, UInt32.toNat_add, e208]
        simp only [Nat.toUInt32, UInt32.toNat_ofNat', UInt32.reduceToNat]
        unfold ramTop at htop; omega]
      exact Hb j hj

set_option maxHeartbeats 2000000 in
/-- From `0x100130` (`l ≥ 16` bytes at `ip`): the whole blocks (pad bit 1), then the tail. -/
theorem upd_full (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 61) (hM : MemOK G N U 272 lU C 236 236 lC P)
    (a1 c1 d1 l ip g0 a0 esi0 edi0 ebx0 ebp0 ret inp len h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3 : UInt32)
    (hlU : LK lU (W9 a0 esi0 edi0 ebx0 ebp0 ret C inp len))
    (hlC : LK lC (W13 h0 h1 h2 h3 h4 r0 r1 r2 r3 s0 s1 s2 s3))
    (hl : 16 ≤ l.toNat) (E : ExtR G P ip l.toNat)
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0) (hh4 : h4.toNat ≤ 4) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf o0 o1 o2 o3 o4 : UInt32) (ic : UInt64),
      Run img (St.m ⟨N.get, a1, c1, d1, UInt32.land l 15, UInt32.add U 236, l, C, ip, 0x100130, efl g0,
          icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      LK lC' (W13 o0 o1 o2 o3 o4 r0 r1 r2 r3 s0 s1 s2 s3) ∧ LK lC' [(224, UInt32.land l 15)] ∧ o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = accB G (val4 r0 r1 r2 r3) 1 ip (l.toNat / 16) (val5 h0 h1 h2 h3 h4 % p) ∧
      ∀ j, j < l.toNat % 16 →
        memByte N'.get (C + (208 + j).toUInt32) = memByte G.get (ip + (16 * (l.toNat / 16) + j).toUInt32) := by
  obtain ⟨N1, lU1, v1, g2, R1, M1, LU1, -, ev1⟩ := upd_c ic0 (by omega) G N U C lU lC P hM a1 c1 d1
    (UInt32.land l 15) l ip g0 a0 esi0 edi0 ebx0 ebp0 ret inp len hlU trivial
  have hlt := l.toNat_lt
  have hn : 1 ≤ l.toNat / 16 := by omega
  have hv1 : v1.toNat = 16 * (l.toNat / 16) := by rw [ev1, landm16_sem]
  have E1 : ExtR N1 (BQ U C) ip (16 * (l.toNat / 16)) :=
    ⟨by rw [M1.size]; have := E.fit; omega, by rw [M1.size]; exact E.top,
      fun x h1 h2 => M1.bq x (E.cov x h1 (by omega))⟩
  obtain ⟨N2, eax, ecx, edx, gf, o0, o1, o2, o3, o4, R2, M2, ho4, hv⟩ := upd_blk (icAdd ic0 6) M1 (l.toNat / 16) hn
    (by rw [icAdd_toNat _ _ (by omega)]; omega) a1 ip (UInt32.land l 15) v1 C ip g2 1048895 v1 1
    a0 esi0 edi0 ebx0 ebp0 ret C inp len h0 h1 h2 h3 h4 r0 r1 r2 r3 LU1
    ⟨hlC.1, hlC.2.1, hlC.2.2.1, hlC.2.2.2.1, hlC.2.2.2.2.1, hlC.2.2.2.2.2.1, hlC.2.2.2.2.2.2.1, hlC.2.2.2.2.2.2.2.1,
      hlC.2.2.2.2.2.2.2.2.1, trivial⟩
    [(192, s0), (196, s1), (200, s2), (204, s3)]
    ⟨hlC.2.2.2.2.2.2.2.2.2.1, hlC.2.2.2.2.2.2.2.2.2.2.1, hlC.2.2.2.2.2.2.2.2.2.2.2.1,
      hlC.2.2.2.2.2.2.2.2.2.2.2.2.1, trivial⟩
    (fun k v hm => by have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega)
    hv1 E1 hr0 hr1 hr2 hr3 hq1 hq2 hq3 hh4 (by decide)
  have hv' : val5 o0 o1 o2 o3 o4 % p = accB G (val4 r0 r1 r2 r3) 1 ip (l.toNat / 16) (val5 h0 h1 h2 h3 h4 % p) := by
    rw [hv]; exact accB_congr M1.pres _ 1 _ _ _ (E.mono (by omega))
  have ic1 : (icAdd (icAdd ic0 6) (61 + 184 * (l.toNat / 16))).toNat = ic0.toNat + 6 + (61 + 184 * (l.toNat / 16)) := by
    rw [icAdd_toNat _ _ (by rw [icAdd_toNat _ _ (by omega)]; omega), icAdd_toNat _ _ (by omega)]
  obtain ⟨N3, lU3, v2, g3, R3, M3, LU3, -, ev2⟩ := upd_d (icAdd (icAdd ic0 6) (61 + 184 * (l.toNat / 16)))
    (by rw [ic1]; omega) G N2 U C _ _ P M2 eax ecx edx (UInt32.land l 15) v1 ip gf a0 esi0 edi0 ebx0 ebp0 ret inp len
    (lk_W9 _ _ _ _ _ _ _ _ _) trivial
  have e2 : v2 = UInt32.add ip v1 := by rw [ev2, addF_fst']
  have E3 : (UInt32.land l 15).toNat ≠ 0 → ExtR G P v2 (UInt32.land l 15).toNat := fun _ => by
    rw [e2, land15_sem]; exact E.drop v1 _ (by rw [hv1]; omega)
  obtain ⟨N4, lU4, lC4, eax', ecx', edx', gf', ic, R4, M4, LU4, LC4, LT4, Hb⟩ :=
    upd_tail (icAdd (icAdd (icAdd ic0 6) (61 + 184 * (l.toNat / 16))) 2)
      (by rw [icAdd_toNat _ _ (by rw [ic1]; omega), ic1]; omega) M3 eax ecx edx (UInt32.land l 15) v1 v2 g3 a0 esi0
      edi0 ebx0 ebp0 ret inp len o0 o1 o2 o3 o4 r0 r1 r2 r3 s0 s1 s2 s3 LU3 (lk_W13 _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by rw [land15_sem]; omega) E3
  refine ⟨N4, lU4, lC4, eax', ecx', edx', gf', o0, o1, o2, o3, o4, ic, R1.trans (R2.trans (R3.trans R4)), M4, LU4,
    LC4, LT4, ho4, hv', fun j hj => ?_⟩
  rw [Hb j (by rw [land15_sem]; exact hj), e2]
  congr 1
  apply UInt32.toNat_inj.1
  have := E.fit; have := E.top; unfold ramTop at *
  rw [UInt32.toNat_add, uadd_sem, hv1, UInt32.toNat_add]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega

end Solutions.OpensslPoly1305
