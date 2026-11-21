import Solutions.OpensslPoly1305.FinImg
import Solutions.OpensslPoly1305.UpdOk
/-!
# The arithmetic of `Poly1305_Final`

`emit_spec`: the words `poly1305_emit` stores are `(h mod p + s) mod 2^128` when `h4 ≤ 4` (then
`h < 2p`, and `h + 5 ≥ 2^130` exactly when `h ≥ p`). `tag_bytes`: four words in memory are the
16 little-endian bytes of their value. `leNat_pad`: the padded last block.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305 Solutions.Exec.Mul
  Solutions.Exec.Fast

set_option autoImplicit false

theorem land_ones (x : UInt32) : UInt32.land x 4294967295 = x := by
  apply UInt32.toNat_inj.1
  show (x &&& 4294967295).toNat = _
  rw [UInt32.toNat_and, show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

theorem ones_land (x : UInt32) : UInt32.land 4294967295 x = x := by
  apply UInt32.toNat_inj.1
  show (4294967295 &&& x).toNat = _
  rw [UInt32.toNat_and, Nat.and_comm, show (4294967295 : UInt32).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

theorem land_zero' (x : UInt32) : UInt32.land x 0 = 0 := by
  apply UInt32.toNat_inj.1
  show (x &&& 0).toNat = _
  rw [UInt32.toNat_and]; simp

theorem zero_land' (x : UInt32) : UInt32.land 0 x = 0 := by
  apply UInt32.toNat_inj.1
  show (0 &&& x).toNat = _
  rw [UInt32.toNat_and]; simp

theorem lor_zero' (x : UInt32) : UInt32.lor x 0 = x := by
  apply UInt32.toNat_inj.1
  show (x ||| 0).toNat = _
  rw [UInt32.toNat_or]; simp

theorem zero_lor' (x : UInt32) : UInt32.lor 0 x = x := by
  apply UInt32.toNat_inj.1
  show (0 ||| x).toNat = _
  rw [UInt32.toNat_or]; simp

theorem em_sum5 (h0 h1 h2 h3 h4 g0 g1 g2 g3 g4 c0 c1 c2 c3 c4 : Nat) (a0 : g0 + 2 ^ 32 * c0 = h0 + 5 + 0)
    (a1 : g1 + 2 ^ 32 * c1 = h1 + 0 + c0) (a2 : g2 + 2 ^ 32 * c2 = h2 + 0 + c1) (a3 : g3 + 2 ^ 32 * c3 = h3 + 0 + c2)
    (a4 : g4 + 2 ^ 32 * c4 = h4 + 0 + c3) :
    g0 + 2 ^ 32 * g1 + 2 ^ 64 * g2 + 2 ^ 96 * g3 + 2 ^ 128 * g4 + 2 ^ 160 * c4 =
      h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4 + 5 := by omega

theorem em_sum4 (t0 t1 t2 t3 s0 s1 s2 s3 o0 o1 o2 o3 d0 d1 d2 d3 : Nat) (b0 : o0 + 2 ^ 32 * d0 = t0 + s0 + 0)
    (b1 : o1 + 2 ^ 32 * d1 = t1 + s1 + d0) (b2 : o2 + 2 ^ 32 * d2 = t2 + s2 + d1) (b3 : o3 + 2 ^ 32 * d3 = t3 + s3 + d2) :
    o0 + 2 ^ 32 * o1 + 2 ^ 64 * o2 + 2 ^ 96 * o3 + 2 ^ 128 * d3 =
      (t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3) + (s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3) := by omega

theorem em_lt128 (o0 o1 o2 o3 : Nat) (l0 : o0 < 2 ^ 32) (l1 : o1 < 2 ^ 32) (l2 : o2 < 2 ^ 32) (l3 : o3 < 2 ^ 32) :
    o0 + 2 ^ 32 * o1 + 2 ^ 64 * o2 + 2 ^ 96 * o3 < 2 ^ 128 := by omega

theorem em_mod128 (O T S d : Nat) (hO : O < 2 ^ 128) (e : O + 2 ^ 128 * d = T + S) : O = (T + S) % 2 ^ 128 := by
  rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hO]

/-- `h < p`: the low words of `h`. -/
theorem em_sel_h (L h4 S : Nat) (hlt : L + 2 ^ 128 * h4 < p) :
    ((L + 2 ^ 128 * h4) % p + S) % 2 ^ 128 = (L + S) % 2 ^ 128 := by
  rw [Nat.mod_eq_of_lt hlt, Nat.add_right_comm, Nat.add_mul_mod_self_left]

/-- `p ≤ h < 2p`: the low words of `h + 5`. -/
theorem em_sel_g (H Lg g4 S : Nat) (hg : Lg + 2 ^ 128 * g4 = H + 5) (h4 : 4 ≤ g4) (h2 : H < 2 * p) :
    (H % p + S) % 2 ^ 128 = (Lg + S) % 2 ^ 128 := by
  have hp : p = 2 ^ 130 - 5 := rfl
  rw [hp] at h2 ⊢
  have hge : 2 ^ 130 - 5 ≤ H := by omega
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (a := H - (2 ^ 130 - 5)) (b := 2 ^ 130 - 5) (by omega)]
  have e : Lg + S + 2 ^ 128 * (g4 - 4) = H - (2 ^ 130 - 5) + S := by omega
  rw [← e, Nat.add_mul_mod_self_left]

set_option maxHeartbeats 1000000 in
theorem emit_core (h0 h1 h2 h3 h4 s0 s1 s2 s3 : UInt32) (hh4 : h4.toNat ≤ 4)
    (g0 g1 g2 g3 g4 o0 o1 o2 o3 : UInt32 × UInt32) (b t0 t1 t2 t3 : UInt32)
    (eg0 : g0 = addF 4 h0 5 0) (eg1 : g1 = addF 4 h1 0 (cfBit g0.2)) (eg2 : g2 = addF 4 h2 0 (cfBit g1.2))
    (eg3 : g3 = addF 4 h3 0 (cfBit g2.2)) (eg4 : g4 = addF 4 h4 0 (cfBit g3.2))
    (eb : b = UInt32.shiftRight g4.1 2)
    (et0 : t0 = (logicF 4 (UInt32.lor (UInt32.land h0 (UInt32.add b 4294967295)) (UInt32.land g0.1 (UInt32.sub 0 b)))).1)
    (et1 : t1 = (logicF 4 (UInt32.lor (UInt32.land h1 (UInt32.add b 4294967295)) (UInt32.land g1.1 (UInt32.sub 0 b)))).1)
    (et2 : t2 = (logicF 4 (UInt32.lor (UInt32.land h2 (UInt32.add b 4294967295)) (UInt32.land g2.1 (UInt32.sub 0 b)))).1)
    (et3 : t3 = (logicF 4 (UInt32.lor (UInt32.land (UInt32.add b 4294967295) h3) (UInt32.land (UInt32.sub 0 b) g3.1))).1)
    (eo0 : o0 = addF 4 t0 s0 0) (eo1 : o1 = addF 4 t1 s1 (cfBit o0.2)) (eo2 : o2 = addF 4 t2 s2 (cfBit o1.2))
    (eo3 : o3 = addF 4 t3 s3 (cfBit o2.2)) :
    val4 o0.1 o1.1 o2.1 o3.1 = (val5 h0 h1 h2 h3 h4 % p + val4 s0 s1 s2 s3) % 2 ^ 128 := by
  have a0 := add_sem h0 5 0 (by decide); rw [← eg0] at a0
  have a1 := add_sem h1 0 _ (cfBit_le g0.2); rw [← eg1] at a1
  have a2 := add_sem h2 0 _ (cfBit_le g1.2); rw [← eg2] at a2
  have a3 := add_sem h3 0 _ (cfBit_le g2.2); rw [← eg3] at a3
  have a4 := add_sem h4 0 _ (cfBit_le g3.2); rw [← eg4] at a4
  have b0 := add_sem t0 s0 0 (by decide); rw [← eo0] at b0
  have b1 := add_sem t1 s1 _ (cfBit_le o0.2); rw [← eo1] at b1
  have b2 := add_sem t2 s2 _ (cfBit_le o1.2); rw [← eo2] at b2
  have b3 := add_sem t3 s3 _ (cfBit_le o2.2); rw [← eo3] at b3
  simp only [UInt32.reduceToNat] at a0 a1 a2 a3 a4 b0 b1 b2 b3
  have hG := em_sum5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a0 a1 a2 a3 a4
  have hO := em_sum4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b0 b1 b2 b3
  have hc3 := cfBit_le g3.2
  have hc4 : (cfBit g4.2).toNat = 0 := by omega
  rw [hc4, Nat.mul_zero, Nat.add_zero] at hG
  have hlt := em_lt128 _ _ _ _ o0.1.toNat_lt o1.1.toNat_lt o2.1.toNat_lt o3.1.toNat_lt
  have hO' := em_mod128 _ _ _ _ hlt hO
  unfold val4 val5
  rw [hO']
  have hb : b.toNat = g4.1.toNat / 4 := by rw [eb, shr_sem _ _ (by decide)]; rfl
  have hg4 : g4.1.toNat ≤ 5 := by omega
  have hl := em_lt128 _ _ _ _ g0.1.toNat_lt g1.1.toNat_lt g2.1.toNat_lt g3.1.toNat_lt
  have hlh := em_lt128 _ _ _ _ h0.toNat_lt h1.toNat_lt h2.toNat_lt h3.toNat_lt
  by_cases hbz : b.toNat = 0
  · have eb0 : b = 0 := UInt32.toNat_inj.1 hbz
    have hn : UInt32.add b 4294967295 = 4294967295 := by rw [eb0]; rfl
    have hm : UInt32.sub 0 b = 0 := by rw [eb0]; rfl
    rw [hn, hm, land_ones, land_zero', lor_zero', logicF_fst] at et0 et1 et2
    rw [hn, hm, ones_land, zero_land', lor_zero', logicF_fst] at et3
    subst t0 t1 t2 t3
    have hp : p = 2 ^ 130 - 5 := rfl
    exact (em_sel_h _ _ _ (by rw [hp]; omega)).symm
  · have hb1 : b.toNat = 1 := by omega
    have eb1 : b = 1 := UInt32.toNat_inj.1 hb1
    have hn : UInt32.add b 4294967295 = 0 := by rw [eb1]; rfl
    have hm : UInt32.sub 0 b = 4294967295 := by rw [eb1]; rfl
    rw [hn, hm, land_zero', land_ones, zero_lor', logicF_fst] at et0 et1 et2
    rw [hn, hm, zero_land', ones_land, zero_lor', logicF_fst] at et3
    subst t0 t1 t2 t3
    have hp : p = 2 ^ 130 - 5 := rfl
    exact (em_sel_g _ _ _ _ hG (by omega) (by rw [hp]; omega)).symm


theorem emit_spec (h0 h1 h2 h3 h4 s0 s1 s2 s3 : UInt32) (hh4 : h4.toNat ≤ 4) :
    val4 (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).1 (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.1
      (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.2.1 (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.2.2 =
      (val5 h0 h1 h2 h3 h4 % p + val4 s0 s1 s2 s3) % 2 ^ 128 := by
  obtain ⟨g0, eg0⟩ : ∃ g, g = addF 4 h0 5 0 := ⟨_, rfl⟩
  obtain ⟨g1, eg1⟩ : ∃ g, g = addF 4 h1 0 (cfBit g0.2) := ⟨_, rfl⟩
  obtain ⟨g2, eg2⟩ : ∃ g, g = addF 4 h2 0 (cfBit g1.2) := ⟨_, rfl⟩
  obtain ⟨g3, eg3⟩ : ∃ g, g = addF 4 h3 0 (cfBit g2.2) := ⟨_, rfl⟩
  obtain ⟨g4, eg4⟩ : ∃ g, g = addF 4 h4 0 (cfBit g3.2) := ⟨_, rfl⟩
  obtain ⟨b, eb⟩ : ∃ x, x = UInt32.shiftRight g4.1 2 := ⟨_, rfl⟩
  obtain ⟨t0, et0⟩ : ∃ x, x = (logicF 4 (UInt32.lor (UInt32.land h0 (UInt32.add b 4294967295))
      (UInt32.land g0.1 (UInt32.sub 0 b)))).1 := ⟨_, rfl⟩
  obtain ⟨t1, et1⟩ : ∃ x, x = (logicF 4 (UInt32.lor (UInt32.land h1 (UInt32.add b 4294967295))
      (UInt32.land g1.1 (UInt32.sub 0 b)))).1 := ⟨_, rfl⟩
  obtain ⟨t2, et2⟩ : ∃ x, x = (logicF 4 (UInt32.lor (UInt32.land h2 (UInt32.add b 4294967295))
      (UInt32.land g2.1 (UInt32.sub 0 b)))).1 := ⟨_, rfl⟩
  obtain ⟨t3, et3⟩ : ∃ x, x = (logicF 4 (UInt32.lor (UInt32.land (UInt32.add b 4294967295) h3)
      (UInt32.land (UInt32.sub 0 b) g3.1))).1 := ⟨_, rfl⟩
  obtain ⟨o0, eo0⟩ : ∃ g, g = addF 4 t0 s0 0 := ⟨_, rfl⟩
  obtain ⟨o1, eo1⟩ : ∃ g, g = addF 4 t1 s1 (cfBit o0.2) := ⟨_, rfl⟩
  obtain ⟨o2, eo2⟩ : ∃ g, g = addF 4 t2 s2 (cfBit o1.2) := ⟨_, rfl⟩
  obtain ⟨o3, eo3⟩ : ∃ g, g = addF 4 t3 s3 (cfBit o2.2) := ⟨_, rfl⟩
  have := emit_core h0 h1 h2 h3 h4 s0 s1 s2 s3 hh4 g0 g1 g2 g3 g4 o0 o1 o2 o3 b t0 t1 t2 t3 eg0 eg1 eg2 eg3 eg4 eb
    et0 et1 et2 et3 eo0 eo1 eo2 eo3
  subst o3 o2 o1 o0 t3 t2 t1 t0 b g4 g3 g2 g1 g0
  exact this

/-! ## Bytes of the tag and of the padded block -/

theorem leNat_append (A B : List UInt8) : leNat (A ++ B) = leNat A + 256 ^ A.length * leNat B := by
  induction A with
  | nil => simp [leNat]
  | cons a A ih =>
    show a.toNat + 256 * leNat (A ++ B) = a.toNat + 256 * leNat A + 256 ^ (A.length + 1) * leNat B
    rw [ih, Nat.pow_succ]
    generalize leNat A = x; generalize leNat B = y; generalize 256 ^ A.length = q
    rw [Nat.mul_add, Nat.mul_left_comm, ← Nat.mul_assoc, Nat.add_assoc]

theorem leNat_zeros (k : Nat) : leNat (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (0 : UInt8).toNat + 256 * leNat (List.replicate k 0) = 0
    rw [ih]; rfl

/-- The last block padded with `1` and zeros has the value of the short block with its pad bit. -/
theorem leNat_pad (T : List UInt8) (k : Nat) : leNat (T ++ 1 :: List.replicate k 0) = mval T := by
  rw [leNat_append]
  have h1 : leNat (1 :: List.replicate k 0) = 1 := by
    show (1 : UInt8).toNat + 256 * leNat (List.replicate k 0) = 1
    rw [leNat_zeros]; rfl
  rw [h1]; unfold mval; rw [Nat.mul_one, Nat.pow_mul]

set_option maxHeartbeats 4000000 in
/-- Four words in memory are the 16 little-endian bytes of their value. -/
theorem tag_bytes (mem : ByteArray) (a w0 w1 w2 w3 : UInt32) (hfit : a.toNat + 16 ≤ mem.size)
    (htop : mem.size ≤ ramTop) (e0 : rdRaw mem a 4 = w0) (e1 : rdRaw mem (UInt32.add a 4) 4 = w1)
    (e2 : rdRaw mem (UInt32.add a 8) 4 = w2) (e3 : rdRaw mem (UInt32.add a 12) 4 = w3) :
    memBytes mem a 16 = Ssl.Spec.Poly1305.leBytes 16 (val4 w0 w1 w2 w3) := by
  have ea : ∀ (j : UInt32) (k : Nat), j.toNat = k → k ≤ 16 → (UInt32.add a j).toNat = a.toNat + k := by
    intro j k hj hk; rw [uadd_sem, hj]; unfold ramTop at htop; omega
  have r0 := rd4_toNat (mem := mem) (a := a) (by omega)
  have r1 := rd4_toNat (mem := mem) (a := UInt32.add a 4) (by rw [ea 4 4 rfl (by decide)]; omega)
  have r2 := rd4_toNat (mem := mem) (a := UInt32.add a 8) (by rw [ea 8 8 rfl (by decide)]; omega)
  have r3 := rd4_toNat (mem := mem) (a := UInt32.add a 12) (by rw [ea 12 12 rfl (by decide)]; omega)
  rw [ea 4 4 rfl (by decide)] at r1; rw [ea 8 8 rfl (by decide)] at r2; rw [ea 12 12 rfl (by decide)] at r3
  change (rdRaw mem a 4).toNat = _ at r0; change (rdRaw mem (UInt32.add a 4) 4).toNat = _ at r1
  change (rdRaw mem (UInt32.add a 8) 4).toNat = _ at r2; change (rdRaw mem (UInt32.add a 12) 4).toNat = _ at r3
  rw [e0] at r0; rw [e1] at r1; rw [e2] at r2; rw [e3] at r3
  unfold memBytes Ssl.Spec.Poly1305.leBytes
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hai : (a + i.toUInt32).toNat = a.toNat + i := by
    rw [UInt32.toNat_add]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
  rw [memByte_def (by rw [hai]; omega), hai]
  apply UInt8.toNat_inj.1
  rw [Nat.shiftRight_eq_div_pow]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', val4]
  have q : ∀ k, k < 16 → (mem.get! (a.toNat + k)).toNat < 256 := fun k _ => (mem.get! (a.toNat + k)).toNat_lt
  have q0 := q 0 (by decide); have q1 := q 1 (by decide); have q2 := q 2 (by decide); have q3 := q 3 (by decide)
  have q4 := q 4 (by decide); have q5 := q 5 (by decide); have q6 := q 6 (by decide); have q7 := q 7 (by decide)
  have q8 := q 8 (by decide); have q9 := q 9 (by decide); have q10 := q 10 (by decide)
  have q11 := q 11 (by decide); have q12 := q 12 (by decide); have q13 := q 13 (by decide)
  have q14 := q 14 (by decide); have q15 := q 15 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at r0 r1 r2 r3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 ⊢
  rw [r0, r1, r2, r3]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
    i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.add_zero, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] <;> omega

end Solutions.OpensslPoly1305
