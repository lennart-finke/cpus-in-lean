/-!
# `fe_frombytes`: small steps of the limb arithmetic

Each lemma takes the `toNat` facts of a few words of the run (`I/FbMath` shapes) and gives a closed form
(prover R). They are combined in `I/FbLimbs` by term application only, so every `omega` here runs in a
context of a handful of facts.
-/
namespace Solutions.OpensslX25519.I

/-- A 3-byte load `x + 2^16 y` shifted left by `k ≤ 8`: no overflow. -/
theorem fz_ld {y x v w : Nat} (k : Nat) (hk : k ≤ 8) (hy : y < 2 ^ 8) (hx : x < 2 ^ 16)
    (h1 : v = y * 2 ^ 16 % 2 ^ 32) (h2 : w = v + x) :
    w * 2 ^ k % 2 ^ 32 = (y * 65536 + x) * 2 ^ k ∧ (y * 65536 + x) * 2 ^ k < 2 ^ (24 + k) := by
  have hw : w = y * 65536 + x := by omega
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hb : (y * 65536 + x) * 2 ^ k < 2 ^ (24 + k) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right (by omega) hp
  have h32 : 2 ^ (24 + k) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hw, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb h32)]
  exact ⟨rfl, hb⟩

/-- The top load of `fe_frombytes`: `((x + 2^16 y) · 4) mod 2^25` (bit 255 dropped). -/
theorem fz_h9 {y x v w u z : Nat} (hy : y < 2 ^ 8) (hx : x < 2 ^ 16)
    (h1 : v = y * 2 ^ 16 % 2 ^ 32) (h2 : w = v + x) (h3 : u = w * 2 ^ 2 % 2 ^ 32)
    (h4 : z = u % 2 ^ 25 / 2 ^ 2 * 2 ^ 2) :
    z = (y * 65536 + x) * 2 ^ 2 % 2 ^ 25 ∧ (y * 65536 + x) * 2 ^ 2 % 2 ^ 25 < 2 ^ 25 := by
  have := (fz_ld 2 (by decide) hy hx h1 h2).1
  rw [← this, ← h3]
  omega

/-- The carry of an odd limb: `(H + 2^24) >> 25`. -/
theorem fz_codd {H Hw a q c B : Nat} (hH : H < B) (hB : B + 16777216 ≤ 2 ^ 32) (hw : Hw = H)
    (ha : a = (Hw + 16777216) % 2 ^ 32) (hq : q = a / 2 ^ 25) (hc : c = (H + 16777216) / 2 ^ 25) :
    q = c ∧ c ≤ 128 := by
  omega

/-- As `fz_codd`, for the shape `((0 + H) mod 2^32 + 2^24) mod 2^32`. -/
theorem fz_codd0 {H Hw a q c B : Nat} (hH : H < B) (hB : B + 16777216 ≤ 2 ^ 32) (hw : Hw = H)
    (ha : a = ((0 + Hw) % 2 ^ 32 + 16777216) % 2 ^ 32) (hq : q = a / 2 ^ 25)
    (hc : c = (H + 16777216) / 2 ^ 25) : q = c ∧ c ≤ 128 := by
  omega

/-- The carry of an even limb with the incoming carry added: `(H + C + 2^25) >> 26`. -/
theorem fz_ceven {H Hw C cin a q c B : Nat} (hH : H < B) (hB : B + 128 + 33554432 ≤ 2 ^ 32) (hw : Hw = H)
    (hcin : cin = C) (hC : C ≤ 128) (ha : a = ((cin + Hw) % 2 ^ 32 + 33554432) % 2 ^ 32) (hq : q = a / 2 ^ 26)
    (hc : c = (H + C + 33554432) / 2 ^ 26) : q = c ∧ c ≤ 128 := by
  omega

theorem fz_c9 {H c : Nat} (hH : H < 2 ^ 25) (hc : c = (H + 16777216) / 2 ^ 25) : c ≤ 1 := by
  omega

theorem fz_shld {X v : Nat} (hX : X < 2 ^ 34) (h : v = X * 64 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32) : v = X / 2 ^ 26 := by
  omega

theorem fz_shld7 {X v : Nat} (hX : X < 2 ^ 34) (h : v = X * 128 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32) :
    v = X / 2 ^ 25 := by
  omega

/-! ### Primitive steps -/

theorem fz_msub {r A M : Nat} (hM : M ≤ A + 2 ^ 33) (hr : r = (A + 2 ^ 33 - M) % 2 ^ 32) :
    (r : Int) = ((A : Int) - M) % 2 ^ 32 := by omega

theorem fz_madd {v c r : Nat} {E : Int} (hr : (r : Int) = E % 2 ^ 32) (hv : v = (c + r) % 2 ^ 32) :
    (v : Int) = ((c : Int) + E) % 2 ^ 32 := by omega

theorem fz_d25 {H c : Nat} (hc : c = (H + 16777216) / 2 ^ 25) :
    c * 2 ^ 25 ≤ H + 16777216 ∧ H + 16777216 < c * 2 ^ 25 + 2 ^ 25 := by omega

theorem fz_d26 {H C c : Nat} (hc : c = (H + C + 33554432) / 2 ^ 26) :
    c * 2 ^ 26 ≤ H + C + 33554432 ∧ H + C + 33554432 < c * 2 ^ 26 + 2 ^ 26 := by omega

theorem fz_ltk {H B P : Nat} (K : Nat) (hH : H < B) (hB : B + K ≤ P) : H + K < P := by omega

theorem fz_ltk2 {H B C P : Nat} (K : Nat) (hH : H < B) (hC : C ≤ 128) (hB : B + 128 + K ≤ P) :
    C + H + K < P := by omega

theorem fz_le33 {M H : Nat} (K : Nat) (h : M ≤ H + K) (hK : K ≤ 2 ^ 33) : M ≤ H + 2 ^ 33 := by omega

theorem fz_fin_odd {v H c C cin : Nat}
    (h : (v : Int) = ((cin : Int) + ((H : Int) - ((c * 2 ^ 25 : Nat) : Int))) % 2 ^ 32)
    (hd : c * 2 ^ 25 ≤ H + 16777216 ∧ H + 16777216 < c * 2 ^ 25 + 2 ^ 25) (hcin : cin = C) (hC : C ≤ 128) :
    (v : Int) = ((H : Int) - c * 2 ^ 25 + C) % 2 ^ 32 ∧ -16944988 ≤ (H : Int) - c * 2 ^ 25 + C ∧
      (H : Int) - c * 2 ^ 25 + C ≤ 16944988 := by
  subst hcin
  have e : (cin : Int) + ((H : Int) - ((c * 2 ^ 25 : Nat) : Int)) = (H : Int) - c * 2 ^ 25 + cin := by
    omega
  rw [h, e]
  exact ⟨rfl, by omega, by omega⟩

theorem fz_fin_oddB {v s H c C : Nat} (h : (v : Int) = ((s : Int) - ((c * 2 ^ 25 : Nat) : Int)) % 2 ^ 32)
    (hs : s = C + H) (hd : c * 2 ^ 25 ≤ H + 16777216 ∧ H + 16777216 < c * 2 ^ 25 + 2 ^ 25) (hC : C ≤ 128) :
    (v : Int) = ((H : Int) - c * 2 ^ 25 + C) % 2 ^ 32 ∧ -16944988 ≤ (H : Int) - c * 2 ^ 25 + C ∧
      (H : Int) - c * 2 ^ 25 + C ≤ 16944988 := by
  have e : (s : Int) - ((c * 2 ^ 25 : Nat) : Int) = (H : Int) - c * 2 ^ 25 + C := by
    subst hs; omega
  rw [h, e]
  exact ⟨rfl, by omega, by omega⟩

theorem fz_fin_even {v s H c C : Nat} (h : (v : Int) = ((s : Int) - ((c * 2 ^ 26 : Nat) : Int)) % 2 ^ 32)
    (hs : s = C + H) (hd : c * 2 ^ 26 ≤ H + C + 33554432 ∧ H + C + 33554432 < c * 2 ^ 26 + 2 ^ 26) :
    (v : Int) = ((H : Int) + C - c * 2 ^ 26) % 2 ^ 32 ∧ -33889976 ≤ (H : Int) + C - c * 2 ^ 26 ∧
      (H : Int) + C - c * 2 ^ 26 ≤ 33889976 := by
  have e : (s : Int) - ((c * 2 ^ 26 : Nat) : Int) = (H : Int) + C - c * 2 ^ 26 := by
    subst hs; omega
  rw [h, e]
  exact ⟨rfl, by omega, by omega⟩

/-! ### Carries -/

/-- The 64-bit sum `y1 + 19 c9` as low word `v37` and high word `v38`. -/
theorem fz_t0 {y c9 v34 v35 v36 g37 v37 v38 : Nat} (hy : y < 2 ^ 32) (hc9 : c9 ≤ 1) (h34 : v34 = c9)
    (h35 : v35 = v34 * 19 % 2 ^ 32) (h36 : v36 = v34 * 19 / 2 ^ 32) (hg : g37 = (v35 + y) / 2 ^ 32)
    (h37 : v37 = (v35 + y) % 2 ^ 32) (h38 : v38 = (v36 + 0 + g37) % 2 ^ 32) :
    v35 = c9 * 19 ∧ v37 + 2 ^ 32 * v38 = y + 19 * c9 ∧ v38 ≤ 1 := by
  have e35 : v35 = c9 * 19 := by rw [h35, h34]; clear h36 hg h37 h38; omega
  have e36 : v36 = 0 := by rw [h36, h34]; clear h35 hg h37 h38; omega
  have eg : g37 ≤ 1 := by rw [hg, e35]; clear h34 h35 h36 h37 h38; omega
  have e38 : v38 = g37 := by rw [h38, e36]; clear h34 h35 h36 h37 hg; omega
  refine ⟨e35, ?_, by rw [e38]; exact eg⟩
  rw [h37, e38, hg, e35]
  clear h34 h35 h36 h37 h38 hg e36 e38 e35 eg
  omega

/-- `c0`: the high word of `T0 + 2^25` shifted by `shld 6`. -/
theorem fz_c0 {T v37 v38 g55 v58 v59 v60 c0 : Nat} (hT : v37 + 2 ^ 32 * v38 = T) (h38 : v38 ≤ 1)
    (h37 : v37 < 2 ^ 32) (hg : g55 = (v37 + 33554432) / 2 ^ 32) (h58 : v58 = (v37 + 33554432) % 2 ^ 32)
    (h59 : v59 = (v38 + 0 + g55) % 2 ^ 32) (h60 : v60 = (v59 * 2 ^ 32 + v58) * 64 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32)
    (hc : c0 = (T + 33554432) / 2 ^ 26) : v60 = c0 ∧ c0 ≤ 128 := by
  have hX : v59 * 2 ^ 32 + v58 = T + 33554432 := by clear h60 hc; omega
  have := fz_shld (by omega) h60
  rw [hX, ← hc] at this
  exact ⟨this, by clear h60 this hX; omega⟩

/-- `c5`: `(y + 2^24) >> 25` from the 33-bit sum (`setb`, `shld 7`). -/
theorem fz_c5 {y Hw g v49 v48 v50 c : Nat} (hy : y < 2 ^ 32) (hw : Hw = y) (hg : g = (Hw + 16777216) / 2 ^ 32)
    (h49 : v49 = g) (h48 : v48 = (Hw + 16777216) % 2 ^ 32)
    (h50 : v50 = (v49 * 2 ^ 32 + v48) * 128 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32) (hc : c = (y + 16777216) / 2 ^ 25) :
    v50 = c ∧ c ≤ 128 := by
  have hX : v49 * 2 ^ 32 + v48 = y + 16777216 := by clear h50 hc; omega
  have := fz_shld7 (by omega) h50
  rw [hX, ← hc] at this
  exact ⟨this, by clear h50 this hX; omega⟩

/-- `c6`: `(H + C + 2^25) >> 26` through `shld 6` of a sum that does not carry. -/
theorem fz_c6 {H Hw C cin s g v78 v77 v79 c B : Nat} (hH : H < B) (hB : B + 128 + 33554432 ≤ 2 ^ 32)
    (hw : Hw = H) (hcin : cin = C) (hC : C ≤ 128) (hs : s = (cin + Hw) % 2 ^ 32)
    (hg : g = (s + 33554432) / 2 ^ 32) (h78 : v78 = g) (h77 : v77 = (s + 33554432) % 2 ^ 32)
    (h79 : v79 = (v78 * 2 ^ 32 + v77) * 64 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32) (hc : c = (H + C + 33554432) / 2 ^ 26) :
    v79 = c ∧ c ≤ 128 := by
  have hX : v78 * 2 ^ 32 + v77 = H + C + 33554432 := by clear h79 hc; omega
  have := fz_shld (by omega) h79
  rw [hX, ← hc] at this
  exact ⟨this, by clear h79 this hX; omega⟩

/-! ### Limbs -/

/-- Odd limb, carry added after the subtraction: `H - 2^25 c + C`. -/
theorem fz_oddA {H Hw a m r cin C v c B : Nat} (j : Nat) (hj : j ≤ 32) (hH : H < B)
    (hB : B + 16777216 ≤ 2 ^ j) (hw : Hw = H) (ha : a = (Hw + 16777216) % 2 ^ 32)
    (hm : m = a % 2 ^ j / 2 ^ 25 * 2 ^ 25) (hr : r = (Hw + 2 ^ 33 - m) % 2 ^ 32) (hcin : cin = C) (hC : C ≤ 128)
    (hv : v = (cin + r) % 2 ^ 32) (hc : c = (H + 16777216) / 2 ^ 25) :
    (v : Int) = ((H : Int) - c * 2 ^ 25 + C) % 2 ^ 32 ∧ -16944988 ≤ (H : Int) - c * 2 ^ 25 + C ∧
      (H : Int) - c * 2 ^ 25 + C ≤ 16944988 := by
  have hHj : H + 16777216 < 2 ^ j := fz_ltk _ hH hB
  have hH32 : H + 16777216 < 2 ^ 32 := Nat.lt_of_lt_of_le hHj (Nat.pow_le_pow_right (by decide) hj)
  have ha' : a = H + 16777216 := by rw [ha, hw]; exact Nat.mod_eq_of_lt hH32
  have hm' : m = c * 2 ^ 25 := by rw [hm, ha', Nat.mod_eq_of_lt hHj, ← hc]
  have hd := fz_d25 hc
  have hr' := fz_msub (r := r) (A := H) (M := c * 2 ^ 25) (fz_le33 _ hd.1 (by decide)) (by rw [hr, hw, hm'])
  exact fz_fin_odd (fz_madd hr' hv) hd hcin hC

/-- Odd limb, carry added before the subtraction (mask from `H` alone). -/
theorem fz_oddB {H Hw a m s cin C v c B : Nat} (j : Nat) (hj : j ≤ 32) (hH : H < B)
    (hB : B + 16777216 ≤ 2 ^ j) (hw : Hw = H) (ha : a = ((0 + Hw) % 2 ^ 32 + 16777216) % 2 ^ 32)
    (hm : m = a % 2 ^ j / 2 ^ 25 * 2 ^ 25) (hcin : cin = C) (hC : C ≤ 128) (hs : s = (cin + Hw) % 2 ^ 32)
    (hv : v = (s + 2 ^ 33 - m) % 2 ^ 32) (hc : c = (H + 16777216) / 2 ^ 25) :
    (v : Int) = ((H : Int) - c * 2 ^ 25 + C) % 2 ^ 32 ∧ -16944988 ≤ (H : Int) - c * 2 ^ 25 + C ∧
      (H : Int) - c * 2 ^ 25 + C ≤ 16944988 := by
  have hHj : H + 16777216 < 2 ^ j := fz_ltk _ hH hB
  have hH32 : H + 16777216 < 2 ^ 32 := Nat.lt_of_lt_of_le hHj (Nat.pow_le_pow_right (by decide) hj)
  have hH32' : H < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hH32
  have hj' : 2 ^ j ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hj
  have ha' : a = H + 16777216 := by
    rw [ha, hw, Nat.zero_add, Nat.mod_eq_of_lt hH32', Nat.mod_eq_of_lt hH32]
  have hm' : m = c * 2 ^ 25 := by rw [hm, ha', Nat.mod_eq_of_lt hHj, ← hc]
  have hs' : s = C + H := by
    rw [hs, hw, hcin]; exact Nat.mod_eq_of_lt (fz_ltk2 0 hH hC (by clear hs hv hm ha hc; omega))
  have hd := fz_d25 hc
  have hv' := fz_msub (r := v) (A := s) (M := c * 2 ^ 25) (by rw [hs']; clear hs hv hm ha hc hm' ha'; omega)
    (by rw [hv, hm'])
  exact fz_fin_oddB hv' hs' hd hC

/-- Even limb (`s = C + H`, mask of `s + 2^25`), with the sum written out in `a`. -/
theorem fz_evenB2 {H Hw a m s cin C v c B : Nat} (j : Nat) (hj : j ≤ 32) (hH : H < B)
    (hB : B + 128 + 33554432 ≤ 2 ^ j) (hw : Hw = H) (hcin : cin = C) (hC : C ≤ 128)
    (hs : s = (cin + Hw) % 2 ^ 32) (ha : a = ((cin + Hw) % 2 ^ 32 + 33554432) % 2 ^ 32)
    (hm : m = a % 2 ^ j / 2 ^ 26 * 2 ^ 26) (hv : v = (s + 2 ^ 33 - m) % 2 ^ 32)
    (hc : c = (H + C + 33554432) / 2 ^ 26) :
    (v : Int) = ((H : Int) + C - c * 2 ^ 26) % 2 ^ 32 ∧ -33889976 ≤ (H : Int) + C - c * 2 ^ 26 ∧
      (H : Int) + C - c * 2 ^ 26 ≤ 33889976 := by
  have hj' : 2 ^ j ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hj
  have h2 : C + H + 33554432 < 2 ^ j := fz_ltk2 _ hH hC hB
  have h3 : C + H + 33554432 < 2 ^ 32 := Nat.lt_of_lt_of_le h2 hj'
  have h1 : C + H < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h3
  have hs' : s = C + H := by rw [hs, hw, hcin]; exact Nat.mod_eq_of_lt h1
  have ha' : a = C + H + 33554432 := by
    rw [ha, hw, hcin, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3]
  have hm' : m = c * 2 ^ 26 := by
    rw [hm, ha', Nat.mod_eq_of_lt h2, hc, Nat.add_comm C H]
  have hd := fz_d26 hc
  have hv' := fz_msub (r := v) (A := s) (M := c * 2 ^ 26) (by rw [hs']; clear hs hv hm ha hc hm' ha' hs'; omega)
    (by rw [hv, hm'])
  exact fz_fin_even hv' hs' hd

/-- As `fz_evenB2`, with `a` written from `s`. -/
theorem fz_evenB {H Hw a m s cin C v c B : Nat} (j : Nat) (hj : j ≤ 32) (hH : H < B)
    (hB : B + 128 + 33554432 ≤ 2 ^ j) (hw : Hw = H) (hcin : cin = C) (hC : C ≤ 128)
    (hs : s = (cin + Hw) % 2 ^ 32) (ha : a = (s + 33554432) % 2 ^ 32)
    (hm : m = a % 2 ^ j / 2 ^ 26 * 2 ^ 26) (hv : v = (s + 2 ^ 33 - m) % 2 ^ 32)
    (hc : c = (H + C + 33554432) / 2 ^ 26) :
    (v : Int) = ((H : Int) + C - c * 2 ^ 26) % 2 ^ 32 ∧ -33889976 ≤ (H : Int) + C - c * 2 ^ 26 ∧
      (H : Int) + C - c * 2 ^ 26 ≤ 33889976 :=
  fz_evenB2 j hj hH hB hw hcin hC hs (by rw [ha, hs]) hm hv hc

theorem fz_l5a {y a m c : Nat} (ha : a = (y + 16777216) % 2 ^ 32) (hm : m = a / 2 ^ 25 * 2 ^ 25)
    (hc : c = (y + 16777216) / 2 ^ 25) : c * 2 ^ 25 = m + 2 ^ 32 * ((y + 16777216) / 2 ^ 32) := by
  omega

theorem fz_l5b {y m c t r : Nat} (hcm : c * 2 ^ 25 = m + 2 ^ 32 * t)
    (hr : (r : Int) = ((y : Int) - m) % 2 ^ 32) :
    (r : Int) = ((y : Int) - ((c * 2 ^ 25 : Nat) : Int)) % 2 ^ 32 := by
  rw [hr]; clear hr; omega

/-- Limb 5: `H = y` a full word, so `y + 2^24` may wrap. -/
theorem fz_limb5 {H y a m r cin C v c : Nat} (hw : y = H) (ha : a = (y + 16777216) % 2 ^ 32)
    (hm : m = a % 2 ^ 32 / 2 ^ 25 * 2 ^ 25) (hr : r = (y + 2 ^ 33 - m) % 2 ^ 32) (hcin : cin = C) (hC : C ≤ 128)
    (hv : v = (cin + r) % 2 ^ 32) (hc : c = (H + 16777216) / 2 ^ 25) :
    (v : Int) = ((H : Int) - c * 2 ^ 25 + C) % 2 ^ 32 ∧ -16944988 ≤ (H : Int) - c * 2 ^ 25 + C ∧
      (H : Int) - c * 2 ^ 25 + C ≤ 16944988 := by
  subst hw
  have ha32 : a < 2 ^ 32 := by rw [ha]; exact Nat.mod_lt _ (by decide)
  have hm' : m = a / 2 ^ 25 * 2 ^ 25 := by rw [hm, Nat.mod_eq_of_lt ha32]
  have hcm := fz_l5a ha hm' hc
  have hm32 : m ≤ y + 2 ^ 33 := by rw [hm']; clear hcm hm hr hv hc ha; omega
  have hr' := fz_l5b hcm (fz_msub hm32 hr)
  exact fz_fin_odd (fz_madd hr' hv) (fz_d25 hc) hcin hC

theorem fz_l0a {T c0 v37 v38 v58 v62 : Nat} (hT : v37 + 2 ^ 32 * v38 = T)
    (h58 : v58 = (v37 + 33554432) % 2 ^ 32) (h62 : v62 = v58 / 2 ^ 26 * 2 ^ 26)
    (hc : c0 = (T + 33554432) / 2 ^ 26) :
    c0 * 2 ^ 26 = v62 + 2 ^ 32 * (v38 + (v37 + 33554432) / 2 ^ 32) := by
  omega

theorem fz_l0b {T c0 v37 v38 v62 g v63 : Nat} (hT : v37 + 2 ^ 32 * v38 = T)
    (hk : c0 * 2 ^ 26 = v62 + 2 ^ 32 * (v38 + g)) (hr : (v63 : Int) = ((v37 : Int) - v62) % 2 ^ 32) :
    (v63 : Int) = ((T : Int) - c0 * 2 ^ 26) % 2 ^ 32 := by
  have e : (T : Int) - c0 * 2 ^ 26 = (v37 : Int) - v62 + 2 ^ 32 * (-(g : Int)) := by
    clear hr
    omega
  rw [e, Int.add_mul_emod_self_left]; exact hr

/-- Limb 0: `T0 = y + 19 c9` (33 bits) minus `2^26 c0`, from the low words. -/
theorem fz_limb0 {T c0 v37 v38 v58 v62 v63 : Nat} (hT : v37 + 2 ^ 32 * v38 = T)
    (h58 : v58 = (v37 + 33554432) % 2 ^ 32) (h62 : v62 = v58 % 2 ^ 32 / 2 ^ 26 * 2 ^ 26)
    (h63 : v63 = (v37 + 2 ^ 33 - v62) % 2 ^ 32) (hc : c0 = (T + 33554432) / 2 ^ 26) :
    (v63 : Int) = ((T : Int) - c0 * 2 ^ 26) % 2 ^ 32 ∧ -33889976 ≤ (T : Int) - c0 * 2 ^ 26 ∧
      (T : Int) - c0 * 2 ^ 26 ≤ 33889976 := by
  have h58' : v58 < 2 ^ 32 := by rw [h58]; exact Nat.mod_lt _ (by decide)
  have h62' : v62 = v58 / 2 ^ 26 * 2 ^ 26 := by rw [h62, Nat.mod_eq_of_lt h58']
  have hk := fz_l0a hT h58 h62' hc
  have hle : v62 ≤ v37 + 2 ^ 33 := by rw [h62']; clear hk h62 h63 hc h58 hT; omega
  have hr := fz_msub hle h63
  have hd : c0 * 2 ^ 26 ≤ T + 33554432 ∧ T + 33554432 < c0 * 2 ^ 26 + 2 ^ 26 := by
    clear hk h62 h63 h58 h62' hle hr; omega
  refine ⟨fz_l0b hT hk hr, ?_, ?_⟩ <;> clear hk h62 h63 h58 h62' hle hr hT <;> omega

/-! ### Byte sums -/

theorem fz_b4 {a b c d : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) (hc : c < 2 ^ 8) (hd : d < 2 ^ 8) :
    a + 2 ^ 8 * b + 2 ^ 16 * c + 2 ^ 24 * d < 2 ^ 32 := by omega

theorem fz_b2 {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) : a + 2 ^ 8 * b < 2 ^ 16 := by omega

theorem fz_lt10 (i : Nat) (h : i < 10) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega

end Solutions.OpensslX25519.I
