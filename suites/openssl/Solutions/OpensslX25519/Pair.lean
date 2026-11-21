import Solutions.Exec.Mul
/-!
# 64-bit values in register pairs

`fe_mul` and `fe_sq` compute with `int64_t` values held in pairs of 32-bit words. `M64 lo hi E`: the
pair `hi:lo` is `E` modulo `2^64`; `M32 x E`: the word `x` is `E` modulo `2^32`; `sv x` is the
signed value of a word. The lemmas below give these facts for the results of the instructions, in
the forms `cbv` leaves them (`Solutions.Exec.Mul`): products of `imul`, sums and differences of
`add`/`adc` and `sub`/`sbb` chains (exact modulo `2^64`), the carry `(t + 2^(s-1)) >> s` of
`sar`/`shrd` (floor division, for `t` within the signed range), its low word by `shld`, the masking
`t & -2^s` (a multiple of `2^s`), and the `lea` multiples of a word.
-/
namespace Solutions.OpensslX25519
open X86 Solutions.Exec Solutions.Exec.Mul

/-- The signed value of a word. -/
def sv (x : UInt32) : Int := x.toInt32.toInt

/-- The pair `hi:lo` as an unsigned 64-bit number. -/
def pv (lo hi : UInt32) : Int := (hi.toNat : Int) * 2 ^ 32 + (lo.toNat : Int)

/-- The pair `hi:lo` is `E` modulo `2^64`. -/
def M64 (lo hi : UInt32) (E : Int) : Prop := pv lo hi = E % 2 ^ 64

/-- The word `x` is `E` modulo `2^32`. -/
def M32 (x : UInt32) (E : Int) : Prop := (x.toNat : Int) = E % 2 ^ 32

theorem M64.congr {lo hi : UInt32} {E E' : Int} (h : M64 lo hi E) (e : E = E') : M64 lo hi E' := e ▸ h
theorem M32.congr {x : UInt32} {E E' : Int} (h : M32 x E) (e : E = E') : M32 x E' := e ▸ h

theorem sv_eq (x : UInt32) :
    sv x = if x.toNat < 2 ^ 31 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 32 := by
  unfold sv
  rw [show x.toInt32.toInt = x.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_cond]
  simp only [UInt32.toNat_toBitVec]
  split <;> split <;> omega

theorem M32_sv (x : UInt32) : M32 x (sv x) := by
  unfold M32; rw [sv_eq]; have := x.toNat_lt; split <;> omega

theorem sv_of_M32 {x : UInt32} {E : Int} (h : M32 x E) (hb : -2 ^ 31 ≤ E ∧ E < 2 ^ 31) : sv x = E := by
  unfold M32 at h; rw [sv_eq]; have := x.toNat_lt; split <;> omega

theorem M32_lo {lo hi : UInt32} {E : Int} (h : M64 lo hi E) : M32 lo E := by
  unfold M64 pv at h; unfold M32
  have := lo.toNat_lt; have := hi.toNat_lt
  omega

/-! ## Additions and subtractions -/

theorem toNat_sz4_mask (x : UInt32) : (x &&& Sz.mask 4).toNat = x.toNat := by
  rw [show Sz.mask 4 = 0xFFFFFFFF from rfl]
  rw [UInt32.toNat_and]
  have := x.toNat_lt
  rw [show (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem pack_cf (f : AFlags) : f.pack &&& Flag.CF = if f.cf then 1 else 0 := by
  obtain ⟨cf, pf, af, zf, sf, of⟩ := f
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;> decide

theorem cfBit_pack (f : AFlags) : cfBit f.pack = if f.cf then 1 else 0 := by
  unfold cfBit b2u
  rw [pack_cf]
  cases f.cf <;> decide

theorem addF_fst_toNat (a b c : UInt32) :
    (addF 4 a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  simp only [addF, addCore]
  rw [toNat_sz4_mask, UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_add,
    UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt
  omega

theorem addF_cf (a b c : UInt32) :
    cfBit (addF 4 a b c).2 = if 2 ^ 32 ≤ a.toNat + b.toNat + c.toNat then 1 else 0 := by
  simp only [addF, addCore]
  rw [cfBit_pack]
  simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64,
    show (Sz.mask 4).toUInt64.toNat = 2 ^ 32 - 1 from rfl]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt
  split <;> split <;> rename_i h1 h2 <;> (try simp only [decide_eq_true_eq] at h1 h2) <;> first | rfl | omega

theorem subF_fst_toNat (a b c : UInt32) (hc : c.toNat ≤ 1) :
    (subF 4 a b c).1.toNat = (a.toNat + 2 ^ 33 - b.toNat - c.toNat) % 2 ^ 32 := by
  simp only [subF, subCore]
  rw [toNat_sz4_mask, UInt32.toNat_sub, UInt32.toNat_sub]
  have := a.toNat_lt; have := b.toNat_lt
  omega

theorem subF_cf (a b c : UInt32) :
    cfBit (subF 4 a b c).2 = if a.toNat < b.toNat + c.toNat then 1 else 0 := by
  simp only [subF, subCore]
  rw [cfBit_pack]
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt32.toNat_toUInt64]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt
  split <;> split <;> rename_i h1 h2 <;> (try simp only [decide_eq_true_eq] at h1 h2) <;> first | rfl | omega

theorem add_pair {a b c d lo hi g : UInt32} {A B : Int} (h1 : M64 a c A) (h2 : M64 b d B)
    (e1 : lo = (addF 4 a b 0).1) (e2 : g = (addF 4 a b 0).2) (e3 : hi = (addF 4 c d (cfBit g)).1) :
    M64 lo hi (A + B) := by
  subst e1 e2 e3
  unfold M64 pv at *
  rw [addF_fst_toNat, addF_fst_toNat, addF_cf]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt; have := d.toNat_lt
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [h0]
  split <;> simp only [show (1 : UInt32).toNat = 1 from rfl, h0] <;> omega

theorem sub_pair {a b c d lo hi g : UInt32} {A B : Int} (h1 : M64 a c A) (h2 : M64 b d B)
    (e1 : lo = (subF 4 a b 0).1) (e2 : g = (subF 4 a b 0).2) (e3 : hi = (subF 4 c d (cfBit g)).1) :
    M64 lo hi (A - B) := by
  subst e1 e2 e3
  unfold M64 pv at *
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [subF_fst_toNat a b 0 (by decide), subF_cf, h0]
  have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt; have := d.toNat_lt
  split
  · rw [subF_fst_toNat c d 1 (by decide), show (1 : UInt32).toNat = 1 from rfl]; omega
  · rw [subF_fst_toNat c d 0 (by decide), h0]; omega

theorem add32 {a b x : UInt32} {A B : Int} (h1 : M32 a A) (h2 : M32 b B) (e : x = (addF 4 a b 0).1) :
    M32 x (A + B) := by
  subst e; unfold M32 at *
  rw [addF_fst_toNat, show (0 : UInt32).toNat = 0 from rfl]
  omega

theorem sub32 {a b x : UInt32} {A B : Int} (h1 : M32 a A) (h2 : M32 b B) (e : x = (subF 4 a b 0).1) :
    M32 x (A - B) := by
  subst e; unfold M32 at *
  rw [subF_fst_toNat _ _ _ (by decide), show (0 : UInt32).toNat = 0 from rfl]
  have := a.toNat_lt; have := b.toNat_lt
  omega

theorem M64_const (lo hi : UInt32) (E : Int) (h : pv lo hi = E) (h0 : 0 ≤ E) (h1 : E < 2 ^ 64) :
    M64 lo hi E := by
  unfold M64; rw [h]; omega

/-! ## Products and multiples -/

theorem u64_shr (a b : UInt64) : (ShiftRight.shiftRight a b).toNat = a.toNat / 2 ^ (b.toNat % 64) :=
  (UInt64.toNat_shiftRight a b).trans (Nat.shiftRight_eq_div_pow _ _)
theorem u64_shl (a b : UInt64) : (ShiftLeft.shiftLeft a b).toNat = a.toNat * 2 ^ (b.toNat % 64) % 2 ^ 64 :=
  (UInt64.toNat_shiftLeft a b).trans (by rw [Nat.shiftLeft_eq])
theorem u64_shr' (a b : UInt64) : (UInt64.shiftRight a b).toNat = a.toNat / 2 ^ (b.toNat % 64) :=
  (UInt64.toNat_shiftRight a b).trans (Nat.shiftRight_eq_div_pow _ _)
theorem u32_add (a b : UInt32) : (UInt32.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 :=
  UInt32.toNat_add a b
theorem nat_shl (a b : Nat) : ShiftLeft.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem u32_shl (a b : UInt32) : (UInt32.shiftLeft a b).toNat = (a.toNat <<< (b.toNat % 32)) % 2 ^ 32 :=
  UInt32.toNat_shiftLeft a b

theorem or_high (x k i : Nat) (hx : x < 2 ^ i) : x ||| k * 2 ^ i = x + k * 2 ^ i := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  exact Nat.add_comm _ _

theorem and_msb (x : UInt32) : (x &&& 0x80000000 != 0) = decide (2 ^ 31 ≤ x.toNat) := by
  have hx := x.toNat_lt
  have key : x.toNat &&& 2 ^ 31 = if 2 ^ 31 ≤ x.toNat then 2 ^ 31 else 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : 31 = i
    · subst hi
      have : x.toNat.testBit 31 = decide (2 ^ 31 ≤ x.toNat) := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        by_cases h : 2 ^ 31 ≤ x.toNat
        · simp only [h, decide_true]; simp only [decide_eq_true_eq]; omega
        · simp only [h, decide_false]; simp only [decide_eq_false_iff_not]; omega
      rw [this]
      split <;> rename_i h
      · rw [Nat.testBit_two_pow]; simp [h]
      · simp [h]
    · split
      · rw [Nat.testBit_two_pow]; simp [hi]
      · simp [hi]
  have e : (x &&& 0x80000000).toNat = if 2 ^ 31 ≤ x.toNat then 2 ^ 31 else 0 := by
    rw [UInt32.toNat_and, show (0x80000000 : UInt32).toNat = 2 ^ 31 from rfl, key]
  by_cases h : 2 ^ 31 ≤ x.toNat
  · have : x &&& 0x80000000 ≠ 0 := fun h0 => by rw [h0, if_pos h] at e; simp at e
    simp [this, h]
  · have : x &&& 0x80000000 = 0 := UInt32.toNat_inj.1 (by rw [e, if_neg h]; rfl)
    simp [this, h]

theorem sext64_toNat (x : UInt32) : ((sext64 4 x).toNat : Int) = sv x % 2 ^ 64 := by
  rw [sv_eq]
  have hx := x.toNat_lt
  have hs : sext 4 x = x := rfl
  simp only [sext64, hs, and_msb]
  by_cases h : 2 ^ 31 ≤ x.toNat
  · simp only [h, decide_true, ite_true, if_neg (show ¬ x.toNat < 2 ^ 31 by omega)]
    rw [UInt64.toNat_or, UInt32.toNat_toUInt64,
      show (0xFFFFFFFF00000000 : UInt64).toNat = (2 ^ 32 - 1) * 2 ^ 32 from rfl, or_high _ _ _ hx]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, if_pos (show x.toNat < 2 ^ 31 by omega)]
    rw [UInt32.toNat_toUInt64]
    omega

theorem pv_halves (p : UInt64) : pv (UInt64.toUInt32 p) (UInt64.toUInt32 (UInt64.shiftRight p 32)) = p.toNat := by
  unfold pv
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32,
    u64_shr', show (32 : UInt64).toNat % 64 = 32 from rfl]
  have := p.toNat_lt
  omega

theorem imul_pair {a b lo hi : UInt32} {A B : Int}
    (e1 : lo = UInt64.toUInt32 (imulCore 4 a b).1)
    (e2 : hi = UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 a b).1 32))
    (ha : sv a = A) (hb : sv b = B) : M64 lo hi (A * B) := by
  subst e1 e2 ha hb
  unfold M64
  rw [pv_halves]
  show (((sext64 4 a) * (sext64 4 b)).toNat : Int) = _
  rw [UInt64.toNat_mul]
  rw [Int.natCast_emod, Int.natCast_mul, sext64_toNat, sext64_toNat,
    show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 from rfl]
  exact (Int.mul_emod _ _ _).symm

theorem sv_add2 {x v : UInt32} {X B : Int} (e : v = UInt32.add x x) (h : sv x = X)
    (hb : -B ≤ X ∧ X ≤ B) (hB : 2 * B < 2 ^ 31) : sv v = 2 * X := by
  subst e
  apply sv_of_M32 _ (by omega)
  unfold M32
  rw [show UInt32.add x x = x + x from rfl, UInt32.toNat_add]
  have := M32_sv x
  unfold M32 at this
  subst h
  omega

theorem sv_addF2 {x v : UInt32} {X B : Int} (e : v = (addF 4 x x 0).1) (h : sv x = X)
    (hb : -B ≤ X ∧ X ≤ B) (hB : 2 * B < 2 ^ 31) : sv v = 2 * X := by
  subst e
  apply sv_of_M32 _ (by omega)
  unfold M32
  rw [addF_fst_toNat, show (0 : UInt32).toNat = 0 from rfl]
  have := M32_sv x
  unfold M32 at this
  subst h
  omega

theorem sv_lea19 {x d v : UInt32} {X B : Int} (e1 : d = UInt32.add x (UInt32.shiftLeft x 3))
    (e2 : v = UInt32.add x (UInt32.shiftLeft d 1)) (h : sv x = X)
    (hb : -B ≤ X ∧ X ≤ B) (hB : 19 * B < 2 ^ 31) : sv v = 19 * X := by
  subst e1 e2
  apply sv_of_M32 _ (by omega)
  unfold M32
  simp only [u32_add, u32_shl, nat_shl, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow]
  have := M32_sv x
  unfold M32 at this
  subst h
  omega

theorem land_ones (y : UInt32) : UInt32.land y 4294967295 = y :=
  UInt32.toNat_inj.1 (toNat_sz4_mask y)

theorem sv_imul38 {x v : UInt32} {X B : Int}
    (e : v = UInt32.land (UInt64.toUInt32 (imulCore 4 x 38).1) 4294967295)
    (h : sv x = X) (hb : -B ≤ X ∧ X ≤ B) (hB : 38 * B < 2 ^ 31) : sv v = 38 * X := by
  rw [land_ones] at e
  have hp := imul_pair (lo := v) (hi := UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 x 38).1 32)) e rfl h
    (show sv 38 = 38 by rw [sv_eq]; decide)
  apply sv_of_M32 _ (by omega)
  have := M32_lo hp
  unfold M32 at this ⊢
  rw [this]
  omega

theorem M64_c25 : M64 33554432 0 33554432 := by unfold M64 pv; decide
theorem M64_c24 : M64 16777216 0 16777216 := by unfold M64 pv; decide

/-! ## The carry step -/

theorem land_high (x s : Nat) (hs : s ≤ 32) (hx : x < 2 ^ 32) :
    x &&& (2 ^ 32 - 2 ^ s) = x / 2 ^ s * 2 ^ s := by
  have hm : 2 ^ 32 - 2 ^ s = (2 ^ (32 - s) - 1) * 2 ^ s := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hs]
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : s ≤ i
  · rw [Nat.sub_add_cancel h1]
    by_cases h2 : i < 32
    · simp [h1, show i - s < 32 - s by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h1]

/-- The word `t & -2^s`. -/
theorem land_mask (a : UInt32) (s : Nat) (hs : s ≤ 32) (K : UInt32) (hK : K.toNat = 2 ^ 32 - 2 ^ s) :
    (UInt32.land a K).toNat = a.toNat / 2 ^ s * 2 ^ s := by
  rw [show UInt32.land a K = a &&& K from rfl, UInt32.toNat_and, hK, land_high _ _ hs a.toNat_lt]

theorem mask_pair26 {a c m : UInt32} {T C : Int} (h : M64 a c T) (hC : C = T / 67108864)
    (e : m = (logicF 4 (UInt32.land a 4227858432)).1) : M64 m c (C * 67108864) := by
  subst e hC
  unfold M64 pv at *
  rw [show (logicF 4 (UInt32.land a 4227858432)).1 = UInt32.land a 4227858432 from rfl,
    land_mask a 26 (by decide) _ rfl]
  have := a.toNat_lt; have := c.toNat_lt
  omega

theorem mask_pair25 {a c m : UInt32} {T C : Int} (h : M64 a c T) (hC : C = T / 33554432)
    (e : m = (logicF 4 (UInt32.land a 4261412864)).1) : M64 m c (C * 33554432) := by
  subst e hC
  unfold M64 pv at *
  rw [show (logicF 4 (UInt32.land a 4261412864)).1 = UInt32.land a 4261412864 from rfl,
    land_mask a 25 (by decide) _ rfl]
  have := a.toNat_lt; have := c.toNat_lt
  omega

theorem or_lo (c a : UInt32) : ((c.toUInt64 <<< 32) ||| a.toUInt64).toNat = c.toNat * 2 ^ 32 + a.toNat := by
  rw [UInt64.toNat_or, u64_shl, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
    show (32 : UInt64).toNat % 64 = 32 from rfl]
  have := c.toNat_lt; have := a.toNat_lt
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, or_high _ _ _ (by omega)]
  omega

theorem shrd_toNat (a c : UInt32) (k : UInt32) (hk : k.toNat < 32) (hk0 : 0 < k.toNat) :
    (sdR false a c k).toNat = (c.toNat * 2 ^ 32 + a.toNat) / 2 ^ k.toNat % 2 ^ 32 := by
  have e : sdR false a c k = ((((c.toUInt64 <<< 32) ||| a.toUInt64) >>> (k &&& 0x1F).toUInt64).toUInt32) := by
    have h0 : ((k &&& 0x1F).toUInt64 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg UInt64.toNat h
      rw [UInt32.toNat_toUInt64, UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simp at this; omega
    simp only [sdR, shiftDouble, h0]
    rfl
  have hk' : ((k &&& 0x1F).toUInt64).toNat % 64 = k.toNat := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_and, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; omega
  rw [e, UInt64.toNat_toUInt32, u64_shr, hk', or_lo]

theorem sar_toNat26 (c : UInt32) : (sarR c 26).toNat =
    (if 2 ^ 31 ≤ c.toNat then c.toNat + (2 ^ 32 - 1) * 2 ^ 32 else c.toNat) / 2 ^ 26 % 2 ^ 32 := by
  have e : sarR c 26 = ((if c &&& 0x80000000 != 0 then c.toUInt64 ||| 0xFFFFFFFF00000000 else c.toUInt64) >>>
      (26 : UInt64)).toUInt32 &&& Sz.mask 4 := rfl
  rw [e, toNat_sz4_mask, and_msb, UInt64.toNat_toUInt32, u64_shr,
    show (26 : UInt64).toNat % 64 = 26 from rfl]
  have hx := c.toNat_lt
  by_cases h : 2 ^ 31 ≤ c.toNat
  · simp only [h, decide_true, ite_true]
    rw [UInt64.toNat_or, UInt32.toNat_toUInt64,
      show (0xFFFFFFFF00000000 : UInt64).toNat = (2 ^ 32 - 1) * 2 ^ 32 from rfl, or_high _ _ _ hx]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    rw [UInt32.toNat_toUInt64]

theorem sar_toNat25 (c : UInt32) : (sarR c 25).toNat =
    (if 2 ^ 31 ≤ c.toNat then c.toNat + (2 ^ 32 - 1) * 2 ^ 32 else c.toNat) / 2 ^ 25 % 2 ^ 32 := by
  have e : sarR c 25 = ((if c &&& 0x80000000 != 0 then c.toUInt64 ||| 0xFFFFFFFF00000000 else c.toUInt64) >>>
      (25 : UInt64)).toUInt32 &&& Sz.mask 4 := rfl
  rw [e, toNat_sz4_mask, and_msb, UInt64.toNat_toUInt32, u64_shr,
    show (25 : UInt64).toNat % 64 = 25 from rfl]
  have hx := c.toNat_lt
  by_cases h : 2 ^ 31 ≤ c.toNat
  · simp only [h, decide_true, ite_true]
    rw [UInt64.toNat_or, UInt32.toNat_toUInt64,
      show (0xFFFFFFFF00000000 : UInt64).toNat = (2 ^ 32 - 1) * 2 ^ 32 from rfl, or_high _ _ _ hx]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    rw [UInt32.toNat_toUInt64]

theorem shr_pair26 {a c lo hi : UInt32} {T : Int} (h : M64 a c T) (hb : -2 ^ 63 ≤ T ∧ T < 2 ^ 63)
    (e1 : lo = sdR false a c 26) (e2 : hi = sarR c 26) : ∃ C : Int, C = T / 67108864 ∧ M64 lo hi C := by
  refine ⟨_, rfl, ?_⟩
  subst e1 e2
  unfold M64 pv at *
  rw [shrd_toNat a c 26 (by decide) (by decide), sar_toNat26, show (26 : UInt32).toNat = 26 from rfl]
  have := a.toNat_lt; have := c.toNat_lt
  split <;> omega

theorem shr_pair25 {a c lo hi : UInt32} {T : Int} (h : M64 a c T) (hb : -2 ^ 63 ≤ T ∧ T < 2 ^ 63)
    (e1 : lo = sdR false a c 25) (e2 : hi = sarR c 25) : ∃ C : Int, C = T / 33554432 ∧ M64 lo hi C := by
  refine ⟨_, rfl, ?_⟩
  subst e1 e2
  unfold M64 pv at *
  rw [shrd_toNat a c 25 (by decide) (by decide), sar_toNat25, show (25 : UInt32).toNat = 25 from rfl]
  have := a.toNat_lt; have := c.toNat_lt
  split <;> omega

theorem shld_toNat (c a : UInt32) :
    (sdR true c a 6).toNat = (c.toNat * 2 ^ 32 + a.toNat) * 64 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 := by
  have e : sdR true c a 6 = (((((c.toUInt64 <<< 32) ||| a.toUInt64) <<< (6 : UInt64)) >>> 32).toUInt32) := rfl
  rw [e, UInt64.toNat_toUInt32, u64_shr, u64_shl, or_lo,
    show (6 : UInt64).toNat % 64 = 6 from rfl, show (32 : UInt64).toNat % 64 = 32 from rfl]

theorem shld26 {a c x : UInt32} {T : Int} (h : M64 a c T) (e : x = sdR true c a 6) :
    ∃ C : Int, C = T / 67108864 ∧ M32 x C := by
  refine ⟨_, rfl, ?_⟩
  subst e
  unfold M64 pv at h; unfold M32
  rw [shld_toNat]
  have := a.toNat_lt; have := c.toNat_lt
  omega

theorem mul19_pair {a c lo hi1 d e hi : UInt32} {C : Int} (h : M64 a c C)
    (e1 : lo = UInt64.toUInt32 (UInt64.mul (UInt32.toUInt64 a) 19))
    (e2 : hi1 = UInt64.toUInt32 (UInt64.shiftRight (UInt64.mul (UInt32.toUInt64 a) 19) 32))
    (e3 : d = UInt32.add c (UInt32.shiftLeft c 3)) (e4 : e = UInt32.add c (UInt32.shiftLeft d 1))
    (e5 : hi = (addF 4 hi1 e 0).1) : M64 lo hi (19 * C) := by
  have hp := pv_halves (UInt64.mul (UInt32.toUInt64 a) 19)
  rw [← e1, ← e2] at hp
  subst e3 e4 e5
  unfold M64 pv at *
  rw [addF_fst_toNat, show (0 : UInt32).toNat = 0 from rfl]
  rw [show UInt64.mul (UInt32.toUInt64 a) 19 = a.toUInt64 * 19 from rfl, UInt64.toNat_mul,
    UInt32.toNat_toUInt64, show (19 : UInt64).toNat = 19 from rfl] at hp
  simp only [u32_add, u32_shl, nat_shl, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow]
  have := a.toNat_lt; have := c.toNat_lt; have := lo.toNat_lt; have := hi1.toNat_lt
  omega

end Solutions.OpensslX25519
