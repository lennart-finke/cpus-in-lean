import Solutions.OpensslX25519.I.LadHead2
import Solutions.OpensslX25519.I.CSt2
import Solutions.OpensslX25519.I.InvLoop
/-!
# The frame state of the ladder loop, the scalar bit, and the spec step

* `ladSl out b w s0 s1 s2 s3`: the word slots of `x25519_scalar_mult_generic`'s frame (out pointer, the
  bit `b`, the eight words `w t` of the scalar copy `e`, the saved registers); `EB w eb`: the words hold the
  bytes `eb`; `lad_byte`: the byte the loop head reads.
* The bit of the loop head (`setbV_eq`, `btV_toNat`, `lad_bit`).
* `stepOf`, `ladderStep_eq`: `Spec.X25519.ladderStep` after the swap.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Bit
  Ssl.Spec.X25519

/-! ## The bit -/

theorem mix1_land (fl v : UInt32) : (mixF fl v 1) &&& 1 = v &&& 1 := by
  unfold mixF
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    have a2 : (UInt32.toBitVec 1).getLsbD 0 = true := by decide
    rw [a2]; simp
  · have h2 : ∀ j, j < 32 → j ≠ 0 → (UInt32.toBitVec 1).getLsbD j = false := by decide
    rw [h2 i hi h0]; simp

theorem cfB_mix_bitU (fl : UInt32) (c : Bool) : cfB (mixF fl (bitU c) 1) = c := by
  unfold cfB
  rw [show Flag.CF = (1 : UInt32) from rfl, mix1_land]
  cases c <;> decide

theorem setbV_eq (fl y r : UInt32) : setbV fl y r = bitU (btV y r) := by
  unfold setbV; rw [cfB_mix_bitU]; cases btV y r <;> decide

theorem btV_toNat (y r : UInt32) (hr : r.toNat < 8) : (bitU (btV y r)).toNat = (y.toNat >>> r.toNat) % 2 := by
  have e1 : r.land 31 = r := by
    apply UInt32.toNat_inj.1
    show (r &&& 31).toNat = r.toNat
    rw [UInt32.toNat_and, show (31 : UInt32).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : (UInt32.land (y.shiftRight r) 1).toNat = (y.toNat >>> r.toNat) % 2 := by
    have s1 : (y.shiftRight r).toNat = y.toNat >>> (r.toNat % 32) := UInt32.toNat_shiftRight y r
    show ((y.shiftRight r) &&& 1).toNat = _
    rw [UInt32.toNat_and, s1, show (1 : UInt32).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one, Nat.mod_eq_of_lt (a := r.toNat) (by omega)]
  unfold btV
  rw [e1]
  by_cases h : UInt32.land (y.shiftRight r) 1 = 0
  · rw [decide_eq_true h]
    have := congrArg UInt32.toNat h; rw [e2] at this; rw [this]; rfl
  · rw [decide_eq_false h]
    have h' : (UInt32.land (y.shiftRight r) 1).toNat ≠ 0 := fun h2 => h (UInt32.toNat_inj.1 h2)
    rw [e2] at h'
    have : (y.toNat >>> r.toNat) % 2 = 1 := by omega
    rw [this]; rfl

theorem land7_toNat (x : UInt32) : (x.land 7).toNat = x.toNat % 8 := by
  show (x &&& 7).toNat = _
  rw [UInt32.toNat_and, show (7 : UInt32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The bit the loop head computes at position `pos` of the bytes `eb`. -/
theorem lad_bit (fl pos : UInt32) (eb : List UInt8) (hlen : eb.length = 32) (hpos : pos.toNat < 256) :
    (setbV fl (eb[pos.toNat / 8]!).toUInt32 (logicF 4 (pos.land 7)).1).toNat = (leNat eb >>> pos.toNat) % 2 := by
  rw [setbV_eq, show (logicF 4 (pos.land 7)).1 = pos.land 7 from rfl, btV_toNat _ _ (by rw [land7_toNat]; omega), land7_toNat]
  have := leNat_bit eb pos.toNat (by omega)
  simp only [UInt8.toNat_toUInt32]
  exact this.symm

theorem bitU_xor (a b : UInt32) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a.xor b = 0 ∨ a.xor b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem setbV_01 (fl y r : UInt32) : setbV fl y r = 0 ∨ setbV fl y r = 1 := by
  rw [setbV_eq]; exact bitU_01 _

theorem xor_one_iff (a b : UInt32) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a.xor b = 1 ↔ a.toNat ^^^ b.toNat = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-! ## The slots -/

/-- The word slots of the frame of `x25519_scalar_mult_generic`. -/
def ladSl (out b : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32) : List (Nat × UInt32) :=
  [(8, out), (12, b), (16, w 0), (20, w 1), (24, w 2), (28, w 3), (32, w 4), (36, w 5), (40, w 6), (44, w 7),
    (328, s0), (332, s1), (336, s2), (340, s3)]

theorem ladSl_upd (out b b' : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32) :
    upd (ladSl out b w s0 s1 s2 s3) 12 b' = ladSl out b' w s0 s1 s2 s3 := rfl

theorem ladSl_al (out b : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32) :
    ∀ k', k' ∈ (ladSl out b w s0 s1 s2 s3).map Prod.fst → k' % 4 = 0 := by
  intro k hk; simp only [ladSl, List.map, List.mem_cons] at hk; rcases hk with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    first | (subst h; rfl) | simp at h

/-- The words `w t` hold the bytes `eb` (little-endian). -/
def EB (w : Nat → UInt32) (eb : List UInt8) : Prop :=
  ∀ t, t < 8 → ∀ j, j < 4 → (w t >>> (8 * j).toUInt32).toUInt8 = eb[4 * t + j]!

theorem byte_of_join (b0 b1 b2 b3 : UInt8) (j : Nat) (hj : j < 4) :
    ((b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)) >>>
      (8 * j).toUInt32).toUInt8 = [b0, b1, b2, b3][j]! := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp only [shl32, shr32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] <;>
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [BitVec.getLsbD_of_ge]

/-- A byte of a word in memory. -/
theorem rdRaw1_word {m : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ m.size) (ha : a.toNat + 4 < 2 ^ 32) (j : Nat)
    (hj : j < 4) : rdRaw m (a + j.toUInt32) 1 = ((rdRaw m a 4 >>> (8 * j).toUInt32).toUInt8).toUInt32 := by
  unfold rdRaw
  have e : (a + j.toUInt32).toNat = a.toNat + j := by
    rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (a := j) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [rdBytes1_eq (by rw [e]; omega), memByte_def (by rw [e]; omega), e, rdBytes4_eq h, byte_of_join _ _ _ _ j hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The buffers as a list of seven. -/
theorem CSt.set7 {G N : XMem} {L : UInt32} {n W : Nat} {sl : List (Nat × UInt32)} {bf : List (Nat × Array UInt32)}
    (C : CSt G N L n W sl bf) (k1 k2 k3 k4 k5 k6 k7 : Nat) (v1 v2 v3 v4 v5 v6 v7 : Array UInt32)
    (hk : bf.map Prod.fst = [k1, k2, k3, k4, k5, k6, k7]) (h1 : bf.lookup k1 = some v1) (h2 : bf.lookup k2 = some v2)
    (h3 : bf.lookup k3 = some v3) (h4 : bf.lookup k4 = some v4) (h5 : bf.lookup k5 = some v5)
    (h6 : bf.lookup k6 = some v6) (h7 : bf.lookup k7 = some v7) :
    CSt G N L n W sl [(k1, v1), (k2, v2), (k3, v3), (k4, v4), (k5, v5), (k6, v6), (k7, v7)] := by
  refine ⟨C.top, C.fit, C.w_lo, C.hi, C.imgok, C.pres, C.slot, fun k v hl => C.buf k v ?_, ?_⟩
  · simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h1
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h2
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h3
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h4
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h5
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h6
    split at hl
    · rename_i h; simp at h hl; subst h hl; exact h7
    simp at hl
  · have : ([(k1, v1), (k2, v2), (k3, v3), (k4, v4), (k5, v5), (k6, v6), (k7, v7)] : List (Nat × Array UInt32)).map
      Prod.fst = [k1, k2, k3, k4, k5, k6, k7] := rfl
    rw [this, ← hk]; exact C.lay

/-- The byte of the scalar copy that the loop head reads. -/
theorem lad_byte {G N : XMem} {L : UInt32} {W : Nat} {out b s0 s1 s2 s3 : UInt32} {w : Nat → UInt32}
    {bf : List (Nat × Array UInt32)} (C : CSt G N L 344 W (ladSl out b w s0 s1 s2 s3) bf)
    {eb : List UInt8} (heb : EB w eb) (q : UInt32) (hq : q.toNat < 32) :
    rdRaw N.get (UInt32.add (UInt32.add (UInt32.add L 8) q) 8) 1 = (eb[q.toNat]!).toUInt32 := by
  have hi := C.hi; have ht := C.top; unfold ramTop at ht
  obtain ⟨t, j, ht8, hj4, hq'⟩ : ∃ t j, t < 8 ∧ j < 4 ∧ q.toNat = 4 * t + j :=
    ⟨q.toNat / 4, q.toNat % 4, by omega, by omega, by omega⟩
  have hw : rdRaw N.get (UInt32.add L (16 + 4 * t).toUInt32) 4 = w t := by
    apply C.slot
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have ea := C.addr (k := 16 + 4 * t) (by omega)
  have e : UInt32.add (UInt32.add (UInt32.add L 8) q) 8 = UInt32.add L (16 + 4 * t).toUInt32 + j.toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, ea, toNat_uadd, toNat_uadd, toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (a := j) (by omega)]
    simp only [UInt32.reduceToNat]
    omega
  rw [e, rdRaw1_word (by rw [ea]; omega) (by rw [ea]; omega) j hj4, hw, heb t ht8 j hj4, hq']

end Solutions.OpensslX25519.I
