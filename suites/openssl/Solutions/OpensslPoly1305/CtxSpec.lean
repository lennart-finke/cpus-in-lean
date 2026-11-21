import Solutions.OpensslPoly1305.SpecAcc
import Solutions.OpensslPoly1305.Entry
/-!
# The context between the calls

`GoodB key msg st`: the 236 context bytes `st` after `Poly1305_Init` and `Poly1305_Update`s of the
message `msg` so far: the accumulator limbs (`h4 ≤ 4`, value `accOf (r key) msg` modulo `p`), the
clamped `r`, `s`, the number of buffered bytes and the buffered tail. The other context bytes are
unconstrained (the code never reads them).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.Spec.Poly1305

set_option autoImplicit false

/-- The little-endian word at byte `k` of a byte list. -/
def wd (st : List UInt8) (k : Nat) : Nat :=
  st[k]!.toNat + 2 ^ 8 * st[k + 1]!.toNat + 2 ^ 16 * st[k + 2]!.toNat + 2 ^ 24 * st[k + 3]!.toNat

/-- Four words from byte `k`. -/
def wd4 (st : List UInt8) (k : Nat) : Nat :=
  wd st k + 2 ^ 32 * wd st (k + 4) + 2 ^ 64 * wd st (k + 8) + 2 ^ 96 * wd st (k + 12)

def GoodB (key msg st : List UInt8) : Prop :=
  st.length = 236 ∧ wd st 16 ≤ 4 ∧
  (wd4 st 0 + 2 ^ 128 * wd st 16) % p = accOf (r key) msg ∧
  r key = wd4 st 20 ∧
  (wd st 20 < 2 ^ 28 ∧ wd st 24 < 2 ^ 28 ∧ wd st 28 < 2 ^ 28 ∧ wd st 32 < 2 ^ 28 ∧
    wd st 24 % 4 = 0 ∧ wd st 28 % 4 = 0 ∧ wd st 32 % 4 = 0) ∧
  s key = wd4 st 192 ∧
  wd st 224 = msg.length % 16 ∧
  ∀ j, j < msg.length % 16 → st[208 + j]! = msg[fullLen msg + j]!

theorem memBytes_get {mem : ByteArray} {a : UInt32} {n k : Nat} (hk : k < n) :
    (memBytes mem a n)[k]! = memByte mem (a + k.toUInt32) := by
  simp [memBytes, hk]

/-- A word of memory is the word of its bytes. -/
theorem wd_memBytes {mem : ByteArray} {a : UInt32} {n : Nat} (h : a.toNat + n ≤ mem.size)
    (htop : mem.size ≤ ramTop) (k : Nat) (hk : k + 4 ≤ n) (j : UInt32) (hj : j.toNat = k) :
    wd (memBytes mem a n) k = (rdRaw mem (UInt32.add a j) 4).toNat := by
  have ea : (UInt32.add a j).toNat = a.toNat + k := by rw [toNat_uadd, hj]; unfold ramTop at htop; omega
  show _ = (rdBytes mem (UInt32.add a j) 4).toNat
  rw [rd4_toNat (by rw [ea]; omega)]
  unfold wd
  have hb : ∀ i, i < 4 → (memBytes mem a n)[k + i]! = mem.get! (a.toNat + k + i) := by
    intro i hi
    rw [memBytes_get (by omega), memByte_def]
    · congr 1; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
    · rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
  rw [show (memBytes mem a n)[k]! = (memBytes mem a n)[k + 0]! from rfl, hb 0 (by omega), hb 1 (by omega),
    hb 2 (by omega), hb 3 (by omega), ea]
  rfl

/-! ## Clamping -/

theorem land_split (a b c d : Nat) (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  have hac : a &&& c < 2 ^ 32 := Nat.and_lt_two_pow a hc
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc, Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-- `leNat` of the first 16 bytes as four words. -/
theorem leNat_take16 (l : List UInt8) (hl : 16 ≤ l.length) : leNat (l.take 16) = wd4 l 0 := by
  match l, hl with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: t, _ =>
    simp only [List.take, leNat, List.foldr, wd4, wd, List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Nat.zero_add, Nat.reduceAdd]
    omega

theorem r_eq (key : List UInt8) (hk : key.length = 32) :
    r key = (wd key 0 &&& 0x0fffffff) + 2 ^ 32 * (wd key 4 &&& 0x0ffffffc) +
      2 ^ 64 * (wd key 8 &&& 0x0ffffffc) + 2 ^ 96 * (wd key 12 &&& 0x0ffffffc) := by
  unfold r
  rw [leNat_take16 key (by omega)]
  have hb : ∀ k, wd key k < 2 ^ 32 := by
    intro k; unfold wd
    have := key[k]!.toNat_lt; have := key[k + 1]!.toNat_lt; have := key[k + 2]!.toNat_lt
    have := key[k + 3]!.toNat_lt; omega
  unfold wd4 clampMask
  rw [show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
      0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) by decide]
  rw [show wd key 0 + 2 ^ 32 * wd key (0 + 4) + 2 ^ 64 * wd key (0 + 8) + 2 ^ 96 * wd key (0 + 12) =
      wd key 0 + 2 ^ 32 * (wd key 4 + 2 ^ 32 * (wd key 8 + 2 ^ 32 * wd key 12)) by simp; omega]
  rw [land_split _ _ _ _ (hb 0) (by decide)]
  have h1 : wd key 4 + 2 ^ 32 * (wd key 8 + 2 ^ 32 * wd key 12) < 2 ^ 96 := by
    have := hb 4; have := hb 8; have := hb 12; omega
  rw [land_split _ _ _ _ (hb 4) (by decide), land_split _ _ _ _ (hb 8) (by decide)]
  omega

theorem s_eq (key : List UInt8) (hk : key.length = 32) : s key = wd4 key 16 := by
  unfold s
  rw [leNat_take16 _ (by simp; omega)]
  unfold wd4 wd
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

end Solutions.OpensslPoly1305
