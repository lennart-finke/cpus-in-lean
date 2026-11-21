import Ssl.Harness
/-!
# Memory: reads, writes and frames

The memory of the model is a `ByteArray`; `rdBytes`/`wrBytes` access it little-endian, and the
harness reads it byte by byte (`memByte`, `memBytes`). This file relates the two views:

* `memByte_wrBytes1`, `memByte_wrBytes4`: the bytes after a 1- or 4-byte store (the frame rule: a
  store changes only its own bytes);
* `rdBytes1_eq`, `rdBytes4_eq`: a load as the bytes it reads;
* `memBytes_eq_iff`, `memBytes_congr`: `memBytes`, which the statements use, pointwise.
-/
namespace Solutions.Logic
open X86 Ssl

theorem ByteArray.size_set! (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  cases a; simp [ByteArray.set!, ByteArray.size]

theorem ByteArray.get!_set! (a : ByteArray) (i j : Nat) (v : UInt8) :
    (a.set! i v).get! j = if i = j ∧ i < a.size then v else a.get! j := by
  cases a with
  | mk d =>
  simp only [ByteArray.set!, ByteArray.get!, ByteArray.size, Array.set!]
  by_cases h : i = j
  · subst h
    by_cases hi : i < d.size <;> simp [hi]
  · simp [h, getElem!_def]

theorem toNat_add_of_lt {a : UInt32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + k.toUInt32).toNat = a.toNat + k := by
  simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt h]

/-- A byte inside memory. -/
theorem memByte_def {mem : ByteArray} {a : UInt32} (h : a.toNat < mem.size) :
    memByte mem a = mem.get! a.toNat := by
  unfold memByte rdBytes
  have : a.toNat + (1 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  simp

theorem rdBytes1_eq {mem : ByteArray} {a : UInt32} (h : a.toNat < mem.size) :
    rdBytes mem a 1 = (memByte mem a).toUInt32 := by
  rw [memByte_def h]
  unfold rdBytes
  have : a.toNat + (1 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  simp

theorem rdBytes4_eq {mem : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    rdBytes mem a 4 = (mem.get! a.toNat).toUInt32 ||| ((mem.get! (a.toNat + 1)).toUInt32 <<< 8) |||
      ((mem.get! (a.toNat + 2)).toUInt32 <<< 16) ||| ((mem.get! (a.toNat + 3)).toUInt32 <<< 24) := by
  unfold rdBytes
  have : a.toNat + (4 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  rfl

theorem wrBytes1_eq {mem : ByteArray} {a v : UInt32} (h : a.toNat < mem.size) :
    wrBytes mem a 1 v = mem.set! a.toNat v.toUInt8 := by
  unfold wrBytes
  have : a.toNat + (1 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  rfl

theorem wrBytes4_eq {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    wrBytes mem a 4 v = (((mem.set! a.toNat v.toUInt8).set! (a.toNat + 1) (v >>> 8).toUInt8).set!
      (a.toNat + 2) (v >>> 16).toUInt8).set! (a.toNat + 3) (v >>> 24).toUInt8 := by
  unfold wrBytes
  have : a.toNat + (4 : UInt32).toNat ≤ mem.size := by simp; omega
  simp only [this, ite_true]
  rfl

theorem size_wrBytes1 {mem : ByteArray} {a v : UInt32} (h : a.toNat < mem.size) :
    (wrBytes mem a 1 v).size = mem.size := by
  rw [wrBytes1_eq h, ByteArray.size_set!]

theorem size_wrBytes4 {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    (wrBytes mem a 4 v).size = mem.size := by
  rw [wrBytes4_eq h]; simp only [ByteArray.size_set!]

theorem get!_wrBytes1 {mem : ByteArray} {a v : UInt32} (h : a.toNat < mem.size) (j : Nat) :
    (wrBytes mem a 1 v).get! j = if j = a.toNat then v.toUInt8 else mem.get! j := by
  rw [wrBytes1_eq h, ByteArray.get!_set!]
  by_cases hj : j = a.toNat
  · simp [hj, h]
  · simp only [hj, ite_false]
    rw [if_neg (by omega)]

theorem get!_wrBytes4 {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) (j : Nat) :
    (wrBytes mem a 4 v).get! j =
      if j = a.toNat then v.toUInt8 else if j = a.toNat + 1 then (v >>> 8).toUInt8
      else if j = a.toNat + 2 then (v >>> 16).toUInt8 else if j = a.toNat + 3 then (v >>> 24).toUInt8
      else mem.get! j := by
  rw [wrBytes4_eq h]
  simp only [ByteArray.get!_set!, ByteArray.size_set!]
  by_cases h0 : j = a.toNat
  · subst h0; simp; omega
  by_cases h1 : j = a.toNat + 1
  · subst h1; simp; omega
  by_cases h2 : j = a.toNat + 2
  · subst h2; simp; omega
  by_cases h3 : j = a.toNat + 3
  · subst h3; simp; omega
  simp only [h0, h1, h2, h3, ite_false]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `X86` elaborates `<<<`/`>>>` through the homogeneous classes (as `X86.Proofs.Basic` notes). -/
theorem shl32 (a b : UInt32) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl
theorem shr32 (a b : UInt32) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl
theorem shl8 (a b : UInt8) : ShiftLeft.shiftLeft a b = HShiftLeft.hShiftLeft a b := rfl
theorem shr8 (a b : UInt8) : ShiftRight.shiftRight a b = HShiftRight.hShiftRight a b := rfl

/-- Reassembling the four bytes of a word. -/
theorem join_bytes (v : UInt32) :
    v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) ||| ((v >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [shl32, shr32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  have h8 : (UInt32.toBitVec 8 % 32).toNat = 8 := rfl
  have h16 : (UInt32.toBitVec 16 % 32).toNat = 16 := rfl
  have h24 : (UInt32.toBitVec 24 % 32).toNat = 24 := rfl
  simp only [h8, h16, h24, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32)) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h, hi, show i < 16 by omega, show i < 24 by omega]
  · simp [h1, h2, hi, show ¬ i < 8 by omega, show i - 8 < 8 by omega, show i < 24 by omega,
      show 8 + (i - 8) = i by omega, show i - 8 < 32 by omega]
  · simp [h1, h2, hi, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i - 16 < 8 by omega,
      show ¬ i - 8 < 8 by omega, show 16 + (i - 16) = i by omega, show i - 16 < 32 by omega]
  · simp [h1, h2, hi, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega,
      show i - 24 < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show 24 + (i - 24) = i by omega, show i - 24 < 32 by omega]

/-- A word reads back what was stored. -/
theorem rdBytes4_wrBytes4_self {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) :
    rdBytes (wrBytes mem a 4 v) a 4 = v := by
  rw [rdBytes4_eq (by rw [size_wrBytes4 h]; exact h)]
  simp only [get!_wrBytes4 h, show a.toNat + 1 ≠ a.toNat by omega, show a.toNat + 2 ≠ a.toNat by omega,
    show a.toNat + 2 ≠ a.toNat + 1 by omega, show a.toNat + 3 ≠ a.toNat by omega,
    show a.toNat + 3 ≠ a.toNat + 1 by omega, show a.toNat + 3 ≠ a.toNat + 2 by omega, ite_true, ite_false]
  exact join_bytes v

/-- A word load disjoint from a word store reads the old word. -/
theorem rdBytes4_wrBytes4_other {mem : ByteArray} {a b v : UInt32} (ha : a.toNat + 4 ≤ mem.size)
    (hb : b.toNat + 4 ≤ mem.size) (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdBytes (wrBytes mem a 4 v) b 4 = rdBytes mem b 4 := by
  rw [rdBytes4_eq (by rw [size_wrBytes4 ha]; exact hb), rdBytes4_eq hb]
  simp only [get!_wrBytes4 ha]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A byte load disjoint from a word store reads the old byte. -/
theorem rdBytes1_wrBytes4_other {mem : ByteArray} {a b v : UInt32} (ha : a.toNat + 4 ≤ mem.size)
    (hb : b.toNat < mem.size) (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat < a.toNat) :
    rdBytes (wrBytes mem a 4 v) b 1 = rdBytes mem b 1 := by
  rw [rdBytes1_eq (by rw [size_wrBytes4 ha]; exact hb), rdBytes1_eq hb,
    memByte_def (by rw [size_wrBytes4 ha]; exact hb), memByte_def hb, get!_wrBytes4 ha]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A word load disjoint from a byte store reads the old word. -/
theorem rdBytes4_wrBytes1_other {mem : ByteArray} {a b v : UInt32} (ha : a.toNat < mem.size)
    (hb : b.toNat + 4 ≤ mem.size) (hd : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    rdBytes (wrBytes mem a 1 v) b 4 = rdBytes mem b 4 := by
  rw [rdBytes4_eq (by rw [size_wrBytes1 ha]; exact hb), rdBytes4_eq hb]
  simp only [get!_wrBytes1 ha]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A byte load reads back a byte store. -/
theorem rdBytes1_wrBytes1_self {mem : ByteArray} {a v : UInt32} (h : a.toNat < mem.size) :
    rdBytes (wrBytes mem a 1 v) a 1 = v.toUInt8.toUInt32 := by
  rw [rdBytes1_eq (by rw [size_wrBytes1 h]; exact h), memByte_def (by rw [size_wrBytes1 h]; exact h),
    get!_wrBytes1 h]
  simp

/-- A byte load disjoint from a byte store reads the old byte. -/
theorem rdBytes1_wrBytes1_other {mem : ByteArray} {a b v : UInt32} (ha : a.toNat < mem.size)
    (hb : b.toNat < mem.size) (hd : a.toNat ≠ b.toNat) :
    rdBytes (wrBytes mem a 1 v) b 1 = rdBytes mem b 1 := by
  rw [rdBytes1_eq (by rw [size_wrBytes1 ha]; exact hb), rdBytes1_eq hb,
    memByte_def (by rw [size_wrBytes1 ha]; exact hb), memByte_def hb, get!_wrBytes1 ha]
  rw [if_neg (by omega)]

/-- Two memories with the same size and bytes are equal. -/
theorem bytes_ext {a b : ByteArray} (hs : a.size = b.size) (h : ∀ i, i < a.size → a.get! i = b.get! i) :
    a = b := by
  cases a with
  | mk da =>
  cases b with
  | mk db =>
  simp only [ByteArray.size] at hs
  congr 1
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simp only [ByteArray.get!] at this
  simpa [getElem!_pos, h1, h2] using this

/-- A byte store and a word store at disjoint places commute. -/
theorem wrBytes_comm14 {mem : ByteArray} {t a v w : UInt32} (ht : t.toNat + 4 ≤ mem.size)
    (ha : a.toNat < mem.size) (hd : a.toNat < t.toNat ∨ t.toNat + 4 ≤ a.toNat) :
    wrBytes (wrBytes mem t 4 v) a 1 w = wrBytes (wrBytes mem a 1 w) t 4 v := by
  have s1 := size_wrBytes4 (v := v) ht
  have s2 := size_wrBytes1 (v := w) ha
  apply bytes_ext
  · rw [size_wrBytes1 (by rw [s1]; exact ha), s1, size_wrBytes4 (by rw [s2]; exact ht), s2]
  · intro j _
    rw [get!_wrBytes1 (mem := wrBytes mem t 4 v) (by rw [s1]; exact ha),
      get!_wrBytes4 (mem := wrBytes mem a 1 w) (by rw [s2]; exact ht),
      get!_wrBytes4 (mem := mem) ht, get!_wrBytes1 (mem := mem) ha]
    by_cases h0 : j = a.toNat
    · subst h0
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [if_neg h0, if_neg h0]

/-- A word load is determined by the four bytes it reads. -/
theorem rdBytes4_congr {m m' : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ m.size) (h' : a.toNat + 4 ≤ m'.size)
    (hb : ∀ k, k < 4 → m.get! (a.toNat + k) = m'.get! (a.toNat + k)) : rdBytes m a 4 = rdBytes m' a 4 := by
  rw [rdBytes4_eq h, rdBytes4_eq h']
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

/-! ## The harness's byte view -/

theorem memByte_wrBytes1 {mem : ByteArray} {a v : UInt32} (h : a.toNat < mem.size) {b : UInt32}
    (hb : b.toNat < mem.size) :
    memByte (wrBytes mem a 1 v) b = if b = a then v.toUInt8 else memByte mem b := by
  rw [memByte_def (by rw [size_wrBytes1 h]; exact hb), memByte_def hb, get!_wrBytes1 h]
  by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg (fun e => hab (UInt32.toNat_inj.mp e)), if_neg hab]

theorem memByte_wrBytes4 {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) {b : UInt32}
    (hb : b.toNat < mem.size) :
    memByte (wrBytes mem a 4 v) b =
      if b.toNat = a.toNat then v.toUInt8 else if b.toNat = a.toNat + 1 then (v >>> 8).toUInt8
      else if b.toNat = a.toNat + 2 then (v >>> 16).toUInt8 else if b.toNat = a.toNat + 3 then (v >>> 24).toUInt8
      else memByte mem b := by
  rw [memByte_def (by rw [size_wrBytes4 h]; exact hb), memByte_def hb, get!_wrBytes4 h]

/-- A word store leaves the bytes outside it. -/
theorem memByte_wrBytes4_other {mem : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ mem.size) {b : UInt32}
    (hb : b.toNat < mem.size) (hd : b.toNat < a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    memByte (wrBytes mem a 4 v) b = memByte mem b := by
  rw [memByte_wrBytes4 h hb, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem memBytes_length (mem : ByteArray) (a : UInt32) (n : Nat) : (memBytes mem a n).length = n := by
  simp [memBytes]

theorem memBytes_getElem (mem : ByteArray) (a : UInt32) (n i : Nat) (h : i < (memBytes mem a n).length) :
    (memBytes mem a n)[i] = memByte mem (a + i.toUInt32) := by
  simp [memBytes]

/-- `memBytes` pointwise. -/
theorem memBytes_eq_iff {mem : ByteArray} {a : UInt32} {n : Nat} {l : List UInt8} :
    memBytes mem a n = l ↔ l.length = n ∧ ∀ i (h : i < l.length), memByte mem (a + i.toUInt32) = l[i] := by
  constructor
  · rintro rfl
    exact ⟨memBytes_length mem a n, fun i h => (memBytes_getElem mem a n i h).symm⟩
  · rintro ⟨hl, hi⟩
    apply List.ext_getElem
    · rw [memBytes_length, hl]
    · intro i h₁ h₂
      rw [memBytes_getElem, hi i h₂]

theorem memBytes_congr {mem mem' : ByteArray} {a : UInt32} {n : Nat}
    (h : ∀ i, i < n → memByte mem' (a + i.toUInt32) = memByte mem (a + i.toUInt32)) :
    memBytes mem' a n = memBytes mem a n := by
  simp only [memBytes]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- The words of `memWords` one by one. -/
theorem memWords_get {mem : ByteArray} {a : UInt32} {n : Nat} {ws : Array UInt32}
    (h : memWords mem a n = ws) (i : Nat) (hi : i < n) (hw : i < ws.size) :
    memWord mem (a + 4 * i.toUInt32) = ws[i] := by
  subst h
  simp [memWords]

end Solutions.Logic
