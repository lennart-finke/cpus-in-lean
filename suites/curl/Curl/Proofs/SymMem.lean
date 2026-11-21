import Solutions.Logic.Mem
import Solutions.Logic.Decode
import Solutions.Exec.Mem
import Curl.Proofs.Code
/-!
# Memory of the curl image: stores that keep the code, frames

`CMem.wr g a n v h` is a store of 1, 2 or 4 bytes outside the code range, as a new `CMem` (so that
instruction fetches still read the code directly). `Frame g g' lo hi` says that `g'` differs from
`g` at most in the bytes `[lo, hi)`: the contracts of the called functions are stated with it.
Loads are related to stores and frames by `rdBytes_congr`.
-/
namespace Curl.Proofs
open X86 Ssl Solutions.Logic Solutions.Exec Curl.Hostcheck

theorem img_base_toNat : Image.base.toNat = 0x100000 := rfl
theorem img_size_eq : Image.size = 3971 := rfl

/-- A store of `n` bytes at `a` (`n` is 1, 2 or 4) is inside memory and outside the code. -/
def StOk (mem : ByteArray) (a n : UInt32) : Prop :=
  (n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 4) ∧ a.toNat + n.toNat ≤ mem.size ∧
    (a.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 3971 ≤ a.toNat)

theorem wrBytes_get!_out {mem : ByteArray} {a n v : UInt32} (hn : n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 4)
    (h : a.toNat + n.toNat ≤ mem.size) {j : Nat} (hj : j < a.toNat ∨ a.toNat + n.toNat ≤ j) :
    (wrBytes mem a n v).get! j = mem.get! j := by
  rcases hn with hn | hn | hn
  · have : n = 1 := UInt32.toNat_inj.mp (by simpa using hn)
    subst this
    rw [get!_wrBytes1 (by simp at h; omega), if_neg (by simp at hj; omega)]
  · have : n = 2 := UInt32.toNat_inj.mp (by simpa using hn)
    subst this
    unfold wrBytes
    simp only [show a.toNat + (2 : UInt32).toNat ≤ mem.size from h, ite_true]
    simp only [show ((2 : UInt32) == 1) = false by decide, show ((2 : UInt32) == 2) = true by decide,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [ByteArray.get!_set!, ByteArray.size_set!]
    simp at hj
    rw [if_neg (by omega), if_neg (by omega)]
  · have : n = 4 := UInt32.toNat_inj.mp (by simpa using hn)
    subst this
    simp at hj h
    rw [get!_wrBytes4 (by simpa using h)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The memory after a store outside the code. -/
def CMem.wr (g : CMem) (a n v : UInt32) (h : StOk g.mem a n) : CMem where
  mem := wrBytes g.mem a n v
  fits := by rw [size_wrBytes]; exact g.fits
  ok := fun i hi => by
    have := g.ok i hi
    rw [wrBytes_get!_out h.1 h.2.1 (by
      have := h.2.2; simp only [img_base_toNat, img_size_eq] at *; omega)]
    exact this

theorem CMem.wr_get (g : CMem) (a n v : UInt32) (h : StOk g.mem a n) :
    (CMem.wr g a n v h).get = wrBytes g.get a n v := rfl

theorem CMem.wr_size (g : CMem) (a n v : UInt32) (h : StOk g.mem a n) :
    (CMem.wr g a n v h).get.size = g.get.size := size_wrBytes _ _ _ _

/-! ## Loads -/

theorem rdBytes_congr {m m' : ByteArray} {b k : UInt32} (hk : k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 4)
    (h : b.toNat + k.toNat ≤ m.size) (h' : b.toNat + k.toNat ≤ m'.size)
    (he : ∀ j, b.toNat ≤ j → j < b.toNat + k.toNat → m.get! j = m'.get! j) :
    rdBytes m b k = rdBytes m' b k := by
  unfold rdBytes
  simp only [h, h', ite_true]
  rcases hk with hk | hk | hk
  · have : k = 1 := UInt32.toNat_inj.mp (by simpa using hk)
    subst this
    simp only [show ((1 : UInt32) == 1) = true by decide, ite_true]
    rw [he b.toNat (Nat.le_refl _) (by simp)]
  · have : k = 2 := UInt32.toNat_inj.mp (by simpa using hk)
    subst this
    simp only [show ((2 : UInt32) == 1) = false by decide, show ((2 : UInt32) == 2) = true by decide,
      Bool.false_eq_true, ite_false, ite_true]
    rw [he b.toNat (Nat.le_refl _) (by simp), he (b.toNat + 1) (by omega) (by simp)]
  · have : k = 4 := UInt32.toNat_inj.mp (by simpa using hk)
    subst this
    simp only [show ((4 : UInt32) == 1) = false by decide, show ((4 : UInt32) == 2) = false by decide,
      Bool.false_eq_true, ite_false]
    rw [he b.toNat (Nat.le_refl _) (by simp), he (b.toNat + 1) (by omega) (by simp),
      he (b.toNat + 2) (by omega) (by simp), he (b.toNat + 3) (by omega) (by simp)]

/-- A load disjoint from a store reads the older memory. -/
theorem rdRaw_wr_other (g : CMem) (a n v : UInt32) (h : StOk g.mem a n) {b k : UInt32}
    (hk : k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 4) (hb : b.toNat + k.toNat ≤ g.get.size)
    (hd : b.toNat + k.toNat ≤ a.toNat ∨ a.toNat + n.toNat ≤ b.toNat) :
    rdRaw (CMem.wr g a n v h).get b k = rdRaw g.get b k := by
  unfold rdRaw
  rw [CMem.wr_get]
  apply rdBytes_congr hk (by rw [size_wrBytes]; exact hb) hb
  intro j h1 h2
  exact wrBytes_get!_out h.1 h.2.1 (by omega)

theorem rdRaw_wr_same4 (g : CMem) (a b v : UInt32) (h : StOk g.mem a 4) (hab : a.toNat = b.toNat) :
    rdRaw (CMem.wr g a 4 v h).get b 4 = v := by
  have := UInt32.toNat_inj.mp hab; subst this
  exact rdBytes4_wrBytes4_self (by have := h.2.1; simpa using this)

theorem rdRaw_wr_same1 (g : CMem) (a b v : UInt32) (h : StOk g.mem a 1) (hab : a.toNat = b.toNat) :
    rdRaw (CMem.wr g a 1 v h).get b 1 = v.toUInt8.toUInt32 := by
  have := UInt32.toNat_inj.mp hab; subst this
  exact rdBytes1_wrBytes1_self (by have := h.2.1; simp at this; omega)

/-! ## Frames -/

/-- `g'` differs from `g` at most in the bytes `[lo, hi)`. -/
def Frame (g g' : CMem) (lo hi : Nat) : Prop :=
  g'.get.size = g.get.size ∧ ∀ j, j < lo ∨ hi ≤ j → g'.get.get! j = g.get.get! j

theorem Frame.refl (g : CMem) (lo hi : Nat) : Frame g g lo hi := ⟨rfl, fun _ _ => rfl⟩

theorem Frame.trans {g g' g'' : CMem} {lo hi lo' hi' : Nat} (h : Frame g g' lo hi) (h' : Frame g' g'' lo' hi')
    {L H : Nat} (hL : L ≤ lo ∧ L ≤ lo') (hH : hi ≤ H ∧ hi' ≤ H) : Frame g g'' L H :=
  ⟨h'.1.trans h.1, fun j hj => (h'.2 j (by omega)).trans (h.2 j (by omega))⟩

theorem Frame.mono {g g' : CMem} {lo hi L H : Nat} (h : Frame g g' lo hi) (hL : L ≤ lo) (hH : hi ≤ H) :
    Frame g g' L H :=
  ⟨h.1, fun j hj => h.2 j (by omega)⟩

theorem Frame.wr (g : CMem) (a n v : UInt32) (h : StOk g.mem a n) {lo hi : Nat}
    (hl : lo ≤ a.toNat) (hh : a.toNat + n.toNat ≤ hi) : Frame g (CMem.wr g a n v h) lo hi :=
  ⟨CMem.wr_size g a n v h, fun j hj => wrBytes_get!_out h.1 h.2.1 (by omega)⟩

/-- A store inside the frame of `g` keeps the frame. -/
theorem Frame.wr_right {g g' : CMem} {lo hi : Nat} (hf : Frame g g' lo hi) (a n v : UInt32)
    (h : StOk g'.mem a n) (hl : lo ≤ a.toNat) (hh : a.toNat + n.toNat ≤ hi) :
    Frame g (CMem.wr g' a n v h) lo hi :=
  hf.trans (Frame.wr g' a n v h hl hh) ⟨Nat.le_refl _, Nat.le_refl _⟩ ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- A load outside the frame reads the older memory. -/
theorem rdRaw_frame {g g' : CMem} {lo hi : Nat} (hf : Frame g g' lo hi) {b k : UInt32}
    (hk : k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 4) (hb : b.toNat + k.toNat ≤ g.get.size)
    (hd : b.toNat + k.toNat ≤ lo ∨ hi ≤ b.toNat) :
    rdRaw g'.get b k = rdRaw g.get b k := by
  unfold rdRaw
  apply rdBytes_congr hk (by rw [hf.1]; exact hb) hb
  intro j h1 h2
  exact hf.2 j (by omega)

/-- A byte outside the frame is the older byte. -/
theorem memByte_frame {g g' : CMem} {lo hi : Nat} (hf : Frame g g' lo hi) {a : UInt32}
    (ha : a.toNat < g.get.size) (hd : a.toNat < lo ∨ hi ≤ a.toNat) :
    memByte g'.get a = memByte g.get a := by
  rw [memByte_def (by rw [hf.1]; exact ha), memByte_def ha, hf.2 _ hd]

/-! ## Code reads -/

/-- A byte of the code. -/
theorem rdBytes_code1 (g : CMem) (a : UInt32) (h1 : 0x100000 ≤ a.toNat) (h2 : a.toNat < 0x100000 + 3971) :
    rdBytes g.get a 1 = (Image.byte (a.toNat - Image.base.toNat)).toUInt32 := by
  have e := rdBytes_codeMem g a 1
  have hc : (1 : UInt32) = 1 ∧ Image.base.toNat ≤ a.toNat ∧ a.toNat < Image.base.toNat + Image.size :=
    ⟨rfl, by rw [img_base_toNat]; exact h1, by rw [img_base_toNat, img_size_eq]; exact h2⟩
  rw [if_pos hc] at e
  exact e

/-- The little-endian word of the code at offset `i`. -/
def codeWord (i : Nat) : UInt32 :=
  (Image.byte i).toUInt32 ||| ShiftLeft.shiftLeft (Image.byte (i + 1)).toUInt32 8 |||
    ShiftLeft.shiftLeft (Image.byte (i + 2)).toUInt32 16 ||| ShiftLeft.shiftLeft (Image.byte (i + 3)).toUInt32 24

theorem codeMem_get_k (g : CMem) (a : UInt32) (k : Nat) (h1 : Image.base.toNat ≤ a.toNat)
    (h2 : a.toNat + k < Image.base.toNat + Image.size) :
    g.get.get! (a.toNat + k) = Image.byte (a.toNat - Image.base.toNat + k) := by
  have := g.ok (a.toNat - Image.base.toNat + k) (by omega)
  have e : Image.base.toNat + (a.toNat - Image.base.toNat + k) = a.toNat + k := by omega
  rw [e] at this
  exact this

theorem codeMem_get_0 (g : CMem) (a : UInt32) (h1 : Image.base.toNat ≤ a.toNat)
    (h2 : a.toNat < Image.base.toNat + Image.size) :
    g.get.get! a.toNat = Image.byte (a.toNat - Image.base.toNat) := by
  have := g.ok (a.toNat - Image.base.toNat) (by omega)
  have e : Image.base.toNat + (a.toNat - Image.base.toNat) = a.toNat := by omega
  rw [e] at this
  exact this

theorem rdBytes_code4 (g : CMem) (a : UInt32) (h1 : Image.base.toNat ≤ a.toNat)
    (h2 : a.toNat + 4 ≤ Image.base.toNat + Image.size) :
    rdBytes g.get a 4 = codeWord (a.toNat - Image.base.toNat) := by
  have hs : a.toNat + 4 ≤ g.get.size := Nat.le_trans h2 g.fits
  rw [rdBytes4_eq hs]
  unfold codeWord
  rw [codeMem_get_0 g a h1 (by omega), codeMem_get_k g a 1 h1 (by omega), codeMem_get_k g a 2 h1 (by omega),
    codeMem_get_k g a 3 h1 (by omega)]

end Curl.Proofs
