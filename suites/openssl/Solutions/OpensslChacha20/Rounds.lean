import Ssl.Spec.Chacha
/-!
# The double round on sixteen named words

`dround` is `Spec.Chacha.doubleRound` on a state of sixteen words given one by one (`V16`), written
with the operations in the order the compiled code performs them (`doubleRound_toArr`).
-/
namespace Solutions.OpensslChacha20
open Ssl.Spec.Chacha

/-- Sixteen words. -/
structure V16 where
  x0 : UInt32
  x1 : UInt32
  x2 : UInt32
  x3 : UInt32
  x4 : UInt32
  x5 : UInt32
  x6 : UInt32
  x7 : UInt32
  x8 : UInt32
  x9 : UInt32
  x10 : UInt32
  x11 : UInt32
  x12 : UInt32
  x13 : UInt32
  x14 : UInt32
  x15 : UInt32

def V16.toArr (v : V16) : Array UInt32 :=
  #[v.x0, v.x1, v.x2, v.x3, v.x4, v.x5, v.x6, v.x7, v.x8, v.x9, v.x10, v.x11, v.x12, v.x13, v.x14, v.x15]

def V16.ofArr (s : Array UInt32) : V16 :=
  ⟨s[0]!, s[1]!, s[2]!, s[3]!, s[4]!, s[5]!, s[6]!, s[7]!, s[8]!, s[9]!, s[10]!, s[11]!, s[12]!, s[13]!,
    s[14]!, s[15]!⟩

theorem V16.toArr_ofArr (s : Array UInt32) (h : s.size = 16) : (V16.ofArr s).toArr = s := by
  apply Array.ext (by simp [V16.toArr, h])
  intro i h1 h2
  simp only [V16.toArr, V16.ofArr]
  rw [h] at h2
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
    i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [getElem!_pos, h]

theorem V16.toArr_size (v : V16) : v.toArr.size = 16 := rfl

/-- RFC 8439 §2.1, on four words. -/
def qr (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let va := a + b
  let vd := rotl (d ^^^ va) 16
  let vc := c + vd
  let vb := rotl (b ^^^ vc) 12
  let va := va + vb
  let vd := rotl (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotl (vb ^^^ vc) 7
  (va, vb, vc, vd)

/-- A column round and a diagonal round. -/
def dround (v : V16) : V16 :=
  let a := qr v.x0 v.x4 v.x8 v.x12
  let b := qr v.x1 v.x5 v.x9 v.x13
  let c := qr v.x2 v.x6 v.x10 v.x14
  let d := qr v.x3 v.x7 v.x11 v.x15
  let e := qr a.1 b.2.1 c.2.2.1 d.2.2.2
  let f := qr b.1 c.2.1 d.2.2.1 a.2.2.2
  let g := qr c.1 d.2.1 a.2.2.1 b.2.2.2
  let h := qr d.1 a.2.1 b.2.2.1 c.2.2.2
  ⟨e.1, f.1, g.1, h.1, h.2.1, e.2.1, f.2.1, g.2.1, g.2.2.1, h.2.2.1, e.2.2.1, f.2.2.1, f.2.2.2, g.2.2.2,
    h.2.2.2, e.2.2.2⟩

theorem qr_0_4_8_12 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 0 4 8 12 =
      #[(qr x0 x4 x8 x12).1, x1, x2, x3, (qr x0 x4 x8 x12).2.1, x5, x6, x7, (qr x0 x4 x8 x12).2.2.1, x9, x10, x11, (qr x0 x4 x8 x12).2.2.2, x13, x14, x15] := by
  simp [quarterRound, qr]

theorem qr_1_5_9_13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 1 5 9 13 =
      #[x0, (qr x1 x5 x9 x13).1, x2, x3, x4, (qr x1 x5 x9 x13).2.1, x6, x7, x8, (qr x1 x5 x9 x13).2.2.1, x10, x11, x12, (qr x1 x5 x9 x13).2.2.2, x14, x15] := by
  simp [quarterRound, qr]

theorem qr_2_6_10_14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 2 6 10 14 =
      #[x0, x1, (qr x2 x6 x10 x14).1, x3, x4, x5, (qr x2 x6 x10 x14).2.1, x7, x8, x9, (qr x2 x6 x10 x14).2.2.1, x11, x12, x13, (qr x2 x6 x10 x14).2.2.2, x15] := by
  simp [quarterRound, qr]

theorem qr_3_7_11_15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 3 7 11 15 =
      #[x0, x1, x2, (qr x3 x7 x11 x15).1, x4, x5, x6, (qr x3 x7 x11 x15).2.1, x8, x9, x10, (qr x3 x7 x11 x15).2.2.1, x12, x13, x14, (qr x3 x7 x11 x15).2.2.2] := by
  simp [quarterRound, qr]

theorem qr_0_5_10_15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 0 5 10 15 =
      #[(qr x0 x5 x10 x15).1, x1, x2, x3, x4, (qr x0 x5 x10 x15).2.1, x6, x7, x8, x9, (qr x0 x5 x10 x15).2.2.1, x11, x12, x13, x14, (qr x0 x5 x10 x15).2.2.2] := by
  simp [quarterRound, qr]

theorem qr_1_6_11_12 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 1 6 11 12 =
      #[x0, (qr x1 x6 x11 x12).1, x2, x3, x4, x5, (qr x1 x6 x11 x12).2.1, x7, x8, x9, x10, (qr x1 x6 x11 x12).2.2.1, (qr x1 x6 x11 x12).2.2.2, x13, x14, x15] := by
  simp [quarterRound, qr]

theorem qr_2_7_8_13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 2 7 8 13 =
      #[x0, x1, (qr x2 x7 x8 x13).1, x3, x4, x5, x6, (qr x2 x7 x8 x13).2.1, (qr x2 x7 x8 x13).2.2.1, x9, x10, x11, x12, (qr x2 x7 x8 x13).2.2.2, x14, x15] := by
  simp [quarterRound, qr]

theorem qr_3_4_9_14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    quarterRound #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] 3 4 9 14 =
      #[x0, x1, x2, (qr x3 x4 x9 x14).1, (qr x3 x4 x9 x14).2.1, x5, x6, x7, x8, (qr x3 x4 x9 x14).2.2.1, x10, x11, x12, x13, (qr x3 x4 x9 x14).2.2.2, x15] := by
  simp [quarterRound, qr]

theorem doubleRound_toArr (v : V16) : doubleRound v.toArr = (dround v).toArr := by
  simp only [doubleRound, V16.toArr, qr_0_4_8_12, qr_1_5_9_13, qr_2_6_10_14, qr_3_7_11_15, qr_0_5_10_15,
    qr_1_6_11_12, qr_2_7_8_13, qr_3_4_9_14]
  rfl

end Solutions.OpensslChacha20
