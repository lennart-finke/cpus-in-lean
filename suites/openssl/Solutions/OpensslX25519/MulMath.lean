import Solutions.OpensslX25519.AddSubMath
/-!
# The arithmetic of `fe_mul` and `fe_sq`

The ref10 multiplication over `ℤ`, with no machine involved: the schoolbook product `mulRaw` with the
`19`-fold of the limbs above `2^255` (`h[k] = Σ_{i+j=k} m·f[i]g[j] + 19·Σ_{i+j=k+10} m·f[i]g[j]`,
`m = 2` when `i` and `j` are both odd), then the carry chain `carryChain` of `curve25519.c`
(`carry0, carry4, carry1, carry5, carry2, carry6, carry3, carry7, carry4, carry8, carry9, carry0`,
each `carry = (h + 2^(s-1)) >> s`). `mulRaw f g` represents `f·g` modulo `p` (`mulRaw_val`, a ring
identity proved by `grind`), the chain changes the represented value by a multiple of `p`
(`carryChain_val`), and from the input bounds `MulIn` the chain's limbs satisfy `MulOut`
(`carryChain_bound`, by `omega` from the bounds of the hundred products).
-/
namespace Solutions.OpensslX25519
open Ssl.OpensslX25519

/-- Ten limbs over `ℤ`. -/
structure L10 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a5 : Int
  a6 : Int
  a7 : Int
  a8 : Int
  a9 : Int

/-- The integer the limbs represent in radix `2^25.5`. -/
def L10.val (v : L10) : Int :=
  v.a0 + v.a1 * 2 ^ 26 + v.a2 * 2 ^ 51 + v.a3 * 2 ^ 77 + v.a4 * 2 ^ 102 + v.a5 * 2 ^ 128 +
    v.a6 * 2 ^ 153 + v.a7 * 2 ^ 179 + v.a8 * 2 ^ 204 + v.a9 * 2 ^ 230

/-- The limb `i`. -/
def L10.get (v : L10) : Nat → Int
  | 0 => v.a0 | 1 => v.a1 | 2 => v.a2 | 3 => v.a3 | 4 => v.a4 | 5 => v.a5 | 6 => v.a6 | 7 => v.a7
  | 8 => v.a8 | _ => v.a9

/-- The schoolbook product with the `19`-fold (before any carry). -/
def mulRaw (f g : L10) : L10 where
  a0 := f.a0 * g.a0 + 19 * (2 * (f.a1 * g.a9) + f.a2 * g.a8 + 2 * (f.a3 * g.a7) + f.a4 * g.a6 + 2 * (f.a5 * g.a5) + f.a6 * g.a4 + 2 * (f.a7 * g.a3) + f.a8 * g.a2 + 2 * (f.a9 * g.a1))
  a1 := f.a0 * g.a1 + f.a1 * g.a0 + 19 * (f.a2 * g.a9 + f.a3 * g.a8 + f.a4 * g.a7 + f.a5 * g.a6 + f.a6 * g.a5 + f.a7 * g.a4 + f.a8 * g.a3 + f.a9 * g.a2)
  a2 := f.a0 * g.a2 + 2 * (f.a1 * g.a1) + f.a2 * g.a0 + 19 * (2 * (f.a3 * g.a9) + f.a4 * g.a8 + 2 * (f.a5 * g.a7) + f.a6 * g.a6 + 2 * (f.a7 * g.a5) + f.a8 * g.a4 + 2 * (f.a9 * g.a3))
  a3 := f.a0 * g.a3 + f.a1 * g.a2 + f.a2 * g.a1 + f.a3 * g.a0 + 19 * (f.a4 * g.a9 + f.a5 * g.a8 + f.a6 * g.a7 + f.a7 * g.a6 + f.a8 * g.a5 + f.a9 * g.a4)
  a4 := f.a0 * g.a4 + 2 * (f.a1 * g.a3) + f.a2 * g.a2 + 2 * (f.a3 * g.a1) + f.a4 * g.a0 + 19 * (2 * (f.a5 * g.a9) + f.a6 * g.a8 + 2 * (f.a7 * g.a7) + f.a8 * g.a6 + 2 * (f.a9 * g.a5))
  a5 := f.a0 * g.a5 + f.a1 * g.a4 + f.a2 * g.a3 + f.a3 * g.a2 + f.a4 * g.a1 + f.a5 * g.a0 + 19 * (f.a6 * g.a9 + f.a7 * g.a8 + f.a8 * g.a7 + f.a9 * g.a6)
  a6 := f.a0 * g.a6 + 2 * (f.a1 * g.a5) + f.a2 * g.a4 + 2 * (f.a3 * g.a3) + f.a4 * g.a2 + 2 * (f.a5 * g.a1) + f.a6 * g.a0 + 19 * (2 * (f.a7 * g.a9) + f.a8 * g.a8 + 2 * (f.a9 * g.a7))
  a7 := f.a0 * g.a7 + f.a1 * g.a6 + f.a2 * g.a5 + f.a3 * g.a4 + f.a4 * g.a3 + f.a5 * g.a2 + f.a6 * g.a1 + f.a7 * g.a0 + 19 * (f.a8 * g.a9 + f.a9 * g.a8)
  a8 := f.a0 * g.a8 + 2 * (f.a1 * g.a7) + f.a2 * g.a6 + 2 * (f.a3 * g.a5) + f.a4 * g.a4 + 2 * (f.a5 * g.a3) + f.a6 * g.a2 + 2 * (f.a7 * g.a1) + f.a8 * g.a0 + 19 * (2 * (f.a9 * g.a9))
  a9 := f.a0 * g.a9 + f.a1 * g.a8 + f.a2 * g.a7 + f.a3 * g.a6 + f.a4 * g.a5 + f.a5 * g.a4 + f.a6 * g.a3 + f.a7 * g.a2 + f.a8 * g.a1 + f.a9 * g.a0

/-- The part of the product above `2^255`, which the `19`-fold replaces. -/
def mulHi (f g : L10) : Int :=
  (2 * (f.a1 * g.a9) + f.a2 * g.a8 + 2 * (f.a3 * g.a7) + f.a4 * g.a6 + 2 * (f.a5 * g.a5) + f.a6 * g.a4 + 2 * (f.a7 * g.a3) + f.a8 * g.a2 + 2 * (f.a9 * g.a1)) * 2 ^ 0 +
    (f.a2 * g.a9 + f.a3 * g.a8 + f.a4 * g.a7 + f.a5 * g.a6 + f.a6 * g.a5 + f.a7 * g.a4 + f.a8 * g.a3 + f.a9 * g.a2) * 2 ^ 26 +
    (2 * (f.a3 * g.a9) + f.a4 * g.a8 + 2 * (f.a5 * g.a7) + f.a6 * g.a6 + 2 * (f.a7 * g.a5) + f.a8 * g.a4 + 2 * (f.a9 * g.a3)) * 2 ^ 51 +
    (f.a4 * g.a9 + f.a5 * g.a8 + f.a6 * g.a7 + f.a7 * g.a6 + f.a8 * g.a5 + f.a9 * g.a4) * 2 ^ 77 +
    (2 * (f.a5 * g.a9) + f.a6 * g.a8 + 2 * (f.a7 * g.a7) + f.a8 * g.a6 + 2 * (f.a9 * g.a5)) * 2 ^ 102 +
    (f.a6 * g.a9 + f.a7 * g.a8 + f.a8 * g.a7 + f.a9 * g.a6) * 2 ^ 128 +
    (2 * (f.a7 * g.a9) + f.a8 * g.a8 + 2 * (f.a9 * g.a7)) * 2 ^ 153 +
    (f.a8 * g.a9 + f.a9 * g.a8) * 2 ^ 179 +
    (2 * (f.a9 * g.a9)) * 2 ^ 204

theorem mulRaw_val (f g : L10) : f.val * g.val = (mulRaw f g).val + (2 ^ 255 - 19) * mulHi f g := by
  cases f; cases g
  simp only [L10.val, mulRaw, mulHi]
  grind

/-- One carry of a limb of `s + 1` bits: `(h + 2^s) >> (s + 1)`. -/
def cr (h : Int) (s : Nat) : Int := (h + 2 ^ s) / 2 ^ (s + 1)

/-- The carry chain of `fe_mul`/`fe_sq`. -/
def carryChain (h : L10) : L10 :=
  let c0 := cr h.a0 25
  let h1 := h.a1 + c0
  let h0 := h.a0 - c0 * 2 ^ 26
  let c4 := cr h.a4 25
  let h5 := h.a5 + c4
  let h4 := h.a4 - c4 * 2 ^ 26
  let c1 := cr h1 24
  let h2 := h.a2 + c1
  let h1 := h1 - c1 * 2 ^ 25
  let c5 := cr h5 24
  let h6 := h.a6 + c5
  let h5 := h5 - c5 * 2 ^ 25
  let c2 := cr h2 25
  let h3 := h.a3 + c2
  let h2 := h2 - c2 * 2 ^ 26
  let c6 := cr h6 25
  let h7 := h.a7 + c6
  let h6 := h6 - c6 * 2 ^ 26
  let c3 := cr h3 24
  let h4 := h4 + c3
  let h3 := h3 - c3 * 2 ^ 25
  let c7 := cr h7 24
  let h8 := h.a8 + c7
  let h7 := h7 - c7 * 2 ^ 25
  let c4 := cr h4 25
  let h5 := h5 + c4
  let h4 := h4 - c4 * 2 ^ 26
  let c8 := cr h8 25
  let h9 := h.a9 + c8
  let h8 := h8 - c8 * 2 ^ 26
  let c9 := cr h9 24
  let h0 := h0 + c9 * 19
  let h9 := h9 - c9 * 2 ^ 25
  let c0 := cr h0 25
  let h1 := h1 + c0
  let h0 := h0 - c0 * 2 ^ 26
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem carryChain_dvd (h : L10) : (2 ^ 255 - 19 : Int) ∣ h.val - (carryChain h).val := by
  cases h
  simp only [carryChain, L10.val]
  omega

/-- The input bounds `MulIn` as integer bounds (`⌊1.65·2^26⌋`, `⌊1.65·2^25⌋`). -/
def InB (f : L10) : Prop :=
  -110729625 ≤ f.a0 ∧ f.a0 ≤ 110729625 ∧
    -55364812 ≤ f.a1 ∧ f.a1 ≤ 55364812 ∧
    -110729625 ≤ f.a2 ∧ f.a2 ≤ 110729625 ∧
    -55364812 ≤ f.a3 ∧ f.a3 ≤ 55364812 ∧
    -110729625 ≤ f.a4 ∧ f.a4 ≤ 110729625 ∧
    -55364812 ≤ f.a5 ∧ f.a5 ≤ 55364812 ∧
    -110729625 ≤ f.a6 ∧ f.a6 ≤ 110729625 ∧
    -55364812 ≤ f.a7 ∧ f.a7 ≤ 55364812 ∧
    -110729625 ≤ f.a8 ∧ f.a8 ≤ 110729625 ∧
    -55364812 ≤ f.a9 ∧ f.a9 ≤ 55364812

/-- Bounds of the raw product limbs. -/
def RawB (h : L10) : Prop :=
  -1526500696134443485 ≤ h.a0 ∧ h.a0 ≤ 1526500696134443485 ∧
    -944100830127147000 ≤ h.a1 ∧ h.a1 ≤ 944100830127147000 ∧
    -1195452352106279851 ≤ h.a2 ∧ h.a2 ≤ 1195452352106279851 ∧
    -723401934772749000 ≤ h.a3 ∧ h.a3 ≤ 723401934772749000 ∧
    -864404008078116217 ≤ h.a4 ∧ h.a4 ≤ 864404008078116217 ∧
    -502703039418351000 ≤ h.a5 ∧ h.a5 ≤ 502703039418351000 ∧
    -533355664049952583 ≤ h.a6 ∧ h.a6 ≤ 533355664049952583 ∧
    -282004144063953000 ≤ h.a7 ∧ h.a7 ≤ 282004144063953000 ∧
    -202307320021788949 ≤ h.a8 ∧ h.a8 ≤ 202307320021788949 ∧
    -61305248709555000 ≤ h.a9 ∧ h.a9 ≤ 61305248709555000

theorem mul_le {a b A B : Int} (ha1 : -A ≤ a) (ha2 : a ≤ A) (hb1 : -B ≤ b) (hb2 : b ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have h1 : a.natAbs ≤ A.natAbs := by omega
  have h2 : b.natAbs ≤ B.natAbs := by omega
  have h3 : (a * b).natAbs ≤ A.natAbs * B.natAbs := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul h1 h2
  have h4 : (A * B).natAbs = A.natAbs * B.natAbs := Int.natAbs_mul A B
  have h5 : 0 ≤ A := by omega
  have h6 : 0 ≤ B := by omega
  have h7 : 0 ≤ A * B := Int.mul_nonneg h5 h6
  omega

theorem mulRaw_bound0 (f g : L10) (hf : InB f) (hg : InB g) :
    -1526500696134443485 ≤ (mulRaw f g).a0 ∧ (mulRaw f g).a0 ≤ 1526500696134443485 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p00 := mul_le f0 f0' g0 g0'
  have p19 := mul_le f1 f1' g9 g9'
  have p28 := mul_le f2 f2' g8 g8'
  have p37 := mul_le f3 f3' g7 g7'
  have p46 := mul_le f4 f4' g6 g6'
  have p55 := mul_le f5 f5' g5 g5'
  have p64 := mul_le f6 f6' g4 g4'
  have p73 := mul_le f7 f7' g3 g3'
  have p82 := mul_le f8 f8' g2 g2'
  have p91 := mul_le f9 f9' g1 g1'
  simp only [mulRaw]
  omega

theorem mulRaw_bound1 (f g : L10) (hf : InB f) (hg : InB g) :
    -944100830127147000 ≤ (mulRaw f g).a1 ∧ (mulRaw f g).a1 ≤ 944100830127147000 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p01 := mul_le f0 f0' g1 g1'
  have p10 := mul_le f1 f1' g0 g0'
  have p29 := mul_le f2 f2' g9 g9'
  have p38 := mul_le f3 f3' g8 g8'
  have p47 := mul_le f4 f4' g7 g7'
  have p56 := mul_le f5 f5' g6 g6'
  have p65 := mul_le f6 f6' g5 g5'
  have p74 := mul_le f7 f7' g4 g4'
  have p83 := mul_le f8 f8' g3 g3'
  have p92 := mul_le f9 f9' g2 g2'
  simp only [mulRaw]
  omega

theorem mulRaw_bound2 (f g : L10) (hf : InB f) (hg : InB g) :
    -1195452352106279851 ≤ (mulRaw f g).a2 ∧ (mulRaw f g).a2 ≤ 1195452352106279851 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p02 := mul_le f0 f0' g2 g2'
  have p11 := mul_le f1 f1' g1 g1'
  have p20 := mul_le f2 f2' g0 g0'
  have p39 := mul_le f3 f3' g9 g9'
  have p48 := mul_le f4 f4' g8 g8'
  have p57 := mul_le f5 f5' g7 g7'
  have p66 := mul_le f6 f6' g6 g6'
  have p75 := mul_le f7 f7' g5 g5'
  have p84 := mul_le f8 f8' g4 g4'
  have p93 := mul_le f9 f9' g3 g3'
  simp only [mulRaw]
  omega

theorem mulRaw_bound3 (f g : L10) (hf : InB f) (hg : InB g) :
    -723401934772749000 ≤ (mulRaw f g).a3 ∧ (mulRaw f g).a3 ≤ 723401934772749000 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p03 := mul_le f0 f0' g3 g3'
  have p12 := mul_le f1 f1' g2 g2'
  have p21 := mul_le f2 f2' g1 g1'
  have p30 := mul_le f3 f3' g0 g0'
  have p49 := mul_le f4 f4' g9 g9'
  have p58 := mul_le f5 f5' g8 g8'
  have p67 := mul_le f6 f6' g7 g7'
  have p76 := mul_le f7 f7' g6 g6'
  have p85 := mul_le f8 f8' g5 g5'
  have p94 := mul_le f9 f9' g4 g4'
  simp only [mulRaw]
  omega

theorem mulRaw_bound4 (f g : L10) (hf : InB f) (hg : InB g) :
    -864404008078116217 ≤ (mulRaw f g).a4 ∧ (mulRaw f g).a4 ≤ 864404008078116217 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p04 := mul_le f0 f0' g4 g4'
  have p13 := mul_le f1 f1' g3 g3'
  have p22 := mul_le f2 f2' g2 g2'
  have p31 := mul_le f3 f3' g1 g1'
  have p40 := mul_le f4 f4' g0 g0'
  have p59 := mul_le f5 f5' g9 g9'
  have p68 := mul_le f6 f6' g8 g8'
  have p77 := mul_le f7 f7' g7 g7'
  have p86 := mul_le f8 f8' g6 g6'
  have p95 := mul_le f9 f9' g5 g5'
  simp only [mulRaw]
  omega

theorem mulRaw_bound5 (f g : L10) (hf : InB f) (hg : InB g) :
    -502703039418351000 ≤ (mulRaw f g).a5 ∧ (mulRaw f g).a5 ≤ 502703039418351000 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p05 := mul_le f0 f0' g5 g5'
  have p14 := mul_le f1 f1' g4 g4'
  have p23 := mul_le f2 f2' g3 g3'
  have p32 := mul_le f3 f3' g2 g2'
  have p41 := mul_le f4 f4' g1 g1'
  have p50 := mul_le f5 f5' g0 g0'
  have p69 := mul_le f6 f6' g9 g9'
  have p78 := mul_le f7 f7' g8 g8'
  have p87 := mul_le f8 f8' g7 g7'
  have p96 := mul_le f9 f9' g6 g6'
  simp only [mulRaw]
  omega

theorem mulRaw_bound6 (f g : L10) (hf : InB f) (hg : InB g) :
    -533355664049952583 ≤ (mulRaw f g).a6 ∧ (mulRaw f g).a6 ≤ 533355664049952583 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p06 := mul_le f0 f0' g6 g6'
  have p15 := mul_le f1 f1' g5 g5'
  have p24 := mul_le f2 f2' g4 g4'
  have p33 := mul_le f3 f3' g3 g3'
  have p42 := mul_le f4 f4' g2 g2'
  have p51 := mul_le f5 f5' g1 g1'
  have p60 := mul_le f6 f6' g0 g0'
  have p79 := mul_le f7 f7' g9 g9'
  have p88 := mul_le f8 f8' g8 g8'
  have p97 := mul_le f9 f9' g7 g7'
  simp only [mulRaw]
  omega

theorem mulRaw_bound7 (f g : L10) (hf : InB f) (hg : InB g) :
    -282004144063953000 ≤ (mulRaw f g).a7 ∧ (mulRaw f g).a7 ≤ 282004144063953000 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p07 := mul_le f0 f0' g7 g7'
  have p16 := mul_le f1 f1' g6 g6'
  have p25 := mul_le f2 f2' g5 g5'
  have p34 := mul_le f3 f3' g4 g4'
  have p43 := mul_le f4 f4' g3 g3'
  have p52 := mul_le f5 f5' g2 g2'
  have p61 := mul_le f6 f6' g1 g1'
  have p70 := mul_le f7 f7' g0 g0'
  have p89 := mul_le f8 f8' g9 g9'
  have p98 := mul_le f9 f9' g8 g8'
  simp only [mulRaw]
  omega

theorem mulRaw_bound8 (f g : L10) (hf : InB f) (hg : InB g) :
    -202307320021788949 ≤ (mulRaw f g).a8 ∧ (mulRaw f g).a8 ≤ 202307320021788949 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p08 := mul_le f0 f0' g8 g8'
  have p17 := mul_le f1 f1' g7 g7'
  have p26 := mul_le f2 f2' g6 g6'
  have p35 := mul_le f3 f3' g5 g5'
  have p44 := mul_le f4 f4' g4 g4'
  have p53 := mul_le f5 f5' g3 g3'
  have p62 := mul_le f6 f6' g2 g2'
  have p71 := mul_le f7 f7' g1 g1'
  have p80 := mul_le f8 f8' g0 g0'
  have p99 := mul_le f9 f9' g9 g9'
  simp only [mulRaw]
  omega

theorem mulRaw_bound9 (f g : L10) (hf : InB f) (hg : InB g) :
    -61305248709555000 ≤ (mulRaw f g).a9 ∧ (mulRaw f g).a9 ≤ 61305248709555000 := by
  obtain ⟨f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5, f5', f6, f6', f7, f7', f8, f8', f9, f9'⟩ := hf
  obtain ⟨g0, g0', g1, g1', g2, g2', g3, g3', g4, g4', g5, g5', g6, g6', g7, g7', g8, g8', g9, g9'⟩ := hg
  have p09 := mul_le f0 f0' g9 g9'
  have p18 := mul_le f1 f1' g8 g8'
  have p27 := mul_le f2 f2' g7 g7'
  have p36 := mul_le f3 f3' g6 g6'
  have p45 := mul_le f4 f4' g5 g5'
  have p54 := mul_le f5 f5' g4 g4'
  have p63 := mul_le f6 f6' g3 g3'
  have p72 := mul_le f7 f7' g2 g2'
  have p81 := mul_le f8 f8' g1 g1'
  have p90 := mul_le f9 f9' g0 g0'
  simp only [mulRaw]
  omega

theorem mulRaw_bound (f g : L10) (hf : InB f) (hg : InB g) : RawB (mulRaw f g) :=
  ⟨(mulRaw_bound0 f g hf hg).1, (mulRaw_bound0 f g hf hg).2, (mulRaw_bound1 f g hf hg).1,
    (mulRaw_bound1 f g hf hg).2, (mulRaw_bound2 f g hf hg).1, (mulRaw_bound2 f g hf hg).2,
    (mulRaw_bound3 f g hf hg).1, (mulRaw_bound3 f g hf hg).2, (mulRaw_bound4 f g hf hg).1,
    (mulRaw_bound4 f g hf hg).2, (mulRaw_bound5 f g hf hg).1, (mulRaw_bound5 f g hf hg).2,
    (mulRaw_bound6 f g hf hg).1, (mulRaw_bound6 f g hf hg).2, (mulRaw_bound7 f g hf hg).1,
    (mulRaw_bound7 f g hf hg).2, (mulRaw_bound8 f g hf hg).1, (mulRaw_bound8 f g hf hg).2,
    (mulRaw_bound9 f g hf hg).1, (mulRaw_bound9 f g hf hg).2⟩

/-- The output bounds `MulOut` for the limbs of the chain. -/
theorem carryChain_bound (h : L10) (hb : RawB h) (i : Nat) (hi : i < 10) :
    ((carryChain h).get i).natAbs * 100 ≤ 101 * 2 ^ (25 - i % 2) := by
  obtain ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ := hb
  cases h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [carryChain, L10.get, cr, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] at *
    omega

/-- The limbs of a word vector, as signed integers. -/
def lift (v : Array UInt32) : L10 :=
  ⟨v[0]!.toInt32.toInt, v[1]!.toInt32.toInt, v[2]!.toInt32.toInt, v[3]!.toInt32.toInt,
    v[4]!.toInt32.toInt, v[5]!.toInt32.toInt, v[6]!.toInt32.toInt, v[7]!.toInt32.toInt,
    v[8]!.toInt32.toInt, v[9]!.toInt32.toInt⟩

theorem lift_val (v : Array UInt32) : (lift v).val = feValI v := (feValI_eq v).symm

theorem inB_of_mulIn {v : Array UInt32} (h : MulIn v) : InB (lift v) := by
  have b0 := h.2 0 (by decide)
  have b1 := h.2 1 (by decide)
  have b2 := h.2 2 (by decide)
  have b3 := h.2 3 (by decide)
  have b4 := h.2 4 (by decide)
  have b5 := h.2 5 (by decide)
  have b6 := h.2 6 (by decide)
  have b7 := h.2 7 (by decide)
  have b8 := h.2 8 (by decide)
  have b9 := h.2 9 (by decide)
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reducePow, Nat.reduceMul] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  simp only [InB, lift]
  omega

theorem pI_eq : pI = 2 ^ 255 - 19 := by
  simp [pI, Ssl.Spec.X25519.p]

/-- `w` holds the limbs of the chain over the product of `fv` and `gv`: then it satisfies `MulOut`
and represents `fv·gv` modulo `p`. -/
theorem fe_mul_math (fv gv w : Array UInt32) (hf : MulIn fv) (hg : MulIn gv) (hw : w.size = 10)
    (hwi : ∀ i, i < 10 → w[i]!.toInt32.toInt = (carryChain (mulRaw (lift fv) (lift gv))).get i) :
    MulOut w ∧ feValI w % pI = feValI fv * feValI gv % pI := by
  have hr := mulRaw_bound _ _ (inB_of_mulIn hf) (inB_of_mulIn hg)
  refine ⟨⟨hw, fun i hi => ?_⟩, ?_⟩
  · rw [hwi i hi]
    exact carryChain_bound _ hr i hi
  · have ev : feValI w = (carryChain (mulRaw (lift fv) (lift gv))).val := by
      rw [feValI_eq, hwi 0 (by decide), hwi 1 (by decide), hwi 2 (by decide), hwi 3 (by decide),
        hwi 4 (by decide), hwi 5 (by decide), hwi 6 (by decide), hwi 7 (by decide), hwi 8 (by decide),
        hwi 9 (by decide)]
      rfl
    rw [ev, ← lift_val fv, ← lift_val gv, mulRaw_val, pI_eq]
    have hd := carryChain_dvd (mulRaw (lift fv) (lift gv))
    generalize (carryChain (mulRaw (lift fv) (lift gv))).val = a at *
    generalize (mulRaw (lift fv) (lift gv)).val = b at *
    generalize mulHi (lift fv) (lift gv) = c
    omega

end Solutions.OpensslX25519
