import X86.Float80
/-!
# x87 transcendental functions, correctly rounded

F2XM1, FYL2X, FYL2XP1, FPATAN, FSIN, FCOS, FSINCOS and FPTAN deliver the correctly rounded value
(64-bit significand, rounding control RC, the overflow/underflow responses of `round80`; precision
control does not apply) of the exact mathematical function. The SDM only promises an error below
1 ulp in round-to-nearest and below 1.5 ulps in the directed modes (vol. 1, 8.3.10); correct rounding
is the one deterministic choice within those bounds. No host floating point is involved.

## Rounding engine (Ziv's strategy)
A function is evaluated at working precision `p` in ball arithmetic (`Ball`: an integer center and
radius with a binary exponent; every operation returns a ball that encloses the exact result for
all values of its operand balls, see the comment on each operation). The enclosure (lo, hi) of the
exact value t is rounded twice: just above lo and just below hi (`Q.nudge`). Rounding to 64 bits is
constant between consecutive multiples of 2^(msb - 65) (representable values, midpoints, the
denormal grid, the overflow threshold), so if both roundings agree in value and in every status bit,
that is the rounding of t. Otherwise `p` grows (96, 160, 320, ... 2560 bits).

Results that are exactly representable or exact midpoints never separate this way, so they are
computed directly: 2^x - 1 at x = ±1, y·log2(2^k) = y·k, log2(1 ± 0), and the zero / infinity /
multiple-of-π/4 rows of the SDM tables. All other results are irrational (Lindemann–Weierstrass for
exp, sin, cos, tan, atan of nonzero rationals; log2 of a rational that is not a power of two is
irrational). Where the function value is extremely close to a dyadic expression of the argument
(sin x ≈ x, cos x ≈ 1, tan x ≈ x, cot x ≈ 1/x, atan q ≈ q for tiny arguments), the ball is intersected
with exact elementary bounds (e.g. x - x³/6 < sin x < x), so the precision needed does not grow with
the exponent of the argument. If 2560 bits do not decide (not observed; correctly rounding a 64-bit
result normally needs about 130 bits), the value just above the lower end of the last enclosure is
rounded.

## Argument reduction of FSIN, FCOS, FSINCOS, FPTAN
SDM vol. 1, 8.3.8: the reduction uses Pi, the 66-bit approximation 0.C90FDAA22168C234C × 2^2 of π
(π truncated to 66 bits), "through the same reduction mechanism used by FPREM and FPREM1". The model
reduces exactly by Pi/2 with the nearest quotient k (as FPREM1 would): r = |x| - k·Pi/2, |r| ≤ Pi/4,
and returns the correctly rounded ±sin r, ±cos r, tan r or -cot r (by k mod 4). For |x| ≤ Pi/4 there
is no reduction, so small arguments get the correctly rounded sin x etc. For larger arguments the
result is sin(x + k(π - Pi)/2) rather than sin x, which is why the SDM describes these instructions
as approximating sin(x·π/Pi) (the two agree to a relative 2^-69 in the reduced argument). Operands
with |x| ≥ 2^63 are out of range (C2 = 1; handled by the caller).
-/
namespace X86
namespace Trans

/-! ## Integer helpers -/

/-- Bit length (0 for 0): n < 2^(blen n). -/
@[inline] def blen (n : Nat) : Nat := if n == 0 then 0 else n.log2 + 1

/-- m · 2^k. -/
@[inline] def shlI (m : Int) (k : Nat) : Int :=
  if m ≥ 0 then ((m.toNat <<< k : Nat) : Int) else -((m.natAbs <<< k : Nat) : Int)

/-- m / 2^k truncated toward zero (error below 1). -/
@[inline] def shrI (m : Int) (k : Nat) : Int :=
  if m ≥ 0 then ((m.toNat >>> k : Nat) : Int) else -((m.natAbs >>> k : Nat) : Int)

/-! ## Ball arithmetic -/

/-- The interval [m - r, m + r] · 2^e, which encloses the exact value being computed. `ok = false`
means no enclosure is known (a division by a ball containing 0, or a series that did not converge
within its fuel); such balls are never rounded. -/
structure Ball where
  m : Int
  r : Nat
  e : Int
  ok : Bool := true
  deriving Inhabited

namespace Ball

def exact (m : Int) (e : Int := 0) : Ball := { m, r := 0, e }
def bad : Ball := { m := 0, r := 1, e := 0, ok := false }
@[inline] def isExactZero (b : Ball) : Bool := b.m == 0 && b.r == 0

/-- Every element x of the ball has |x| < 2^top. -/
@[inline] def top (b : Ball) : Int := b.e + blen (b.m.natAbs + b.r)

/-- Drop `s` low bits: m' = trunc(m / 2^s) is within 1 of m / 2^s, and r' = ⌈r / 2^s⌉ + 1 covers
the old radius plus that error. -/
def shr (b : Ball) (s : Nat) : Ball :=
  if s == 0 then b else
  { b with m := shrI b.m s, r := ((b.r + (1 <<< s) - 1) >>> s) + 1, e := b.e + s }

/-- Keep at most `p` significant bits of |m| + r. -/
def norm (p : Nat) (b : Ball) : Ball :=
  let L := blen (b.m.natAbs + b.r)
  if L > p then b.shr (L - p) else b

def neg (b : Ball) : Ball := { b with m := -b.m }

/-- Sum. Parts of an operand below 2^(top - p - 2) are first moved into its radius (`shr`), then the
operands are aligned exactly. -/
def add (p : Nat) (a b : Ball) : Ball :=
  if a.isExactZero then { b with ok := a.ok && b.ok } else
  if b.isExactZero then { a with ok := a.ok && b.ok } else
  let lim := max a.top b.top - ((p : Int) + 2)
  let a := if a.e < lim then a.shr (lim - a.e).toNat else a
  let b := if b.e < lim then b.shr (lim - b.e).toNat else b
  let e := min a.e b.e
  let sa := (a.e - e).toNat
  let sb := (b.e - e).toNat
  norm p { m := shlI a.m sa + shlI b.m sb, r := (a.r <<< sa) + (b.r <<< sb), e, ok := a.ok && b.ok }

def sub (p : Nat) (a b : Ball) : Ball := add p a b.neg

/-- Product: |xy - m₁m₂| ≤ |m₁|r₂ + |m₂|r₁ + r₁r₂. -/
def mul (p : Nat) (a b : Ball) : Ball :=
  let a := a.norm p
  let b := b.norm p
  norm p { m := a.m * b.m, r := a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r, e := a.e + b.e,
           ok := a.ok && b.ok }

def mulNat (p : Nat) (a : Ball) (k : Nat) : Ball := norm p { a with m := a.m * k, r := a.r * k }

/-- Quotient by a positive integer k, computed at scale 2^s: the center is within 1 of m·2^s/k and
the radius is ⌈r·2^s/k⌉ + 1. -/
def divNat (p : Nat) (a : Ball) (k : Nat) : Ball :=
  let s := blen k + 2 + (p - min p (blen (a.m.natAbs + a.r)))
  norm p { m := shlI a.m s / (k : Int), r := ((a.r <<< s) + k - 1) / k + 1, e := a.e - s, ok := a.ok }

/-- Quotient, if the divisor excludes 0 (|m₂| > r₂). For x ∈ a, y ∈ b:
|x/y - m₁/m₂| = |(x - m₁)m₂ - m₁(y - m₂)| / (|y||m₂|) ≤ (r₁|m₂| + |m₁|r₂) / ((|m₂| - r₂)|m₂|);
at scale 2^s the center (any integer division) adds at most 1. -/
def div (p : Nat) (a b : Ball) : Ball :=
  let a := a.norm p
  let b := b.norm p
  let bm := b.m.natAbs
  if bm ≤ b.r || !(a.ok && b.ok) then bad else
  let s := (p + 2 + blen bm) - min (p + 2 + blen bm) (blen a.m.natAbs)
  let num := (a.r * bm + a.m.natAbs * b.r) <<< s
  let den := (bm - b.r) * bm
  norm p { m := shlI a.m s / b.m, r := (num + den - 1) / den + 1, e := a.e - b.e - s }

/-- An error term [-2^-(p+k), 2^-(p+k)] for a truncated series. -/
def tail (p : Nat) (k : Nat := 4) : Ball := { m := 0, r := 1, e := -((p + k : Nat) : Int) }

/-- Scale by 2^k (exact). -/
def scale (b : Ball) (k : Int) : Ball := { b with e := b.e + k }

end Ball

open Ball

/-! ## Constants -/

/-- Σ_{k ≥ 0} (±1)^k / ((2k+1) m^(2k+1)) for m ≥ 3 (alternating: atan(1/m); else atanh(1/m)) at
scale 2^-P. The power ⌊2^P/m^(2k+1)⌋ is exact up to its floor (⌊⌊a/b⌋/c⌋ = ⌊a/(bc)⌋), so each term
is within 2 units; once that power is 0 the omitted tail is below 1/(1 - 1/m²) < 2 units. -/
def invSeries (m : Nat) (alt : Bool) (P : Nat) : Ball := Id.run do
  let mut pw := (1 <<< P) / m
  let mut sum : Int := 0
  let mut k : Nat := 0
  for _ in [0:P] do
    if pw == 0 then break
    let t : Int := ((pw / (2 * k + 1) : Nat) : Int)
    sum := if alt && k % 2 == 1 then sum - t else sum + t
    pw := pw / (m * m)
    k := k + 1
  return { m := sum, r := 2 * k + 2, e := -(P : Int), ok := pw == 0 }

/-- π = 16 atan(1/5) - 4 atan(1/239) (Machin). -/
def pi (p : Nat) : Ball :=
  let P := p + 8
  let a := invSeries 5 true P
  let b := invSeries 239 true P
  norm p { m := 16 * a.m - 4 * b.m, r := 16 * a.r + 4 * b.r, e := -(P : Int), ok := a.ok && b.ok }

/-- ln 2 = 2 atanh(1/3). -/
def ln2 (p : Nat) : Ball :=
  let P := p + 8
  let a := invSeries 3 false P
  norm p { m := 2 * a.m, r := 2 * a.r, e := -(P : Int), ok := a.ok }

/-! ## Series

Each loop has fuel p + 8 terms; every series gains more than 2 bits per term, so the fuel is not
exhausted (if it were, the result is `bad` and a higher precision is tried). -/

/-- expm1(y)/y = Σ_{k ≥ 0} y^k/(k+1)! for |y| ≤ 0.7. From the second term on the term ratio
|y|/(k+2) is below 1/4, so the omitted tail is below a third of the last term (< 2^-(p+4)). -/
def expm1Rel (p : Nat) (y : Ball) : Ball := Id.run do
  let mut s := exact 1
  let mut t := exact 1
  for k in [1:p+8] do
    t := (t.mul p y).divNat p (k + 1)
    s := s.add p t
    if t.top < -((p : Int) + 4) then return s.add p (tail p)
  return bad

/-- Σ_{j ≥ 0} (-u)^j/(2j+1)! (`odd`: sin r / r) or Σ_{j ≥ 0} (-u)^j/(2j)! (cos r) for u = r² ≤ 0.65.
The series alternates with decreasing terms (ratio ≤ u/6 < 1), so the tail is below the last term
computed (< 2^-(p+4)). -/
def sinCosSum (p : Nat) (u : Ball) (odd : Bool) : Ball := Id.run do
  let mut s := exact 1
  let mut t := exact 1
  for j in [1:p+8] do
    let d := if odd then (2 * j) * (2 * j + 1) else (2 * j - 1) * (2 * j)
    t := ((t.mul p u).divNat p d).neg
    s := s.add p t
    if t.top < -((p : Int) + 4) then return s.add p (tail p)
  return bad

/-- atanh(s)/s = Σ_{j ≥ 0} u^j/(2j+1) for u = s² ≤ 0.03: after the term with u^j the tail is at
most u^(j+1)/(1 - u) < u^j/16 < 2^-(p+4) once u^j < 2^-p. -/
def atanhRel (p : Nat) (u : Ball) : Ball := Id.run do
  let mut s := exact 1
  let mut pw := exact 1
  for j in [1:p+8] do
    pw := pw.mul p u
    s := s.add p (pw.divNat p (2 * j + 1))
    if pw.top < -(p : Int) then return s.add p (tail p)
  return bad

/-- Euler's series: atan(w) = w/(1+w²) · Σ_{n ≥ 0} t_n with t_0 = 1, t_n = t_{n-1} · z · 2n/(2n+1)
and z = w²/(1+w²) ≤ 1/5 (w ≤ 1/2). The terms are positive with ratio below z, so the tail is below
z/(1-z) ≤ 1/4 of the last term (< 2^-(p+4)). -/
def atanSum (p : Nat) (z : Ball) : Ball := Id.run do
  let mut s := exact 1
  let mut t := exact 1
  for n in [1:p+8] do
    t := ((t.mul p z).mulNat p (2 * n)).divNat p (2 * n + 1)
    s := s.add p t
    if t.top < -((p : Int) + 4) then return s.add p (tail p)
  return bad

/-! ## Exact rationals and rounding of an enclosure -/

/-- A nonnegative rational n/d · 2^e (d > 0). -/
structure Q where
  n : Nat
  d : Nat := 1
  e : Int := 0
  deriving Inhabited

namespace Q
@[inline] def align (a b : Q) : Nat × Nat :=
  let E := Min.min a.e b.e
  ((a.n * b.d) <<< (a.e - E).toNat, (b.n * a.d) <<< (b.e - E).toNat)
def lt (a b : Q) : Bool := let (x, y) := align a b; x < y
def max (a b : Q) : Q := if a.lt b then b else a
def min (a b : Q) : Q := if a.lt b then a else b
def mul (a b : Q) : Q := ⟨a.n * b.n, a.d * b.d, a.e + b.e⟩
def inv (a : Q) : Q := ⟨a.d, a.n, -a.e⟩
def divNat (a : Q) (k : Nat) : Q := { a with d := a.d * k }
/-- a + b and a - b (the latter truncated at 0). -/
def add (a b : Q) : Q := let (x, y) := align a b; ⟨x + y, a.d * b.d, Min.min a.e b.e⟩
def sub (a b : Q) : Q := let (x, y) := align a b; ⟨x - y, a.d * b.d, Min.min a.e b.e⟩
def one : Q := ⟨1, 1, 0⟩

/-- v + δ (`up`) or v - δ with 0 < δ ≤ 2^(min(s, e) - 1)/d, s ≤ msb(v) - 66. The points where
rounding to 64 bits (or to the denormal grid) changes are multiples of 2^(msb(v) - 65) near v, and a
nonzero |v - j·2^s| is at least 2^min(s,e)/d, so no such point lies strictly between v and v ± δ:
round(v ± δ) is the rounding of every value just above (below) v. -/
def nudge (v : Q) (up : Bool) : Q :=
  let s : Int := (v.n.log2 : Int) - v.d.log2 - 1 + v.e - 66
  let j := (Max.max 1 (v.e - s + 1)).toNat
  let n := v.n <<< j
  { v with n := if up then n + 1 else n - 1, e := v.e - j }
end Q

/-- The ball as an open interval of magnitudes (sign, lo, hi), if it excludes 0. -/
def Ball.toOpen (b : Ball) : Option (Bool × Q × Q) :=
  if !b.ok || b.m.natAbs ≤ b.r + 1 then none else
  some (decide (b.m < 0), ⟨b.m.natAbs - b.r - 1, 1, b.e⟩, ⟨b.m.natAbs + b.r + 1, 1, b.e⟩)

/-- Round every value of the open interval (lo, hi) (magnitudes, 0 < lo): `some` if they all round
to the same value with the same status. -/
def roundOpen (neg : Bool) (lo hi : Q) (cw : UInt32) : Option (F80 × UInt32) :=
  if lo.n == 0 || !(lo.lt hi) then none else
  let a := lo.nudge true
  let b := hi.nudge false
  let ra := round80 neg a.n a.d a.e 64 cw
  let rb := round80 neg b.n b.d b.e 64 cw
  if ra == rb then some ra else none

def precisions : List Nat := [96, 160, 320, 640, 1280, 2560]

/-- Ziv's loop: `f p` encloses the exact value at precision p as (sign, lo, hi). -/
def ziv (cw : UInt32) (f : Nat → Option (Bool × Q × Q)) : F80 × UInt32 :=
  go precisions
where
  go : List Nat → F80 × UInt32
  | [] =>
    match f 2560 with
    | some (neg, lo, _) => let a := lo.nudge true; round80 neg a.n a.d a.e 64 cw
    | none => (F80.indefinite, FPF.IE)
  | p :: ps =>
    match f p with
    | some (neg, lo, hi) =>
      match roundOpen neg lo hi cw with
      | some r => r
      | none => go ps
    | none => go ps

/-- Intersect an enclosure with exact bounds clo < |t| < chi. -/
def clampOpen (iv : Option (Bool × Q × Q)) (clo chi : Q) : Option (Bool × Q × Q) :=
  iv.map fun (neg, lo, hi) => (neg, lo.max clo, hi.min chi)

@[inline] def signed (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

/-- Round ±k·π/4. -/
def piQuarter (k : Nat) (neg : Bool) (cw : UInt32) : F80 × UInt32 :=
  ziv cw fun p => (((pi p).scale (-2)).mulNat p k).toOpen.map fun (_, lo, hi) => (neg, lo, hi)

/-! ## The instructions (pure part)

Each returns the value for the destination and the status bits; DE is reported as in `F80.arith`
(not when a masked invalid-operation or zero-divide response decides the result). -/

/-- F2XM1: 2^x - 1 for -1 ≤ x ≤ 1. The SDM leaves other operands undefined; as in QEMU, they
(including ±∞) are invalid operations. -/
def f2xm1 (a : F80) (cw : UInt32) : F80 × UInt32 :=
  if a.unsupported then (F80.indefinite, FPF.IE)
  else if a.isNaN then (a.quiet, if a.isSNaN then FPF.IE else 0)
  else if a.isZero then (a, 0)
  else if a.exp > 16383 || (a.exp == 16383 && a.sig != 0x8000000000000000) then (F80.indefinite, FPF.IE)
  else if a.exp == 16383 then (if a.neg then { sig := 0x8000000000000000, se := 0xBFFE } else a, 0)
  else
    let de := if a.isDenormal then FPF.DE else 0
    let (n, e) := a.dyadic
    let (v, fl) := ziv cw fun p =>
      let y := (exact (signed a.neg n) e).mul p (ln2 p)
      (y.mul p (expm1Rel p y)).toOpen
    (v, fl ||| de)

/-- log2(n · 2^e) for n > 0 not a power of two: n/D ∈ [√2/2, √2) with D = 2^log2(n) or twice that,
ln(n/D) = 2 atanh(s) with s = (n - D)/(n + D), |s| ≤ 3 - 2√2 < 0.172. -/
def log2Ball (p : Nat) (n : Nat) (e : Int) : Ball :=
  let L := n.log2
  let (D, k) : Nat × Int :=
    if n * n ≥ 1 <<< (2 * L + 1) then (1 <<< (L + 1), e + L + 1) else (1 <<< L, e + L)
  let s := div p (exact ((n : Int) - D)) (exact (n + D))
  let lnm := (s.mul p (atanhRel p (s.mul p s))).mulNat p 2
  (exact k).add p (lnm.div p (ln2 p))

/-- FYL2X: y · log2(x), x = ST(0), y = ST(1) (SDM table "FYL2X Results"). -/
def fyl2x (x y : F80) (cw : UInt32) : F80 × UInt32 :=
  match F80.special2 x y with
  | some r => r
  | none =>
  let de := F80.denFlag x y
  if x.neg && !x.isZero then (F80.indefinite, FPF.IE)
  else if x.isZero then
    if y.isZero then (F80.indefinite, FPF.IE)
    else if y.isInf then (F80.inf !y.neg, de)
    else (F80.inf !y.neg, FPF.ZE)
  else if x.isInf then
    if y.isZero then (F80.indefinite, FPF.IE) else (F80.inf y.neg, de)
  else
    let c := F80.cmpVal x F80.one
    if y.isInf then
      if c == 0 then (F80.indefinite, FPF.IE) else (F80.inf (y.neg != decide (c < 0)), de)
    else if y.isZero then (F80.zero (y.neg != decide (c < 0)), de)
    else
      let (nx, ex) := x.dyadic
      let (ny, ey) := y.dyadic
      if nx &&& (nx - 1) == 0 then
        -- x = 2^k: the exact product y·k
        let k : Int := ex + nx.log2
        let (v, fl) := round80 (y.neg != decide (k < 0)) (ny * k.natAbs) 1 ey 64 cw
        (v, fl ||| de)
      else
        let (v, fl) := ziv cw fun p => ((exact (signed y.neg ny) ey).mul p (log2Ball p nx ex)).toOpen
        (v, fl ||| de)

/-- The FYL2XP1 domain √2/2 - 1 ≤ x ≤ √2 - 1 (AMD's; Intel documents |x| < 1 - √2/2 and leaves the
rest undefined). As in QEMU, operands outside it are invalid. The bounds are the floors of the
irrational limits at the scale of the binade [1/4, 1/2). -/
def lnp1Domain (x : F80) : Bool :=
  x.isZero || x.exp < 16381 ||
    (x.exp == 16381 && x.sig ≤ (if x.neg then 0x95F619980C4336F7 else 0xD413CCCFE7799211))

/-- FYL2XP1: y · log2(x + 1), x = ST(0), y = ST(1) (SDM table "FYL2XP1 Results"; log2(1 ± 0) = ±0). -/
def fyl2xp1 (x y : F80) (cw : UInt32) : F80 × UInt32 :=
  match F80.special2 x y with
  | some r => r
  | none =>
  let de := F80.denFlag x y
  if !lnp1Domain x then (F80.indefinite, FPF.IE)
  else if x.isZero then
    if y.isInf then (F80.indefinite, FPF.IE) else (F80.zero (x.neg != y.neg), de)
  else if y.isInf then (F80.inf (x.neg != y.neg), de)
  else if y.isZero then (F80.zero (x.neg != y.neg), de)
  else
    let (nx, ex) := x.dyadic
    let (ny, ey) := y.dyadic
    let sx := signed x.neg nx
    -- s = x/(2 + x) = sx/(2^(1-e) + sx), |s| ≤ 3 - 2√2 (|x| < 1/2, so e < 0)
    let D : Int := ((1 <<< (1 - ex).toNat : Nat) : Int)
    let (v, fl) := ziv cw fun p =>
      let s := div p (exact sx) (exact (D + sx))
      let l2 := ((s.mul p (atanhRel p (s.mul p s))).mulNat p 2).div p (ln2 p)
      ((exact (signed y.neg ny) ey).mul p l2).toOpen
    (v, fl ||| de)

/-- atan(a/b) for 0 ≤ a/b ≤ 1/2. -/
def atanW (p : Nat) (a b : Nat) : Ball :=
  if a == 0 then exact 0 else
  let den := a * a + b * b
  (div p (exact (a * b)) (exact den)).mul p (atanSum p (div p (exact (a * a)) (exact den)))

/-- atan q for 0 < q ≤ 1: directly for q ≤ 1/2, else π/4 - atan((1 - q)/(1 + q)). -/
def atanQ (p : Nat) (q : Q) : Ball :=
  let (a, b) := if q.e ≥ 0 then (q.n <<< q.e.toNat, q.d) else (q.n, q.d <<< (-q.e).toNat)
  if 2 * a ≤ b then atanW p a b
  else ((pi p).scale (-2)).sub p (atanW p (b - a) (b + a))

/-- FPATAN: the angle of (x, y) = (ST(0), ST(1)) in [-π, π] (SDM table "FPATAN Results"; the zero
and infinite rows have no invalid cases). -/
def fpatan (x y : F80) (cw : UInt32) : F80 × UInt32 :=
  match F80.special2 x y with
  | some r => r
  | none =>
  let de := F80.denFlag x y
  let withDe := fun (r : F80 × UInt32) => (r.1, r.2 ||| de)
  if y.isZero then
    if x.neg then withDe (piQuarter 4 y.neg cw) else (F80.zero y.neg, de)
  else if y.isInf then
    if x.isInf then withDe (piQuarter (if x.neg then 3 else 1) y.neg cw)
    else withDe (piQuarter 2 y.neg cw)
  else if x.isZero then withDe (piQuarter 2 y.neg cw)
  else if x.isInf then
    if x.neg then withDe (piQuarter 4 y.neg cw) else (F80.zero y.neg, de)
  else
    let (nx, ex) := x.dyadic
    let (ny, ey) := y.dyadic
    let q : Q := ⟨ny, nx, ey - ex⟩
    let small := !(Q.one.lt q)
    withDe <| ziv cw fun p =>
      let a := if small then atanQ p q else ((pi p).scale (-1)).sub p (atanQ p q.inv)
      let a := if x.neg then (pi p).sub p a else a
      let iv := a.toOpen.map fun (_, lo, hi) => (y.neg, lo, hi)
      -- q - q³/3 < atan q < q
      if !x.neg && small then clampOpen iv (q.sub ((q.mul (q.mul q)).divNat 3)) q else iv

/-- Pi/2 = hPi · 2^-67, from the SDM's 66-bit Pi = 0.C90FDAA22168C234C × 2^2. -/
def hPi : Nat := 0xC90FDAA22168C234C

/-- |sin ρ| (0), cos ρ (1), |tan ρ| (2), |cot ρ| (3) for ρ = n · 2^e, 0 < ρ ≤ 0.79. -/
def trigBall (p : Nat) (g : Nat) (n : Nat) (e : Int) : Ball :=
  let r := exact n e
  let u := r.mul p r
  match g with
  | 0 => r.mul p (sinCosSum p u true)
  | 1 => sinCosSum p u false
  | 2 => (r.mul p (sinCosSum p u true)).div p (sinCosSum p u false)
  | _ => (sinCosSum p u false).div p (r.mul p (sinCosSum p u true))

/-- Exact bounds for 0 < ρ ≤ 0.79: ρ - ρ³/6 < sin ρ < ρ, 1 - ρ²/2 < cos ρ < 1, ρ < tan ρ < ρ + ρ³,
1/ρ - ρ < cot ρ < 1/ρ. -/
def trigBounds (g : Nat) (ρ : Q) : Q × Q :=
  let ρ2 := ρ.mul ρ
  let ρ3 := ρ2.mul ρ
  match g with
  | 0 => (ρ.sub (ρ3.divNat 6), ρ)
  | 1 => (Q.one.sub (ρ2.divNat 2), Q.one)
  | 2 => (ρ, ρ.add ρ3)
  | _ => (ρ.inv.sub ρ, ρ.inv)

/-- sin (`which` = 0), cos (1) or tan (2) of a supported finite operand with |a| < 2^63. -/
def trigFinite (which : Nat) (a : F80) (cw : UInt32) : F80 × UInt32 :=
  if a.isZero then (if which == 1 then F80.one else a, 0) else
  let de := if a.isDenormal then FPF.DE else 0
  let (n, ex) := a.dyadic
  -- k = round(|a| / (Pi/2)) (never a tie: k·Pi/2 needs at least 66 significant bits)
  let (num, den) := if ex + 67 ≥ 0 then (n <<< (ex + 67).toNat, hPi) else (n, hPi <<< (-(ex + 67)).toNat)
  let k := (2 * num + den) / (2 * den)
  -- r = |a| - k·Pi/2 = R · 2^e0 exactly, |r| ≤ Pi/4; R ≠ 0 for the same reason
  let e0 := min ex (-67)
  let R : Int := ((n <<< (ex - e0).toNat : Nat) : Int) - (((k * hPi) <<< (-67 - e0).toNat : Nat) : Int)
  let rn := decide (R < 0)
  let j := k % 4
  -- the magnitude function of ρ = |r| and the sign of the result, by quadrant
  let (g, neg) : Nat × Bool := match which with
    | 0 => if j % 2 == 0 then (0, (a.neg != (j == 2)) != rn) else (1, a.neg != (j == 3))
    | 1 => if j % 2 == 0 then (1, j == 2) else (0, (j == 1) != rn)
    | _ => if j % 2 == 0 then (2, a.neg != rn) else (3, !(a.neg != rn))
  if R == 0 then (if g == 1 then F80.one.withNeg neg else F80.zero neg, de) else
  let ρ : Q := ⟨R.natAbs, 1, e0⟩
  let (clo, chi) := trigBounds g ρ
  let (v, fl) := ziv cw fun p =>
    clampOpen ((trigBall p g R.natAbs e0).toOpen.map fun (_, lo, hi) => (neg, lo, hi)) clo chi
  (v, fl ||| de)

/-- FSIN/FCOS/FPTAN/FSINCOS operands with |x| ≥ 2^63, the SDM's "outside the range −2^63 to +2^63"
(supported and finite). -/
def trigOutOfRange (a : F80) : Bool := !a.unsupported && a.exp ≥ 16446 && a.exp != 0x7FFF

/-- The result of FSIN/FCOS/FPTAN/FSINCOS for operands that are not numbers: an invalid operand
(unsupported, ±∞, SNaN) or a QNaN gives this value in every destination. -/
def trigSpecial (a : F80) : Option (F80 × UInt32) :=
  if a.unsupported || a.isInf then some (F80.indefinite, FPF.IE)
  else if a.isNaN then some (a.quiet, if a.isSNaN then FPF.IE else 0)
  else none

end Trans
end X86
