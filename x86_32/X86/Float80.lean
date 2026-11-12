import X86.Word
/-!
# x87 floating point: the 80-bit extended format and exact arithmetic

Values are computed exactly as dyadic rationals with `Nat`/`Int` arithmetic and rounded once, so
every result is the correctly rounded one (no host floating point is involved).

An `F80` is the register/memory format: a 64-bit significand with an explicit integer bit J
(bit 63) and a 16-bit sign/exponent word (bias 16383). Encodings (SDM vol. 1, 4.2.2, 8.2.2):
zero (E = 0, significand 0), denormal (E = 0, J = 0), pseudo-denormal (E = 0, J = 1; read like a
denormal of exponent 1), normal (0 < E < 0x7FFF, J = 1), infinity / NaN (E = 0x7FFF, J = 1), and the
unsupported encodings with J = 0 and E ≠ 0 (unnormals, pseudo-infinities, pseudo-NaNs), which are
invalid operands.

Status results use the layout of the x87 status word: IE, DE, ZE, OE, UE, PE in bits 0..5 and the
round-up indicator C1 in bit 9 (SDM vol. 1, 8.1.3.1 and 8.4).

Rounding (SDM vol. 1, 4.8.4, 8.1.5.2): RC (control word bits 10..11) selects nearest-even, down,
up or toward zero; PC (bits 8..9; 0 = 24, 2 = 53, 3 = 64 significand bits, the reserved value 1
acts as 64) applies to the basic arithmetic operations, with the full extended exponent range.
Tininess is detected after rounding. Masked overflow and underflow produce infinity/the largest
finite value and denormals; unmasked ones (register destinations) produce the result with the
exponent wrapped by 24576 (SDM vol. 1, 8.5.4, 8.5.5).
-/
namespace X86

structure F80 where
  sig : UInt64 := 0
  se : UInt16 := 0
  deriving Repr, Inhabited, BEq

namespace FPF
def IE : UInt32 := 0x1
def DE : UInt32 := 0x2
def ZE : UInt32 := 0x4
def OE : UInt32 := 0x8
def UE : UInt32 := 0x10
def PE : UInt32 := 0x20
def SF : UInt32 := 0x40
def C1 : UInt32 := 0x200
end FPF

namespace F80

@[inline] def exp (a : F80) : Nat := (a.se &&& 0x7FFF).toNat
@[inline] def neg (a : F80) : Bool := a.se &&& 0x8000 != 0
@[inline] def jbit (a : F80) : Bool := a.sig >>> 63 != 0
@[inline] def isZero (a : F80) : Bool := a.exp == 0 && a.sig == 0
/-- Denormal or pseudo-denormal. -/
@[inline] def isDenormal (a : F80) : Bool := a.exp == 0 && a.sig != 0
@[inline] def isInf (a : F80) : Bool := a.exp == 0x7FFF && a.sig == 0x8000000000000000
@[inline] def isNaN (a : F80) : Bool := a.exp == 0x7FFF && a.jbit && a.sig <<< 1 != 0
@[inline] def isSNaN (a : F80) : Bool := a.isNaN && a.sig &&& 0x4000000000000000 == 0
/-- Unnormal, pseudo-infinity or pseudo-NaN. -/
@[inline] def unsupported (a : F80) : Bool := a.exp != 0 && !a.jbit
/-- Finite, supported, nonzero. -/
@[inline] def finiteNZ (a : F80) : Bool := !a.unsupported && a.exp != 0x7FFF && !a.isZero

def indefinite : F80 := { sig := 0xC000000000000000, se := 0xFFFF }
@[inline] def quiet (a : F80) : F80 := { a with sig := a.sig ||| 0x4000000000000000 }
@[inline] def zero (n : Bool) : F80 := { sig := 0, se := if n then 0x8000 else 0 }
@[inline] def inf (n : Bool) : F80 := { sig := 0x8000000000000000, se := (if n then 0x8000 else 0) ||| 0x7FFF }
/-- The canonical encoding of the same value: pseudo-denormals get exponent field 1. -/
@[inline] def canon (a : F80) : F80 := if a.exp == 0 && a.jbit then { a with se := a.se ||| 1 } else a
@[inline] def withNeg (a : F80) (n : Bool) : F80 := { a with se := (a.se &&& 0x7FFF) ||| (if n then 0x8000 else 0) }
@[inline] def one : F80 := { sig := 0x8000000000000000, se := 16383 }

/-- A finite value as significand · 2^exponent (pseudo-denormals have exponent field 1). -/
def dyadic (a : F80) : Nat × Int := (a.sig.toNat, (max a.exp 1 : Nat) - 16383 - 63)

/-- x87 NaN propagation for two operands (SDM vol. 1, table 4-7): an SNaN and a QNaN give the QNaN;
two NaNs of the same kind give the one with the larger significand (on a tie, the positive one);
the result is quiet. -/
def pickNaN (a b : F80) : F80 :=
  if a.isNaN && b.isNaN then
    if a.isSNaN && !b.isSNaN then b.quiet
    else if b.isSNaN && !a.isSNaN then a.quiet
    else if a.sig > b.sig then a.quiet
    else if b.sig > a.sig then b.quiet
    else if !a.neg then a.quiet else b.quiet
  else if a.isNaN then a.quiet else b.quiet

end F80

/-! ## Rounding -/

/-- Significand precision for precision control `pc`. -/
@[inline] def pcBits (pc : UInt32) : Nat := if pc == 0 then 24 else if pc == 2 then 53 else 64

/-- Round n/d to an integer in rounding mode `rc`; returns (quotient, inexact, rounded up in magnitude). -/
def roundQ (n d : Nat) (negative : Bool) (rc : UInt32) : Nat × Bool × Bool :=
  let q := n / d
  let r := n % d
  let up := if rc == 0 then r*2 > d || (r*2 == d && q % 2 == 1)
            else if rc == 1 then negative && r != 0
            else if rc == 2 then !negative && r != 0 else false
  (q + if up then 1 else 0, r != 0, up)

@[inline] def scaleQ (n d : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (n * 2^e.toNat, d) else (n, d * 2^(-e).toNat)

/-- A destination format: significand bits and the exponent range of normal numbers
(a value in [2^E, 2^(E+1)) is normal if `emin ≤ E ≤ emax`). -/
structure FFmt where
  p : Nat
  emin : Int
  emax : Int

def fmtExt (p : Nat) : FFmt := ⟨p, -16382, 16383⟩
def fmtF64 : FFmt := ⟨53, -1022, 1023⟩
def fmtF32 : FFmt := ⟨24, -126, 127⟩

/-- The outcome of rounding an exact nonzero value. `q · 2^ulp` is the rounded magnitude
(denormalized below `emin`); `uq · 2^uulp` the magnitude rounded with an unbounded exponent range. -/
structure Rnd where
  q : Nat
  ulp : Int
  inexact : Bool
  up : Bool
  uq : Nat
  uulp : Int
  uinexact : Bool
  uup : Bool
  tiny : Bool
  overflow : Bool

/-- Round the exact positive value n/d · 2^e (n > 0) to format `f` in mode `rc`. -/
def rnd (f : FFmt) (negative : Bool) (n d : Nat) (e : Int) (rc : UInt32) : Rnd :=
  let guess : Int := (n.log2 : Int) - d.log2
  let (nn, dd) := scaleQ n d (-guess)
  let exponent := e + guess - (if nn < dd then 1 else 0)
  let go := fun (ulp : Int) =>
    let (a, b) := scaleQ n d (e - ulp)
    let (q, inexact, up) := roundQ a b negative rc
    if q ≥ 2^f.p then (q / 2, ulp + 1, inexact, up) else (q, ulp, inexact, up)
  let (uq, uulp, uinexact, uup) := go (exponent - (f.p - 1))
  let (q, ulp, inexact, up) := go (max f.emin exponent - (f.p - 1))
  let uexp := uulp + (uq.log2 : Int)
  { q, ulp, inexact, up, uq, uulp, uinexact, uup,
    tiny := uexp < f.emin, overflow := uexp > f.emax }

/-- Encode magnitude q · 2^ulp (q < 2^64) as an extended value; `bias` adjusts the exponent field
for wrapped results. -/
def enc80 (negative : Bool) (q : Nat) (ulp : Int) (wrap : Int := 0) : F80 :=
  if q == 0 then F80.zero negative else
  -- exact values may come with trailing zero bits beyond 64 significant bits
  let (q, ulp) := if q.log2 > 63 then (q / 2^(q.log2 - 63), ulp + (q.log2 - 63 : Nat)) else (q, ulp)
  let k := q.log2
  let e := ulp + k + 16383 + wrap
  let sgn : UInt16 := if negative then 0x8000 else 0
  if e ≥ 1 then { sig := (q * 2^(63 - k)).toUInt64, se := sgn ||| (e.toNat % 0x8000).toUInt16 }
  else { sig := (q * 2^(ulp + 16445).toNat).toUInt64, se := sgn }

/-- Encode magnitude q · 2^ulp as an IEEE binary32/64 bit pattern (fraction bits `fb`, bias). -/
def encIeee (negative : Bool) (q : Nat) (ulp : Int) (fb : Nat) (bias : Int) : UInt64 :=
  let sgn : UInt64 := if negative then (1 : UInt64) <<< (fb + (if fb == 52 then 11 else 8)).toUInt64 else 0
  if q == 0 then sgn else
  let k := q.log2
  let e := ulp + k + bias
  if e ≥ 1 then sgn ||| (e.toNat.toUInt64 <<< fb.toUInt64) ||| ((q * 2^(fb - k)).toUInt64 &&& ((1 <<< fb.toUInt64) - 1))
  else sgn ||| (q * 2^(ulp + bias - 1 + fb).toNat).toUInt64

/-- Masked overflow result magnitude: infinity, or the largest finite value of the format. -/
def ovfToInf (negative : Bool) (rc : UInt32) : Bool :=
  rc == 0 || (rc == 1 && negative) || (rc == 2 && !negative)

/-- Round an exact value n/d · 2^e to a register with precision `p` and control word `cw`
(masks bits 0..5, RC). Returns the value and the status bits. -/
def round80 (negative : Bool) (n d : Nat) (e : Int) (p : Nat) (cw : UInt32) : F80 × UInt32 :=
  if n == 0 then (F80.zero negative, 0) else
  let rc := (cw >>> 10) &&& 3
  let r := rnd (fmtExt p) negative n d e rc
  -- the biased exponent of the unbounded result; a wrapped result whose exponent is still out of range
  -- (only FSCALE gets there) is the "massive" overflow/underflow of SDM vol. 1, 8.5.4/8.5.5: a signed
  -- ∞ or 0. The EPYC 7742 also reports PE, and C1 = 1 for ∞ (native `x87_exceptions`/`x87_random`
  -- FSCALE cases)
  let ub : Int := r.uulp + (r.uq.log2 : Int) + 16383
  if r.overflow then
    if cw &&& FPF.OE != 0 then
      if ovfToInf negative rc then (F80.inf negative, FPF.OE ||| FPF.PE ||| FPF.C1)
      else (enc80 negative (2^p - 1) (16383 - (p - 1)), FPF.OE ||| FPF.PE)
    else if ub - 24576 > 0x7FFE then (F80.inf negative, FPF.OE ||| FPF.PE ||| FPF.C1)
    else (enc80 negative r.uq r.uulp (-24576),
          FPF.OE ||| (if r.uinexact then FPF.PE else 0) ||| (if r.uup then FPF.C1 else 0))
  else if r.tiny && cw &&& FPF.UE == 0 then
    if ub + 24576 < 1 then (F80.zero negative, FPF.UE ||| FPF.PE) else
    (enc80 negative r.uq r.uulp 24576,
     FPF.UE ||| (if r.uinexact then FPF.PE else 0) ||| (if r.uup then FPF.C1 else 0))
  else
    (enc80 negative r.q r.ulp,
     (if r.inexact then FPF.PE ||| (if r.tiny then FPF.UE else 0) else 0) ||| (if r.up then FPF.C1 else 0))

/-- Round an exact value to binary32/64 for a store. `none`: unmasked overflow/underflow (nothing
is stored). -/
def roundIeee (f : FFmt) (fb : Nat) (bias : Int) (negative : Bool) (n d : Nat) (e : Int) (cw : UInt32) :
    Option UInt64 × UInt32 :=
  if n == 0 then (some (encIeee negative 0 0 fb bias), 0) else
  let rc := (cw >>> 10) &&& 3
  let r := rnd f negative n d e rc
  if r.overflow then
    if cw &&& FPF.OE == 0 then (none, FPF.OE ||| (if r.uinexact then FPF.PE else 0)) else
    let infBits := encIeee negative 1 (f.emax + 1) fb bias
    if ovfToInf negative rc then (some infBits, FPF.OE ||| FPF.PE ||| FPF.C1)
    else (some (encIeee negative (2^f.p - 1) (f.emax - (f.p - 1)) fb bias), FPF.OE ||| FPF.PE)
  else if r.tiny && cw &&& FPF.UE == 0 then (none, FPF.UE ||| (if r.uinexact then FPF.PE else 0))
  else
    (some (encIeee negative r.q r.ulp fb bias),
     (if r.inexact then FPF.PE ||| (if r.tiny then FPF.UE else 0) else 0) ||| (if r.up then FPF.C1 else 0))

/-! ## Operations

Each returns the result (if one is written) and status bits. Invalid operands and NaNs are handled
first; the denormal-operand flag DE is reported alongside, except when a masked invalid-operation or
zero-divide response decides the result without using the operand's value. Callers suppress the result when an
unmasked IE, DE or ZE is reported. -/

namespace F80

/-- Common NaN/invalid handling for two operands: `some` result if one of them decides it. -/
def special2 (a b : F80) : Option (F80 × UInt32) :=
  if a.unsupported || b.unsupported then some (indefinite, FPF.IE)
  else if a.isNaN || b.isNaN then some (pickNaN a b, if a.isSNaN || b.isSNaN then FPF.IE else 0)
  else none

@[inline] def denFlag (a b : F80) : UInt32 := if a.isDenormal || b.isDenormal then FPF.DE else 0

inductive Op where
  | add | sub | mul | div
  deriving BEq, Inhabited

/-- a op b, rounded to precision `p` under control word `cw`. -/
def arith (op : Op) (a b : F80) (p : Nat) (cw : UInt32) : F80 × UInt32 :=
  match special2 a b with
  | some r => r
  | none =>
  let de := denFlag a b
  let rc := (cw >>> 10) &&& 3
  let sa := a.neg
  let sb := b.neg != (op == .sub)
  let negP := a.neg != b.neg
  let (na, ea) := a.dyadic
  let (nb, eb) := b.dyadic
  match op with
  | .mul =>
    if (a.isInf && b.isZero) || (b.isInf && a.isZero) then (indefinite, FPF.IE)
    else if a.isInf || b.isInf then (inf negP, de)
    else let (v, fl) := round80 negP (na * nb) 1 (ea + eb) p cw; (v, fl ||| de)
  | .div =>
    if (a.isInf && b.isInf) || (a.isZero && b.isZero) then (indefinite, FPF.IE)
    else if a.isInf then (inf negP, de)
    else if b.isInf then (zero negP, de)
    else if b.isZero then (inf negP, FPF.ZE)
    else let (v, fl) := round80 negP na nb (ea - eb) p cw; (v, fl ||| de)
  | _ =>
    if a.isInf && b.isInf && sa != sb then (indefinite, FPF.IE)
    else if a.isInf then (inf sa, de)
    else if b.isInf then (inf sb, de)
    else
      let e := min ea eb
      let x : Int := (if sa then -1 else 1) * ((na * 2^(ea - e).toNat : Nat) : Int)
      let y : Int := (if sb then -1 else 1) * ((nb * 2^(eb - e).toNat : Nat) : Int)
      let s := x + y
      let negS := if s == 0 then (sa && sb) || (sa != sb && rc == 1) else s < 0
      let (v, fl) := round80 negS s.natAbs 1 e p cw
      (v, fl ||| de)

/-- Square root rounded to precision `p`. -/
def sqrt (a : F80) (p : Nat) (cw : UInt32) : F80 × UInt32 :=
  if a.unsupported then (indefinite, FPF.IE)
  else if a.isNaN then (a.quiet, if a.isSNaN then FPF.IE else 0)
  else if a.isZero then (a, 0)
  else if a.neg then (indefinite, FPF.IE)
  else if a.isInf then (a, 0)
  else
    let de := if a.isDenormal then FPF.DE else 0
    let (n, e) := a.dyadic
    -- floor(sqrt(n · 2^e · 4^k)) with enough bits, plus a sticky bit, then round exactly
    let k : Nat := 70 + (if e < 0 then ((-e).toNat + 1) / 2 else 0)
    let (m, ee) := if (e + 2 * (k : Int)) % 2 == 0 then (n, e) else (2 * n, e - 1)
    let rad := m * 2^(ee + 2 * (k : Int)).toNat
    let s := rad.sqrt
    let sticky := s * s != rad
    let (v, fl) := round80 false (2 * s + (if sticky then 1 else 0)) 2 (-(k : Int)) p cw
    (v, fl ||| de)

/-- Exact comparison of supported, non-NaN values: -1, 0, 1. -/
def cmpVal (a b : F80) : Int :=
  if a.isZero && b.isZero then 0
  else if a.isInf || b.isInf then
    if a.isInf && b.isInf && a.neg == b.neg then 0
    else if a.isInf then (if a.neg then -1 else 1) else (if b.neg then 1 else -1)
  else
    let (na, ea) := a.dyadic
    let (nb, eb) := b.dyadic
    let e := min ea eb
    let x : Int := (if a.neg then -1 else 1) * ((na * 2^(ea - e).toNat : Nat) : Int)
    let y : Int := (if b.neg then -1 else 1) * ((nb * 2^(eb - e).toNat : Nat) : Int)
    if x < y then -1 else if x == y then 0 else 1

/-- Compare: `some` order (-1/0/1), or `none` if unordered. `quiet` (FUCOM*) signals IE only for
SNaNs; ordered compares (FCOM*) also for QNaNs. -/
def compare (a b : F80) (quiet : Bool) : Option Int × UInt32 :=
  if a.unsupported || b.unsupported then (none, FPF.IE)
  else if a.isNaN || b.isNaN then
    (none, if !quiet || a.isSNaN || b.isSNaN then FPF.IE else 0)
  else (some (cmpVal a b), denFlag a b)

/-- Round to an integer in the current rounding mode (FRNDINT; precision control does not apply). -/
def roundInt (a : F80) (cw : UInt32) : F80 × UInt32 :=
  if a.unsupported then (indefinite, FPF.IE)
  else if a.isNaN then (a.quiet, if a.isSNaN then FPF.IE else 0)
  else if a.isInf || a.isZero then (a, 0)
  else
    let de := if a.isDenormal then FPF.DE else 0
    let (n, e) := a.dyadic
    if e ≥ 0 then (a, de) else
    let (nn, dd) := scaleQ n 1 e
    let (q, inexact, up) := roundQ nn dd a.neg ((cw >>> 10) &&& 3)
    let (v, _) := round80 a.neg q 1 0 64 cw
    (v, de ||| (if inexact then FPF.PE else 0) ||| (if up then FPF.C1 else 0))

/-- Integer value with rounding mode `rc`: `none` if NaN, infinite or unsupported. -/
def toIntRC (a : F80) (rc : UInt32) : Option (Int × Bool × Bool) :=
  if a.unsupported || a.isNaN || a.isInf then none
  else if a.isZero then some (0, false, false)
  else
    let (n, e) := a.dyadic
    let (nn, dd) := scaleQ n 1 e
    let (q, inexact, up) := roundQ nn dd a.neg rc
    some (if a.neg then -(q : Int) else q, inexact, up)

/-- Convert to a `bits`-bit integer (FIST/FISTP): out of range, NaN or infinity is invalid
(masked response: the integer indefinite, the most negative value). -/
def toInt (a : F80) (bits : Nat) (cw : UInt32) : Option UInt64 × UInt32 :=
  let indef : UInt64 := (1 : UInt64) <<< (bits - 1).toUInt64
  -- FIST/FISTP do not report denormal operands (SDM: #IS, #IA, #P only)
  let de : UInt32 := 0
  match a.toIntRC ((cw >>> 10) &&& 3) with
  | none => (if cw &&& FPF.IE != 0 then some indef else none, FPF.IE)
  | some (z, inexact, up) =>
    if z < -((2 ^ (bits - 1) : Nat) : Int) || z ≥ ((2 ^ (bits - 1) : Nat) : Int) then
      (if cw &&& FPF.IE != 0 then some indef else none, FPF.IE ||| de)
    else
      (some ((z % ((2 ^ bits : Nat) : Int)).toNat.toUInt64),
       de ||| (if inexact then FPF.PE else 0) ||| (if up then FPF.C1 else 0))

/-- Exact conversion from an integer (FILD). -/
def ofInt (z : Int) : F80 :=
  (round80 (z < 0) z.natAbs 1 0 64 0x37F).1

/-- Load a binary32/64 value exactly; denormals report DE. With `quietSNaN` (FLD) an SNaN becomes a
QNaN with IE; arithmetic operands keep the SNaN for the NaN rules of the operation. -/
def ofIeee (bits : UInt64) (fb : Nat) (ebits : Nat) (quietSNaN : Bool := true) : F80 × UInt32 :=
  let emaxF := (1 <<< ebits) - 1
  let negative := (bits >>> (fb + ebits).toUInt64) &&& 1 != 0
  let e := ((bits >>> fb.toUInt64) &&& ((1 <<< ebits.toUInt64) - 1)).toNat
  let frac := bits &&& ((1 <<< fb.toUInt64) - 1)
  let bias : Int := (2 ^ (ebits - 1) : Nat) - 1
  if e == emaxF then
    if frac == 0 then (inf negative, 0)
    else
      let s := (frac <<< (63 - fb).toUInt64) ||| 0x8000000000000000
      let v : F80 := { sig := s, se := (if negative then 0x8000 else 0) ||| 0x7FFF }
      if quietSNaN then (v.quiet, if s &&& 0x4000000000000000 == 0 then FPF.IE else 0) else (v, 0)
  else if e == 0 then
    if frac == 0 then (zero negative, 0)
    else (enc80 negative frac.toNat (1 - bias - fb), FPF.DE)
  else (enc80 negative (frac.toNat + 2^fb) (e - bias - fb), 0)

/-- Store as binary32/64 (FST/FSTP m32/m64): `none` when nothing may be stored (unmasked invalid,
overflow or underflow). -/
def toIeee (a : F80) (fb ebits : Nat) (cw : UInt32) : Option UInt64 × UInt32 :=
  let bias : Int := (2 ^ (ebits - 1) : Nat) - 1
  let f : FFmt := ⟨fb + 1, 1 - bias, bias⟩
  let sgnBit : UInt64 := (1 : UInt64) <<< (fb + ebits).toUInt64
  let expAll : UInt64 := ((1 <<< ebits.toUInt64) - 1) <<< fb.toUInt64
  let sgn : UInt64 := if a.neg then sgnBit else 0
  let ieeeIndef := sgnBit ||| expAll ||| ((1 : UInt64) <<< (fb - 1).toUInt64)
  if a.unsupported then (if cw &&& FPF.IE != 0 then some ieeeIndef else none, FPF.IE)
  else if a.isNaN then
    if a.isSNaN && cw &&& FPF.IE == 0 then (none, FPF.IE) else
    (some (sgn ||| expAll ||| ((a.sig >>> (63 - fb).toUInt64) &&& ((1 <<< fb.toUInt64) - 1))
           ||| ((1 : UInt64) <<< (fb - 1).toUInt64)), if a.isSNaN then FPF.IE else 0)
  else if a.isInf then (some (sgn ||| expAll), 0)
  else if a.isZero then (some sgn, 0)
  else
    -- a denormal ST(0) is not a denormal-operand exception for FST/FSTP m32/m64: the SDM lists only
    -- #IS, #IA, #U, #O, #P for FST, and the EPYC 7742 reports no DE (native `x87_memory`, 48 cases)
    let (n, e) := a.dyadic
    roundIeee f fb bias a.neg n 1 e cw

/-- FSCALE: a · 2^trunc(b). -/
def scale (a b : F80) (cw : UInt32) : F80 × UInt32 :=
  match special2 a b with
  | some r => r
  | none =>
  let de := denFlag a b
  if b.isInf then
    if b.neg then
      if a.isInf then (indefinite, FPF.IE) else (zero a.neg, de)
    else if a.isZero then (indefinite, FPF.IE) else (inf a.neg, de)
  else if a.isInf || a.isZero then (a, de)
  else
    let k := match b.toIntRC 3 with | some (z, _, _) => z | none => 0
    let k := max (-70000) (min 70000 k)
    let (n, e) := a.dyadic
    let (v, fl) := round80 a.neg n 1 (e + k) 64 cw
    (v, fl ||| de)

/-- FXTRACT: (exponent, significand) of a. -/
def xtract (a : F80) : (F80 × F80) × UInt32 :=
  if a.unsupported then ((indefinite, indefinite), FPF.IE)
  else if a.isNaN then ((a.quiet, a.quiet), if a.isSNaN then FPF.IE else 0)
  else if a.isInf then ((inf false, a), 0)
  else if a.isZero then ((inf true, a), FPF.ZE)
  else
    let (n, e) := a.dyadic
    let k : Int := e + n.log2
    ((ofInt k, enc80 a.neg n (-(n.log2 : Int))), if a.isDenormal then FPF.DE else 0)

/-- FPREM (`ieee = false`, truncating quotient) and FPREM1 (round-to-nearest quotient): the
(partial) remainder, the low three quotient bits, and whether the reduction is complete. Exponent
differences of 64 or more are reduced by 32..63 bits per step (as QEMU and AMD document). -/
def prem (a b : F80) (ieee : Bool) (cw : UInt32 := 0x37F) : (F80 × Nat × Bool) × UInt32 :=
  match special2 a b with
  | some (v, fl) => ((v, 0, true), fl)
  | none =>
  let de := denFlag a b
  -- The remainder is exact, but a denormal (tiny) one is an underflow when UE is unmasked: the
  -- result is delivered with the exponent wrapped by 24576 and UE set (EPYC 7742, native
  -- `x87_exceptions`: FPREM/FPREM1 of a denormal by a huge or infinite divisor, 4 cases); masked, the
  -- exact denormal is delivered without UE (`round80` of the exact value does both).
  let res := fun (neg : Bool) (n : Nat) (e : Int) =>
    if n == 0 then (zero neg, (0 : UInt32)) else round80 neg n 1 e 64 cw
  if a.isInf || b.isZero then ((indefinite, 0, true), FPF.IE)
  -- the dividend is the result; a pseudo-denormal is delivered in its canonical encoding (exponent
  -- field 1): pseudo-denormals are accepted as operands but never produced (SDM vol. 1, 8.2.2)
  else if a.isZero then ((a.canon, 0, true), de)
  else if b.isInf then
    let (na, ea) := a.dyadic
    let (v, fl) := res a.neg na ea
    ((v, 0, true), de ||| fl)
  else
    let (na, ea) := a.dyadic
    let (nb, eb) := b.dyadic
    let xa : Int := ea + na.log2
    let xb : Int := eb + nb.log2
    let diff := xa - xb
    if diff ≥ 64 then
      -- partial: subtract the largest multiple of b · 2^(diff - n) not exceeding |a|, truncating
      let nshift := 32 + (diff.toNat % 32)
      let sh := diff - nshift
      let e := min ea (eb + sh)
      let x := na * 2^(ea - e).toNat
      let y := nb * 2^(eb + sh - e).toNat
      let r := x % y
      let (v, fl) := res a.neg r e
      ((v, 0, false), de ||| fl)
    else
      let e := min ea eb
      let x := na * 2^(ea - e).toNat
      let y := nb * 2^(eb - e).toNat
      let q0 := x / y
      let r0 := x % y
      let (q, rmag, rneg) :=
        if ieee && (2 * r0 > y || (2 * r0 == y && q0 % 2 == 1)) then (q0 + 1, y - r0, !a.neg)
        else (q0, r0, a.neg)
      let (v, fl) := if rmag == 0 then (zero a.neg, 0) else res rneg rmag e
      ((v, q % 8, true), de ||| fl)

end F80

/-- Constants of FLDPI, FLDL2T, FLDL2E, FLDLG2, FLDLN2 as 128-bit fixed-point numerators with their
exponent: value ≈ n · 2^e. They are rounded to 64 bits in the current rounding mode. -/
def fpConst (k : Nat) : Nat × Int :=
  match k with
  | 0 => (0xC90FDAA22168C234C4C6628B80DC1CD1, -126)  -- pi
  | 1 => (0xD49A784BCD1B8AFE492BF6FF4DAFDB4C, -126)  -- log2(10)
  | 2 => (0xB8AA3B295C17F0BBBE87FED0691D3E88, -127)  -- log2(e)
  | 3 => (0x9A209A84FBCFF7988F8959AC0B7C9178, -129)  -- log10(2)
  | _ => (0xB17217F7D1CF79ABC9E3B39803F2F6AF, -128)  -- ln(2)

end X86
