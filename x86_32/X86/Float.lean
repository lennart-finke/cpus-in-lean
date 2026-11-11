
import X86.Word
import Init.Data.Nat.Sqrt.Basic

/-!
# SSE floating point: exact binary32/binary64 arithmetic

Exact-integer binary32/binary64 arithmetic (ported from the 64-bit model, `x86_64/X64/Float.lean`,
where it is validated against QEMU and hardware). All operations are pure Lean definitions;
there are no host floating-point primitives or external numerical routines here.
The result records the six MXCSR exception-status bits (IE, DE, ZE, OE, UE, PE); the MXCSR
argument supplies RC (bits 13..14), DAZ (bit 6), FTZ (bit 15) and the UM/OM/PM masks.
-/
namespace X86.FP

structure Format where
  fraction : Nat
  exponent : Nat
  bias : Int
  deriving Repr

def binary32 : Format := ⟨23, 8, 127⟩
def binary64 : Format := ⟨52, 11, 1023⟩
def Format.signBit (f : Format) : UInt64 := (1 : UInt64) <<< (f.fraction + f.exponent).toUInt64
def Format.fractionMask (f : Format) : UInt64 := ((1 : UInt64) <<< f.fraction.toUInt64) - 1
def Format.exponentMax (f : Format) : Nat := 2^f.exponent - 1
def Format.infinity (f : Format) : UInt64 := f.exponentMax.toUInt64 <<< f.fraction.toUInt64
def Format.quietBit (f : Format) : UInt64 := (1 : UInt64) <<< (f.fraction - 1).toUInt64

def sign (f : Format) (v : UInt64) : Bool := v &&& f.signBit != 0
def expField (f : Format) (v : UInt64) : Nat := ((v >>> f.fraction.toUInt64) &&& f.exponentMax.toUInt64).toNat
def fraction (f : Format) (v : UInt64) : UInt64 := v &&& f.fractionMask
def isNaN (f : Format) (v : UInt64) : Bool := expField f v == f.exponentMax && fraction f v != 0
def isSNaN (f : Format) (v : UInt64) : Bool := isNaN f v && v &&& f.quietBit == 0
def isInf (f : Format) (v : UInt64) : Bool := expField f v == f.exponentMax && fraction f v == 0
def isZero (f : Format) (v : UInt64) : Bool := expField f v == 0 && fraction f v == 0
def isDenormal (f : Format) (v : UInt64) : Bool := expField f v == 0 && fraction f v != 0
def signedBits (f : Format) (negative : Bool) (v : UInt64) : UInt64 := v ||| (if negative then f.signBit else 0)
def indefinite (f : Format) : UInt64 := f.signBit ||| f.infinity ||| f.quietBit

def prepare (f : Format) (mxcsr : UInt64) (v : UInt64) : UInt64 × UInt64 :=
  if isDenormal f v then
    if mxcsr &&& 0x40 != 0 then (v &&& f.signBit, 0) else (v, 2)
  else (v, 0)

/-- Finite magnitude as an exact dyadic rational: significand * 2^exponent. -/
def dyadic (f : Format) (v : UInt64) : Nat × Int :=
  let e := expField f v
  let mantissa := (fraction f v).toNat + if e == 0 then 0 else 2^f.fraction
  (mantissa, (max e 1 : Nat) - f.bias - (f.fraction : Int))

/-- Round n/d to an integer in one of the four MXCSR rounding modes. -/
def roundQuotient (n d : Nat) (negative : Bool) (mode : UInt64) : Nat × Bool :=
  let q := n / d
  let r := n % d
  let up := if mode == 0 then r*2 > d || (r*2 == d && q % 2 == 1)
            else if mode == 1 then negative && r != 0
            else if mode == 2 then !negative && r != 0 else false
  (q + if up then 1 else 0, r != 0)

/-- Multiply a rational by an exact power of two. -/
def scale (n d : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (n * 2^e.toNat, d) else (n, d * 2^(-e).toNat)

/-- Round an exact positive rational times a power of two to the target format.
The caller supplies a sign, including the sign of an exact zero. -/
def pack (f : Format) (negative : Bool) (n d : Nat) (e : Int) (mxcsr : UInt64) : UInt64 × UInt64 := Id.run do
  if n == 0 then return (signedBits f negative 0, 0)
  let mode := (mxcsr >>> 13) &&& 3
  let guess := (n.log2 : Int) - d.log2
  let (nn, dd) := scale n d (-guess)
  let log := guess - if nn < dd then 1 else 0
  let exponent := e + log
  let emin := 1 - f.bias
  let emax := (f.exponentMax : Int) - 1 - f.bias
  -- Unmasked range exceptions use precision rounded with an unbounded
  -- exponent, before gradual underflow or overflow saturation. In particular,
  -- an exact tiny result raises UE without PE when UM is clear.
  -- Intel SDM vol. 1, 11.5.2.4-5 and tables E-16/E-17.
  let (un, ud) := scale n d (e - (exponent - (f.fraction : Int)))
  let (uq, unboundedInexact) := roundQuotient un ud negative mode
  let unboundedExp := exponent + if uq ≥ 2^(f.fraction+1) then 1 else 0
  let tiny := unboundedExp < emin
  let ulp := max emin exponent - (f.fraction : Int)
  let (nn, dd) := scale n d (e - ulp)
  let (q, inexact) := roundQuotient nn dd negative mode
  let (q, ulp) := if q ≥ 2^(f.fraction+1) then (q/2, ulp+1) else (q,ulp)
  let roundedExp := ulp + f.fraction
  if roundedExp > emax then
    let infinite := mode == 0 || (mode == 1 && negative) || (mode == 2 && !negative)
    let precision := mxcsr &&& 0x400 != 0 || unboundedInexact
    return (signedBits f negative (if infinite then f.infinity else f.infinity - 1),
      0x08 ||| if precision then 0x20 else 0)
  let normal := q ≥ 2^f.fraction
  let ef := if normal then (roundedExp + f.bias).toNat else 0
  let bits := (ef.toUInt64 <<< f.fraction.toUInt64) ||| (q.toUInt64 &&& f.fractionMask)
  if tiny && mxcsr &&& 0x800 == 0 then
    -- The returned value is not committed when UE is unmasked; FTZ is ignored.
    return (signedBits f negative bits, 0x10 ||| if unboundedInexact then 0x20 else 0)
  -- FTZ uses tininess before gradual underflow, even if denormalization
  -- rounding would produce the smallest normal value (SDM 10.2.3.3).
  if tiny && mxcsr &&& 0x8000 != 0 then
    return (signedBits f negative 0, 0x30)
  return (signedBits f negative bits, (if inexact then 0x20 else 0) ||| (if tiny && inexact then 0x10 else 0))

inductive Op where
  | add | sub | mul | div
  deriving BEq, Repr

/-- Arithmetic with x86 NaN propagation and signed zero; status flags are returned
separately so instruction semantics can apply MXCSR exception masks atomically. -/
def binary (f : Format) (op : Op) (a b : UInt64) (mxcsr : UInt64) : UInt64 × UInt64 := Id.run do
  let (a, da) := prepare f mxcsr a
  let (b, db) := prepare f mxcsr b
  if isNaN f a || isNaN f b then
    let result := (if isNaN f a then a else b) ||| f.quietBit
    return (result, if isSNaN f a || isSNaN f b then 1 else 0)
  let sa := sign f a
  let sb := sign f b != (op == .sub)
  let ia := isInf f a
  let ib := isInf f b
  let za := isZero f a
  let zb := isZero f b
  let negative := sa != sign f b
  let (na, ea) := dyadic f a
  let (nb, eb) := dyadic f b
  let flags := da ||| db
  if op == .mul then
    if (ia && zb) || (ib && za) then return (indefinite f, 1)
    if ia || ib then return (signedBits f negative f.infinity, flags)
    let (v, fl) := pack f negative (na*nb) 1 (ea+eb) mxcsr
    return (v, fl ||| flags)
  if op == .div then
    if (ia && ib) || (za && zb) then return (indefinite f, 1)
    if ia then return (signedBits f negative f.infinity, flags)
    if ib then return (signedBits f negative 0, flags)
    if zb then return (signedBits f negative f.infinity, 4)
    let (v, fl) := pack f negative na nb (ea-eb) mxcsr
    return (v, fl ||| flags)
  if ia && ib && sa != sb then return (indefinite f, 1)
  if ia then return (signedBits f sa f.infinity, flags)
  if ib then return (signedBits f sb f.infinity, flags)
  let e := min ea eb
  let aa : Int := (if sa then -1 else 1) * (na * 2^(ea-e).toNat : Nat)
  let bb : Int := (if sb then -1 else 1) * (nb * 2^(eb-e).toNat : Nat)
  let sum := aa + bb
  let negative := if sum == 0 then (sa && sb) || (sa != sb && (mxcsr >>> 13) &&& 3 == 1) else sum < 0
  let (v, fl) := pack f negative sum.natAbs 1 e mxcsr
  return (v, fl ||| flags)

/-- Square root rounded by exact comparisons against adjacent representable values.
Nonzero roots of binary32/64 subnormals are normal in the same format. -/
def sqrt (f : Format) (a mxcsr : UInt64) : UInt64 × UInt64 := Id.run do
  let (a, flags) := prepare f mxcsr a
  if isNaN f a then return (a ||| f.quietBit, if isSNaN f a then 1 else 0)
  if isZero f a then return (a, 0)
  if sign f a then return (indefinite f, 1)
  if isInf f a then return (a, 0)
  let (n,e) := dyadic f a
  let exponent := ((n.log2 : Int) + e) / 2
  let ulp := exponent - (f.fraction : Int)
  let (n,d) := scale n 1 (e - 2*ulp)
  let q := (n/d).sqrt
  let inexact := q*q*d != n
  let mode := (mxcsr >>> 13) &&& 3
  let middle := d*(2*q+1)^2
  let up := if mode == 0 then 4*n > middle || (4*n == middle && q%2 == 1)
            else mode == 2 && inexact
  let (result, _) := pack f false (q + if up then 1 else 0) 1 ulp mxcsr
  return (result, flags ||| if inexact then 0x20 else 0)

/-- Exact finite comparison. Returns -1, 0, or 1; caller handles NaNs. -/
def compare (f : Format) (a b : UInt64) : Int :=
  if (isZero f a && isZero f b) || a == b then 0
  else if sign f a != sign f b then if sign f a then -1 else 1
  else if (a < b) != sign f a then -1 else 1

def convert (src dst : Format) (a mxcsr : UInt64) : UInt64 × UInt64 :=
  let (a, flags) := prepare src mxcsr a
  if isNaN src a then
    let payload := if dst.fraction ≥ src.fraction then fraction src a <<< (dst.fraction-src.fraction).toUInt64
                   else fraction src a >>> (src.fraction-dst.fraction).toUInt64
    (signedBits dst (sign src a) (dst.infinity ||| payload ||| dst.quietBit), if isSNaN src a then 1 else 0)
  else if isInf src a then (signedBits dst (sign src a) dst.infinity, 0)
  else
    let (n,e) := dyadic src a
    let (r,fl) := pack dst (sign src a) n 1 e mxcsr
    (r, fl ||| flags)

def fromInt (f : Format) (a : Int) (mxcsr : UInt64) : UInt64 × UInt64 :=
  pack f (a < 0) a.natAbs 1 0 mxcsr

def toInt (f : Format) (a mxcsr : UInt64) (width : Nat) (truncate : Bool) : UInt64 × UInt64 := Id.run do
  let (a, _) := prepare f mxcsr a
  let bad : UInt64 := 1 <<< (width - 1).toUInt64
  if isNaN f a || isInf f a then return (bad, 1)
  let (n,e) := dyadic f a
  let (n,d) := scale n 1 e
  let mode := if truncate then 3 else (mxcsr >>> 13) &&& 3
  let (q, inexact) := roundQuotient n d (sign f a) mode
  let z : Int := if sign f a then -(q : Int) else q
  if z < -(2^(width-1) : Nat) || z ≥ (2^(width-1) : Nat) then return (bad, 1)
  return ((z % (2^width : Nat)).toNat.toUInt64, if inexact then 0x20 else 0)

end X86.FP
