import X64.Word

namespace X64
open Flag

structure AFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

@[inline] def AFlags.pack (f : AFlags) : UInt64 :=
  (if f.cf then CF else 0) ||| (if f.pf then PF else 0) ||| (if f.af then AF else 0) |||
  (if f.zf then ZF else 0) ||| (if f.sf then SF else 0) ||| (if f.of then OF else 0)

@[inline] def addCore (sz : Sz) (a b : UInt64) (carry : Bool) : UInt64 × AFlags :=
  let s := (a + b) &&& sz.mask
  let r := (s + b2u carry) &&& sz.mask
  (r, { cf := s < a || (carry && r == 0), pf := parity r,
        af := (a ^^^ b ^^^ r) &&& 16 != 0, zf := r == 0, sf := r &&& sz.msb != 0,
        of := (a ^^^ r) &&& (b ^^^ r) &&& sz.msb != 0 })

@[inline] def subCore (sz : Sz) (a b : UInt64) (borrow : Bool) : UInt64 × AFlags :=
  let r := (a - b - b2u borrow) &&& sz.mask
  (r, { cf := a < b || (borrow && a == b), pf := parity r,
        af := (a ^^^ b ^^^ r) &&& 16 != 0, zf := r == 0, sf := r &&& sz.msb != 0,
        of := (a ^^^ b) &&& (a ^^^ r) &&& sz.msb != 0 })

@[inline] def logicCore (sz : Sz) (r : UInt64) : UInt64 × AFlags :=
  (r, { cf := false, pf := parity r, af := false, zf := r == 0,
        sf := r &&& sz.msb != 0, of := false })

@[inline] def alu (op : UInt8) (sz : Sz) (a b : UInt64) (cf : Bool) : UInt64 × AFlags :=
  match op with
  | 0 => addCore sz a b false | 1 => logicCore sz (a ||| b)
  | 2 => addCore sz a b cf | 3 => subCore sz a b cf
  | 4 => logicCore sz (a &&& b) | 6 => logicCore sz (a ^^^ b)
  | _ => subCore sz a b false

@[inline] def evalCC (f : UInt64) (cc : UInt8) : Bool :=
  let sf := f &&& SF != 0
  let ofl := f &&& OF != 0
  let r := match cc >>> 1 with
    | 0 => ofl | 1 => f &&& CF != 0 | 2 => f &&& ZF != 0
    | 3 => f &&& (CF ||| ZF) != 0 | 4 => sf | 5 => f &&& PF != 0
    | 6 => sf != ofl | _ => f &&& ZF != 0 || sf != ofl
  if cc &&& 1 == 1 then !r else r

/-- Width-bounded shifts/rotates. Undefined flags use a deterministic representative;
tests compare only flags defined by the architecture. -/
def shiftOp (op : UInt8) (sz : Sz) (a cnt : UInt64) (cfIn : Bool) : Option (UInt64 × UInt64 × UInt64) := Id.run do
  let cnt := cnt &&& (if sz == 8 then 63 else 31)
  if cnt == 0 then return none
  let bits := sz.bits
  if op ≥ 4 && op ≤ 7 then
    let left := op == 4 || op == 6
    let sign := a &&& sz.msb != 0
    let r := if left then (if cnt ≥ bits then 0 else (a <<< cnt) &&& sz.mask)
      else if op == 5 then (if cnt ≥ bits then 0 else a >>> cnt)
      else if cnt ≥ bits then (if sign then sz.mask else 0)
      else ((a >>> cnt) ||| (if sign then sz.mask <<< (bits-cnt) else 0)) &&& sz.mask
    let cf := if left then cnt ≤ bits && (a >>> (bits-cnt)) &&& 1 != 0
      else if cnt ≤ bits then (a >>> (cnt-1)) &&& 1 != 0 else op == 7 && sign
    let ofl := if left then (r &&& sz.msb != 0) != cf else op == 5 && sign
    return some (r, arith, { (logicCore sz r).2 with cf, of := ofl }.pack)
  let mut r := a
  let mut cf := cfIn
  let count := if op < 2 then cnt % bits else if op < 4 && sz < 4 then cnt % (bits + 1) else cnt
  if count == 0 && (op == 2 || op == 3) then return none
  for _ in [0:count.toNat] do
    let old := r
    let oldCf := cf
    if op == 0 || op == 2 || op == 4 || op == 6 then
      cf := old &&& sz.msb != 0
      r := (old <<< 1) &&& sz.mask
      if op == 0 then r := r ||| b2u cf
      if op == 2 then r := r ||| b2u oldCf
    else
      cf := old &&& 1 != 0
      r := old >>> 1
      if op == 1 then r := r ||| (if cf then sz.msb else 0)
      if op == 3 then r := r ||| (if oldCf then sz.msb else 0)
      if op == 7 then r := r ||| (old &&& sz.msb)
  if op == 0 then cf := r &&& 1 != 0
  if op == 1 then cf := r &&& sz.msb != 0
  let ofl := if op == 0 || op == 2 || op == 4 || op == 6 then (r &&& sz.msb != 0) != cf
             else if op == 5 then a &&& sz.msb != 0
             else if op == 7 then false
             else (r &&& sz.msb != 0) != (r &&& (sz.msb >>> 1) != 0)
  let f := { (logicCore sz r).2 with cf, of := ofl }
  return some (r, if op < 4 then CF ||| OF else arith, f.pack)

/-- Double-width multiplication represented mathematically, including 128-bit products. -/
def mulWide (sz : Sz) (a b : UInt64) : Nat := (a &&& sz.mask).toNat * (b &&& sz.mask).toNat

def divU (sz : Sz) (a : Nat) (d : UInt64) : Option (UInt64 × UInt64) :=
  if d == 0 then none else
  let q := a / d.toNat
  if q > sz.mask.toNat then none else some (q.toUInt64, (a % d.toNat).toUInt64)

def divS (sz : Sz) (a d : Int) : Option (UInt64 × UInt64) :=
  if d == 0 then none else
  let q := a.tdiv d
  let lim : Int := (2 ^ (sz.bits.toNat - 1) : Nat)
  if q < -lim || q ≥ lim then none else
  some ((q % (2^64 : Int)).toNat.toUInt64, (a.tmod d % (2^64 : Int)).toNat.toUInt64)

/-- Evaluate condition code `cc` (0..15) on unpacked flags. -/
def condB (f : AFlags) (cc : UInt8) : Bool :=
  let r := match cc >>> 1 with
    | 0 => f.of
    | 1 => f.cf
    | 2 => f.zf
    | 3 => f.cf || f.zf
    | 4 => f.sf
    | 5 => f.pf
    | 6 => f.sf != f.of
    | _ => f.zf || f.sf != f.of
  if cc &&& 1 == 1 then !r else r


end X64
