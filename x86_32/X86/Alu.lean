import X86.Word
/-!
# Integer ALU

Pure functions computing a result and the new arithmetic flags. Each returns
`(result, flags)` where `flags` contains only bits within `Flag.arith`; callers merge
them into EFLAGS under the mask they affect. Inputs must be masked to the operand size.
-/
namespace X86
open Flag

/-- The six arithmetic status flags, unpacked. -/
structure AFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

/-- Place the flags at their EFLAGS bit positions. -/
@[inline] def AFlags.pack (f : AFlags) : UInt32 :=
  (if f.cf then CF else 0) ||| (if f.pf then PF else 0) ||| (if f.af then AF else 0) |||
  (if f.zf then ZF else 0) ||| (if f.sf then SF else 0) ||| (if f.of then OF else 0)

@[inline] def szp (sz : Sz) (r : UInt32) : UInt32 :=
  (if r == 0 then ZF else 0) ||| (if r &&& sz.msb != 0 then SF else 0) |||
  (if parity r then PF else 0)

/-- ADD/ADC core: `a + b + cin` at size `sz`. -/
@[inline] def addCore (sz : Sz) (a b cin : UInt32) : UInt32 × AFlags :=
  let s : UInt64 := a.toUInt64 + b.toUInt64 + cin.toUInt64
  let r := s.toUInt32 &&& sz.mask
  (r, { cf := s > sz.mask.toUInt64, pf := parity r, af := (a ^^^ b ^^^ r) &&& 0x10 != 0,
        zf := r == 0, sf := r &&& sz.msb != 0, of := (a ^^^ r) &&& (b ^^^ r) &&& sz.msb != 0 })

/-- SUB/SBB/CMP core: `a - b - bin` at size `sz`. -/
@[inline] def subCore (sz : Sz) (a b bin : UInt32) : UInt32 × AFlags :=
  let r := (a - b - bin) &&& sz.mask
  (r, { cf := a.toUInt64 < b.toUInt64 + bin.toUInt64, pf := parity r,
        af := (a ^^^ b ^^^ r) &&& 0x10 != 0, zf := r == 0, sf := r &&& sz.msb != 0,
        of := (a ^^^ b) &&& (a ^^^ r) &&& sz.msb != 0 })

/-- Logical operations: CF = OF = 0, AF = 0 (architecturally undefined). -/
@[inline] def logicCore (sz : Sz) (r : UInt32) : UInt32 × AFlags :=
  (r, { cf := false, pf := parity r, af := false, zf := r == 0, sf := r &&& sz.msb != 0, of := false })

@[inline] def addF (sz : Sz) (a b cin : UInt32) : UInt32 × UInt32 :=
  let (r, f) := addCore sz a b cin; (r, f.pack)

@[inline] def subF (sz : Sz) (a b bin : UInt32) : UInt32 × UInt32 :=
  let (r, f) := subCore sz a b bin; (r, f.pack)

@[inline] def logicF (sz : Sz) (r : UInt32) : UInt32 × UInt32 :=
  let (r, f) := logicCore sz r; (r, f.pack)

/-- The eight classic ALU operations: ADD OR ADC SBB AND SUB XOR CMP. -/
@[inline] def alu (op : UInt8) (sz : Sz) (a b : UInt32) (cf : Bool) : UInt32 × UInt32 :=
  match op with
  | 0 => addF sz a b 0
  | 1 => logicF sz (a ||| b)
  | 2 => addF sz a b (b2u cf)
  | 3 => subF sz a b (b2u cf)
  | 4 => logicF sz (a &&& b)
  | 6 => logicF sz (a ^^^ b)
  | _ => subF sz a b 0

/-- Shift/rotate group (ROL ROR RCL RCR SHL SHR SAL SAR).
Returns `none` when the masked count is zero (no state change), otherwise
`(result, affected flag mask, flag values)`. -/
def shiftOp (op : UInt8) (sz : Sz) (a cnt : UInt32) (cfIn : Bool) : Option (UInt32 × UInt32 × UInt32) :=
  let cnt := cnt &&& 0x1F
  if cnt == 0 then none else
  let bits := sz.bits
  let mask := sz.mask
  let msb := fun (x : UInt32) => x &&& sz.msb != 0
  let fl := fun (cf of : Bool) => (if cf then CF else 0) ||| (if of then OF else 0)
  let a64 := a.toUInt64
  match op with
  | 0 => -- ROL
    let c := cnt % bits
    let r := if c == 0 then a else ((a <<< c) ||| (a >>> (bits - c))) &&& mask
    let cf := r &&& 1 != 0
    some (r, CF ||| OF, fl cf (msb r != cf))
  | 1 => -- ROR
    let c := cnt % bits
    let r := if c == 0 then a else ((a >>> c) ||| (a <<< (bits - c))) &&& mask
    let cf := msb r
    some (r, CF ||| OF, fl cf (msb r != (r &&& (sz.msb >>> 1) != 0)))
  | 2 => -- RCL
    let c := if sz == 4 then cnt else cnt % (bits + 1)
    let w := bits.toUInt64 + 1
    let wm : UInt64 := (1 <<< w) - 1
    let v : UInt64 := (if cfIn then 1 <<< bits.toUInt64 else 0) ||| a64
    let v' := if c == 0 then v else ((v <<< c.toUInt64) ||| (v >>> (w - c.toUInt64))) &&& wm
    let r := v'.toUInt32 &&& mask
    let cf := (v' >>> bits.toUInt64) &&& 1 != 0
    some (r, CF ||| OF, fl cf (msb r != cf))
  | 3 => -- RCR
    let c := if sz == 4 then cnt else cnt % (bits + 1)
    let w := bits.toUInt64 + 1
    let wm : UInt64 := (1 <<< w) - 1
    let v : UInt64 := (if cfIn then 1 <<< bits.toUInt64 else 0) ||| a64
    let v' := if c == 0 then v else ((v >>> c.toUInt64) ||| (v <<< (w - c.toUInt64))) &&& wm
    let r := v'.toUInt32 &&& mask
    let cf := (v' >>> bits.toUInt64) &&& 1 != 0
    some (r, CF ||| OF, fl cf (msb a != cfIn))
  | 5 => -- SHR
    let r := (a64 >>> cnt.toUInt64).toUInt32 &&& mask
    let cf := (a64 >>> (cnt.toUInt64 - 1)) &&& 1 != 0
    some (r, arith, szp sz r ||| fl cf (msb a))
  | 7 => -- SAR
    let s : UInt64 := if msb a then a64 ||| (0xFFFFFFFFFFFFFFFF <<< bits.toUInt64) else a64
    let r := (s >>> cnt.toUInt64).toUInt32 &&& mask
    let cf := (s >>> (cnt.toUInt64 - 1)) &&& 1 != 0
    some (r, arith, szp sz r ||| fl cf false)
  | _ => -- SHL / SAL
    let v := a64 <<< cnt.toUInt64
    let r := v.toUInt32 &&& mask
    let cf := (v >>> bits.toUInt64) &&& 1 != 0
    some (r, arith, szp sz r ||| fl cf (msb r != cf))

/-- SHLD (`left = true`) / SHRD. Returns `none` for a zero count. -/
def shiftDouble (left : Bool) (sz : Sz) (dst src cnt : UInt32) : Option (UInt32 × UInt32) :=
  let cnt := (cnt &&& 0x1F).toUInt64
  if cnt == 0 then none else
  let bits := sz.bits.toUInt64
  let mask := sz.mask
  let d := dst.toUInt64
  let s := src.toUInt64
  -- concatenate into 64 bits (for 16-bit operands with count > 16 the result is
  -- architecturally undefined; we follow the dst:src:dst concatenation)
  let (r, cf) :=
    if left then
      let v : UInt64 := if sz == 4 then (d <<< 32) ||| s else (d <<< 48) ||| (s <<< 32) ||| (d <<< 16)
      let r := if sz == 4 then (v <<< cnt) >>> 32 else (v <<< cnt) >>> 48
      let cf := if sz == 4 then (v >>> (64 - cnt)) &&& 1 != 0 else (v >>> (64 - cnt)) &&& 1 != 0
      (r.toUInt32 &&& mask, cf)
    else
      let v : UInt64 := if sz == 4 then (s <<< 32) ||| d else (d <<< 32) ||| (s <<< 16) ||| d
      let r := v >>> cnt
      let cf := (v >>> (cnt - 1)) &&& 1 != 0
      (r.toUInt32 &&& mask, cf)
  let _ := bits
  let of := (r ^^^ dst) &&& sz.msb != 0
  some (r, szp sz r ||| (if cf then CF else 0) ||| (if of then OF else 0))

/-- Unsigned division of the double-width dividend `a` by `d` at size `sz`
(quotient, remainder); `none` signals #DE (division by zero or quotient overflow). -/
def divU (sz : Sz) (a : UInt64) (d : UInt32) : Option (UInt32 × UInt32) :=
  if d == 0 then none else
  let q := a / d.toUInt64
  if q > sz.mask.toUInt64 then none else some (q.toUInt32, (a % d.toUInt64).toUInt32)

/-- Signed (truncating) division of `a` by `d` with a quotient of `bits` bits;
`none` signals #DE. -/
def divS (bits : Nat) (a d : Int) : Option (Int × Int) :=
  if d == 0 then none else
  let q := a.tdiv d
  let lim : Int := (2 ^ (bits - 1) : Nat)
  if q ≥ lim || q < -lim then none else some (q, a.tmod d)

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

/-- Evaluate condition code `cc` (0..15) on EFLAGS `f`. -/
@[inline] def evalCC (f : UInt32) (cc : UInt8) : Bool :=
  let sf := f &&& SF != 0
  let ofl := f &&& OF != 0
  let r := match cc >>> 1 with
    | 0 => ofl
    | 1 => f &&& CF != 0
    | 2 => f &&& ZF != 0
    | 3 => f &&& (CF ||| ZF) != 0
    | 4 => sf
    | 5 => f &&& PF != 0
    | 6 => sf != ofl
    | _ => f &&& ZF != 0 || sf != ofl
  if cc &&& 1 == 1 then !r else r

end X86
