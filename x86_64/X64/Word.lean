/-!
# Machine words

Operands are carried in a `UInt64` together with a size of 1, 2, 4 or 8 bytes.
All values are kept zero-extended / masked to their size.
-/
namespace X64

/- Elaborate shifts through the homogeneous `ShiftLeft`/`ShiftRight` classes, so that the
result type is known immediately and numeric literals in surrounding bitwise expressions
get the operand type (instead of defaulting to `Nat`). -/
scoped macro_rules | `($x <<< $y) => `(ShiftLeft.shiftLeft $x $y)
scoped macro_rules | `($x >>> $y) => `(ShiftRight.shiftRight $x $y)

/-- Operand size in bytes: 1, 2, 4 or 8. -/
abbrev Sz := UInt8

@[inline] def Sz.mask (s : Sz) : UInt64 :=
  if s == 1 then 0xFF else if s == 2 then 0xFFFF else if s == 4 then 0xFFFFFFFF else 0xFFFFFFFFFFFFFFFF

@[inline] def Sz.msb (s : Sz) : UInt64 :=
  if s == 1 then 0x80 else if s == 2 then 0x8000 else if s == 4 then 0x80000000 else 0x8000000000000000

@[inline] def Sz.bits (s : Sz) : UInt64 := s.toUInt64 * 8

/-- Sign extension to the architectural register width. -/
@[inline] def sext (s : Sz) (x : UInt64) : UInt64 :=
  if x &&& s.msb != 0 then x ||| ~~~s.mask else x &&& s.mask

/-- Sign-extend a value of size `s` to a mathematical integer. -/
@[inline] def toSInt (s : Sz) (x : UInt64) : Int :=
  let v := (x &&& s.mask).toNat
  if x &&& s.msb != 0 then (v : Int) - ((s.mask.toNat + 1 : Nat) : Int) else v

/-- `true` iff the low byte of `x` has an even number of set bits (x86 PF). -/
@[inline] def parity (x : UInt64) : Bool :=
  let b := x &&& 0xFF
  let b := b ^^^ (b >>> 4)
  let b := b ^^^ (b >>> 2)
  let b := b ^^^ (b >>> 1)
  (b &&& 1) == 0

@[inline] def bit (x : UInt64) (i : UInt64) : Bool := (x >>> i) &&& 1 != 0

@[inline] def b2u (b : Bool) : UInt64 := if b then 1 else 0

-- EFLAGS bit masks.
namespace Flag
def CF   : UInt64 := 0x1
def PF   : UInt64 := 0x4
def AF   : UInt64 := 0x10
def ZF   : UInt64 := 0x40
def SF   : UInt64 := 0x80
def TF   : UInt64 := 0x100
def IF   : UInt64 := 0x200
def DF   : UInt64 := 0x400
def OF   : UInt64 := 0x800
def IOPL : UInt64 := 0x3000
def NT   : UInt64 := 0x4000
def RF   : UInt64 := 0x10000
def VM   : UInt64 := 0x20000
def AC   : UInt64 := 0x40000
def ID   : UInt64 := 0x200000
/-- The six arithmetic status flags. -/
def arith : UInt64 := 0x8D5
/-- Bits that exist on this CPU model (bit 1 is reserved-one). -/
def valid : UInt64 := 0x00277FD5
end Flag

namespace CR0
def PE : UInt64 := 0x1
def MP : UInt64 := 0x2
def EM : UInt64 := 0x4
def TS : UInt64 := 0x8
def ET : UInt64 := 0x10
def NE : UInt64 := 0x20
def WP : UInt64 := 0x10000
def AM : UInt64 := 0x40000
def PG : UInt64 := 0x80000000
end CR0

namespace CR4
def TSD : UInt64 := 0x4
def DE  : UInt64 := 0x8
def PSE : UInt64 := 0x10
def PGE : UInt64 := 0x80
end CR4

/-- Read up to eight little-endian bytes. Unmapped physical memory is open bus. -/
def rdBytes (a : ByteArray) (p n : UInt64) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for k in [0:n.toNat] do
    let j := p.toNat + k
    let b := if j < a.size then a.get! j else 0xFF
    v := v ||| (b.toUInt64 <<< (k.toUInt64 * 8))
  return v

/-- Write up to eight little-endian bytes; unmapped physical writes are discarded. -/
def wrBytes (a : ByteArray) (p n v : UInt64) : ByteArray := Id.run do
  let mut a := a
  for k in [0:n.toNat] do
    let j := p.toNat + k
    if j < a.size then a := a.set! j (v >>> (k.toUInt64 * 8)).toUInt8
  return a

/-- Canonical address for four-level (48-bit linear-address) paging. -/
@[inline] def canonical (a : UInt64) : Bool :=
  a >>> 47 == 0 || a >>> 47 == 0x1FFFF

end X64
