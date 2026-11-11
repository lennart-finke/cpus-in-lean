/-!
# Machine words

Operands are carried in a `UInt32` together with an operand size `Sz` (1, 2 or 4 bytes).
All values are kept zero-extended / masked to their size.
-/
namespace X86

/- Elaborate shifts through the homogeneous `ShiftLeft`/`ShiftRight` classes, so that the
result type is known immediately and numeric literals in surrounding bitwise expressions
get the operand type (instead of defaulting to `Nat`). -/
scoped macro_rules | `($x <<< $y) => `(ShiftLeft.shiftLeft $x $y)
scoped macro_rules | `($x >>> $y) => `(ShiftRight.shiftRight $x $y)

/-- Operand size in bytes: 1, 2 or 4. -/
abbrev Sz := UInt8

@[inline] def Sz.mask (s : Sz) : UInt32 :=
  if s == 1 then 0xFF else if s == 2 then 0xFFFF else 0xFFFFFFFF

@[inline] def Sz.msb (s : Sz) : UInt32 :=
  if s == 1 then 0x80 else if s == 2 then 0x8000 else 0x80000000

@[inline] def Sz.bits (s : Sz) : UInt32 := s.toUInt32 * 8

/-- Sign-extend a value of size `s` to 32 bits. -/
@[inline] def sext (s : Sz) (x : UInt32) : UInt32 :=
  if s == 1 then (if x &&& 0x80 != 0 then x ||| 0xFFFFFF00 else x &&& 0xFF)
  else if s == 2 then (if x &&& 0x8000 != 0 then x ||| 0xFFFF0000 else x &&& 0xFFFF)
  else x

/-- Sign-extend a value of size `s` to a mathematical integer. -/
@[inline] def toSInt (s : Sz) (x : UInt32) : Int :=
  let v := (x &&& s.mask).toNat
  if x &&& s.msb != 0 then (v : Int) - ((s.mask.toNat + 1 : Nat) : Int) else v

/-- `true` iff the low byte of `x` has an even number of set bits (x86 PF). -/
@[inline] def parity (x : UInt32) : Bool :=
  let b := x &&& 0xFF
  let b := b ^^^ (b >>> 4)
  let b := b ^^^ (b >>> 2)
  let b := b ^^^ (b >>> 1)
  (b &&& 1) == 0

@[inline] def bit (x : UInt32) (i : UInt32) : Bool := (x >>> i) &&& 1 != 0

@[inline] def b2u (b : Bool) : UInt32 := if b then 1 else 0

-- EFLAGS bit masks.
namespace Flag
def CF   : UInt32 := 0x1
def PF   : UInt32 := 0x4
def AF   : UInt32 := 0x10
def ZF   : UInt32 := 0x40
def SF   : UInt32 := 0x80
def TF   : UInt32 := 0x100
def IF   : UInt32 := 0x200
def DF   : UInt32 := 0x400
def OF   : UInt32 := 0x800
def IOPL : UInt32 := 0x3000
def NT   : UInt32 := 0x4000
def RF   : UInt32 := 0x10000
def VM   : UInt32 := 0x20000
def AC   : UInt32 := 0x40000
/-- Virtual interrupt flag and virtual interrupt pending (CR4.VME/PVI). Names only: POPF, IRET and
`valid` do not implement them yet. -/
def VIF  : UInt32 := 0x80000
def VIP  : UInt32 := 0x100000
def ID   : UInt32 := 0x200000
/-- The six arithmetic status flags. -/
def arith : UInt32 := 0x8D5
/-- Bits that exist on this CPU model (bit 1 is reserved-one). -/
def valid : UInt32 := 0x00277FD5
end Flag

namespace DR6
def BD : UInt32 := 0x2000
def BS : UInt32 := 0x4000
def BT : UInt32 := 0x8000
end DR6

namespace CR0
def PE : UInt32 := 0x1
def MP : UInt32 := 0x2
def EM : UInt32 := 0x4
def TS : UInt32 := 0x8
def ET : UInt32 := 0x10
def NE : UInt32 := 0x20
def WP : UInt32 := 0x10000
def AM : UInt32 := 0x40000
def NW : UInt32 := 0x20000000
def CD : UInt32 := 0x40000000
def PG : UInt32 := 0x80000000
end CR0

namespace CR4
def VME : UInt32 := 0x1
def PVI : UInt32 := 0x2
def TSD : UInt32 := 0x4
def DE  : UInt32 := 0x8
def PSE : UInt32 := 0x10
def PAE : UInt32 := 0x20
def MCE : UInt32 := 0x40
def PGE : UInt32 := 0x80
def PCE : UInt32 := 0x100
def OSFXSR : UInt32 := 0x200
def OSXMMEXCPT : UInt32 := 0x400
def UMIP : UInt32 := 0x800
def FSGSBASE : UInt32 := 0x10000
def PCIDE : UInt32 := 0x20000
def OSXSAVE : UInt32 := 0x40000
def SMEP : UInt32 := 0x100000
def SMAP : UInt32 := 0x200000
def PKE : UInt32 := 0x400000
end CR4

/- IA32_EFER (MSR 0xC0000080), AMD APM vol. 2, 3.1.7. Which bits WRMSR accepts is
`Cpuid.eferWritable` (today only NXE); the others are names for later work. -/
namespace EFER
def msr : UInt32 := 0xC0000080
def SCE : UInt32 := 0x1
def LME : UInt32 := 0x100
def LMA : UInt32 := 0x400
def NXE : UInt32 := 0x800
def SVME : UInt32 := 0x1000
def LMSLE : UInt32 := 0x2000
def FFXSR : UInt32 := 0x4000
def TCE : UInt32 := 0x8000
end EFER

-- XCR0 (XFEATURE_ENABLED_MASK) state-component bits (SDM vol. 1, 13.1).
namespace XCR0
def X87 : UInt64 := 0x1
def SSE : UInt64 := 0x2
def YMM : UInt64 := 0x4
end XCR0

/-- Read a little-endian value of `n` bytes (1..4) from a byte array; out-of-range bytes read as 0xFF. -/
@[inline] def rdBytes (a : ByteArray) (p : UInt32) (n : UInt32) : UInt32 :=
  let i := p.toNat
  if i + n.toNat ≤ a.size then
    if n == 1 then (a.get! i).toUInt32
    else if n == 2 then (a.get! i).toUInt32 ||| ((a.get! (i+1)).toUInt32 <<< 8)
    else (a.get! i).toUInt32 ||| ((a.get! (i+1)).toUInt32 <<< 8)
       ||| ((a.get! (i+2)).toUInt32 <<< 16) ||| ((a.get! (i+3)).toUInt32 <<< 24)
  else
    -- slow path: byte-wise, open bus beyond the end
    let rec go (k : Nat) (acc : UInt32) : UInt32 :=
      match k with
      | 0 => acc
      | k+1 =>
        let j := i + k
        let b : UInt32 := if j < a.size then (a.get! j).toUInt32 else 0xFF
        go k (acc ||| (b <<< (k.toUInt32 * 8)))
    go n.toNat 0

/-- Write a little-endian value of `n` bytes; bytes beyond the end are dropped. -/
@[inline] def wrBytes (a : ByteArray) (p : UInt32) (n : UInt32) (v : UInt32) : ByteArray :=
  let i := p.toNat
  if i + n.toNat ≤ a.size then
    if n == 1 then a.set! i v.toUInt8
    else if n == 2 then (a.set! i v.toUInt8).set! (i+1) (v >>> 8).toUInt8
    else (((a.set! i v.toUInt8).set! (i+1) (v >>> 8).toUInt8).set! (i+2) (v >>> 16).toUInt8).set!
            (i+3) (v >>> 24).toUInt8
  else
    let rec go (k : Nat) (a : ByteArray) : ByteArray :=
      match k with
      | 0 => a
      | k+1 => go k (if i + k < a.size then a.set! (i+k) (v >>> (k.toUInt32*8)).toUInt8 else a)
    go n.toNat a

end X86
