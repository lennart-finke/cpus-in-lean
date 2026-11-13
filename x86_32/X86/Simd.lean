import X86.Fpu
import X86.Float
import X86.Cpuid
import X86.Zen2Rcp
/-!
# MMX, SSE and SSE2 (Pentium 4 level), FXSAVE/FXRSTOR

**MMX** (SDM vol. 1, chapter 9). MM0..MM7 are the significands of the x87 physical registers
R0..R7. Every MMX instruction except EMMS sets TOP = 0 and marks all registers valid; a write to
MMk also sets the sign/exponent word of Rk to 0xFFFF. EMMS marks all registers empty. CR0.EM
raises #UD, CR0.TS #NM, and a pending unmasked x87 exception #MF (or FERR# with CR0.NE = 0,
see `fpPending`), in that order. The SSE and SSE2 additions that operate on MMX registers only
(PAVGB, PSHUFW, PADDQ on MMX, ...) follow the same rules; CR4.OSFXSR does not affect them
(SDM vol. 3, 13.1.? lists PSHUFW and MOVNTQ explicitly).

**SSE/SSE2** (SDM vol. 1, chapters 10 and 11). XMM0..XMM7 and MXCSR. CR0.EM = 1 or
CR4.OSFXSR = 0 raise #UD, CR0.TS #NM. The instructions that also use an MMX register
(CVTPI2PS, CVTPS2PI, CVTTPS2PI, CVTPI2PD with an MMX source, CVTPD2PI, CVTTPD2PI, MOVQ2DQ,
MOVDQ2Q) additionally take a pending x87 exception and switch to MMX operation. Arithmetic uses
the exact binary32/binary64 arithmetic of `X86/Float.lean`: masked exceptions set MXCSR flags; an
unmasked one sets the flags, leaves the destination unchanged and raises #XM with
CR4.OSXMMEXCPT = 1, otherwise #UD (SDM vol. 1, 11.5). 128-bit memory operands of packed
instructions must be 16-byte aligned (#GP(0)), except MOVUPS/MOVUPD/MOVDQU and MASKMOVDQU; with
MXCSR.MM (AMD Misaligned SSE mode) only MOVAPx, MOVDQA, MOVNTPx, MOVNTDQ, MOVNTDQA and
FXSAVE/FXRSTOR keep the requirement (`vecAddr`).

The decoder keeps the 66/F2/F3 prefixes (`Inst.p66`, `Inst.rep`); for the 0F map they select the
instruction: F2 or F3 (the last one wins) take precedence over 66. A prefix combination with no
instruction in the SDM opcode map (blank cells of tables A-3/A-4, e.g. F3 0F 58 is ADDSS but
F3 0F 54 is undefined) raises #UD. SSE3 and later extensions are in `X86/Ext/Sse.lean`.

**RCPPS/RCPSS/RSQRTPS/RSQRTSS** return approximations whose exact bits are implementation
specific (relative error ≤ 1.5·2^-12, SDM). The model computes the EPYC 7742's function (`FP.rcp`,
`FP.rsqrt`): a 4096-entry table indexed by fraction bits 22..11 of the operand (two tables by exponent
parity for RSQRT), 12-bit result fractions, independent of MXCSR.RC/DAZ/FTZ and without flags
(`X86/Zen2Rcp.lean`, reconstructed from the native family `sse_rcp_sweep`, every entry observed at four
points, and checked against all 52,794 RCP/RSQRT lanes of the extended run). The former definition,
RNE(1/x) and RNE(1/RNE(√x)), is kept as `FP.rcpSpec`/`FP.rsqrtSpec`; the table function is within the
SDM's 1.5·2^-12 of exact 1/x and 1/√x over every entry (`Proofs/EpycHw.lean`).

**FXSAVE/FXRSTOR** use the 512-byte 32-bit format. MXCSR_MASK is 0x2FFFF (all MXCSR bits
including DAZ, and MM, bit 17, of AMD's Misaligned SSE mode; `mxcsrMask`). With CR4.OSFXSR = 0,
MXCSR, MXCSR_MASK and the XMM registers are neither saved nor restored (the SDM leaves this
implementation dependent). Reserved fields of the image are not written, apart from the zero
upper halves of FTW, FCS and FDS.

CLFLUSH, CLFLUSHOPT and CLWB are `X86/Ext/Gpr.lean`'s. LFENCE, MFENCE, SFENCE and the PREFETCH hints
are no-ops in this sequential model; non-temporal stores are ordinary stores.
-/
namespace X86

namespace V128
@[inline] def lane (v : V128) (bits k : Nat) : UInt64 :=
  let shift := bits * k
  let word := if shift < 64 then v.lo else v.hi
  let x := word >>> (shift % 64).toUInt64
  if bits == 64 then x else x &&& (((1 : UInt64) <<< bits.toUInt64) - 1)

@[inline] def setLane (v : V128) (bits k : Nat) (x : UInt64) : V128 :=
  let shift := bits * k
  let mask : UInt64 := if bits == 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< bits.toUInt64) - 1
  let s := (shift % 64).toUInt64
  let update := fun (w : UInt64) => (w &&& ~~~(mask <<< s)) ||| ((x &&& mask) <<< s)
  if shift < 64 then { v with lo := update v.lo } else { v with hi := update v.hi }

/-- The `w / bits` lanes of the low `w` bits. -/
def lanes (v : V128) (w bits : Nat) : Array UInt64 := (Array.range (w / bits)).map (v.lane bits ·)

def ofLanes (bits : Nat) (ls : Array UInt64) : V128 := Id.run do
  let mut r : V128 := {}
  for k in [0:ls.size] do r := r.setLane bits k ls[k]!
  return r

/-- Lane-wise binary operation on the low `w` bits. -/
def map2 (w bits : Nat) (f : UInt64 → UInt64 → UInt64) (a b : V128) : V128 :=
  ofLanes bits ((Array.range (w / bits)).map fun k => f (a.lane bits k) (b.lane bits k))
end V128

/-! ## Integer lane arithmetic -/

/-- Signed value of a `bits`-wide lane. -/
@[inline] def lsx (bits : Nat) (x : UInt64) : Int :=
  if bits == 64 then (if x >>> 63 != 0 then (x.toNat : Int) - (2^64 : Nat) else x.toNat)
  else if x >>> (bits - 1).toUInt64 &&& 1 != 0 then (x.toNat : Int) - (2^bits : Nat) else x.toNat

/-- Two's-complement encoding of an integer in a lane. -/
@[inline] def lenc (bits : Nat) (z : Int) : UInt64 := (z % (2^bits : Nat)).toNat.toUInt64

@[inline] def satS (bits : Nat) (z : Int) : UInt64 :=
  let hi : Int := (2^(bits - 1) : Nat) - 1
  let lo : Int := -((2^(bits - 1) : Nat) : Int)
  lenc bits (if z > hi then hi else if z < lo then lo else z)

@[inline] def satU (bits : Nat) (z : Int) : UInt64 :=
  let hi : Int := (2^bits : Nat) - 1
  lenc bits (if z > hi then hi else if z < 0 then 0 else z)

@[inline] def allOnes (b : Bool) : UInt64 := if b then 0xFFFFFFFFFFFFFFFF else 0

/-- Shift every `bits`-wide lane by `cnt`: kind 0 logical right, 1 arithmetic right, 2 left. -/
def pshift (w bits : Nat) (kind : Nat) (cnt : UInt64) (a : V128) : V128 :=
  V128.ofLanes bits ((a.lanes w bits).map fun x =>
    if kind == 1 then
      let c := if cnt ≥ bits.toUInt64 then bits - 1 else cnt.toNat
      lenc bits (lsx bits x / (2^c : Nat))  -- Int division rounds down for positive divisors
    else if cnt ≥ bits.toUInt64 then 0
    else if kind == 0 then x >>> cnt
    else lenc bits ((x <<< cnt).toNat))

/-- Byte shift of a 128-bit value (PSLLDQ / PSRLDQ). -/
def byteShift (left : Bool) (cnt : UInt64) (a : V128) : V128 :=
  let c := if cnt > 16 then 16 else cnt.toNat
  V128.ofLanes 8 ((Array.range 16).map fun k =>
    if left then (if k ≥ c then a.lane 8 (k - c) else 0)
    else (if k + c < 16 then a.lane 8 (k + c) else 0))

/-- The packed-integer instructions with operands `a` (destination) and `b` (source), on `w`
(64 for MMX, 128 for XMM) bits. `b0` is the second opcode byte. -/
def pint (b0 : UInt8) (w : Nat) (a b : V128) : V128 :=
  let m2 := fun (bits : Nat) (f : UInt64 → UInt64 → UInt64) => V128.map2 w bits f a b
  let unpack := fun (bits : Nat) (high : Bool) =>
    let n := w / bits
    let start := if high then n / 2 else 0
    V128.ofLanes bits ((Array.range n).map fun k =>
      if k % 2 == 0 then a.lane bits (start + k / 2) else b.lane bits (start + k / 2))
  let pack := fun (bits : Nat) (sat : Nat → Int → UInt64) =>
    V128.ofLanes (bits / 2) ((a.lanes w bits ++ b.lanes w bits).map fun x => sat (bits / 2) (lsx bits x))
  match b0 with
  | 0x60 => unpack 8 false | 0x61 => unpack 16 false | 0x62 => unpack 32 false
  | 0x68 => unpack 8 true | 0x69 => unpack 16 true | 0x6A => unpack 32 true
  | 0x6C => unpack 64 false | 0x6D => unpack 64 true
  | 0x63 => pack 16 satS | 0x6B => pack 32 satS | 0x67 => pack 16 satU
  | 0x64 => m2 8 fun x y => allOnes (lsx 8 x > lsx 8 y)
  | 0x65 => m2 16 fun x y => allOnes (lsx 16 x > lsx 16 y)
  | 0x66 => m2 32 fun x y => allOnes (lsx 32 x > lsx 32 y)
  | 0x74 => m2 8 fun x y => allOnes (x == y)
  | 0x75 => m2 16 fun x y => allOnes (x == y)
  | 0x76 => m2 32 fun x y => allOnes (x == y)
  | 0xD1 => pshift w 16 0 b.lo a | 0xD2 => pshift w 32 0 b.lo a | 0xD3 => pshift w 64 0 b.lo a
  | 0xE1 => pshift w 16 1 b.lo a | 0xE2 => pshift w 32 1 b.lo a
  | 0xF1 => pshift w 16 2 b.lo a | 0xF2 => pshift w 32 2 b.lo a | 0xF3 => pshift w 64 2 b.lo a
  | 0xD4 => m2 64 (· + ·)
  | 0xD5 => m2 16 fun x y => x * y
  | 0xD8 => m2 8 fun x y => satU 8 ((x.toNat : Int) - y.toNat)
  | 0xD9 => m2 16 fun x y => satU 16 ((x.toNat : Int) - y.toNat)
  | 0xDA => m2 8 min
  | 0xDB => { lo := a.lo &&& b.lo, hi := a.hi &&& b.hi }
  | 0xDC => m2 8 fun x y => satU 8 ((x + y).toNat)
  | 0xDD => m2 16 fun x y => satU 16 ((x + y).toNat)
  | 0xDE => m2 8 max
  | 0xDF => { lo := ~~~a.lo &&& b.lo, hi := ~~~a.hi &&& b.hi }
  | 0xE0 => m2 8 fun x y => (x + y + 1) >>> 1
  | 0xE3 => m2 16 fun x y => (x + y + 1) >>> 1
  | 0xE4 => m2 16 fun x y => (x * y) >>> 16
  | 0xE5 => m2 16 fun x y => lenc 16 ((lsx 16 x * lsx 16 y) / 65536)
  | 0xE8 => m2 8 fun x y => satS 8 (lsx 8 x - lsx 8 y)
  | 0xE9 => m2 16 fun x y => satS 16 (lsx 16 x - lsx 16 y)
  | 0xEA => m2 16 fun x y => if lsx 16 x < lsx 16 y then x else y
  | 0xEB => { lo := a.lo ||| b.lo, hi := a.hi ||| b.hi }
  | 0xEC => m2 8 fun x y => satS 8 (lsx 8 x + lsx 8 y)
  | 0xED => m2 16 fun x y => satS 16 (lsx 16 x + lsx 16 y)
  | 0xEE => m2 16 fun x y => if lsx 16 x > lsx 16 y then x else y
  | 0xEF => { lo := a.lo ^^^ b.lo, hi := a.hi ^^^ b.hi }
  | 0xF4 => m2 64 fun x y => (x &&& 0xFFFFFFFF) * (y &&& 0xFFFFFFFF)
  | 0xF5 => m2 32 fun x y =>
      lenc 32 (lsx 16 (x &&& 0xFFFF) * lsx 16 (y &&& 0xFFFF) + lsx 16 (x >>> 16) * lsx 16 (y >>> 16))
  | 0xF6 => m2 64 fun x y => Id.run do
      let mut s : UInt64 := 0
      for k in [0:8] do
        let p := (x >>> (8 * k).toUInt64) &&& 0xFF
        let q := (y >>> (8 * k).toUInt64) &&& 0xFF
        s := s + (if p ≥ q then p - q else q - p)
      return s
  | 0xF8 => m2 8 (· - ·) | 0xF9 => m2 16 (· - ·) | 0xFA => m2 32 (· - ·) | 0xFB => m2 64 (· - ·)
  | 0xFC => m2 8 (· + ·) | 0xFD => m2 16 (· + ·) | _ => m2 32 (· + ·)

/-- Second opcode bytes of the packed-integer instructions computed by `pint` (MMX form without
prefix, XMM form with 66; 6C/6D exist only with 66). -/
def isPint (b0 : UInt8) : Bool :=
  (0x60 ≤ b0 && b0 ≤ 0x6D) || (0x74 ≤ b0 && b0 ≤ 0x76) || (0xD1 ≤ b0 && b0 ≤ 0xD5) ||
  (0xD8 ≤ b0 && b0 ≤ 0xE5) || (0xE8 ≤ b0 && b0 ≤ 0xEF) || (0xF1 ≤ b0 && b0 ≤ 0xF6) ||
  (0xF8 ≤ b0 && b0 ≤ 0xFE)

/-! ## Floating-point lanes -/

namespace FP
/-- The correctly rounded reciprocal RNE(1/x) with the SDM's special cases: the model's RCPPS/RCPSS
before the EPYC 7742's table was known, kept as the specification the hardware function `rcp` is
checked against (`Proofs/EpycHw.lean`: relative error ≤ 1.5·2^-12 over every table entry). -/
def rcpSpec (x : UInt64) : UInt64 :=
  let f := binary32
  let s := x &&& 0x80000000
  if isNaN f x then x ||| f.quietBit
  else if expField f x == 0 then s ||| f.infinity
  else if isInf f x then s
  else
    let (n, e) := dyadic f x
    let (r, _) := pack f (s != 0) 1 n (-e) 0x1F80
    if expField f r == 0 then s else r

/-- RNE(1/RNE(√x)) with the SDM's special cases (as `rcpSpec`, for RSQRTPS/RSQRTSS). -/
def rsqrtSpec (x : UInt64) : UInt64 :=
  let f := binary32
  let s := x &&& 0x80000000
  if isNaN f x then x ||| f.quietBit
  else if expField f x == 0 then s ||| f.infinity
  else if s != 0 then indefinite f
  else if isInf f x then 0
  else
    let (q, _) := sqrt f x 0x1F80
    let (n, e) := dyadic f q
    let (r, _) := pack f false 1 n (-e) 0x1F80
    if expField f r == 0 then 0 else r

/-- RCPPS/RCPSS (and VEX) of one binary32 lane on the EPYC 7742 (`X86/Zen2Rcp.lean`): NaN quieted;
±0 and denormals (whatever DAZ) give ±∞; ±∞ gives ±0; a normal x with biased exponent E and fraction
bits 22..11 = t gives the sign of x, biased exponent 253 − E and fraction `rcpTable[t]` << 11, or ±0
when 253 − E ≤ 0 (whatever FTZ). No MXCSR effect or flag. -/
def rcp (x : UInt64) : UInt64 :=
  let s := x &&& 0x80000000
  let e := (x >>> 23) &&& 0xFF
  let t := ((x &&& 0x7FFFFF) >>> 11).toNat
  if e == 0xFF && x &&& 0x7FFFFF != 0 then x ||| 0x400000
  else if e == 0 then s ||| 0x7F800000
  else if e == 0xFF then s
  else if e ≥ 253 then s
  else s ||| ((253 - e) <<< 23) ||| ((Zen2Rcp.rcpTable[t]!).toUInt64 <<< 11)

/-- RSQRTPS/RSQRTSS (and VEX) of one binary32 lane on the EPYC 7742 (`X86/Zen2Rcp.lean`): NaN quieted
(also a negative one); ±0 and denormals give ±∞; +∞ gives +0; other negative operands the default NaN
FFC00000h; a positive normal x gives, for odd E, exponent (379 − E)/2 and fraction
`rsqrtOddTable[t]` << 11, for even E, (380 − E)/2 and `rsqrtEvenTable[t]` << 11. No MXCSR effect. -/
def rsqrt (x : UInt64) : UInt64 :=
  let s := x &&& 0x80000000
  let e := (x >>> 23) &&& 0xFF
  let t := ((x &&& 0x7FFFFF) >>> 11).toNat
  if e == 0xFF && x &&& 0x7FFFFF != 0 then x ||| 0x400000
  else if e == 0 then s ||| 0x7F800000
  else if s != 0 then 0xFFC00000
  else if e == 0xFF then 0
  else if e &&& 1 == 1 then (((379 - e) / 2) <<< 23) ||| ((Zen2Rcp.rsqrtOddTable[t]!).toUInt64 <<< 11)
  else (((380 - e) / 2) <<< 23) ||| ((Zen2Rcp.rsqrtEvenTable[t]!).toUInt64 <<< 11)

/-- MINPS/MAXPS lane: the second operand unless the first is strictly smaller/larger; any NaN
gives the second operand and IE. -/
def minmax (f : Format) (isMax : Bool) (a b mx : UInt64) : UInt64 × UInt64 :=
  let (a, da) := prepare f mx a
  let (b, db) := prepare f mx b
  let nan := isNaN f a || isNaN f b
  let c := compare f a b
  (if !nan && (if isMax then c > 0 else c < 0) then a else b, if nan then 1 else da ||| db)

/-- CMPPS lane with predicate `pred` (imm8 bits 2..0): all ones if true. -/
def cmp (f : Format) (pred : UInt32) (a b mx : UInt64) : UInt64 × UInt64 :=
  let (a, da) := prepare f mx a
  let (b, db) := prepare f mx b
  let unord := isNaN f a || isNaN f b
  let c := compare f a b
  let yes := match pred with
    | 0 => !unord && c == 0 | 1 => !unord && c < 0 | 2 => !unord && c ≤ 0 | 3 => unord
    | 4 => unord || c != 0 | 5 => unord || c ≥ 0 | 6 => unord || c > 0 | _ => !unord
  let signaling := pred == 1 || pred == 2 || pred == 5 || pred == 6
  (if yes then 0xFFFFFFFFFFFFFFFF else 0,
   if (signaling && unord) || isSNaN f a || isSNaN f b then 1 else if unord then 0 else da ||| db)
end FP

/-! ## State access and checks -/

@[inline] def getXmm (r : UInt8) : M V128 := fun m => .ok m.cpu.xmm[(r &&& 7).toNat]! m
@[inline] def setXmm (r : UInt8) (v : V128) : M Unit :=
  modCpu fun c => { c with sse := { c.sse with xmm := c.sse.xmm.set! (r &&& 7).toNat v } }
@[inline] def getMm (r : UInt8) : M UInt64 := fun m => .ok m.cpu.fpr[(r &&& 7).toNat]!.sig m
/-- Write MMk: the significand of Rk, with the sign/exponent word set to all ones. -/
@[inline] def setMm (r : UInt8) (v : UInt64) : M Unit :=
  modCpu fun c => { c with fpr := c.fpr.set! (r &&& 7).toNat { sig := v, se := 0xFFFF } }

namespace Cpu
/-- The x87-to-MMX transition: TOP = 0 and all registers valid. -/
@[inline] def mmxEnter (c : Cpu) : Cpu := { c.setTop 0 with fempty := 0 }
end Cpu

def mmxEnter : M Unit := modCpu Cpu.mmxEnter

/-- Checks of an MMX instruction (and EMMS): CR0.EM, CR0.TS, pending x87 exception. -/
def mmxPre : M Unit := do
  let c ← cpu
  if c.cr0 &&& CR0.EM != 0 then ud
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM
  if c.fsw &&& 0x80 != 0 then fpPending

/-- Checks of an MMX instruction, then the switch to MMX operation. -/
def mmxCheck : M Unit := do
  mmxPre
  mmxEnter

/-- Checks of an SSE/SSE2 instruction. -/
def sseCheck : M Unit := do
  let c ← cpu
  if c.cr0 &&& CR0.EM != 0 || c.cr4 &&& CR4.OSFXSR == 0 then ud
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM

/-- An SSE instruction that also uses an MMX register: pending x87 exception, MMX transition. -/
def sseMmx : M Unit := do
  if (← cpu).fsw &&& 0x80 != 0 then fpPending
  mmxEnter

/-- Merge SIMD exception flags into MXCSR; an unmasked one raises #XM (or #UD with
CR4.OSXMMEXCPT = 0) before any destination is written. If any lane has an unmasked input exception
(IE, DE, ZE), no output exceptions (OE, UE, PE) are reported (SDM vol. 1, 11.5.3). The MXCSR flags
survive the fault (`faultCpu`). -/
def sseStatus (flags : UInt64) : M Unit := do
  let c ← cpu
  let fl := flags.toUInt32 &&& 0x3F
  let unmasked := fl &&& ~~~(c.mxcsr >>> 7) &&& 0x3F
  let fl := if unmasked &&& 7 != 0 then fl &&& 7 else fl
  modCpu fun c => { c with sse := { c.sse with mxcsr := c.mxcsr ||| fl } }
  if unmasked != 0 then
    if c.cr4 &&& CR4.OSXMMEXCPT != 0 then exc Vec.XM else ud

/-- Mandatory prefix: 0 none, 1 66, 2 F3, 3 F2 (F2/F3 take precedence over 66); `Inst.pp`. -/
@[inline] def pfx (i : Inst) : Nat := i.pp.toNat

/-! ## Memory operands -/

/-- MXCSR.MM (bit 17, AMD Misaligned SSE mode, `Sse.lean`). -/
def MXCSR_MM : UInt32 := 0x20000

/-- Instructions whose 16-byte alignment requirement MXCSR.MM does not lift (AMD APM vol. 1, 4.3.2):
MOVAPS/MOVAPD (0F 28/29), MOVNTPS/MOVNTPD (0F 2B), MOVDQA (66 0F 6F/7F), MOVNTDQ (66 0F E7), FXSAVE and
FXRSTOR (0F AE), MOVNTDQA (66 0F 38 2A, APM vol. 4 MOVNTDQA); and every VEX form that requests
alignment (MM controls only legacy SSE instructions). -/
def alignStrict (i : Inst) : Bool :=
  i.vex || i.op == 0x128 || i.op == 0x129 || i.op == 0x12B || i.op == 0x1E7 || i.op == 0x1AE ||
  i.op == 0x22A || ((i.op == 0x16F || i.op == 0x17F) && i.pp == 1)

/-- The exception (error code 0) for a misaligned operand that must be 16-byte aligned: #GP, or with
MXCSR.MM = 1 for a non-strict instruction #AC when alignment checking is enabled and none otherwise. -/
def misalignExc (c : Cpu) (i : Inst) : Option UInt8 :=
  if c.mxcsr &&& MXCSR_MM == 0 || alignStrict i then some Vec.GP
  else if c.acEnabled then some Vec.AC
  else none

/-- Linear address of an `n`-byte vector operand: segment checks, 16-byte alignment if `align`, and
for a store a write check of the whole range before anything is written. A misaligned operand
raises #GP(0); with MXCSR.MM = 1 (Misaligned SSE mode), except for `alignStrict` instructions, it
raises #AC(0) instead when alignment checking is enabled (CR0.AM, EFLAGS.AC, CPL 3) and nothing
otherwise (AMD APM vol. 1, 4.2.2 and 4.3.2). -/
def vecAddr (i : Inst) (n : UInt32) (write align : Bool) (acFirst : UInt32 := 0) : M UInt32 := do
  let off ← fpEa i
  -- the alignment checks come before the segment-limit check: a misaligned 16-byte operand whose
  -- range wraps past the 4 GiB limit of SS raises #GP(0), not #SS(0), on the EPYC 7742 (native
  -- `enc_fuzz`: PMADDWD; wrapping operands without an alignment requirement raise #SS(0) there too)
  let lin0 := ((← cpu).getSeg i.seg).base + off
  -- `acFirst`: an #AC check at this alignment that comes before the 16-byte #GP check (FXSAVE, FXRSTOR)
  if acFirst != 0 then acChk lin0 acFirst (← isUser)
  if align && lin0 &&& 15 != 0 then
    match misalignExc (← cpu) i with
    | some v => exc v (some 0)
    | none => pure ()
  let lin ← segAddr i.seg off n write
  -- alignment check of the operand (#AC at CPL 3: 64-bit media 8, 128-bit media 16, smaller operands
  -- by their size; AMD APM vol. 2, table 8-7; system A, `acChk`)
  acChk lin (if n > 16 then 16 else n) (← isUser)
  if write then linProbeWr lin n (← isUser)
  return lin

def rdLin (lin n : UInt32) : M V128 := do
  let u ← isUser
  if n ≤ 4 then return { lo := (← linRd lin n u).toUInt64 }
  let lo := (← linRd lin 4 u).toUInt64 ||| ((← linRd (lin + 4) 4 u).toUInt64 <<< 32)
  if n == 8 then return { lo }
  let hi := (← linRd (lin + 8) 4 u).toUInt64 ||| ((← linRd (lin + 12) 4 u).toUInt64 <<< 32)
  return { lo, hi }

def wrLin (lin n : UInt32) (v : V128) : M Unit := do
  let u ← isUser
  if n ≤ 4 then linWr lin n v.lo.toUInt32 u
  else
    linWr lin 4 v.lo.toUInt32 u
    linWr (lin + 4) 4 (v.lo >>> 32).toUInt32 u
    if n == 16 then
      linWr (lin + 8) 4 v.hi.toUInt32 u
      linWr (lin + 12) 4 (v.hi >>> 32).toUInt32 u

/-- Read the `n`-byte memory operand (zero-extended). -/
def rdVM (i : Inst) (n : UInt32) (align : Bool := false) : M V128 := do
  rdLin (← vecAddr i n false align) n

def wrVM (i : Inst) (n : UInt32) (v : V128) (align : Bool := false) : M Unit := do
  wrLin (← vecAddr i n true align) n v

/-- XMM register or `n`-byte memory operand. -/
@[inline] def rdXE (i : Inst) (n : UInt32) (align : Bool := false) : M V128 := do
  if i.isMem then rdVM i n align else getXmm i.rm

/-- MMX register or `n`-byte memory operand. -/
@[inline] def rdME (i : Inst) (n : UInt32 := 8) : M UInt64 := do
  if i.isMem then return (← rdVM i n).lo else getMm i.rm

/-- 32-bit general register or memory operand. -/
@[inline] def rdGE32 (i : Inst) : M UInt32 := do
  if i.isMem then rdMem i.seg (← fpEa i) 4 else getReg i.rm

@[inline] def needMemS (i : Inst) : M Unit := if i.isMem then pure () else ud
@[inline] def needReg (i : Inst) : M Unit := if i.isMem then ud else pure ()

/-! ## Instructions -/

/-- Packed floating-point arithmetic, compares and the approximations (opcodes 51..53, 58..5F,
C2): packed single (no prefix), packed double (66), scalar single (F3), scalar double (F2). -/
def sseArith (i : Inst) (b0 : UInt8) (p : Nat) : M Unit := do
  sseCheck
  let scalar := p ≥ 2
  let double := p == 1 || p == 3
  let f := if double then FP.binary64 else FP.binary32
  let bits := if double then 64 else 32
  let a ← getXmm i.reg
  let src ← rdXE i (if scalar then (bits / 8).toUInt32 else 16) (!scalar)
  let mx := (← cpu).mxcsr.toUInt64
  let mut r := a
  let mut flags : UInt64 := 0
  for k in [0:if scalar then 1 else 128 / bits] do
    let x := a.lane bits k
    let y := src.lane bits k
    let (v, fl) := match b0 with
      | 0x58 => FP.binary f .add x y mx
      | 0x59 => FP.binary f .mul x y mx
      | 0x5C => FP.binary f .sub x y mx
      | 0x5E => FP.binary f .div x y mx
      | 0x51 => FP.sqrt f y mx
      | 0x52 => (FP.rsqrt y, 0)
      | 0x53 => (FP.rcp y, 0)
      | 0x5D => FP.minmax f false x y mx
      | 0x5F => FP.minmax f true x y mx
      | _ => FP.cmp f (i.imm &&& 7) x y mx
    r := r.setLane bits k v
    flags := flags ||| fl
  sseStatus flags
  setXmm i.reg r

/-- COMISS/UCOMISS/COMISD/UCOMISD: ZF, PF, CF from the comparison; OF, SF, AF cleared. -/
def sseComi (i : Inst) (signaling double : Bool) : M Unit := do
  sseCheck
  let f := if double then FP.binary64 else FP.binary32
  let bits := if double then 64 else 32
  let a := (← getXmm i.reg).lane bits 0
  let b := (← rdXE i (bits / 8).toUInt32).lane bits 0
  let mx := (← cpu).mxcsr.toUInt64
  let (a, da) := FP.prepare f mx a
  let (b, db) := FP.prepare f mx b
  let unord := FP.isNaN f a || FP.isNaN f b
  let invalid := if signaling then unord else FP.isSNaN f a || FP.isSNaN f b
  sseStatus (if invalid then 1 else if unord then 0 else da ||| db)
  let c := FP.compare f a b
  setFlags Flag.arith (if unord then Flag.ZF ||| Flag.PF ||| Flag.CF else if c == 0 then Flag.ZF
                       else if c < 0 then Flag.CF else 0)

/-- Convert lanes of `src` (format `sf`, or int32 if `none`) to format `df` (or int32 if `none`,
truncating if `trunc`), `n` lanes. -/
def cvtLanes (sf df : Option FP.Format) (trunc : Bool) (n : Nat) (src : V128) (mx : UInt64) :
    Array UInt64 × UInt64 := Id.run do
  let sb := match sf with | some f => f.fraction + f.exponent + 1 | none => 32
  let mut out : Array UInt64 := #[]
  let mut flags : UInt64 := 0
  for k in [0:n] do
    let x := src.lane sb k
    let (v, fl) := match sf, df with
      | none, some f => FP.fromInt f (lsx 32 x) mx
      | some f, none => FP.toInt f x mx 32 trunc
      | some f, some g => FP.convert f g x mx
      | none, none => (x, 0)
    out := out.push v
    flags := flags ||| fl
  return (out, flags)

/-- The conversions 2A, 2C, 2D, 5A, 5B, E6. -/
def sseCvt (i : Inst) (b0 : UInt8) (p : Nat) : M Unit := do
  let s32 := some FP.binary32
  let s64 := some FP.binary64
  let mx := fun (_ : Unit) => (do return (← cpu).mxcsr.toUInt64 : M UInt64)
  match b0, p with
  | 0x2A, 0 | 0x2A, 1 => -- CVTPI2PS xmm, mm/m64 / CVTPI2PD xmm, mm/m64
    sseCheck
    -- a memory source touches no MMX register: no transition to MMX operation for CVTPI2PS m64 either
    -- (EPYC 7742, native `enc_fuzz`: 8 cases with TOP ≠ 0 or registers empty; was: CVTPI2PS
    -- transitioned for both forms, CVTPI2PD only for the register form)
    if !i.isMem then sseMmx
    let src : V128 := { lo := ← rdME i }
    let (ls, fl) := cvtLanes none (if p == 0 then s32 else s64) false 2 src (← mx ())
    sseStatus fl
    let a ← getXmm i.reg
    setXmm i.reg (if p == 0 then { a with lo := (V128.ofLanes 32 ls).lo } else V128.ofLanes 64 ls)
  | 0x2A, _ => -- CVTSI2SS / CVTSI2SD xmm, r/m32
    sseCheck
    let x ← rdGE32 i
    let f := if p == 2 then FP.binary32 else FP.binary64
    let (v, fl) := FP.fromInt f (lsx 32 x.toUInt64) (← mx ())
    sseStatus fl
    setXmm i.reg ((← getXmm i.reg).setLane (if p == 2 then 32 else 64) 0 v)
  | 0x2C, 0 | 0x2D, 0 | 0x2C, 1 | 0x2D, 1 => -- CVT(T)PS2PI mm, xmm/m64 / CVT(T)PD2PI mm, xmm/m128
    sseCheck
    sseMmx
    let src ← rdXE i (if p == 0 then 8 else 16) (p == 1)
    let (ls, fl) := cvtLanes (if p == 0 then s32 else s64) none (b0 == 0x2C) 2 src (← mx ())
    sseStatus fl
    setMm i.reg (V128.ofLanes 32 ls).lo
  | 0x2C, _ | 0x2D, _ => -- CVT(T)SS2SI / CVT(T)SD2SI r32, xmm/m32/m64
    sseCheck
    let f := if p == 2 then FP.binary32 else FP.binary64
    let src ← rdXE i (if p == 2 then 4 else 8)
    let (v, fl) := FP.toInt f (src.lane (if p == 2 then 32 else 64) 0) (← mx ()) 32 (b0 == 0x2C)
    sseStatus fl
    setReg i.reg v.toUInt32
  | 0x5A, _ =>
    sseCheck
    let a ← getXmm i.reg
    match p with
    | 0 => -- CVTPS2PD xmm, xmm/m64
      let (ls, fl) := cvtLanes s32 s64 false 2 (← rdXE i 8) (← mx ())
      sseStatus fl
      setXmm i.reg (V128.ofLanes 64 ls)
    | 1 => -- CVTPD2PS xmm, xmm/m128
      let (ls, fl) := cvtLanes s64 s32 false 2 (← rdXE i 16 true) (← mx ())
      sseStatus fl
      setXmm i.reg (V128.ofLanes 32 ls)
    | 2 => -- CVTSS2SD
      let (ls, fl) := cvtLanes s32 s64 false 1 (← rdXE i 4) (← mx ())
      sseStatus fl
      setXmm i.reg { a with lo := ls[0]! }
    | _ => -- CVTSD2SS
      let (ls, fl) := cvtLanes s64 s32 false 1 (← rdXE i 8) (← mx ())
      sseStatus fl
      setXmm i.reg (a.setLane 32 0 ls[0]!)
  | 0x5B, 3 => ud
  | 0x5B, _ => -- CVTDQ2PS / CVTPS2DQ / CVTTPS2DQ
    sseCheck
    let src ← rdXE i 16 true
    let m ← mx ()
    let (ls, fl) := if p == 0 then cvtLanes none s32 false 4 src m
                    else cvtLanes s32 none (p == 2) 4 src m
    sseStatus fl
    setXmm i.reg (V128.ofLanes 32 ls)
  | _, 0 => ud
  | _, _ => -- E6: CVTTPD2DQ (66), CVTDQ2PD (F3), CVTPD2DQ (F2)
    sseCheck
    if p == 2 then
      let (ls, fl) := cvtLanes none s64 false 2 (← rdXE i 8) (← mx ())
      sseStatus fl
      setXmm i.reg (V128.ofLanes 64 ls)
    else
      let (ls, fl) := cvtLanes s64 none (p == 1) 2 (← rdXE i 16 true) (← mx ())
      sseStatus fl
      setXmm i.reg (V128.ofLanes 32 ls)

/-- MMX-form packed-integer instruction. -/
def mmxInt (i : Inst) (b0 : UInt8) : M Unit := do
  mmxCheck
  let a ← getMm i.reg
  -- PUNPCKLBW/WD/DQ mm, mm/m32 read only 32 bits from memory
  let s ← rdME i (if b0 == 0x60 || b0 == 0x61 || b0 == 0x62 then 4 else 8)
  setMm i.reg (pint b0 64 { lo := a } { lo := s }).lo

/-- XMM-form packed-integer instruction. -/
def xmmInt (i : Inst) (b0 : UInt8) : M Unit := do
  sseCheck
  let a ← getXmm i.reg
  let s ← rdXE i 16 true
  setXmm i.reg (pint b0 128 a s)

/-- Shift by immediate (groups 12..14: 0F 71/72/73), register operand only. -/
def shiftImm (i : Inst) (b0 : UInt8) (xmm : Bool) : M Unit := do
  if xmm then sseCheck else mmxCheck
  needReg i
  let bits := if b0 == 0x71 then 16 else if b0 == 0x72 then 32 else 64
  let cnt := (i.imm &&& 0xFF).toUInt64
  let kind ← match i.reg with
    | 2 => pure 0
    | 4 => if b0 == 0x73 then ud else pure 1
    | 6 => pure 2
    | 3 | 7 => if b0 == 0x73 && xmm then pure (i.reg.toNat + 0) else ud
    | _ => ud
  if xmm then
    let a ← getXmm i.rm
    setXmm i.rm (if kind == 3 then byteShift false cnt a else if kind == 7 then byteShift true cnt a
                 else pshift 128 bits kind cnt a)
  else
    setMm i.rm (pshift 64 bits kind cnt { lo := ← getMm i.rm }).lo

/-- PSHUFW / PSHUFD / PSHUFHW / PSHUFLW. -/
def pshuf (i : Inst) (p : Nat) : M Unit := do
  let sel := fun (k : Nat) => ((i.imm >>> (2 * k).toUInt32) &&& 3).toNat
  if p == 0 then
    mmxCheck
    let s : V128 := { lo := ← rdME i }
    setMm i.reg (V128.ofLanes 16 ((Array.range 4).map fun k => s.lane 16 (sel k))).lo
  else
    sseCheck
    let s ← rdXE i 16 true
    let r := match p with
      | 1 => V128.ofLanes 32 ((Array.range 4).map fun k => s.lane 32 (sel k))
      | 2 => { s with hi := (V128.ofLanes 16 ((Array.range 4).map fun k => s.lane 16 (4 + sel k))).lo }
      | _ => { s with lo := (V128.ofLanes 16 ((Array.range 4).map fun k => s.lane 16 (sel k))).lo }
    setXmm i.reg r

/-- Byte-masked store to DS:(E)DI (MASKMOVQ / MASKMOVDQU): only the bytes whose mask byte has bit
7 set are written; all of them are checked before the first is written. -/
def maskMov (data mask : V128) (n : Nat) (i : Inst) : M Unit := do
  needReg i
  let c ← cpu
  let s := if i.segOvr != 0xFF then i.segOvr else SegN.DS
  let di := if i.adsz == 2 then c.edi &&& 0xFFFF else c.edi
  let sel := (List.range n).filter fun k => mask.lane 8 k &&& 0x80 != 0
  -- #AC for DS:(E)DI not 8-byte aligned, for MASKMOVQ and MASKMOVDQU alike, whatever the mask (EPYC
  -- 7742, native `alignment_check`: MASKMOVDQU at offset 8 stores without #AC, offsets 1..6 and 12
  -- raise it; the APM's table 8-7 does not single out the masked stores)
  acChk (((← cpu).getSeg s).base + di) 8 (← isUser)
  -- with a byte selected, the whole n-byte region is checked first: a page fault reports DS:(E)DI
  -- whichever bytes are selected (EPYC 7742, native `enc_fuzz`: MASKMOVQ and MASKMOVDQU on an unmapped
  -- page, 19 cases; was: the first selected byte)
  if !sel.isEmpty then linProbeWr (((← cpu).getSeg s).base + di) n.toUInt32 (← isUser)
  let mut lins : Array UInt32 := #[]
  for k in sel do
    let lin ← segAddr s (di + k.toUInt32) 1 true
    linProbeWr lin 1 (← isUser)
    lins := lins.push lin
  let u ← isUser
  for (k, lin) in sel.zip lins.toList do linWr lin 1 (data.lane 8 k).toUInt32 u

/-! ## FXSAVE / FXRSTOR / LDMXCSR / STMXCSR -/

/-- Writable MXCSR bits, reported as MXCSR_MASK by FXSAVE: bits 15:0 (DAZ included) and, with
Misaligned SSE mode, MM (bit 17; AMD APM vol. 1, 4.2.2: "The corresponding MXCSR_MASK bit (17) is
1, regardless of whether MM is set or not"). -/
def mxcsrMask : UInt32 := if implemented .misalignSse then 0x2FFFF else 0xFFFF

/-! The pieces of the FXSAVE image below are shared with XSAVE/XRSTOR, whose legacy region has the
same layout (`X86/Ext/Xsave.lean`). -/

/-- Bytes 0..23 of the FXSAVE image: FCW, FSW, abridged FTW (byte 5 written as 0), FOP, FIP, FCS,
FDP, FDS (the upper halves of FCS and FDS written as 0). The error pointers (FOP, FIP, FCS, FDP, FDS)
are written only when FSW.ES = 1, as zeros otherwise, by FXSAVE and the XSAVE family alike: the EPYC
7742 does so (native `fpu_pointers`: FXSAVE and XSAVE images with ES = 0 hold zeros although FNSTENV
of the same state stores the pointers, 16 cases) although it reports CPUID Fn8000_0008_EBX[2]
(XSaveErPtr / RstrFpErrPtrs; AMD APM vol. 3, appendix E: "... always save error pointers"); the
restoring instructions load them always (the oracle's XRSTOR of a signal frame with ES = 0 loads the
input pointers: FNSTENV shows them). Was: always written (open questions F5, X6). -/
def fxsaveEnv (c : Cpu) (lin : UInt32) : M Unit := do
  let u ← isUser
  let es := c.fsw &&& 0x80 != 0
  linWr lin 4 (c.fcw.toUInt32 ||| (c.fsw.toUInt32 <<< 16)) u
  linWr (lin + 4) 4 ((~~~c.fempty).toUInt32 ||| (if es then (c.fop.toUInt32 &&& 0x7FF) <<< 16 else 0)) u
  linWr (lin + 8) 4 (if es then c.fip else 0) u
  linWr (lin + 12) 4 (if es then c.fcs.toUInt32 else 0) u
  linWr (lin + 16) 4 (if es then c.fdp else 0) u
  linWr (lin + 20) 4 (if es then c.fds.toUInt32 else 0) u

/-- Bytes 32..159 of the FXSAVE image: ST0..ST7, 10 bytes each in 16-byte slots. With `pad` (FXSAVE and
the XSAVE family's x87 component) bytes 10..15 of a slot are written as zero, as the EPYC 7742 does (the
FXSAVE images of the native `alignment_check` family; XSAVE and XSAVEOPT: `xsave_padding`, 132 cases). -/
def fxsaveRegs (c : Cpu) (lin : UInt32) (pad : Bool := false) : M Unit := do
  let u ← isUser
  for k in [0:8] do
    let v := c.st k
    let a := lin + 32 + 16 * k.toUInt32
    wrLin a 8 { lo := v.sig }
    linWr (a + 8) 2 v.se.toUInt32 u
    if pad then
      linWr (a + 10) 2 0 u
      linWr (a + 12) 4 0 u

/-- Bytes 160..287 of the FXSAVE image: XMM0..XMM7. -/
def fxsaveXmm (c : Cpu) (lin : UInt32) : M Unit := do
  for k in [0:8] do wrLin (lin + 160 + 16 * k.toUInt32) 16 c.xmm[k]!

/-- Read bytes 0..23 of an FXSAVE image: (FCW/FSW, FTW/FOP, FIP, FCS, FDP, FDS). -/
def fxrstorEnv (lin : UInt32) : M (UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := do
  let u ← isUser
  let w0 ← linRd lin 4 u
  let w1 ← linRd (lin + 4) 4 u
  let fip ← linRd (lin + 8) 4 u
  let fcs ← linRd (lin + 12) 2 u
  let fdp ← linRd (lin + 16) 4 u
  let fds ← linRd (lin + 20) 2 u
  return (w0, w1, fip, fcs, fdp, fds)

/-- Read ST0..ST7 (bytes 32..159) of an FXSAVE image. -/
def fxrstorRegs (lin : UInt32) : M (Array F80) := do
  let u ← isUser
  let mut regs : Array F80 := #[]
  for k in [0:8] do
    let a := lin + 32 + 16 * k.toUInt32
    let sig := (← rdLin a 8).lo
    let se ← linRd (a + 8) 2 u
    regs := regs.push { sig, se := se.toUInt16 }
  return regs

/-- The x87 state of an FXSAVE image loaded (`env` from `fxrstorEnv`, `regs` from `fxrstorRegs`):
ST(k) goes to physical register (TOP + k) mod 8; as FLDENV, FSW.ES and B stay set only if an
unmasked exception flag is set. -/
def Cpu.loadFxX87 (c : Cpu) (env : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32)
    (regs : Array F80) : Cpu :=
  let (w0, w1, fip, fcs, fdp, fds) := env
  let fsw := (w0 >>> 16).toUInt16
  let top := ((fsw >>> 11) &&& 7).toNat
  let fpr := (List.range 8).foldl (fun fpr k => fpr.set! ((top + k) % 8) regs[k]!) c.fpr
  { c with fcw := fcwLoad w0, fsw := fswLoad fsw (fcwLoad w0), fempty := ~~~(w1.toUInt8), fpr,
           fop := ((w1 >>> 16) &&& 0x7FF).toUInt16, fip, fcs := fcs.toUInt16,
           fdp, fds := fds.toUInt16 }

def fxsave (i : Inst) : M Unit := do
  let c ← cpu
  if c.cr0 &&& (CR0.EM ||| CR0.TS) != 0 then exc Vec.NM
  -- with alignment checking (CPL 3, CR0.AM, EFLAGS.AC) an operand that is not 4-byte aligned raises
  -- #AC before the 16-byte #GP(0) check; a 4-byte aligned misaligned one still raises #GP(0) (EPYC
  -- 7742, native `alignment_check`: offsets 1, 2, 3, 6 #AC, offsets 4, 8, 12 #GP; AMD APM vol. 2,
  -- table 8-7 does not list FXSAVE). FXRSTOR likewise (native `fxsave_align`, 12 cases).
  let lin ← vecAddr i 512 false true (acFirst := 4)
  let u ← isUser
  -- the last byte of the area is checked first: a page fault in an area crossing into an unmapped page
  -- reports its last byte (EPYC 7742, native `fxsave_align`: FXSAVE and FXRSTOR, 16 cases)
  linProbeWr (lin + 511) 1 u
  linProbeWr lin 512 u
  fxsaveEnv c lin
  let sse := c.cr4 &&& CR4.OSFXSR != 0
  if sse then
    linWr (lin + 24) 4 c.mxcsr u
    linWr (lin + 28) 4 mxcsrMask u
  fxsaveRegs c lin (pad := true)
  if sse then fxsaveXmm c lin

def fxrstor (i : Inst) : M Unit := do
  let c ← cpu
  if c.cr0 &&& (CR0.EM ||| CR0.TS) != 0 then exc Vec.NM
  let lin ← vecAddr i 512 false true (acFirst := 4)
  let u ← isUser
  let _ ← linRd (lin + 511) 1 u   -- the last byte first, as FXSAVE (see there)
  let env ← fxrstorEnv lin
  let sse := c.cr4 &&& CR4.OSFXSR != 0
  let mut mxcsr := c.mxcsr
  if sse then
    mxcsr ← linRd (lin + 24) 4 u
    if mxcsr &&& ~~~mxcsrMask != 0 then gp 0
  let regs ← fxrstorRegs lin
  let mut xmm := c.xmm
  if sse then
    for k in [0:8] do xmm := xmm.set! k (← rdLin (lin + 160 + 16 * k.toUInt32) 16)
  modCpu fun c => { c.loadFxX87 env regs with sse := { c.sse with mxcsr, xmm } }

/-- 0F AE: FXSAVE, FXRSTOR, LDMXCSR, STMXCSR, CLFLUSH (memory forms) and LFENCE, MFENCE,
SFENCE (register forms). -/
def grp15 (i : Inst) : M Unit := do
  if pfx i != 0 then ud
  if !i.isMem then
    if i.reg ≥ 5 then pure () else ud
  else
    match i.reg with
    | 0 => fxsave i
    | 1 => fxrstor i
    | 2 =>
      sseCheck
      let v ← rdMem i.seg (← fpEa i) 4
      if v &&& ~~~mxcsrMask != 0 then gp 0
      modCpu fun c => { c with sse := { c.sse with mxcsr := v } }
    | 3 =>
      sseCheck
      wrMem i.seg (← fpEa i) 4 (← cpu).mxcsr
    | _ => ud

/-- EMMS: mark all x87 registers empty and set TOP = 0 (SDM vol. 1, table 9-2; the EPYC 7742 clears
TOP: native `enc_fuzz`, `code16`, `fpu_pointers`: 49 cases with TOP ≠ 0; was: TOP kept). -/
def emms : M Unit := do
  mmxPre
  modCpu fun c => { c.setTop 0 with fempty := 0xFF }

/-- Moves and the remaining data-movement instructions of the 0F map. -/
def sseMove (i : Inst) (b0 : UInt8) (p : Nat) : M Unit := do
  match b0 with
  | 0x10 | 0x11 =>
    sseCheck
    if p ≤ 1 then -- MOVUPS / MOVUPD
      if b0 == 0x10 then setXmm i.reg (← rdXE i 16)
      else if i.isMem then wrVM i 16 (← getXmm i.reg) else setXmm i.rm (← getXmm i.reg)
    else -- MOVSS / MOVSD
      let bits := if p == 2 then 32 else 64
      let n := (bits / 8).toUInt32
      if b0 == 0x10 then
        if i.isMem then setXmm i.reg (← rdVM i n)
        else setXmm i.reg ((← getXmm i.reg).setLane bits 0 ((← getXmm i.rm).lane bits 0))
      else
        let v ← getXmm i.reg
        if i.isMem then wrVM i n v
        else setXmm i.rm ((← getXmm i.rm).setLane bits 0 (v.lane bits 0))
  | 0x12 | 0x16 => -- MOVLPS/MOVHLPS, MOVLPD, MOVHPS/MOVLHPS, MOVHPD
    if p ≥ 2 then ud
    sseCheck
    if p == 1 then needMemS i
    let a ← getXmm i.reg
    let s ← rdXE i 8
    if b0 == 0x12 then setXmm i.reg { a with lo := if i.isMem then s.lo else s.hi }
    else setXmm i.reg { a with hi := s.lo }
  | 0x13 | 0x17 => -- MOVLPS/MOVLPD m64, xmm; MOVHPS/MOVHPD m64, xmm
    if p ≥ 2 then ud
    sseCheck
    needMemS i
    let a ← getXmm i.reg
    wrVM i 8 { lo := if b0 == 0x13 then a.lo else a.hi }
  | 0x14 | 0x15 => -- UNPCKLPS/PD, UNPCKHPS/PD
    if p ≥ 2 then ud
    sseCheck
    let a ← getXmm i.reg
    let s ← rdXE i 16 true
    let bits := if p == 1 then 64 else 32
    let n := 128 / bits
    let start := if b0 == 0x15 then n / 2 else 0
    setXmm i.reg (V128.ofLanes bits ((Array.range n).map fun k =>
      if k % 2 == 0 then a.lane bits (start + k / 2) else s.lane bits (start + k / 2)))
  | 0x28 | 0x29 => -- MOVAPS / MOVAPD
    if p ≥ 2 then ud
    sseCheck
    if b0 == 0x28 then setXmm i.reg (← rdXE i 16 true)
    else if i.isMem then wrVM i 16 (← getXmm i.reg) true else setXmm i.rm (← getXmm i.reg)
  | 0x2B => -- MOVNTPS / MOVNTPD
    if p ≥ 2 then ud
    sseCheck
    needMemS i
    wrVM i 16 (← getXmm i.reg) true
  | 0x50 => -- MOVMSKPS / MOVMSKPD
    if p ≥ 2 then ud
    sseCheck
    needReg i
    let s ← getXmm i.rm
    let bits := if p == 1 then 64 else 32
    let mut msk : UInt32 := 0
    for k in [0:128 / bits] do
      if s.lane bits k >>> (bits - 1).toUInt64 != 0 then msk := msk ||| ((1 : UInt32) <<< k.toUInt32)
    setReg i.reg msk
  | 0x54 | 0x55 | 0x56 | 0x57 => -- ANDPS, ANDNPS, ORPS, XORPS (and PD)
    if p ≥ 2 then ud
    sseCheck
    let a ← getXmm i.reg
    let s ← rdXE i 16 true
    setXmm i.reg (match b0 with
      | 0x54 => { lo := a.lo &&& s.lo, hi := a.hi &&& s.hi }
      | 0x55 => { lo := ~~~a.lo &&& s.lo, hi := ~~~a.hi &&& s.hi }
      | 0x56 => { lo := a.lo ||| s.lo, hi := a.hi ||| s.hi }
      | _ => { lo := a.lo ^^^ s.lo, hi := a.hi ^^^ s.hi })
  | 0x6E => -- MOVD mm/xmm, r/m32
    if p == 0 then
      mmxCheck
      setMm i.reg (← rdGE32 i).toUInt64
    else if p == 1 then
      sseCheck
      setXmm i.reg { lo := (← rdGE32 i).toUInt64 }
    else ud
  | 0x7E =>
    if p == 0 || p == 1 then -- MOVD r/m32, mm/xmm
      let v ← if p == 0 then (do mmxCheck; getMm i.reg) else (do sseCheck; return (← getXmm i.reg).lo)
      if i.isMem then wrMem i.seg (← fpEa i) 4 v.toUInt32 else setReg i.rm v.toUInt32
    else if p == 2 then -- MOVQ xmm, xmm/m64
      sseCheck
      setXmm i.reg { lo := (← rdXE i 8).lo }
    else ud
  | 0x6F | 0x7F =>
    if p == 0 then -- MOVQ mm, mm/m64 / MOVQ mm/m64, mm
      mmxCheck
      if b0 == 0x6F then setMm i.reg (← rdME i)
      else if i.isMem then wrVM i 8 { lo := ← getMm i.reg } else setMm i.rm (← getMm i.reg)
    else if p ≤ 2 then -- MOVDQA (66), MOVDQU (F3)
      sseCheck
      let al := p == 1
      if b0 == 0x6F then setXmm i.reg (← rdXE i 16 al)
      else if i.isMem then wrVM i 16 (← getXmm i.reg) al else setXmm i.rm (← getXmm i.reg)
    else ud
  | 0xD6 =>
    if p == 1 then -- MOVQ xmm/m64, xmm
      sseCheck
      let v ← getXmm i.reg
      if i.isMem then wrVM i 8 { lo := v.lo } else setXmm i.rm { lo := v.lo }
    else if p == 2 then -- MOVQ2DQ xmm, mm
      sseCheck
      needReg i
      sseMmx
      setXmm i.reg { lo := ← getMm i.rm }
    else if p == 3 then -- MOVDQ2Q mm, xmm
      sseCheck
      needReg i
      sseMmx
      setMm i.reg (← getXmm i.rm).lo
    else ud
  | 0xD7 => -- PMOVMSKB r32, mm/xmm
    if p ≥ 2 then ud
    if p == 0 then mmxCheck else sseCheck
    needReg i
    let s ← if p == 0 then pure ({ lo := ← getMm i.rm } : V128) else getXmm i.rm
    let mut msk : UInt32 := 0
    for k in [0:if p == 0 then 8 else 16] do
      if s.lane 8 k &&& 0x80 != 0 then msk := msk ||| ((1 : UInt32) <<< k.toUInt32)
    setReg i.reg msk
  | 0xE7 => -- MOVNTQ m64, mm / MOVNTDQ m128, xmm
    if p ≥ 2 then ud
    needMemS i
    if p == 0 then
      mmxCheck
      wrVM i 8 { lo := ← getMm i.reg }
    else
      sseCheck
      wrVM i 16 (← getXmm i.reg) true
  | 0xF7 => -- MASKMOVQ mm, mm / MASKMOVDQU xmm, xmm
    if p ≥ 2 then ud
    if p == 0 then
      mmxCheck
      needReg i
      maskMov { lo := ← getMm i.reg } { lo := ← getMm i.rm } 8 i
    else
      sseCheck
      needReg i
      maskMov (← getXmm i.reg) (← getXmm i.rm) 16 i
  | 0xC4 => -- PINSRW mm/xmm, r32/m16, imm8
    if p ≥ 2 then ud
    if p == 0 then mmxCheck else sseCheck
    let v ← if i.isMem then rdMem i.seg (← fpEa i) 2 else getReg i.rm
    if p == 0 then
      setMm i.reg (({ lo := ← getMm i.reg } : V128).setLane 16 (i.imm &&& 3).toNat v.toUInt64).lo
    else setXmm i.reg ((← getXmm i.reg).setLane 16 (i.imm &&& 7).toNat v.toUInt64)
  | 0xC5 => -- PEXTRW r32, mm/xmm, imm8
    if p ≥ 2 then ud
    if p == 0 then mmxCheck else sseCheck
    needReg i
    let v ← if p == 0 then pure (({ lo := ← getMm i.rm } : V128).lane 16 (i.imm &&& 3).toNat)
            else pure ((← getXmm i.rm).lane 16 (i.imm &&& 7).toNat)
    setReg i.reg v.toUInt32
  | 0xC6 => -- SHUFPS / SHUFPD
    if p ≥ 2 then ud
    sseCheck
    let a ← getXmm i.reg
    let s ← rdXE i 16 true
    let r := if p == 0 then
        V128.ofLanes 32 ((Array.range 4).map fun k =>
          (if k < 2 then a else s).lane 32 ((i.imm >>> (2 * k).toUInt32) &&& 3).toNat)
      else V128.ofLanes 64 #[a.lane 64 (i.imm &&& 1).toNat, s.lane 64 ((i.imm >>> 1) &&& 1).toNat]
    setXmm i.reg r
  | 0xC3 => -- MOVNTI m32, r32
    if p != 0 then ud
    needMemS i
    wrMem i.seg (← fpEa i) 4 (← getReg i.reg)
  | _ => ud

/-- MMX, SSE and SSE2 instructions of the 0F map (see `isSimdOp`). -/
def simd (i : Inst) : M Unit := do
  let b0 := (i.op &&& 0xFF).toUInt8
  let p := pfx i
  if isPint b0 then
    if p == 0 && b0 != 0x6C && b0 != 0x6D then mmxInt i b0
    else if p == 1 then xmmInt i b0
    else ud
  else match b0 with
    | 0x77 => if p != 0 then ud else emms
    | 0xAE => grp15 i
    | 0x51 | 0x58 | 0x59 | 0x5C | 0x5D | 0x5E | 0x5F | 0xC2 => sseArith i b0 p
    | 0x52 | 0x53 => if p == 0 || p == 2 then sseArith i b0 p else ud
    | 0x2E | 0x2F => if p ≥ 2 then ud else sseComi i (b0 == 0x2F) (p == 1)
    | 0x2A | 0x2C | 0x2D | 0x5A | 0x5B | 0xE6 => sseCvt i b0 p
    | 0x70 => pshuf i p
    | 0x71 | 0x72 | 0x73 => if p == 0 then shiftImm i b0 false else if p == 1 then shiftImm i b0 true else ud
    | _ => sseMove i b0 p

/-- Second opcode bytes handled by `simd`. -/
def isSimdOp (b0 : Nat) : Bool :=
  (0x10 ≤ b0 && b0 ≤ 0x17) || (0x28 ≤ b0 && b0 ≤ 0x2F) || (0x50 ≤ b0 && b0 ≤ 0x77) ||
  b0 == 0x7E || b0 == 0x7F || b0 == 0xAE || (0xC2 ≤ b0 && b0 ≤ 0xC6) || (0xD1 ≤ b0 && b0 ≤ 0xFE)

end X86
