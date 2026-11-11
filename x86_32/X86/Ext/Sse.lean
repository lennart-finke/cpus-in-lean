import X86.Exec
/-!
# SSE3, SSSE3, SSE4.1, SSE4.2, SSE4a, MisalignSse

Owner: the SSE workstream (legacy encodings; the VEX forms belong to `Avx.lean`).

## Semantic kernels (reused by the AVX work)

The instruction semantics are pure functions on 128-bit values (`V128`) with explicit operands,
independent of the destructive two-operand legacy form. A VEX three-operand form passes VEX.vvvv as
the first source; a 256-bit form applies the kernel to each 128-bit half (all of these instructions
work within 128-bit lanes, except as noted). MMX forms use `w = 64` (the operands in `lo`). FP kernels
take MXCSR (`mx`, as `UInt64`) and return `(result, flags)`; the flags are the MXCSR exception bits to
report through `sseStatus` (or `statusStaged` for DPPS/DPPD), so the caller decides about #XM/#UD
before writing. Arguments named `a` are the first source (the legacy destination), `b` the second
(ModRM r/m or memory).

| kernel | instructions |
|---|---|
| `addsub double a b mx` | ADDSUBPS/PD |
| `hop double sub a b mx` | HADDPS/PD, HSUBPS/PD |
| `movsldup`, `movshdup`, `movddup` | MOVSLDUP, MOVSHDUP, MOVDDUP (`movddup` takes the 64-bit source) |
| `pshufb w a b` | PSHUFB |
| `phop w bits f a b` with `phAdd`, `phSub`, `phAddS`, `phSubS` | PHADDW/D/SW, PHSUBW/D/SW |
| `pmaddubsw w a b`, `pmulhrsw w a b` | PMADDUBSW, PMULHRSW |
| `psign w bits a b`, `pabs w bits b` | PSIGNB/W/D, PABSB/W/D |
| `palignr w a b imm` | PALIGNR (`a` high, `b` low) |
| `blend bits imm a b`, `blendv bits a b mask` | BLENDPS/PD, PBLENDW; BLENDVPS/PD, PBLENDVB (mask = XMM0 / the VEX is4 register) |
| `dpps a b imm mx`, `dppd a b imm mx` | DPPS, DPPD (staged flags, see `statusStaged`) |
| `insertps a s imm` | INSERTPS (`s` = the selected source dword) |
| `mpsadbw a b imm` | MPSADBW |
| `packusdw a b`, `pcmpeqq a b`, `pcmpgtq a b`, `pminmax op a b`, `pmuldq a b`, `pmulld a b` | |
| `pmovx src fromBits toBits signed` | PMOVSX*/PMOVZX* |
| `ptest a b` | PTEST (ZF, CF) |
| `phminposuw b` | PHMINPOSUW |
| `round double scalar a b imm mx` / `FP.roundToIntegral` | ROUNDPS/PD/SS/SD |
| `pcmpstr imm a b la lb`, `strIndex`, `strMask`, `strFlags`, `strLenE`, `strLenI` | PCMPESTRI/M, PCMPISTRI/M |
| `extrq v len idx`, `insertq d s len idx` | EXTRQ, INSERTQ (64-bit fields) |

## Hooks (called by `X86/Dispatch.lean`; `none` = not handled here)

* `op0F?`: F3 0F 12 MOVSLDUP, F2 0F 12 MOVDDUP, F3 0F 16 MOVSHDUP, F3/F2 0F 2B MOVNTSS/MOVNTSD,
  66/F2 0F 78 and 0F 79 EXTRQ/INSERTQ (for 66/F2 0F 78 the decoder puts the two imm8 into `imm` and
  `imm2`), 66/F2 0F 7C/7D HADDPx/HSUBPx, 66/F2 0F D0 ADDSUBPx, F2 0F F0 LDDQU. Other prefixes:
  `none` (the core's #UD).
* `map2?` (0F 38) and `map3?` (0F 3A): SSSE3 (no prefix: MMX form, 66: XMM form), SSE4.1, SSE4.2
  (66 only). Not here: 0F 38 F0/F1 (MOVBE/CRC32, `Gpr.lean`), AES/SHA/PCLMULQDQ (`Crypto.lean`).

## Exceptions and alignment

XMM forms: `sseCheck` (#UD for CR0.EM or CR4.OSFXSR = 0, #NM for CR0.TS) before any memory access;
MMX forms of SSSE3 (PSHUFB mm, ..., PALIGNR mm): `mmxCheck` (CR0.EM #UD, CR0.TS #NM, pending x87
exception #MF, then the switch to MMX operation; CR4.OSFXSR does not matter; SDM vol. 3B, 23.25.3
"Exception Conditions of Legacy SIMD Instructions Operating on MMX Registers", table 23-7
"Exception Conditions for SIMD/MMX Instructions with Memory Reference" (rev. 084; table 22-7 in rev.
076): no CR4.OSFXSR condition, applicable to PSHUFB, PALIGNR, PHADDx, PABSx, PSIGNx, PMADDUBSW,
PMULHRSW among others; AMD APM vol. 4/5). 128-bit memory operands of packed
instructions must be 16-byte aligned (#GP(0), unless MXCSR.MM, see `Simd.vecAddr`); not aligned:
scalar and narrower operands (MOVDDUP m64, PMOVSX/ZX, INSERTPS m32, ROUNDSS/SD, PINSR/PEXTR,
EXTRACTPS, MOVNTSS/SD), LDDQU and PCMPxSTRx (APM vol. 1, 4.3.2; SDM PCMPESTRI "memory operand need
not be aligned"). MOVNTDQA requires alignment. EXTRQ/INSERTQ have register operands only (#UD for a
memory operand, and for 66 0F 78 with ModRM.reg ≠ 0: APM vol. 3 table A-7, group 17 /0).

## Choices where the manuals leave the result undefined

* EXTRQ/INSERTQ (APM vol. 4): bits 127:64 of the destination are "undefined"; the model leaves them
  unchanged (as QEMU and Bochs do; real Zen 2 behaviour unknown, recorded by the native campaign
  family `sse4a`). A field length of 0 means 64. If index + length > 64 the result is undefined; the
  model computes it with the bits above bit 63 as zeros (EXTRQ: `(v >>> idx) &&& mask`; INSERTQ:
  the mask shifted left, truncated at bit 63), as QEMU and Bochs do.
* HADDPx with two NaN operands of one addition: the higher-indexed element is the first operand
  (its NaN is returned; SDM vol. 1, table 4-7 and AMD APM vol. 1, table 4-7: the first source
  operand's NaN), as both manuals write the addition: SDM HADDPS "DEST[31:0] := SRC1[63:32] +
  SRC1[31:0]", HADDPD "DEST[63:0] := SRC1[127:64] + SRC1[63:0]"; AMD APM vol. 4 HADDPS "Adds the
  packed single-precision values in bits [63:32] and bits [31:0] of the first source", HADDPD "in bits
  [127:64] and bits [63:0]". (Older SDM editions wrote `xmm1[0..31] + xmm1[32..63]`.) The order on
  real hardware is not documented beyond this and is recorded by the native campaign family
  `sse3_hadd_nan`. HSUBPx subtracts the higher element from the lower (`x[2j] - x[2j+1]`), so its
  first operand is the lower element.
* DPPS/DPPD: the masked-out products are +0.0 and raise nothing; exceptions are detected per stage
  (multiplies, then the additions in their order, SDM DPPS "Exceptions are determined separately
  for each add and multiply operation, in the order of their execution"), see `statusStaged`.
-/
namespace X86
namespace Sse

open FP in
/-- Format of a `double` (binary64) or single (binary32) lane. -/
@[inline] def fmt (double : Bool) : FP.Format := if double then FP.binary64 else FP.binary32

/-- Lane results and the OR of their flags. -/
def collect (bits : Nat) (rs : Array (UInt64 × UInt64)) : V128 × UInt64 :=
  (V128.ofLanes bits (rs.map (·.1)), rs.foldl (fun acc r => acc ||| r.2) 0)

/-! ## SSE3 kernels -/

/-- ADDSUBPS/PD: even lanes `a - b`, odd lanes `a + b`. -/
def addsub (double : Bool) (a b : V128) (mx : UInt64) : V128 × UInt64 :=
  let bits := if double then 64 else 32
  collect bits ((Array.range (128 / bits)).map fun k =>
    FP.binary (fmt double) (if k % 2 == 0 then .sub else .add) (a.lane bits k) (b.lane bits k) mx)

/-- HADDPx/HSUBPx: the pairs of adjacent lanes of `a`, then of `b`: HSUB `x[2j] - x[2j+1]`, HADD
`x[2j+1] + x[2j]` (the operand order of the manuals, see the module documentation; it matters only for
which of two NaN operands is returned). -/
def hop (double sub : Bool) (a b : V128) (mx : UInt64) : V128 × UInt64 :=
  let bits := if double then 64 else 32
  let n := 128 / bits
  let half := n / 2
  collect bits ((Array.range n).map fun k =>
    let src := if k < half then a else b
    let j := 2 * (k % half)
    if sub then FP.binary (fmt double) .sub (src.lane bits j) (src.lane bits (j + 1)) mx
    else FP.binary (fmt double) .add (src.lane bits (j + 1)) (src.lane bits j) mx)

def movsldup (s : V128) : V128 := V128.ofLanes 32 #[s.lane 32 0, s.lane 32 0, s.lane 32 2, s.lane 32 2]
def movshdup (s : V128) : V128 := V128.ofLanes 32 #[s.lane 32 1, s.lane 32 1, s.lane 32 3, s.lane 32 3]
/-- MOVDDUP: the low quadword of `s` in both halves. -/
def movddup (s : V128) : V128 := { lo := s.lo, hi := s.lo }

/-! ## SSSE3 kernels (`w` = 64 for MMX, 128 for XMM) -/

/-- PSHUFB: byte k is 0 if bit 7 of `b[k]` is set, else `a[b[k] mod (w/8)]`. -/
def pshufb (w : Nat) (a b : V128) : V128 :=
  V128.ofLanes 8 ((Array.range (w / 8)).map fun k =>
    let c := b.lane 8 k
    if c &&& 0x80 != 0 then 0 else a.lane 8 (c.toNat % (w / 8)))

/-- Horizontal pairs: lanes of `a`, then of `b`, as `f x[2j] x[2j+1]`. -/
def phop (w bits : Nat) (f : UInt64 → UInt64 → UInt64) (a b : V128) : V128 :=
  let n := w / bits
  let half := n / 2
  V128.ofLanes bits ((Array.range n).map fun k =>
    let src := if k < half then a else b
    let j := 2 * (k % half)
    f (src.lane bits j) (src.lane bits (j + 1)))

def phAdd : UInt64 → UInt64 → UInt64 := (· + ·)
def phSub : UInt64 → UInt64 → UInt64 := (· - ·)
def phAddS (x y : UInt64) : UInt64 := satS 16 (lsx 16 x + lsx 16 y)
def phSubS (x y : UInt64) : UInt64 := satS 16 (lsx 16 x - lsx 16 y)

/-- PMADDUBSW: unsigned bytes of `a` times signed bytes of `b`, adjacent products added with
signed saturation to words. -/
def pmaddubsw (w : Nat) (a b : V128) : V128 :=
  V128.ofLanes 16 ((Array.range (w / 16)).map fun k =>
    let p := fun (j : Nat) => ((a.lane 8 j).toNat : Int) * lsx 8 (b.lane 8 j)
    satS 16 (p (2 * k) + p (2 * k + 1)))

/-- PMULHRSW: `((a * b) >> 14 + 1) >> 1` of signed words, bits 16:1 of the rounded product. -/
def pmulhrsw (w : Nat) (a b : V128) : V128 :=
  V128.map2 w 16 (fun x y => lenc 16 ((lsx 16 x * lsx 16 y / 16384 + 1) / 2)) a b

/-- PSIGNB/W/D: `a`, its negation or 0 by the sign of `b`. -/
def psign (w bits : Nat) (a b : V128) : V128 :=
  V128.map2 w bits (fun x y =>
    let s := lsx bits y
    if s < 0 then lenc bits (-(lsx bits x)) else if s == 0 then 0 else x) a b

/-- PABSB/W/D: unsigned absolute value (the most negative value stays itself). -/
def pabs (w bits : Nat) (b : V128) : V128 :=
  V128.ofLanes bits ((b.lanes w bits).map fun x => lenc bits (lsx bits x).natAbs)

/-- PALIGNR: bytes `imm ..` of the concatenation `a:b` (`b` in the low half). -/
def palignr (w : Nat) (a b : V128) (imm : Nat) : V128 :=
  let n := w / 8
  V128.ofLanes 8 ((Array.range n).map fun k =>
    let j := k + imm
    if j < n then b.lane 8 j else if j < 2 * n then a.lane 8 (j - n) else 0)

/-! ## SSE4.1 kernels -/

/-- BLENDPS/BLENDPD/PBLENDW: lane k from `b` if bit k of `imm` is set, else from `a`. -/
def blend (bits imm : Nat) (a b : V128) : V128 :=
  V128.ofLanes bits ((Array.range (128 / bits)).map fun k =>
    if (imm >>> k) % 2 == 1 then b.lane bits k else a.lane bits k)

/-- BLENDVPS/BLENDVPD/PBLENDVB: lane k from `b` if the sign bit of `mask[k]` is set. -/
def blendv (bits : Nat) (a b mask : V128) : V128 :=
  V128.ofLanes bits ((Array.range (128 / bits)).map fun k =>
    if mask.lane bits k >>> (bits - 1).toUInt64 != 0 then b.lane bits k else a.lane bits k)

/-- The MXCSR flags of one stage of a multi-stage operation, with the input-exception rule of
`sseStatus` (an unmasked IE/DE/ZE suppresses OE/UE/PE), and whether it raised an unmasked one. -/
def stageFlags (fl mx : UInt64) : UInt64 × Bool :=
  let fl := fl &&& 0x3F
  let unmasked := fl &&& ~~~(mx >>> 7) &&& 0x3F
  ((if unmasked &&& 7 != 0 then fl &&& 7 else fl), unmasked != 0)

/-- Accumulate stages: the flags of each stage until the first with an unmasked exception (the
later stages are not executed); the second component is the unmasked marker. -/
def stages (mx : UInt64) (fls : List UInt64) : UInt64 × Bool :=
  fls.foldl (fun (acc, stop) fl =>
    if stop then (acc, stop) else
    let (f, u) := stageFlags fl mx
    (acc ||| f, u)) (0, false)

/-- DPPS of one 128-bit lane: the result and the raw flags of its three stages (multiplies, the two
first additions, the last addition), before `stages`. The VEX.256 form ORs the flags of the two lanes
stage by stage (`Avx.map3`, VDPPS). -/
def dppsStages (a b : V128) (imm : Nat) (mx : UInt64) : V128 × List UInt64 :=
  let f := FP.binary32
  let prod := fun (k : Nat) => if (imm >>> (4 + k)) % 2 == 1 then FP.binary f .mul (a.lane 32 k) (b.lane 32 k) mx else (0, 0)
  let (p0, f0) := prod 0
  let (p1, f1) := prod 1
  let (p2, f2) := prod 2
  let (p3, f3) := prod 3
  let (s1, g1) := FP.binary f .add p0 p1 mx
  let (s2, g2) := FP.binary f .add p2 p3 mx
  let (s, g) := FP.binary f .add s1 s2 mx
  (V128.ofLanes 32 ((Array.range 4).map fun k => if (imm >>> k) % 2 == 1 then s else 0),
   [f0 ||| f1 ||| f2 ||| f3, g1 ||| g2, g])

/-- DPPS: products of the lanes selected by imm[7:4] (others +0.0), summed as
`(p0 + p1) + (p2 + p3)`, written to the lanes selected by imm[3:0] (others +0.0). Flags: staged
(multiplies, the two first additions, the last addition); returns `(result, flags, unmasked)`. -/
def dpps (a b : V128) (imm : Nat) (mx : UInt64) : V128 × UInt64 × Bool :=
  let (r, fls) := dppsStages a b imm mx
  let (fl, u) := stages mx fls
  (r, fl, u)

/-- DPPD: as DPPS with two binary64 lanes, product mask imm[5:4], result mask imm[1:0]. -/
def dppd (a b : V128) (imm : Nat) (mx : UInt64) : V128 × UInt64 × Bool :=
  let f := FP.binary64
  let prod := fun (k : Nat) => if (imm >>> (4 + k)) % 2 == 1 then FP.binary f .mul (a.lane 64 k) (b.lane 64 k) mx else (0, 0)
  let (p0, f0) := prod 0
  let (p1, f1) := prod 1
  let (s, g) := FP.binary f .add p0 p1 mx
  let (fl, u) := stages mx [f0 ||| f1, g]
  (V128.ofLanes 64 ((Array.range 2).map fun k => if (imm >>> k) % 2 == 1 then s else 0), fl, u)

/-- INSERTPS: `s` (the source dword: lane imm[7:6] of a register, or the m32) into lane imm[5:4]
of `a`, then the lanes selected by imm[3:0] zeroed. -/
def insertps (a : V128) (s : UInt64) (imm : Nat) : V128 :=
  let r := a.setLane 32 ((imm >>> 4) % 4) s
  V128.ofLanes 32 ((Array.range 4).map fun k => if (imm >>> k) % 2 == 1 then 0 else r.lane 32 k)

/-- MPSADBW: word i = Σ_{k<4} |a[o1 + i + k] - b[o2 + k]| (bytes) for o1 = 4·imm[2], o2 = 4·imm[1:0]. -/
def mpsadbw (a b : V128) (imm : Nat) : V128 :=
  let o1 := 4 * ((imm >>> 2) % 2)
  let o2 := 4 * (imm % 4)
  V128.ofLanes 16 ((Array.range 8).map fun i =>
    ((List.range 4).foldl (fun acc k =>
      let x := (a.lane 8 (o1 + i + k)).toNat
      let y := (b.lane 8 (o2 + k)).toNat
      acc + (if x ≥ y then x - y else y - x)) 0).toUInt64)

/-- PACKUSDW: signed dwords of `a`, then `b`, to unsigned words with saturation. -/
def packusdw (a b : V128) : V128 :=
  V128.ofLanes 16 ((a.lanes 128 32 ++ b.lanes 128 32).map fun x => satU 16 (lsx 32 x))

def pcmpeqq (a b : V128) : V128 := V128.map2 128 64 (fun x y => allOnes (x == y)) a b
def pcmpgtq (a b : V128) : V128 := V128.map2 128 64 (fun x y => allOnes (lsx 64 x > lsx 64 y)) a b

/-- PMINSB (0F 38 38), PMINSD (39), PMINUW (3A), PMINUD (3B), PMAXSB (3C), PMAXSD (3D),
PMAXUW (3E), PMAXUD (3F). -/
def pminmax (op : UInt8) (a b : V128) : V128 :=
  let bits := match op &&& 3 with | 0 => 8 | 2 => 16 | _ => 32
  let signed := op &&& 3 ≤ 1
  let isMax := op ≥ 0x3C
  V128.map2 128 bits (fun x y =>
    let c : Int := if signed then lsx bits x - lsx bits y else (x.toNat : Int) - y.toNat
    if (if isMax then c ≥ 0 else c ≤ 0) then x else y) a b

/-- PMULDQ: signed products of dwords 0 and 2. -/
def pmuldq (a b : V128) : V128 :=
  V128.ofLanes 64 #[lenc 64 (lsx 32 (a.lane 32 0) * lsx 32 (b.lane 32 0)),
                    lenc 64 (lsx 32 (a.lane 32 2) * lsx 32 (b.lane 32 2))]

/-- PMULLD: low dwords of the products. -/
def pmulld (a b : V128) : V128 := V128.map2 128 32 (fun x y => x * y) a b

/-- PMOVSX/PMOVZX: the low lanes of `src` (`fromBits` wide) extended to `toBits`. -/
def pmovx (src : V128) (fromBits toBits : Nat) (signed : Bool) : V128 :=
  V128.ofLanes toBits ((Array.range (128 / toBits)).map fun k =>
    let x := src.lane fromBits k
    if signed then lenc toBits (lsx fromBits x) else x)

/-- PTEST: (ZF, CF) = (a AND b = 0, (NOT a) AND b = 0). -/
def ptest (a b : V128) : Bool × Bool :=
  ((a.lo &&& b.lo) ||| (a.hi &&& b.hi) == 0, (~~~a.lo &&& b.lo) ||| (~~~a.hi &&& b.hi) == 0)

/-- PHMINPOSUW: the minimum unsigned word in bits 15:0, the index of its first occurrence in
bits 18:16, zeros elsewhere. -/
def phminposuw (b : V128) : V128 :=
  let (m, idx) := (List.range 8).foldl (fun (m, idx) k =>
    let x := b.lane 16 k
    if x < m then (x, k) else (m, idx)) (b.lane 16 0, 0)
  { lo := m ||| (idx.toUInt64 <<< 16), hi := 0 }

/-- ROUNDPS/PD (`scalar` false) and ROUNDSS/SD (`scalar`: lane 0 from `b`, the other lanes of
`a`): imm[1:0] rounding mode unless imm[2] (MXCSR.RC), imm[3] suppresses PE. -/
def round (double scalar : Bool) (a b : V128) (imm : Nat) (mx : UInt64) : V128 × UInt64 :=
  let bits := if double then 64 else 32
  let mode : UInt64 := if (imm >>> 2) % 2 == 1 then (mx >>> 13) &&& 3 else (imm % 4).toUInt64
  let sup := (imm >>> 3) % 2 == 1
  if scalar then
    let (v, fl) := FP.roundToIntegral (fmt double) (b.lane bits 0) mode mx sup
    (a.setLane bits 0 v, fl)
  else
    collect bits ((Array.range (128 / bits)).map fun k =>
      FP.roundToIntegral (fmt double) (b.lane bits k) mode mx sup)

/-! ## SSE4.2: PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM (SDM vol. 2B, 4.1; AMD APM vol. 4) -/

/-- Elements of a string operand: 16 bytes or 8 words (imm[0]), signed if imm[1]. -/
def strElems (imm : Nat) (v : V128) : Array Int :=
  let bits := if imm % 2 == 1 then 16 else 8
  (v.lanes 128 bits).map fun x => if (imm >>> 1) % 2 == 1 then lsx bits x else (x.toNat : Int)

/-- Number of elements: 16 (bytes) or 8 (words). -/
@[inline] def strN (imm : Nat) : Nat := if imm % 2 == 1 then 8 else 16

/-- Explicit length (PCMPESTRx, EAX/EDX): |value| as a signed 32-bit integer, saturated to n. -/
def strLenE (imm : Nat) (r : UInt32) : Nat := min (lsx 32 r.toUInt64).natAbs (strN imm)

/-- Implicit length (PCMPISTRx): the index of the first zero element, or n. -/
def strLenI (imm : Nat) (v : V128) : Nat :=
  let e := strElems imm v
  (List.range (strN imm)).foldr (fun k acc => if e[k]! == 0 then k else acc) (strN imm)

/-- IntRes2 of the string comparison: `a` (first operand, xmm1: the set, ranges or needle) of
valid length `la`, `b` (second operand, xmm2/m128: the data) of valid length `lb`. Aggregation
imm[3:2]: equal any, ranges, equal each, equal ordered, with the SDM's rules for invalid elements;
polarity imm[5:4]: +, -, + (masked), - masked (only bits of valid elements of `b` are inverted). -/
def pcmpstr (imm : Nat) (a b : V128) (la lb : Nat) : Nat :=
  let n := strN imm
  let ea := strElems imm a
  let eb := strElems imm b
  let agg := (imm >>> 2) % 4
  let res1 := fun (j : Nat) => match agg with
    | 0 => (List.range n).any fun i => i < la && j < lb && ea[i]! == eb[j]!
    | 1 => (List.range (n / 2)).any fun p =>   -- pairs (lower, upper); an invalid bound: no range
             let i := 2 * p
             i + 1 < la && j < lb && eb[j]! ≥ ea[i]! && eb[j]! ≤ ea[i + 1]!
    | 2 => if j ≥ la && j ≥ lb then true else if j < la && j < lb then ea[j]! == eb[j]! else false
    | _ => (List.range (n - j)).all fun k =>
             if k ≥ la then true else if j + k ≥ lb then false else ea[k]! == eb[j + k]!
  let pol := (imm >>> 4) % 4
  (List.range n).foldl (fun acc j =>
    let r := res1 j
    let r := if pol == 1 || (pol == 3 && j < lb) then !r else r
    if r then acc ||| (1 <<< j) else acc) 0

/-- PCMPxSTRI's ECX: the index of the least (imm[6] = 0) or most significant set bit of IntRes2,
or n if it is 0. -/
def strIndex (imm res : Nat) : UInt32 :=
  let n := strN imm
  if res == 0 then n.toUInt32
  else if (imm >>> 6) % 2 == 0 then
    ((List.range n).foldr (fun k acc => if (res >>> k) % 2 == 1 then k else acc) n).toUInt32
  else ((List.range n).foldl (fun acc k => if (res >>> k) % 2 == 1 then k else acc) 0).toUInt32

/-- PCMPxSTRM's XMM0: IntRes2 zero-extended (imm[6] = 0) or expanded to an element mask. -/
def strMask (imm res : Nat) : V128 :=
  if (imm >>> 6) % 2 == 0 then { lo := res.toUInt64, hi := 0 }
  else
    let bits := if imm % 2 == 1 then 16 else 8
    V128.ofLanes bits ((Array.range (strN imm)).map fun k => if (res >>> k) % 2 == 1 then 0xFFFF else 0)

/-- EFLAGS of PCMPxSTRx: CF = IntRes2 ≠ 0, ZF = `b` shorter than n, SF = `a` shorter than n,
OF = IntRes2[0], AF = PF = 0. -/
def strFlags (imm res la lb : Nat) : UInt32 :=
  let n := strN imm
  (if res != 0 then Flag.CF else 0) ||| (if lb < n then Flag.ZF else 0) |||
  (if la < n then Flag.SF else 0) ||| (if res % 2 == 1 then Flag.OF else 0)

/-! ## SSE4a: EXTRQ, INSERTQ (AMD APM vol. 4) -/

/-- Mask of a field of `len` bits (6-bit field; 0 means 64). -/
@[inline] def fieldMask (len : Nat) : UInt64 :=
  if len % 64 == 0 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< (len % 64).toUInt64) - 1

/-- EXTRQ: bits idx + len - 1 .. idx of `v`, zero-extended (len, idx: 6-bit fields). -/
def extrq (v : UInt64) (len idx : Nat) : UInt64 :=
  (v >>> (idx % 64).toUInt64) &&& fieldMask len

/-- INSERTQ: the low `len` bits of `s` into bits idx + len - 1 .. idx of `d`. -/
def insertq (d s : UInt64) (len idx : Nat) : UInt64 :=
  let m := fieldMask len
  let sh := (idx % 64).toUInt64
  (d &&& ~~~(m <<< sh)) ||| ((s &&& m) <<< sh)

/-! ## Instruction glue -/

/-- Report staged flags (DPPS/DPPD): merge into MXCSR, then #XM (or #UD with CR4.OSXMMEXCPT = 0)
if a stage raised an unmasked exception; the destination is not written then. -/
def statusStaged (fl : UInt64) (unmasked : Bool) : M Unit := do
  let c ← cpu
  modCpu fun c => { c with sse := { c.sse with mxcsr := c.mxcsr ||| (fl.toUInt32 &&& 0x3F) } }
  if unmasked then
    if c.cr4 &&& CR4.OSXMMEXCPT != 0 then exc Vec.XM else ud

@[inline] def mxcsr64 : M UInt64 := do return (← cpu).mxcsr.toUInt64

/-- XMM form: `xmm(reg) := f xmm(reg) (xmm/m128)`. -/
def xmmOp (i : Inst) (f : V128 → V128 → V128) (align : Bool := true) : M Unit := do
  sseCheck
  let a ← getXmm i.reg
  let s ← rdXE i 16 align
  setXmm i.reg (f a s)

/-- MMX form: `mm(reg) := f mm(reg) (mm/m64)`. -/
def mmxOp (i : Inst) (f : V128 → V128 → V128) : M Unit := do
  mmxCheck
  let a ← getMm i.reg
  let s ← rdME i 8
  setMm i.reg (f { lo := a } { lo := s }).lo

/-- Packed FP XMM form with MXCSR flags. -/
def fpOp (i : Inst) (f : V128 → V128 → UInt64 → V128 × UInt64) (n : UInt32 := 16)
    (align : Bool := true) : M Unit := do
  sseCheck
  let a ← getXmm i.reg
  let s ← rdXE i n align
  let (r, fl) := f a s (← mxcsr64)
  sseStatus fl
  setXmm i.reg r

/-- SSSE3: no prefix MMX form, 66 XMM form. -/
def ssse3 (i : Inst) (f : Nat → V128 → V128 → V128) : Option (M Unit) :=
  match i.pp with
  | 0 => some (mmxOp i (f 64))
  | 1 => some (xmmOp i (f 128))
  | _ => none

/-- Write a 32-bit general register (ModRM r/m) or a 1/2/4-byte memory destination. -/
def wrGE (i : Inst) (n : UInt32) (v : UInt32) : M Unit := do
  if i.isMem then wrMem i.seg (← fpEa i) n v else setReg i.rm v

/-- PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM (66 0F 3A 60..63). -/
def pcmpstrOp (i : Inst) (b0 : UInt8) : M Unit := do
  sseCheck
  let imm := (i.imm &&& 0xFF).toNat
  let a ← getXmm i.reg
  let b ← rdXE i 16 false
  let explicit := b0 ≤ 0x61
  let eax ← getReg 0
  let edx ← getReg 2
  let la := if explicit then strLenE imm eax else strLenI imm a
  let lb := if explicit then strLenE imm edx else strLenI imm b
  let res := pcmpstr imm a b la lb
  if b0 &&& 1 == 1 then setReg 1 (strIndex imm res) else setXmm 0 (strMask imm res)
  setFlags Flag.arith (strFlags imm res la lb)

/-- 0F 38 (legacy): SSSE3 and SSE4.1/4.2. -/
def map2? (i : Inst) : Option (M Unit) :=
  let b0 := i.byte
  match b0 with
  | 0x00 => ssse3 i pshufb
  | 0x01 => ssse3 i fun w => phop w 16 phAdd
  | 0x02 => ssse3 i fun w => phop w 32 phAdd
  | 0x03 => ssse3 i fun w => phop w 16 phAddS
  | 0x04 => ssse3 i pmaddubsw
  | 0x05 => ssse3 i fun w => phop w 16 phSub
  | 0x06 => ssse3 i fun w => phop w 32 phSub
  | 0x07 => ssse3 i fun w => phop w 16 phSubS
  | 0x08 => ssse3 i fun w => psign w 8
  | 0x09 => ssse3 i fun w => psign w 16
  | 0x0A => ssse3 i fun w => psign w 32
  | 0x0B => ssse3 i pmulhrsw
  | 0x1C => ssse3 i fun w _ b => pabs w 8 b
  | 0x1D => ssse3 i fun w _ b => pabs w 16 b
  | 0x1E => ssse3 i fun w _ b => pabs w 32 b
  | _ =>
    if i.pp != 1 then none else
    match b0 with
    | 0x10 => some do  -- PBLENDVB xmm1, xmm2/m128, <XMM0>
      sseCheck
      let a ← getXmm i.reg
      let s ← rdXE i 16 true
      setXmm i.reg (blendv 8 a s (← getXmm 0))
    | 0x14 | 0x15 => some do  -- BLENDVPS / BLENDVPD
      sseCheck
      let a ← getXmm i.reg
      let s ← rdXE i 16 true
      setXmm i.reg (blendv (if b0 == 0x14 then 32 else 64) a s (← getXmm 0))
    | 0x17 => some do  -- PTEST
      sseCheck
      let a ← getXmm i.reg
      let s ← rdXE i 16 true
      let (zf, cf) := ptest a s
      setFlags Flag.arith ((if zf then Flag.ZF else 0) ||| (if cf then Flag.CF else 0))
    | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25 | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 => some do
      -- PMOVSX/PMOVZX: BW, BD, BQ, WD, WQ, DQ (memory: 8, 4, 2, 8, 4, 8 bytes)
      sseCheck
      let k := (b0 &&& 0xF).toNat
      let (fb, tb) := match k with
        | 0 => (8, 16) | 1 => (8, 32) | 2 => (8, 64) | 3 => (16, 32) | 4 => (16, 64) | _ => (32, 64)
      let n : UInt32 := (fb * (128 / tb) / 8).toUInt32
      let s ← rdXE i n
      setXmm i.reg (pmovx s fb tb (b0 < 0x30))
    | 0x28 => some (xmmOp i pmuldq)
    | 0x29 => some (xmmOp i pcmpeqq)
    | 0x2A => some do  -- MOVNTDQA xmm, m128
      sseCheck
      needMemS i
      setXmm i.reg (← rdXE i 16 true)
    | 0x2B => some (xmmOp i packusdw)
    | 0x37 => some (xmmOp i pcmpgtq)
    | 0x38 | 0x39 | 0x3A | 0x3B | 0x3C | 0x3D | 0x3E | 0x3F => some (xmmOp i (pminmax b0))
    | 0x40 => some (xmmOp i pmulld)
    | 0x41 => some (xmmOp i fun _ s => phminposuw s)
    | _ => none

/-- 0F 3A (legacy, imm8 in `imm`): PALIGNR, SSE4.1, SSE4.2 string compares. -/
def map3? (i : Inst) : Option (M Unit) :=
  let b0 := i.byte
  let imm := (i.imm &&& 0xFF).toNat
  if b0 == 0x0F then ssse3 i fun w a b => palignr w a b imm
  else if i.pp != 1 then none else
  match b0 with
  | 0x08 | 0x09 => some (fpOp i fun a b mx => round (b0 == 0x09) false a b imm mx)
  | 0x0A | 0x0B => some (fpOp i (n := if b0 == 0x0A then 4 else 8) (align := false)
                    fun a b mx => round (b0 == 0x0B) true a b imm mx)
  | 0x0C => some (xmmOp i (blend 32 imm))
  | 0x0D => some (xmmOp i (blend 64 imm))
  | 0x0E => some (xmmOp i (blend 16 imm))
  | 0x14 | 0x15 | 0x16 | 0x17 => some do  -- PEXTRB, PEXTRW, PEXTRD, EXTRACTPS r/m
    sseCheck
    let s ← getXmm i.reg
    let (bits, k) := match b0 with
      | 0x14 => (8, imm % 16) | 0x15 => (16, imm % 8) | _ => (32, imm % 4)
    wrGE i (bits / 8).toUInt32 (s.lane bits k).toUInt32
  | 0x20 => some do  -- PINSRB xmm, r32/m8
    sseCheck
    let v ← if i.isMem then rdMem i.seg (← fpEa i) 1 else getReg i.rm
    setXmm i.reg ((← getXmm i.reg).setLane 8 (imm % 16) v.toUInt64)
  | 0x21 => some do  -- INSERTPS xmm, xmm/m32
    sseCheck
    let s ← if i.isMem then pure (← rdVM i 4).lo else pure ((← getXmm i.rm).lane 32 (imm >>> 6))
    setXmm i.reg (insertps (← getXmm i.reg) s imm)
  | 0x22 => some do  -- PINSRD xmm, r/m32
    sseCheck
    let v ← rdGE32 i
    setXmm i.reg ((← getXmm i.reg).setLane 32 (imm % 4) v.toUInt64)
  | 0x40 | 0x41 => some do  -- DPPS / DPPD
    sseCheck
    let a ← getXmm i.reg
    let s ← rdXE i 16 true
    let (r, fl, u) := (if b0 == 0x40 then dpps else dppd) a s imm (← mxcsr64)
    statusStaged fl u
    setXmm i.reg r
  | 0x42 => some (xmmOp i fun a b => mpsadbw a b imm)
  | 0x60 | 0x61 | 0x62 | 0x63 => some (pcmpstrOp i b0)
  | _ => none

/-- 0F map: SSE3 and SSE4a forms (see the module documentation). -/
def op0F? (i : Inst) : Option (M Unit) :=
  let b0 := i.byte
  let p := i.pp
  match b0, p with
  | 0x12, 2 => some (xmmOp i fun _ s => movsldup s)            -- MOVSLDUP
  | 0x16, 2 => some (xmmOp i fun _ s => movshdup s)            -- MOVSHDUP
  | 0x12, 3 => some do                                          -- MOVDDUP xmm, xmm/m64
    sseCheck
    setXmm i.reg (movddup (← rdXE i 8))
  | 0x2B, 2 | 0x2B, 3 => some do                                -- MOVNTSS m32 / MOVNTSD m64
    sseCheck
    needMemS i
    let v ← getXmm i.reg
    wrVM i (if p == 2 then 4 else 8) v
  | 0x7C, 1 | 0x7C, 3 | 0x7D, 1 | 0x7D, 3 => some (fpOp i (hop (p == 1) (b0 == 0x7D)))
  | 0xD0, 1 | 0xD0, 3 => some (fpOp i (addsub (p == 1)))
  | 0xF0, 3 => some do                                          -- LDDQU xmm, m128
    sseCheck
    needMemS i
    setXmm i.reg (← rdVM i 16)
  | 0x78, 1 => some do                                          -- EXTRQ xmm, imm8, imm8
    sseCheck
    needReg i
    if i.reg != 0 then ud
    let v ← getXmm i.rm
    setXmm i.rm { v with lo := extrq v.lo (i.imm &&& 0x3F).toNat (i.imm2 &&& 0x3F).toNat }
  | 0x78, 3 => some do                                          -- INSERTQ xmm, xmm, imm8, imm8
    sseCheck
    needReg i
    let d ← getXmm i.reg
    let s ← getXmm i.rm
    setXmm i.reg { d with lo := insertq d.lo s.lo (i.imm &&& 0x3F).toNat (i.imm2 &&& 0x3F).toNat }
  | 0x79, 1 => some do                                          -- EXTRQ xmm, xmm
    sseCheck
    needReg i
    let d ← getXmm i.reg
    let c ← getXmm i.rm
    setXmm i.reg { d with lo := extrq d.lo (c.lo &&& 0x3F).toNat ((c.lo >>> 8) &&& 0x3F).toNat }
  | 0x79, 3 => some do                                          -- INSERTQ xmm, xmm
    sseCheck
    needReg i
    let d ← getXmm i.reg
    let s ← getXmm i.rm
    setXmm i.reg { d with lo := insertq d.lo s.lo (s.hi &&& 0x3F).toNat ((s.hi >>> 8) &&& 0x3F).toNat }
  | _, _ => none

end Sse
end X86
