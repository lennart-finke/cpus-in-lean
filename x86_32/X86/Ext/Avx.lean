import X86.Ext.Vex
import X86.Ext.Sse
import X86.Ext.Crypto
/-!
# AVX

Owner: the AVX workstream. The AVX (AVX1) instructions of Zen 2 in 32-bit mode: the VEX-encoded
128- and 256-bit forms of the SSE..SSE4.2 instructions, the VEX.128 forms of AES-NI and PCLMULQDQ
(Zen 2 has neither VAES nor 256-bit VPCLMULQDQ), and the AVX-only instructions (VBROADCASTSS/SD/F128,
VINSERTF128, VEXTRACTF128, VPERMILPS/PD, VPERM2F128, VMASKMOVPS/PD, VTESTPS/PD, VZEROALL,
VZEROUPPER, the 32 VCMP predicates). The shared VEX layer (checks, 256-bit operands, exception
classes) is `X86/Ext/Vex.lean`; read its documentation first.

Hook (called by `X86/Dispatch.lean` after `Gpr.vex?`; `none` = not handled here):

* `vex?`: maps 0F (`map1`), 0F 38 (`map2`) and 0F 3A (`map3`), keyed on (opcode byte, `pp`).

Semantics come from the pure kernels of `X86/Simd.lean` (`pint`, `FP.*`, `cvtLanes`), `Sse.lean`
(its kernel table) and `Crypto.lean`, applied to (VEX.vvvv, ModRM.r/m) instead of the legacy
(ModRM.reg, ModRM.r/m) and, for VEX.256, to each 128-bit half (`Vex.lanes`). The few kernels that
exist only inside the monadic legacy code (unpack, shuffle, PSHUFD/HW/LW, MOVMSK) are restated here
as pure functions with the same definitions.

## Extension point for AVX2 (`Avx2.lean`)

The VEX.256 forms of the integer opcodes are AVX2. For them `vex?` returns `none` (`only128`), and
`Avx2.vex?`, the next hook, implements them; without it the fallback is #UD. The same holds for the
opcodes AVX does not have at all (VEX.0F38 13, 16, 36, 45..47, 58..5A, 78, 79, 8C, 8E, 90..93,
96..BF, the register forms of VBROADCASTSS/SD, VEX.0F3A 00..02, 1D, 38, 39, 46). `intOp b0` is the
per-lane integer form of an 0F-map opcode for both lengths (the AVX2 workstream can call it for VEX.256
of every 0F-map integer opcode whose operation stays within 128-bit lanes: all `pint` opcodes; the
shift-by-xmm forms D1..D3, E1, E2, F1..F3 take one 64-bit count for both lanes, which `pint` does per
lane from the low quadword of each half of the source and is therefore NOT the AVX2 semantics).

## Choices where the manuals leave room

* VMASKMOVPS/PD: masked-out elements raise no exception and are not accessed (Intel SDM VMASKMOV:
  "Faults occur only due to mask-bit required memory accesses"); AMD APM vol. 4 VMASKMOVPS says the
  exception behaviour of masked-out elements is implementation dependent. Segment checks are made
  per selected element. Stores check every selected element before writing any. No #AC (SDM:
  "No AC# reported for any mask bit combinations"; AMD's exception table lists none). The native
  campaign family `avx_maskmov` records what a Zen 2 does.
* VDPPS (VEX.256): two independent dot products; their staged flags (`Sse.dpps`) are merged.
* VZEROALL/VZEROUPPER: AMD APM vol. 4 lists "VEX.W = 1" as #UD for VZEROALL while its encoding
  table and Intel give "WIG"; the model ignores VEX.W (open doubt, recorded by the native campaign).
* VMOVSS/VMOVSD loads ignore VEX.vvvv: both manuals require 1111b only for the store form (SDM
  MOVSS/MOVSD note, APM vol. 4 MOVSS/MOVSD exception table), although APM's encoding table shows 1111b
  for the load too. The native campaign case `vmovss_ld_vvvv` records Zen 2's behaviour.
* VEX.W is ignored outside 64-bit mode by VMOVD, VPEXTRD, VPINSRD, VCVTSI2SS/SD, VCVT(T)SS2SI,
  VCVT(T)SD2SI and VPCMPESTRx (AMD APM vol. 4, VPEXTRD/VPINSRD: "x" encodings "only available in
  non-64-bit modes").
-/
namespace X86
namespace Avx
open Vex

/-! ## Kernels -/

/-- VCMPPS/PD/SS/SD with the 32 predicates of imm8[4:0] (SDM vol. 2 CMPPS, table 3-1; AMD APM vol.
4 VCMPPS): bits 3:0 select the relation (EQ, LT, LE, UNORD, NEQ, NLT, NLE, ORD, EQ_UQ, NGE, NGT,
FALSE, NEQ_OQ, GE, GT, TRUE), bit 4 inverts whether a QNaN operand signals (IE). Predicates 0..7
are the legacy `FP.cmp`. Flags as `FP.cmp`: IE for an SNaN operand or a NaN with a signaling
predicate, no DE when unordered. -/
def cmpPred (f : FP.Format) (pred : UInt32) (a b mx : UInt64) : UInt64 × UInt64 :=
  let p := pred &&& 31
  if p < 8 then FP.cmp f p a b mx else
  let (a, da) := FP.prepare f mx a
  let (b, db) := FP.prepare f mx b
  let unord := FP.isNaN f a || FP.isNaN f b
  let c := FP.compare f a b
  let base := p &&& 15
  let yes := match base with
    | 0 => !unord && c == 0 | 1 => !unord && c < 0 | 2 => !unord && c ≤ 0 | 3 => unord
    | 4 => unord || c != 0 | 5 => unord || c ≥ 0 | 6 => unord || c > 0 | 7 => !unord
    | 8 => unord || c == 0 | 9 => unord || c < 0 | 10 => unord || c ≤ 0 | 11 => false
    | 12 => !unord && c != 0 | 13 => !unord && c ≥ 0 | 14 => !unord && c > 0 | _ => true
  let sig0 := base == 1 || base == 2 || base == 5 || base == 6 || base == 9 || base == 10 ||
    base == 13 || base == 14
  let signaling := if p ≥ 16 then !sig0 else sig0
  (if yes then 0xFFFFFFFFFFFFFFFF else 0,
   if (signaling && unord) || FP.isSNaN f a || FP.isSNaN f b then 1 else if unord then 0 else da ||| db)

/-- One lane of the FP arithmetic opcodes 51..53, 58..5F, C2 (as `sseArith`). -/
def fpLane (b0 : UInt8) (double : Bool) (imm : UInt32) (x y mx : UInt64) : UInt64 × UInt64 :=
  let f := Sse.fmt double
  match b0 with
  | 0x58 => FP.binary f .add x y mx
  | 0x59 => FP.binary f .mul x y mx
  | 0x5C => FP.binary f .sub x y mx
  | 0x5E => FP.binary f .div x y mx
  | 0x51 => FP.sqrt f y mx
  | 0x52 => (FP.rsqrt y, 0)
  | 0x53 => (FP.rcp y, 0)
  | 0x5D => FP.minmax f false x y mx
  | 0x5F => FP.minmax f true x y mx
  | _ => cmpPred f imm x y mx

/-- Packed form on 128 bits. -/
def packedFp (b0 : UInt8) (double : Bool) (imm : UInt32) (a b : V128) (mx : UInt64) : V128 × UInt64 :=
  let bits := if double then 64 else 32
  Sse.collect bits ((Array.range (128 / bits)).map fun k =>
    fpLane b0 double imm (a.lane bits k) (b.lane bits k) mx)

/-- Scalar form: lane 0 computed from `a` and `b`, the other lanes of `a`. -/
def scalarFp (b0 : UInt8) (double : Bool) (imm : UInt32) (a b : V128) (mx : UInt64) : V128 × UInt64 :=
  let bits := if double then 64 else 32
  let (v, fl) := fpLane b0 double imm (a.lane bits 0) (b.lane bits 0) mx
  (a.setLane bits 0 v, fl)

/-- UNPCKLPx (`high` false) / UNPCKHPx on 128 bits (as `sseMove`). -/
def unpck (high : Bool) (bits : Nat) (a b : V128) : V128 :=
  let n := 128 / bits
  let start := if high then n / 2 else 0
  V128.ofLanes bits ((Array.range n).map fun k =>
    if k % 2 == 0 then a.lane bits (start + k / 2) else b.lane bits (start + k / 2))

/-- SHUFPS on 128 bits: lanes 0, 1 from `a`, lanes 2, 3 from `b`, selected by imm8 pairs. -/
def shufps (imm : UInt32) (a b : V128) : V128 :=
  V128.ofLanes 32 ((Array.range 4).map fun k =>
    (if k < 2 then a else b).lane 32 ((imm >>> (2 * k).toUInt32) &&& 3).toNat)

/-- SHUFPD on 128 bits: imm8 bit 0 selects from `a`, bit 1 from `b`. -/
def shufpd (imm : UInt32) (a b : V128) : V128 :=
  V128.ofLanes 64 #[a.lane 64 (imm &&& 1).toNat, b.lane 64 ((imm >>> 1) &&& 1).toNat]

/-- PSHUFD (`p` = 1), PSHUFHW (2), PSHUFLW (3) on 128 bits (as `pshuf`). -/
def pshufK (p : Nat) (imm : UInt32) (s : V128) : V128 :=
  let sel := fun (k : Nat) => ((imm >>> (2 * k).toUInt32) &&& 3).toNat
  match p with
  | 1 => V128.ofLanes 32 ((Array.range 4).map fun k => s.lane 32 (sel k))
  | 2 => { s with hi := (V128.ofLanes 16 ((Array.range 4).map fun k => s.lane 16 (4 + sel k))).lo }
  | _ => { s with lo := (V128.ofLanes 16 ((Array.range 4).map fun k => s.lane 16 (sel k))).lo }

/-- Sign-bit mask of the first `n` `bits`-wide elements (MOVMSKPS/PD, PMOVMSKB). -/
def signMask (bits n : Nat) (v : V256) : UInt32 :=
  (List.range n).foldl (fun acc k =>
    if v.lane bits k >>> (bits - 1).toUInt64 != 0 then acc ||| ((1 : UInt32) <<< k.toUInt32) else acc) 0

/-- VPERMILPS (variable): dword k of a 128-bit lane is dword ctrl[k][1:0] of `a`'s lane. -/
def permilpsV (a ctrl : V128) : V128 :=
  V128.ofLanes 32 ((Array.range 4).map fun k => a.lane 32 (ctrl.lane 32 k &&& 3).toNat)

/-- VPERMILPD (variable): qword k of a 128-bit lane is qword ctrl[k][1] of `a`'s lane. -/
def permilpdV (a ctrl : V128) : V128 :=
  V128.ofLanes 64 ((Array.range 2).map fun k => a.lane 64 ((ctrl.lane 64 k >>> 1) &&& 1).toNat)

/-- VPERMILPS (imm8): dword k of each lane is dword imm8[2k+1:2k] of that lane. -/
def permilpsI (imm : UInt32) (a : V128) : V128 :=
  V128.ofLanes 32 ((Array.range 4).map fun k => a.lane 32 ((imm >>> (2 * k).toUInt32) &&& 3).toNat)

/-- VPERMILPD (imm8) on one lane, with the two selector bits of that lane in imm8[1:0]. -/
def permilpdI (imm : UInt32) (a : V128) : V128 :=
  V128.ofLanes 64 #[a.lane 64 (imm &&& 1).toNat, a.lane 64 ((imm >>> 1) &&& 1).toNat]

/-- VPERM2F128: each half of the result is chosen by an imm8 nibble (bits 1:0 / 5:4: a.lo, a.hi,
b.lo, b.hi) and zeroed by bit 3 / 7. -/
def perm2f128 (imm : UInt32) (a b : V256) : V256 :=
  let sel := fun (s : UInt32) => if s &&& 8 != 0 then ({} : V128)
    else match s &&& 3 with | 0 => a.lo | 1 => a.hi | 2 => b.lo | _ => b.hi
  { lo := sel imm, hi := sel (imm >>> 4) }

/-- VTESTPS/VTESTPD (sign bits of `bits`-wide elements) and VPTEST (`bits` = 1: all bits) over the
first `n` bytes: (ZF, CF) = ((a AND b) = 0, (NOT a AND b) = 0) on the tested bits. -/
def testFlags (bits : Nat) (L : Bool) (a b : V256) : Bool × Bool :=
  let m : UInt64 := if bits == 32 then 0x8000000080000000 else if bits == 64 then 0x8000000000000000
    else 0xFFFFFFFFFFFFFFFF
  let ws := fun (v : V256) => if L then [v.lo.lo, v.lo.hi, v.hi.lo, v.hi.hi] else [v.lo.lo, v.lo.hi]
  let z := (List.zip (ws a) (ws b)).all fun (x, y) => x &&& y &&& m == 0
  let c := (List.zip (ws a) (ws b)).all fun (x, y) => ~~~x &&& y &&& m == 0
  (z, c)

/-- The value with every `bits`-wide element of both halves equal to `x`. -/
def broadcast (bits : Nat) (x : UInt64) : V256 :=
  let h := V128.ofLanes bits ((Array.range (128 / bits)).map fun _ => x)
  { lo := h, hi := h }

/-! ## Helpers -/

@[inline] def mx64 : M UInt64 := do return (← cpu).mxcsr.toUInt64

/-- A form that AVX has only as VEX.128: VEX.256 is left to `Avx2.vex?` (extension point). -/
@[inline] def only128 (i : Inst) (a : M Unit) : Option (M Unit) := if i.vexL then none else some a

/-- The per-lane integer form of an 0F-map `pint` opcode, both lengths (see the module doc). -/
def intOp (i : Inst) (b0 : UInt8) : M Unit := op3 i true (pint b0 128)

/-- Scalar FP 3-operand form (VADDSS xmm1, xmm2, xmm3/m32, ...): VEX.L ignored. -/
def scalarOp (i : Inst) (b0 : UInt8) (double : Bool) : M Unit := do
  start i true
  let a ← src1 i
  let b ← rdRm i (if double then 8 else 4)
  let (r, fl) := scalarFp b0 double i.imm a.lo b.lo (← mx64)
  sseStatus fl
  setX i.reg r

/-- 32-bit general register or memory operand of `n` (1, 2, 4) bytes, zero-extended. -/
def rdGE (i : Inst) (n : UInt32) : M UInt32 := do
  if i.isMem then return (← rdVex i n).lo.lo.toUInt32 &&& (if n == 4 then 0xFFFFFFFF else ((1 : UInt32) <<< (8 * n)) - 1)
  else getReg i.rm

/-- VCOMISS/VUCOMISS/VCOMISD/VUCOMISD (as `sseComi`). -/
def comi (i : Inst) (signaling double : Bool) : M Unit := do
  start i (noV i)
  let f := Sse.fmt double
  let bits := if double then 64 else 32
  let a := (← getY i.reg).lo.lane bits 0
  let b := (← rdRm i (bits / 8).toUInt32).lo.lane bits 0
  let mx ← mx64
  let (a, da) := FP.prepare f mx a
  let (b, db) := FP.prepare f mx b
  let unord := FP.isNaN f a || FP.isNaN f b
  let invalid := if signaling then unord else FP.isSNaN f a || FP.isSNaN f b
  sseStatus (if invalid then 1 else if unord then 0 else da ||| db)
  let c := FP.compare f a b
  setFlags Flag.arith (if unord then Flag.ZF ||| Flag.PF ||| Flag.CF else if c == 0 then Flag.ZF
                       else if c < 0 then Flag.CF else 0)

/-- A conversion with `n` lanes per 128-bit source half (`cvtLanes`), source r/m of `srcBytes`. The
result lanes of both halves are concatenated into the low half (narrowing) or spread over the
destination (widening, `wide`). -/
def cvt (i : Inst) (sf df : Option FP.Format) (trunc : Bool) : M Unit := do
  start i (noV i)
  let sb := match sf with | some f => f.fraction + f.exponent + 1 | none => 32
  let db := match df with | some f => f.fraction + f.exponent + 1 | none => 32
  let L := i.vexL
  let mx ← mx64
  if sb == db then
    -- same width: lane-wise
    let s ← rdRmV i
    let (r, fl) := lanesFp L (fun _ y => let (ls, fl) := cvtLanes sf df trunc (128 / sb) y mx
                                         (V128.ofLanes db ls, fl)) {} s
    sseStatus fl
    setV i i.reg r
  else if sb < db then
    -- widening (CVTPS2PD, CVTDQ2PD): 2 or 4 elements from 8 or 16 source bytes
    let n := if L then 4 else 2
    let s ← rdRm i (if L then 16 else 8)
    let (ls, fl) := cvtLanes sf df trunc n s.lo mx
    sseStatus fl
    setV i i.reg (V256.ofLanes 64 ls)
  else
    -- narrowing (CVTPD2PS, CVT(T)PD2DQ): the source's 2 or 4 elements to the low half
    let s ← rdRmV i
    let (l0, f0) := cvtLanes sf df trunc 2 s.lo mx
    let (l1, f1) := if L then cvtLanes sf df trunc 2 s.hi mx else (#[], 0)
    sseStatus (f0 ||| f1)
    setX i.reg (V128.ofLanes 32 (l0 ++ l1))

/-- Store of the destination register: memory (`n` bytes) or ModRM.r/m register (VEX.L zeroing). -/
def storeRm (i : Inst) (n : UInt32) (v : V256) (align : Bool := false) : M Unit := do
  if i.isMem then wrVex i n v align else setV i i.rm v

/-- The elements of `n` `bits`-wide elements selected by a VMASKMOVPS/PD mask (sign bit set). -/
def maskSel (bits n : Nat) (mask : V256) : List Nat :=
  (List.range n).filter fun k => mask.lane bits k >>> (bits - 1).toUInt64 != 0

/-- VMASKMOVPS/PD load (`bits` 32/64): the elements selected by the mask (VEX.vvvv) are read, in
ascending order; the others are 0 and not accessed (see the module documentation). -/
def maskLoad (i : Inst) (bits : Nat) : M Unit := do
  start i (w0 i && i.isMem)
  let mask ← src1 i
  let off ← fpEa i
  let n := (if i.vexL then 256 else 128) / bits
  let sz := (bits / 8).toUInt32
  let mut out : Array UInt64 := Array.replicate n 0
  for k in maskSel bits n mask do
    let lin ← segAddr i.seg (off + sz * k.toUInt32) sz false
    out := out.set! k (← rdLin lin sz).lo
  setV i i.reg (V256.ofLanes bits out)

/-- VMASKMOVPS/PD store: the selected elements of ModRM.reg are written; all of them are checked
(segment, page) before the first is written; the others are not accessed. -/
def maskStore (i : Inst) (bits : Nat) : M Unit := do
  start i (w0 i && i.isMem)
  let mask ← src1 i
  let data ← getY i.reg
  let off ← fpEa i
  let n := (if i.vexL then 256 else 128) / bits
  let sz := (bits / 8).toUInt32
  let sel := maskSel bits n mask
  let mut lins : Array UInt32 := #[]
  for k in sel do
    let lin ← segAddr i.seg (off + sz * k.toUInt32) sz true
    linProbeWr lin sz (← isUser)
    lins := lins.push lin
  for (k, lin) in sel.zip lins.toList do
    wrLin lin sz { lo := data.lane bits k }

/-! ## VEX.0F -/

/-- The moves of 10..17, 28, 29, 2B. -/
def moves (i : Inst) (b0 : UInt8) (p : Nat) : Option (M Unit) :=
  let L := i.vexL
  match b0, p with
  | 0x10, 0 | 0x10, 1 => some do        -- VMOVUPS/PD load
    start i (noV i); setV i i.reg (← rdRmV i)
  | 0x11, 0 | 0x11, 1 => some do        -- VMOVUPS/PD store
    start i (noV i); storeRm i (vsz i) (← getY i.reg)
  | 0x28, 0 | 0x28, 1 => some do        -- VMOVAPS/PD load (aligned)
    start i (noV i); setV i i.reg (← rdRmV i true)
  | 0x29, 0 | 0x29, 1 => some do        -- VMOVAPS/PD store (aligned)
    start i (noV i); storeRm i (vsz i) (← getY i.reg) true
  | 0x2B, 0 | 0x2B, 1 => some do        -- VMOVNTPS/PD (aligned)
    start i (noV i && i.isMem); wrVex i (vsz i) (← getY i.reg) true
  | 0x10, _ => some do                   -- VMOVSS/SD load, or merge (register form)
    let bits := if p == 2 then 32 else 64
    if i.isMem then
      -- VEX.vvvv is ignored by the load: only the store requires 1111b (SDM vol. 2 MOVSS/MOVSD: "For
      -- memory store form instruction VMOVSS m32, xmm1, VEX.vvvv is reserved and must be 1111b";
      -- AMD APM vol. 4 MOVSS/MOVSD: "#UD: VEX.vvvv != 1111b (for memory destination encoding only)")
      start i true
      setX i.reg (← rdVex i (bits / 8).toUInt32).lo
    else
      start i true
      setX i.reg ((← src1 i).lo.setLane bits 0 ((← getY i.rm).lo.lane bits 0))
  | 0x11, _ => some do                   -- VMOVSS/SD store, or merge into ModRM.r/m
    let bits := if p == 2 then 32 else 64
    if i.isMem then
      start i (noV i)
      wrVex i (bits / 8).toUInt32 (← getY i.reg)
    else
      start i true
      setX i.rm ((← src1 i).lo.setLane bits 0 ((← getY i.reg).lo.lane bits 0))
  | 0x12, 0 | 0x12, 1 => some do         -- VMOVLPS/PD xmm, xmm, m64; VMOVHLPS xmm, xmm, xmm
    start i (!L && (p == 0 || i.isMem))
    let a := (← src1 i).lo
    let s := (← rdRm i 8).lo
    setX i.reg { a with lo := if i.isMem then s.lo else s.hi }
  | 0x16, 0 | 0x16, 1 => some do         -- VMOVHPS/PD xmm, xmm, m64; VMOVLHPS
    start i (!L && (p == 0 || i.isMem))
    let a := (← src1 i).lo
    let s := (← rdRm i 8).lo
    setX i.reg { a with hi := s.lo }
  | 0x13, 0 | 0x13, 1 | 0x17, 0 | 0x17, 1 => some do   -- VMOVLPx / VMOVHPx m64, xmm
    start i (!L && noV i && i.isMem)
    let v := (← getY i.reg).lo
    wrVex i 8 (V256.ofLo { lo := if b0 == 0x13 then v.lo else v.hi })
  | 0x12, 2 => some (op2 i true Sse.movsldup)
  | 0x16, 2 => some (op2 i true Sse.movshdup)
  | 0x12, 3 => some do                   -- VMOVDDUP xmm, xmm/m64; ymm, ymm/m256
    start i (noV i)
    let s ← rdRm i (if L then 32 else 8)
    setV i i.reg (lanes L (fun _ y => Sse.movddup y) {} s)
  | 0x14, 0 | 0x15, 0 => some (op3 i true (unpck (b0 == 0x15) 32))
  | 0x14, 1 | 0x15, 1 => some (op3 i true (unpck (b0 == 0x15) 64))
  | _, _ => none

/-- Conversions, compares and the other FP forms of 2A..2F, 50..5F, C2, E6. -/
def fpOps (i : Inst) (b0 : UInt8) (p : Nat) : Option (M Unit) :=
  let s32 := some FP.binary32
  let s64 := some FP.binary64
  match b0, p with
  | 0x2A, 2 | 0x2A, 3 => some do         -- VCVTSI2SS/SD xmm, xmm, r/m32 (VEX.W ignored)
    start i true
    let x ← rdGE i 4
    let a := (← src1 i).lo
    let f := if p == 2 then FP.binary32 else FP.binary64
    let (v, fl) := FP.fromInt f (lsx 32 x.toUInt64) (← mx64)
    sseStatus fl
    setX i.reg (a.setLane (if p == 2 then 32 else 64) 0 v)
  | 0x2C, 2 | 0x2C, 3 | 0x2D, 2 | 0x2D, 3 => some do   -- VCVT(T)SS2SI / VCVT(T)SD2SI r32
    start i (noV i)
    let bits := if p == 2 then 32 else 64
    let f := if p == 2 then FP.binary32 else FP.binary64
    let s ← rdRm i (bits / 8).toUInt32
    let (v, fl) := FP.toInt f (s.lo.lane bits 0) (← mx64) 32 (b0 == 0x2C)
    sseStatus fl
    setReg i.reg v.toUInt32
  | 0x2E, 0 | 0x2E, 1 | 0x2F, 0 | 0x2F, 1 => some (comi i (b0 == 0x2F) (p == 1))
  | 0x50, 0 | 0x50, 1 => some do         -- VMOVMSKPS/PD r32, xmm/ymm
    start i (noV i && !i.isMem)
    let bits := if p == 1 then 64 else 32
    setReg i.reg (signMask bits ((if i.vexL then 256 else 128) / bits) (← getY i.rm))
  | 0x51, 0 | 0x51, 1 | 0x52, 0 | 0x53, 0 =>   -- VSQRTPS/PD, VRSQRTPS, VRCPPS
    some (op2Fp i true fun y mx => packedFp b0 (p == 1) 0 {} y mx)
  | 0x51, _ | 0x52, 2 | 0x53, 2 => some (scalarOp i b0 (p == 3))
  | 0x54, 0 | 0x54, 1 => some (op3 i true fun a b => { lo := a.lo &&& b.lo, hi := a.hi &&& b.hi })
  | 0x55, 0 | 0x55, 1 => some (op3 i true fun a b => { lo := ~~~a.lo &&& b.lo, hi := ~~~a.hi &&& b.hi })
  | 0x56, 0 | 0x56, 1 => some (op3 i true fun a b => { lo := a.lo ||| b.lo, hi := a.hi ||| b.hi })
  | 0x57, 0 | 0x57, 1 => some (op3 i true fun a b => { lo := a.lo ^^^ b.lo, hi := a.hi ^^^ b.hi })
  | 0x58, _ | 0x59, _ | 0x5C, _ | 0x5D, _ | 0x5E, _ | 0x5F, _ | 0xC2, _ =>
    if p ≥ 2 then some (scalarOp i b0 (p == 3))
    else some (op3Fp i true fun a b mx => packedFp b0 (p == 1) i.imm a b mx)
  | 0x5A, 0 => some (cvt i s32 s64 false)          -- VCVTPS2PD
  | 0x5A, 1 => some (cvt i s64 s32 false)          -- VCVTPD2PS
  | 0x5A, 2 | 0x5A, 3 => some do                    -- VCVTSS2SD / VCVTSD2SS xmm, xmm, xmm/m
    start i true
    let a := (← src1 i).lo
    let (sf, df) := if p == 2 then (s32, s64) else (s64, s32)
    let s ← rdRm i (if p == 2 then 4 else 8)
    let (ls, fl) := cvtLanes sf df false 1 s.lo (← mx64)
    sseStatus fl
    setX i.reg (if p == 2 then { a with lo := ls[0]! } else a.setLane 32 0 ls[0]!)
  | 0x5B, 0 => some (cvt i none s32 false)         -- VCVTDQ2PS
  | 0x5B, 1 => some (cvt i s32 none false)         -- VCVTPS2DQ
  | 0x5B, 2 => some (cvt i s32 none true)          -- VCVTTPS2DQ
  | 0xE6, 1 => some (cvt i s64 none true)          -- VCVTTPD2DQ
  | 0xE6, 2 => some (cvt i none s64 false)         -- VCVTDQ2PD
  | 0xE6, 3 => some (cvt i s64 none false)         -- VCVTPD2DQ
  | _, _ => none

/-- Integer and data-movement forms of the 0F map with VEX.66 (and VMOVDQU, VPSHUFHW/LW, VMOVQ,
VLDDQU). VEX.256 of the integer forms: `only128`. -/
def intMoves (i : Inst) (b0 : UInt8) (p : Nat) : Option (M Unit) :=
  let L := i.vexL
  if p == 1 && isPint b0 then only128 i (intOp i b0) else
  match b0, p with
  | 0x6E, 1 => some do                   -- VMOVD xmm, r/m32
    start i (!L && noV i)
    setX i.reg { lo := (← rdGE i 4).toUInt64 }
  | 0x7E, 1 => some do                   -- VMOVD r/m32, xmm
    start i (!L && noV i)
    let v := (← getY i.reg).lo.lo
    if i.isMem then wrVex i 4 (V256.ofLo { lo := v }) else setReg i.rm v.toUInt32
  | 0x7E, 2 => some do                   -- VMOVQ xmm, xmm/m64
    start i (!L && noV i)
    setX i.reg { lo := (← rdRm i 8).lo.lo }
  | 0xD6, 1 => some do                   -- VMOVQ xmm/m64, xmm
    start i (!L && noV i)
    let v := (← getY i.reg).lo.lo
    if i.isMem then wrVex i 8 (V256.ofLo { lo := v }) else setX i.rm { lo := v }
  | 0x6F, 1 | 0x6F, 2 => some do         -- VMOVDQA / VMOVDQU load
    start i (noV i); setV i i.reg (← rdRmV i (p == 1))
  | 0x7F, 1 | 0x7F, 2 => some do         -- VMOVDQA / VMOVDQU store
    start i (noV i); storeRm i (vsz i) (← getY i.reg) (p == 1)
  | 0xE7, 1 => some do                   -- VMOVNTDQ (aligned)
    start i (noV i && i.isMem); wrVex i (vsz i) (← getY i.reg) true
  | 0xF0, 3 => some do                   -- VLDDQU
    start i (noV i && i.isMem); setV i i.reg (← rdRmV i)
  | 0x70, 1 | 0x70, 2 | 0x70, 3 => only128 i (op2 i true (pshufK p i.imm))
  | 0x71, 1 | 0x72, 1 | 0x73, 1 => only128 i do   -- shifts by imm8: VEX.vvvv := shift (r/m)
    let bits := if b0 == 0x71 then 16 else if b0 == 0x72 then 32 else 64
    let ok := match i.reg with
      | 2 | 6 => true | 4 => b0 != 0x73 | 3 | 7 => b0 == 0x73 | _ => false
    start i (ok && !i.isMem)
    let cnt := (i.imm &&& 0xFF).toUInt64
    let s := (← getY i.rm).lo
    let r := match i.reg with
      | 2 => pshift 128 bits 0 cnt s | 4 => pshift 128 bits 1 cnt s | 6 => pshift 128 bits 2 cnt s
      | 3 => byteShift false cnt s | _ => byteShift true cnt s
    setX i.vvvv r
  | 0xC4, 1 => some do                   -- VPINSRW xmm, xmm, r32/m16, imm8
    start i (!L)
    let v ← rdGE i 2
    setX i.reg ((← src1 i).lo.setLane 16 (i.imm &&& 7).toNat (v &&& 0xFFFF).toUInt64)
  | 0xC5, 1 => some do                   -- VPEXTRW r32, xmm, imm8
    start i (!L && noV i && !i.isMem)
    setReg i.reg ((← getY i.rm).lo.lane 16 (i.imm &&& 7).toNat).toUInt32
  | 0xD7, 1 => only128 i do              -- VPMOVMSKB r32, xmm
    start i (noV i && !i.isMem)
    setReg i.reg (signMask 8 16 (← getY i.rm))
  | 0xF7, 1 => some do                   -- VMASKMOVDQU xmm, xmm
    start i (!L && noV i && !i.isMem)
    maskMov (← getY i.reg).lo (← getY i.rm).lo 16 i
  | _, _ => none

/-- VZEROUPPER (VEX.128), VZEROALL (VEX.256): VEX.0F 77 with VEX.pp = 00. -/
def vzero (i : Inst) : Option (M Unit) :=
  if i.pp != 0 then none else some do
  start i (noV i)
  modCpu fun c => { c with sse := { c.sse with
    ymmh := Array.replicate 8 {}, xmm := if i.vexL then Array.replicate 8 {} else c.sse.xmm } }

/-- VHADDPD/PS, VHSUBPD/PS (7C, 7D), VADDSUBPD/PS (D0). -/
def horiz (i : Inst) (b0 : UInt8) (p : Nat) : Option (M Unit) :=
  if p != 1 && p != 3 then none
  else if b0 == 0xD0 then some (op3Fp i true (Sse.addsub (p == 1)))
  else some (op3Fp i true (Sse.hop (p == 1) (b0 == 0x7D)))

/-- VSHUFPS / VSHUFPD. -/
def shuf (i : Inst) (p : Nat) : Option (M Unit) :=
  if p == 0 then some (op3 i true (shufps i.imm))
  else if p == 1 then some do
    start i true
    let a ← src1 i
    let b ← rdRmV i
    setV i i.reg { lo := shufpd i.imm a.lo b.lo, hi := shufpd (i.imm >>> 2) a.hi b.hi }
  else none

/-- VLDMXCSR m32 (VEX.0F AE /2), VSTMXCSR m32 (/3). -/
def mxcsrOp (i : Inst) (p : Nat) : Option (M Unit) :=
  if p != 0 || !i.isMem || (i.reg != 2 && i.reg != 3) then none else some do
  start i (!i.vexL && noV i)
  if i.reg == 2 then
    let v := (← rdVex i 4).lo.lo.toUInt32
    if v &&& ~~~mxcsrMask != 0 then gp 0
    modCpu fun c => { c with sse := { c.sse with mxcsr := v } }
  else wrVex i 4 (V256.ofLo { lo := (← cpu).mxcsr.toUInt64 })

/-- VEX.0F map. -/
def map1 (i : Inst) : Option (M Unit) :=
  let b0 := i.byte
  let p := i.pp.toNat
  match b0 with
  | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x15 | 0x16 | 0x17 | 0x28 | 0x29 | 0x2B => moves i b0 p
  | 0x2A | 0x2C | 0x2D | 0x2E | 0x2F | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58
  | 0x59 | 0x5A | 0x5B | 0x5C | 0x5D | 0x5E | 0x5F | 0xC2 | 0xE6 => fpOps i b0 p
  | 0x77 => vzero i
  | 0x7C | 0x7D | 0xD0 => horiz i b0 p
  | 0xC6 => shuf i p
  | 0xAE => mxcsrOp i p
  | _ => intMoves i b0 p

/-! ## VEX.0F38 -/

/-- VEX.66.0F38. -/
def map2 (i : Inst) : Option (M Unit) :=
  if i.pp != 1 then none else
  let b0 := i.byte
  let L := i.vexL
  match b0 with
  | 0x00 => only128 i (op3 i true (Sse.pshufb 128))
  | 0x01 => only128 i (op3 i true (Sse.phop 128 16 Sse.phAdd))
  | 0x02 => only128 i (op3 i true (Sse.phop 128 32 Sse.phAdd))
  | 0x03 => only128 i (op3 i true (Sse.phop 128 16 Sse.phAddS))
  | 0x04 => only128 i (op3 i true (Sse.pmaddubsw 128))
  | 0x05 => only128 i (op3 i true (Sse.phop 128 16 Sse.phSub))
  | 0x06 => only128 i (op3 i true (Sse.phop 128 32 Sse.phSub))
  | 0x07 => only128 i (op3 i true (Sse.phop 128 16 Sse.phSubS))
  | 0x08 => only128 i (op3 i true (Sse.psign 128 8))
  | 0x09 => only128 i (op3 i true (Sse.psign 128 16))
  | 0x0A => only128 i (op3 i true (Sse.psign 128 32))
  | 0x0B => only128 i (op3 i true (Sse.pmulhrsw 128))
  | 0x0C => some (op3 i (w0 i) permilpsV)    -- VPERMILPS (variable)
  | 0x0D => some (op3 i (w0 i) permilpdV)    -- VPERMILPD (variable)
  | 0x0E | 0x0F | 0x17 => some do            -- VTESTPS, VTESTPD, VPTEST
    start i (noV i && (b0 == 0x17 || w0 i))
    let a ← getY i.reg
    let b ← rdRmV i
    let (zf, cf) := testFlags (if b0 == 0x0E then 32 else if b0 == 0x0F then 64 else 1) L a b
    setFlags Flag.arith ((if zf then Flag.ZF else 0) ||| (if cf then Flag.CF else 0))
  | 0x18 =>                                 -- VBROADCASTSS xmm/ymm, m32 (register form: AVX2)
    if !i.isMem then none else some do
    start i (w0 i && noV i)
    setV i i.reg (broadcast 32 (← rdVex i 4).lo.lo)
  | 0x19 =>                                 -- VBROADCASTSD ymm, m64 (register form: AVX2)
    if !i.isMem then none else some do
    start i (w0 i && noV i && L)
    setY i.reg (broadcast 64 (← rdVex i 8).lo.lo)
  | 0x1A => some do                         -- VBROADCASTF128 ymm, m128
    start i (w0 i && noV i && L && i.isMem)
    let v := (← rdVex i 16).lo
    setY i.reg { lo := v, hi := v }
  | 0x1C => only128 i (op2 i true (Sse.pabs 128 8))
  | 0x1D => only128 i (op2 i true (Sse.pabs 128 16))
  | 0x1E => only128 i (op2 i true (Sse.pabs 128 32))
  | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25 | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 =>
    only128 i do                            -- VPMOVSX/VPMOVZX
    start i (noV i)
    let k := (b0 &&& 0xF).toNat
    let (fb, tb) := match k with
      | 0 => (8, 16) | 1 => (8, 32) | 2 => (8, 64) | 3 => (16, 32) | 4 => (16, 64) | _ => (32, 64)
    let s ← rdRm i (fb * (128 / tb) / 8).toUInt32
    setX i.reg (Sse.pmovx s.lo fb tb (b0 < 0x30))
  | 0x28 => only128 i (op3 i true Sse.pmuldq)
  | 0x29 => only128 i (op3 i true Sse.pcmpeqq)
  | 0x2A => only128 i do                    -- VMOVNTDQA xmm, m128 (aligned)
    start i (noV i && i.isMem)
    setX i.reg (← rdVex i 16 true).lo
  | 0x2B => only128 i (op3 i true Sse.packusdw)
  | 0x2C => some (maskLoad i 32)
  | 0x2D => some (maskLoad i 64)
  | 0x2E => some (maskStore i 32)
  | 0x2F => some (maskStore i 64)
  | 0x37 => only128 i (op3 i true Sse.pcmpgtq)
  | 0x38 | 0x39 | 0x3A | 0x3B | 0x3C | 0x3D | 0x3E | 0x3F => only128 i (op3 i true (Sse.pminmax b0))
  | 0x40 => only128 i (op3 i true Sse.pmulld)
  | 0x41 => some do                         -- VPHMINPOSUW (VEX.128 only, also with AVX2)
    start i (!L && noV i)
    setX i.reg (Sse.phminposuw (← rdRm i 16).lo)
  | 0xDB => only128 i (op2 i true Crypto.aesimc)
  | 0xDC => only128 i (op3 i true Crypto.aesenc)
  | 0xDD => only128 i (op3 i true Crypto.aesenclast)
  | 0xDE => only128 i (op3 i true Crypto.aesdec)
  | 0xDF => only128 i (op3 i true Crypto.aesdeclast)
  | _ => none

/-! ## VEX.0F3A -/

/-- VPCMPESTRI/M, VPCMPISTRI/M (as `Sse.pcmpstrOp`; VPCMPxSTRM writes XMM0 with VEX.128 zeroing). -/
def pcmpstr (i : Inst) (b0 : UInt8) : M Unit := do
  start i (!i.vexL && noV i)
  let imm := (i.imm &&& 0xFF).toNat
  let a := (← getY i.reg).lo
  let b := (← rdRm i 16).lo
  let explicit := b0 ≤ 0x61
  let eax ← getReg 0
  let edx ← getReg 2
  let la := if explicit then Sse.strLenE imm eax else Sse.strLenI imm a
  let lb := if explicit then Sse.strLenE imm edx else Sse.strLenI imm b
  let res := Sse.pcmpstr imm a b la lb
  if b0 &&& 1 == 1 then setReg 1 (Sse.strIndex imm res) else setX 0 (Sse.strMask imm res)
  setFlags Flag.arith (Sse.strFlags imm res la lb)

/-- VEX.66.0F3A (imm8 in `imm`). -/
def map3 (i : Inst) : Option (M Unit) :=
  if i.pp != 1 then none else
  let b0 := i.byte
  let L := i.vexL
  let imm := (i.imm &&& 0xFF).toNat
  match b0 with
  | 0x04 => some (op2 i (w0 i) (permilpsI i.imm))            -- VPERMILPS (imm8)
  | 0x05 => some do                                           -- VPERMILPD (imm8)
    start i (w0 i && noV i)
    let s ← rdRmV i
    setV i i.reg { lo := permilpdI i.imm s.lo, hi := permilpdI (i.imm >>> 2) s.hi }
  | 0x06 => some do                                           -- VPERM2F128
    start i (w0 i && L)
    let a ← src1 i
    let b ← rdRm i 32
    setY i.reg (perm2f128 i.imm a b)
  | 0x08 | 0x09 => some (op2Fp i true fun y mx => Sse.round (b0 == 0x09) false {} y imm mx)
  | 0x0A | 0x0B => some do                                    -- VROUNDSS/SD xmm, xmm, xmm/m
    start i true
    let a := (← src1 i).lo
    let b := (← rdRm i (if b0 == 0x0B then 8 else 4)).lo
    let (r, fl) := Sse.round (b0 == 0x0B) true a b imm (← mx64)
    sseStatus fl
    setX i.reg r
  | 0x0C | 0x0D => some do                                    -- VBLENDPS / VBLENDPD
    start i true
    let bits := if b0 == 0x0C then 32 else 64
    let a ← src1 i
    let b ← rdRmV i
    setV i i.reg { lo := Sse.blend bits imm a.lo b.lo, hi := Sse.blend bits (imm >>> (128 / bits)) a.hi b.hi }
  | 0x0E => only128 i (op3 i true (Sse.blend 16 imm))
  | 0x0F => only128 i (op3 i true fun a b => Sse.palignr 128 a b imm)
  | 0x14 | 0x15 | 0x16 | 0x17 => some do                      -- VPEXTRB/W/D, VEXTRACTPS r/m
    start i (!L && noV i)
    let s := (← getY i.reg).lo
    let (bits, k) := match b0 with
      | 0x14 => (8, imm % 16) | 0x15 => (16, imm % 8) | _ => (32, imm % 4)
    let v := s.lane bits k
    if i.isMem then wrVex i (bits / 8).toUInt32 (V256.ofLo { lo := v }) else setReg i.rm v.toUInt32
  | 0x18 => some do                                           -- VINSERTF128
    start i (w0 i && L)
    let a ← src1 i
    let b := (← rdRm i 16).lo
    setY i.reg (if imm % 2 == 1 then { a with hi := b } else { a with lo := b })
  | 0x19 => some do                                           -- VEXTRACTF128
    start i (w0 i && L && noV i)
    let s ← getY i.reg
    let v := if imm % 2 == 1 then s.hi else s.lo
    if i.isMem then wrVex i 16 (V256.ofLo v) else setX i.rm v
  | 0x20 => some do                                           -- VPINSRB xmm, xmm, r32/m8
    start i (!L)
    let v ← rdGE i 1
    setX i.reg ((← src1 i).lo.setLane 8 (imm % 16) (v &&& 0xFF).toUInt64)
  | 0x21 => some do                                           -- VINSERTPS xmm, xmm, xmm/m32
    start i (!L)
    let s ← if i.isMem then pure (← rdVex i 4).lo.lo else pure ((← getY i.rm).lo.lane 32 (imm >>> 6))
    setX i.reg (Sse.insertps (← src1 i).lo s imm)
  | 0x22 => some do                                           -- VPINSRD xmm, xmm, r/m32
    start i (!L)
    let v ← rdGE i 4
    setX i.reg ((← src1 i).lo.setLane 32 (imm % 4) v.toUInt64)
  | 0x40 => some do                                           -- VDPPS (both lengths)
    start i true
    let a ← src1 i
    let b ← rdRmV i
    let mx ← mx64
    -- VEX.256: the stages are per operation across both lanes (all multiplies, then the first
    -- additions, then the last additions; SDM DPPS: "Exceptions are determined separately for each add
    -- and multiply operation, in the order of their execution"): an unmasked exception in a stage of
    -- either lane suppresses the later stages of both, as for one 256-bit operation (`sseStatus`:
    -- an unmasked IE/DE/ZE suppresses OE/UE/PE of every element)
    let (r0, s0) := Sse.dppsStages a.lo b.lo imm mx
    let (r1, s1) := if L then Sse.dppsStages a.hi b.hi imm mx else ({}, [0, 0, 0])
    let (fl, u) := Sse.stages mx (List.zipWith (· ||| ·) s0 s1)
    Sse.statusStaged fl u
    setV i i.reg { lo := r0, hi := r1 }
  | 0x41 => some do                                           -- VDPPD (VEX.128 only)
    start i (!L)
    let a := (← src1 i).lo
    let b := (← rdRm i 16).lo
    let (r, fl, u) := Sse.dppd a b imm (← mx64)
    Sse.statusStaged fl u
    setX i.reg r
  | 0x42 => only128 i (op3 i true fun a b => Sse.mpsadbw a b imm)
  | 0x44 => only128 i (op3 i true fun a b => Crypto.pclmulqdq a b i.imm.toUInt8)
  | 0x4A | 0x4B => some do                                    -- VBLENDVPS / VBLENDVPD (is4)
    start i (w0 i)
    let bits := if b0 == 0x4A then 32 else 64
    let a ← src1 i
    let b ← rdRmV i
    let m ← getY (is4 i)
    setV i i.reg { lo := Sse.blendv bits a.lo b.lo m.lo, hi := Sse.blendv bits a.hi b.hi m.hi }
  | 0x4C => only128 i do                                      -- VPBLENDVB (is4)
    start i (w0 i)
    let a := (← src1 i).lo
    let b := (← rdRm i 16).lo
    let m := (← getY (is4 i)).lo
    setX i.reg (Sse.blendv 8 a b m)
  | 0x60 | 0x61 | 0x62 | 0x63 => some (pcmpstr i b0)
  | 0xDF => only128 i (op2 i true fun s => Crypto.aeskeygenassist s i.imm.toUInt8)
  | _ => none

/-! ## Hook -/

/-- The AVX instructions (see the module documentation); `none` for everything else. -/
def vex? (i : Inst) : Option (M Unit) :=
  if !implemented .avx then none else
  match i.map with
  | 1 => map1 i
  | 2 => map2 i
  | 3 => map3 i
  | _ => none

end Avx
end X86
