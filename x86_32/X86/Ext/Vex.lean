import X86.Exec
/-!
# Shared VEX infrastructure

Owner: the AVX workstream (`Avx.lean`); `Avx2.lean` (AVX2, FMA3, F16C) builds on it, `Gpr.lean`
(BMI1/BMI2) does not use it (GPR instructions have no XSAVE-managed state).

This is the layer every VEX-encoded SSE/AVX instruction goes through: the #UD/#NM checks, the
256-bit register file, VEX memory operands, the zeroing rule of VEX.128 and the operand plumbing of
three-operand and is4 forms. Sources: Intel SDM vol. 1, 14.1-14.9 (AVX), vol. 2A, 2.3 (VEX) and
2.4-2.8 (exception classes); AMD APM vol. 4, 1.x (AVX/VEX) and the exception tables of each
instruction; AMD APM vol. 3, 1.2.7 (VEX prefix). Where they differ, AMD wins (none found that
matters here; see the notes below).

## Decoding (done before any hook runs)

`Dispatch.vexExec` has already raised #UD for every VEX instruction in real or virtual-8086 mode,
with a 66, F2, F3 or LOCK prefix before the VEX prefix, or with an unknown map (VEX.mmmmm not 1..3).
In 16- and 32-bit code: VEX.R and VEX.X (inverted) are 1 by construction (otherwise C4/C5 are
LES/LDS), VEX.B is ignored, and so is the inverted VEX.vvvv[3] of the three-byte form: "In 32-bit and
16-bit modes bit 6 must be 1 (if bit 6 is not 1, the 2-byte VEX version will generate LDS instruction
and the 3-byte VEX version will ignore this bit)" (SDM vol. 2A, 2.3.5.6). So `Inst.vvvv` is the
register number 0..7. But "VEX.vvvv = 1111b" (`noV`) checks all four bits (`Inst.vvvv3` too): the
EPYC 7742 raises #UD for VMOVAPS and VCVTPS2PH whose vvvv[3] alone is wrong (native campaign
families `avx_encoding`, `avx2_encoding`); where vvvv names a register, bit 3 is ignored (VADDPS with
vvvv = 1001b uses XMM1 on the 7742). The VEX prefix is valid in
16-bit protected-mode code segments too (SDM vol. 2A, 2.3: #UD only in real and virtual-8086 mode);
the decoder accepts it there, and the operand size (66) does not exist for VEX instructions.

## Checks (`start`, `vexCheck`)

In this order, before any state is read or written:

1. **Encoding** (#UD): per-instruction constraints on VEX.L (`L0`: "VEX.128 only", `L1`: "VEX.256
   only"; LIG instructions ignore it), VEX.W (`W0`: "#UD if VEX.W = 1", the instructions of SDM vol.
   2A table 2-16 and AMD's exception classes with a W requirement; WIG instructions and the 32-bit
   forms of VMOVD/VPEXTRD/VPINSRD/VCVTSI2Sx ignore it: "VEX.W1 in non-64-bit mode is ignored"),
   VEX.vvvv (`noV`: "If an instruction does not use VEX.vvvv then it should be set to 1111b otherwise
   instruction will #UD", SDM vol. 2A, 2.3.5.6) and ModRM.mod (memory-only / register-only forms).
   The instruction module evaluates these and passes the result to `start`.
2. **AVX enabled** (#UD): CR4.OSXSAVE = 1 and XCR0[2:1] = 11b (SDM vol. 1, 14.3; AMD APM vol. 2,
   11.5.5; the exception tables "XFEATURE_ENABLED_MASK[2:1] != 11b"). CR0.EM and CR4.OSFXSR do not
   apply to VEX instructions (SDM vol. 2A, tables 2-15..2-22: "Legacy SSE" rows only; AMD APM vol. 4
   marks them "S", SSE-only).
3. **CR0.TS** (#NM).

The #UD conditions come before #NM: both are instruction-decode faults of the same priority class
(SDM vol. 3, table 6-2, class 8), and the encoding is invalid whatever the state.

## Operands

* **256-bit registers**: YMMk = `SseState.ymmh[k]` (bits 255:128) : `SseState.xmm[k]` (bits 127:0),
  as `V256` (`getY`, `setY`).
* **Destination zeroing** (`setV`): a VEX.128 instruction writes bits 127:0 and zeroes bits 255:128
  of its destination register; VEX.256 writes all 256 bits (SDM vol. 1, 14.1.2 "VEX.128 ... zeroes
  the upper bits"; AMD APM vol. 4, 1.x). Legacy SSE instructions (`setXmm`) leave bits 255:128 alone.
  Theorems: `Proofs/ExtAvx.lean`.
* **Memory operands** (`addr`, `rdVex`, `wrVex`, `rdRm`, `rdRmV`): 4, 8, 16 or 32 bytes. Segment checks first
  (#GP(0), #SS(0)), then alignment: only the explicitly aligned moves (VMOVAPS/PD, VMOVDQA,
  VMOVNTPS/PD, VMOVNTDQ, VMOVNTDQA: SDM exception class 1) require 16-byte (VEX.128) or 32-byte
  (VEX.256) alignment, #GP(0); every other VEX memory operand may be misaligned (classes 2..7: "no
  alignment requirement for VEX", SDM vol. 2A, 2.5; AMD APM vol. 4). MXCSR.MM (AMD Misaligned SSE
  mode) does not apply to VEX instructions (it controls legacy SSE only, AMD APM vol. 1, 4.3.2).
  Then alignment checking (`acChk`, the shared #AC rule of `X86/Machine.lean`: CR0.AM, EFLAGS.AC,
  CPL 3): a VEX operand must be aligned to its size, at most 16 bytes ("256-bit media" and "128-bit
  media" both 16, AMD APM vol. 2, table 8-7; APM vol. 4, VADDPS: "#AC: Memory operand not 16-byte
  aligned when alignment checking enabled", scalar forms: "Unaligned memory reference"). Stores check
  the whole range for writability before writing (a #PF leaves memory unchanged).
* **Three operands**: VEX.vvvv is the first source (`src1`), ModRM.r/m the second, ModRM.reg the
  destination; the VEX immediate shifts (VEX.0F 71..73) write VEX.vvvv instead.
* **is4** (`is4`): the fourth register operand of VBLENDVPx/VPBLENDVB is imm8[7:4]; imm8[7] is
  ignored in 32-bit mode (SDM vol. 2A, 2.3.9 "VBLENDVPD, VBLENDVPS, and PBLENDVB use imm8[7:4] to
  encode one of the source registers", and 3.1.1.2, /is4: "a source register specifier in either
  imm8[7:4] (for 64-bit mode) or imm8[6:4] (for 32-bit mode)"; rev. 084).
* **Lanes**: `lanes L f a b` applies a 128-bit kernel to the low halves and, for VEX.256, the high
  halves: every SSE kernel of `X86/Simd.lean`/`X86/Ext/Sse.lean` used by a VEX.256 form works within
  128-bit lanes.

## Exception classes (SDM vol. 2A, 2.4-2.8; AMD APM vol. 4 "AVX exception classes")

| class | instructions | #UD (beyond the checks above) | alignment | #XM |
|---|---|---|---|---|
| 1 | VMOVAPx, VMOVDQA, VMOVNTx (aligned) | L/vvvv/mod | 16/32-byte (#GP(0)) | no |
| 2 | packed FP (VADDPS, VCVTDQ2PS, VROUNDPS, VDPPS, ...) | | none | yes |
| 3 | scalar FP (VADDSS, VCOMISS, VCVTSI2SS, ...) | | none | yes |
| 4 | packed integer, logic, shuffles (VPADDB, VANDPS, VSHUFPS, VAES*, VPCLMULQDQ, ...) | L1 for 128-only | none | no |
| 5 | scalar/partial moves (VMOVSS, VMOVD, VPINSRx, VPEXTRx, VMOVLPS, ...) | | none | no |
| 6 | VEX-only (VBROADCASTx, VPERMILPx, VINSERTF128, VEXTRACTF128, VPERM2F128, VMASKMOVPx, VTESTPx) | W1, L | none | no |
| 7 | no memory operand (VMOVHLPS, VPSLLW imm, VMOVMSKPx, VPMOVMSKB, VPEXTRW r32) | mod != 11b | — | no |
| 8 | VZEROALL, VZEROUPPER | vvvv | — | no |

SIMD floating-point exceptions use the conventions of `sseStatus` (`X86/Simd.lean`): all elements
(both 128-bit halves) are computed, their MXCSR flags merged; an unmasked exception raises #XM (or
#UD with CR4.OSXMMEXCPT = 0) with the flags set and the destination unchanged; an unmasked input
exception (IE/DE/ZE) suppresses the output exceptions.

## Extension point for `Avx2.lean`

`Avx.vex?` returns `none` for VEX.256 forms of the integer opcodes (AVX2) and for the AVX2/FMA/F16C
opcodes, so `Avx2.vex?`, called next by `Dispatch.vexExec`, can add them without editing
`Avx.lean`. Their 128-bit kernels and the operand helpers of this file (`start`, `getY`, `setV`,
`rdRm`, `lanes`, ...) are reusable as they are; `Avx.intOp` implements the per-lane integer forms for
both lengths (see `Avx.lean`).
-/
namespace X86
namespace Vex

/-! ## 256-bit values -/

/-- A 256-bit value: `lo` = bits 127:0, `hi` = bits 255:128. -/
structure V256 where
  lo : V128 := {}
  hi : V128 := {}
  deriving Repr, Inhabited, BEq

namespace V256
/-- A 128-bit value zero-extended to 256 bits. -/
@[inline] def ofLo (v : V128) : V256 := { lo := v }
/-- The 128-bit half `h` (0 low, 1 high). -/
@[inline] def half (v : V256) (h : Nat) : V128 := if h % 2 == 0 then v.lo else v.hi
/-- Element `k` of `bits` width across all 256 bits. -/
@[inline] def lane (v : V256) (bits k : Nat) : UInt64 :=
  let n := 128 / bits
  if k < n then v.lo.lane bits k else v.hi.lane bits (k - n)
def ofLanes (bits : Nat) (ls : Array UInt64) : V256 :=
  let n := 128 / bits
  { lo := V128.ofLanes bits (ls.extract 0 n), hi := V128.ofLanes bits (ls.extract n (2 * n)) }
end V256

/-- Apply a 128-bit kernel to the low halves, and for VEX.256 (`L`) to the high halves (bits
255:128 of the result are 0 for VEX.128). -/
@[inline] def lanes (L : Bool) (f : V128 → V128 → V128) (a b : V256) : V256 :=
  { lo := f a.lo b.lo, hi := if L then f a.hi b.hi else {} }

/-- `lanes` for floating-point kernels returning MXCSR flags: the flags of both halves are merged. -/
@[inline] def lanesFp (L : Bool) (f : V128 → V128 → V128 × UInt64) (a b : V256) : V256 × UInt64 :=
  let (r0, f0) := f a.lo b.lo
  if L then
    let (r1, f1) := f a.hi b.hi
    ({ lo := r0, hi := r1 }, f0 ||| f1)
  else ({ lo := r0 }, f0)

/-! ## Encoding predicates -/

/-- VEX.vvvv = 1111b (no register), all four bits: the EPYC 7742 raises #UD for VMOVAPS and VCVTPS2PH
with only vvvv[3] wrong in 32-bit mode (native campaign families `avx_encoding`, `avx2_encoding`),
although vvvv[3] selects no register there. -/
@[inline] def noV (i : Inst) : Bool := i.vvvv == 0 && !i.vvvv3
/-- VEX.L = 0. -/
@[inline] def l0 (i : Inst) : Bool := !i.vexL
/-- VEX.W = 0. -/
@[inline] def w0 (i : Inst) : Bool := !i.vexW
/-- Vector size in bytes: 16 (VEX.128) or 32 (VEX.256). -/
@[inline] def vsz (i : Inst) : UInt32 := if i.vexL then 32 else 16
/-- The is4 register operand: imm8[7:4], imm8[7] ignored outside 64-bit mode. -/
@[inline] def is4 (i : Inst) : UInt8 := ((i.imm >>> 4) &&& 7).toUInt8

/-! ## Checks -/

/-- AVX state enabled: CR4.OSXSAVE = 1 and XCR0[2:1] = 11b. -/
@[inline] def avxEnabled (c : Cpu) : Bool :=
  c.cr4 &&& CR4.OSXSAVE != 0 && c.xcr0 &&& (XCR0.SSE ||| XCR0.YMM) == XCR0.SSE ||| XCR0.YMM

/-- The checks of a VEX-encoded SSE/AVX instruction before it touches any state (SDM vol. 1, 14.3;
vol. 2A, 2.4; AMD APM vol. 4): #UD unless CR4.OSXSAVE = 1 and XCR0[2:1] = 11b, then #NM with CR0.TS.
CR0.EM and CR4.OSFXSR are not checked (legacy SSE only). Not for BMI1/BMI2. -/
def vexCheck (_i : Inst) : M Unit := do
  let c ← cpu
  if !avxEnabled c then ud
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM

/-- Start a VEX instruction: #UD unless its encoding constraints `enc` hold (VEX.L, VEX.W, VEX.vvvv,
ModRM.mod, evaluated by the caller), then `vexCheck`. -/
@[inline] def start (i : Inst) (enc : Bool) : M Unit := do
  if !enc then ud
  vexCheck i

/-! ## Registers -/

@[inline] def getY (r : UInt8) : M V256 := fun m =>
  let k := (r &&& 7).toNat
  .ok { lo := m.cpu.xmm[k]!, hi := m.cpu.ymmh[k]! } m

/-- Write all 256 bits of YMMr. -/
@[inline] def setY (r : UInt8) (v : V256) : M Unit :=
  modCpu fun c =>
    let k := (r &&& 7).toNat
    { c with sse := { c.sse with xmm := c.sse.xmm.set! k v.lo, ymmh := c.sse.ymmh.set! k v.hi } }

/-- The destination write of a VEX instruction: VEX.256 writes YMMr, VEX.128 writes XMMr and zeroes
bits 255:128. -/
@[inline] def setV (i : Inst) (r : UInt8) (v : V256) : M Unit :=
  setY r (if i.vexL then v else V256.ofLo v.lo)

/-- The destination write of a VEX.128-only (or LIG) instruction: XMMr := v, bits 255:128 := 0. -/
@[inline] def setX (r : UInt8) (v : V128) : M Unit := setY r (V256.ofLo v)

/-! ## Memory -/

/-- Linear address of an `n`-byte VEX memory operand (n ∈ {1, 2, 4, 8, 16, 32}): segment checks;
with `align` (class 1 only) `n`-byte alignment, #GP(0); #AC(0) with alignment checking for an
operand not aligned to min(n, 16) bytes; for a store, the whole range is checked for
writability before anything is written. -/
def addr (i : Inst) (n : UInt32) (write align : Bool) : M UInt32 := do
  let lin ← segAddr i.seg (← fpEa i) n write
  if align && lin &&& (n - 1) != 0 then gp 0
  acChk lin (if n > 16 then 16 else n) (← isUser)
  if write then linProbeWr lin n (← isUser)
  return lin

/-- Read `n` bytes (zero-extended) at a linear address. -/
def rdLinV (lin n : UInt32) : M V256 := do
  if n ≤ 16 then return V256.ofLo (← rdLin lin n)
  let lo ← rdLin lin 16
  let hi ← rdLin (lin + 16) 16
  return { lo, hi }

/-- Write the low `n` bytes of `v` at a linear address. -/
def wrLinV (lin n : UInt32) (v : V256) : M Unit := do
  if n ≤ 16 then wrLin lin n v.lo
  else
    wrLin lin 16 v.lo
    wrLin (lin + 16) 16 v.hi

def rdVex (i : Inst) (n : UInt32) (align : Bool := false) : M V256 := do
  rdLinV (← addr i n false align) n

def wrVex (i : Inst) (n : UInt32) (v : V256) (align : Bool := false) : M Unit := do
  wrLinV (← addr i n true align) n v

/-- The r/m operand: YMM register, or `n` bytes of memory (zero-extended). -/
@[inline] def rdRm (i : Inst) (n : UInt32) (align : Bool := false) : M V256 := do
  if i.isMem then rdVex i n align else getY i.rm

/-- The vector-size r/m operand (16 or 32 bytes by VEX.L). -/
@[inline] def rdRmV (i : Inst) (align : Bool := false) : M V256 := rdRm i (vsz i) align

/-- The first source, VEX.vvvv. -/
@[inline] def src1 (i : Inst) : M V256 := getY i.vvvv

/-! ## Generic forms -/

/-- `reg := f vvvv (r/m)` per 128-bit lane, both lengths (class 4 shape). -/
def op3 (i : Inst) (enc : Bool) (f : V128 → V128 → V128) (align : Bool := false) : M Unit := do
  start i enc
  let a ← src1 i
  let b ← rdRmV i align
  setV i i.reg (lanes i.vexL f a b)

/-- `reg := f (r/m)` per 128-bit lane; VEX.vvvv must be 1111b. -/
def op2 (i : Inst) (enc : Bool) (f : V128 → V128) (align : Bool := false) : M Unit := do
  start i (enc && noV i)
  let b ← rdRmV i align
  setV i i.reg (lanes i.vexL (fun _ y => f y) {} b)

/-- Floating-point `reg := f vvvv (r/m) mxcsr` per lane, flags through `sseStatus` (class 2). -/
def op3Fp (i : Inst) (enc : Bool) (f : V128 → V128 → UInt64 → V128 × UInt64) : M Unit := do
  start i enc
  let a ← src1 i
  let b ← rdRmV i
  let mx := (← cpu).mxcsr.toUInt64
  let (r, fl) := lanesFp i.vexL (fun x y => f x y mx) a b
  sseStatus fl
  setV i i.reg r

/-- Floating-point `reg := f (r/m) mxcsr` per lane; VEX.vvvv must be 1111b. -/
def op2Fp (i : Inst) (enc : Bool) (f : V128 → UInt64 → V128 × UInt64) : M Unit := do
  start i (enc && noV i)
  let b ← rdRmV i
  let mx := (← cpu).mxcsr.toUInt64
  let (r, fl) := lanesFp i.vexL (fun _ y => f y mx) {} b
  sseStatus fl
  setV i i.reg r

end Vex
end X86
