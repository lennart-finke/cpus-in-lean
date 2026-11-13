import X86.Ext.Avx
/-!
# AVX2, FMA3, F16C

Owner: the AVX2 workstream. The instructions of Zen 2's AVX2, FMA (FMA3) and F16C subsets in 32-bit
mode, built on the shared VEX layer (`X86/Ext/Vex.lean`: `start`, `V256`, `getY`/`setY`/`setV`,
`rdRm`, `lanes`, exception classes, the #AC rule) and on the AVX extension point (`Avx.vex?` returns
`none` for the forms below; `Avx.intOp` and the AVX kernels are reused). Zen 2 has no FMA4 (AMD APM
vol. 4: CPUID Fn8000_0001_ECX[FMA4]; the EPYC 7742 reports it clear): VEX.0F3A 5C..5F, 68..6F,
78..7F stay #UD, as do VAES, VPCLMULQDQ ymm, AVX-512 and AVX-VNNI encodings.

Hook (called by `X86/Dispatch.lean` after `Avx.vex?`; `none` = not handled here, the fallback is #UD):

* `vex?`: maps 0F (`map1`), 0F 38 (`map2`), 0F 3A (`map3`).

Sources: AMD APM vol. 4 (instruction pages of each instruction, primary), Intel SDM vol. 2 (the same
pages) and vol. 1, 14.5 (FMA) and 14.4.1 (half precision), SDM vol. 2A, 2.3.12 (VSIB).

## AVX2 integer forms (VEX.256)

* The VEX.256 forms of the 0F-map packed-integer instructions (`pint` opcodes, PSHUFD/HW/LW,
  the shifts by imm8 including VPSLLDQ/VPSRLDQ, the 0F 38/0F 3A SSSE3/SSE4.1 forms) operate within
  each 128-bit lane: PSHUFB, PALIGNR, PACK*, PUNPCK*, PHADD*/PHSUB*, PSLLDQ/PSRLDQ, PBLENDW (the same
  imm8 for both lanes), PSADBW, and VMPSADBW, whose upper lane uses imm8[5:3] (SDM VMPSADBW, AMD APM
  vol. 4 VMPSADBW). Theorems: `Proofs/ExtAvx2.lean` (`pshufb256_lanes`, `palignr256_lanes`, `int256_lanes`).
* The shifts by an XMM count (VPSLLW/D/Q, VPSRLW/D/Q, VPSRAW/D ymm, ymm, xmm/m128) shift both lanes
  by the one 64-bit count in bits 63:0 of the source (a 16-byte memory operand): not per lane.
* VPMOVSX*/VPMOVZX* ymm read 8/4/2 elements (16, 8 or 4 bytes) and widen across the whole register;
  VPMOVMSKB r32, ymm collects 32 sign bits.
* Cross-lane: VPERMD/VPERMPS (indices in VEX.vvvv, data in r/m), VPERMQ/VPERMPD (imm8),
  VPERM2I128, VINSERTI128/VEXTRACTI128, VBROADCASTI128, VPBROADCASTB/W/D/Q and VBROADCASTSS/SD from
  a register, VPBLENDD, and the variable shifts VPSLLVD/Q, VPSRLVD/Q (count ≥ element width gives 0),
  VPSRAVD (sign fill).
* Encoding rules (#UD before the VEX checks, `Vex.start`): VPERMQ/VPERMPD ignore VEX.W (the APM
  requires W1, but the EPYC 7742 executes VPERMQ with W0 as VPERMQ: native `avx2_encoding`); VEX.W0 for
  VPERMD/VPERMPS, VPERM2I128, VINSERTI128, VEXTRACTI128, VBROADCASTI128, VPBROADCAST*, VPBLENDD,
  VPSRAVD, VPBLENDVB, VCVTPH2PS, VCVTPS2PH, VBROADCASTSS/SD (AMD APM vol. 4 exception tables:
  "VEX.W = 1"); VEX.L = 1 for the cross-lane 256-bit-only forms ("VEX.L = 0"); VEX.vvvv = 1111b for
  the forms without a VEX.vvvv operand; memory-only VBROADCASTI128, VMOVNTDQA, VPMASKMOV*.

## Masked moves (VPMASKMOVD/Q)

As VMASKMOVPS/PD in `Avx.lean`: masked-out elements are not accessed and raise no exception (AMD APM
vol. 4 VPMASKMOVD: "Exception and trap behavior for elements not selected ... is implementation
dependent"; the model follows the SDM, "Faults occur only due to mask-bit required memory accesses");
a store checks every selected element before writing any. AMD lists #AC for VPMASKMOVD/Q ("256-bit
memory operand not 32-byte aligned or 128-bit memory operand not 16-byte aligned"), but the EPYC 7742
raises none, for loads and stores, 128 and 256 bits, at offsets 1, 2, 4, 8 with alignment checking
on (native campaign family `avx2_alignment`, 12 cases), as for VMASKMOVPS/PD: the model raises no
#AC for them either (`maskAc` is a no-op).

## Gathers (VSIB)

VPGATHERDD/DQ/QD/QQ, VGATHERDPS/DPD/QPS/QPD (VEX.66.0F38 90..93; VEX.W selects 64-bit data, opcode
bit 0 64-bit indices; dest = ModRM.reg, mask = VEX.vvvv, index = VSIB.index, an XMM/YMM register,
`gatherIndex`). The decoder parses the VSIB byte as a SIB byte; VSIB.index = 100b, "no index" for a
SIB, is XMM4/YMM4 here.
* #UD (encoding, before the VEX checks): ModRM.mod = 11b, ModRM.rm ≠ 100b (no VSIB byte), any two
  of dest, mask and index the same register (AMD APM vol. 4 VGATHERDPS: "YMM/XMM registers specified
  for destination, mask, and index not unique"), 16-bit addressing (a 67 prefix in 32-bit code: SDM
  vol. 2A, 2.3.12, VSIB needs a SIB byte, which 16-bit addressing does not have; QEMU's decoder
  agrees).
* Elements in ascending order: each selected element (mask sign bit) is loaded from
  base + disp + sign-extended index · scale (32-bit wrap-around), with a segment check and paging
  and no alignment check (the EPYC 7742 raises no #AC for misaligned gather elements with alignment
  checking on: native `avx2_alignment`, offsets 1, 2, 4 of VPGATHERDD/DQ, 5 cases); after each element
  (selected or not) its mask element is cleared. A fault at element k leaves elements < k loaded with
  their mask elements zero and the others unchanged, and the instruction can be restarted (SDM:
  "Faults are delivered in a right-to-left manner"; AMD APM vol. 4 VGATHERDPS: "Elements that have
  been loaded will have their mask elements set to zero"); `Step.faultCpu` keeps the vector registers
  of a faulting gather (the one change outside this module). The SDM pseudocode first normalizes
  every mask element to all ones or zero, which is visible only after a fault; AMD describes no such
  step and the model (like QEMU) leaves the unprocessed mask elements as they were (open doubt,
  recorded by the native campaign family `avx2_gather`).
* Completion: the whole mask register is zero, and the destination bits above the gathered elements
  (VEX.128 bits 255:128; bits 127:64 / 255:128 of the 64-bit-index forms with 32-bit data) are zero.
  On a fault these parts are left unchanged (the SDM allows either; QEMU leaves them).
* A gather with an all-zero mask makes no memory access, writes no element and clears the mask
  (`gather_zero_mask`).
* Not modelled: delivering a data breakpoint of an already loaded element instead of a later fault
  (SDM: "If any traps or faults are pending from elements that have been loaded, they will be
  delivered in lieu of the exception; in this case, the RF flag is set"); the model delivers the
  fault and drops the pending trap.

## FMA3

VFMADD/VFMSUB/VFNMADD/VFNMSUB 132/213/231 PS/PD/SS/SD and VFMADDSUB/VFMSUBADD 132/213/231 PS/PD
(VEX.66.0F38 96..9F, A6..AF, B6..BF; VEX.W = 1 double precision). With op1 = ModRM.reg (the
destination), op2 = VEX.vvvv and op3 = ModRM.r/m, the digits name the operands of `x·y + z`
(`fmaOps`): 132 = op1·op3 + op2, 213 = op2·op1 + op3, 231 = op2·op3 + op1. Each element is
`FP.fma` (one rounding; NaN order x, y, z; see its documentation for 0·∞ + QNaN); VFMADDSUB
subtracts in the even elements and adds in the odd ones, VFMSUBADD the reverse. Scalar forms ignore
VEX.L, compute element 0 and keep bits 127:32 (63:64) of op1 (SDM VFMADD132SS:
"DEST[127:32] ← DEST[127:32]"), zeroing bits 255:128. MXCSR flags of all elements are merged and an
unmasked exception leaves the destination unchanged (`sseStatus`).

## F16C

VCVTPH2PS xmm/ymm, xmm/m64/m128 (`FP.halfToSingle`) and VCVTPS2PH xmm/m64/m128, xmm/ymm, imm8
(`FP.singleToHalf`): imm8[2] = 1 rounds by MXCSR.RC, otherwise by imm8[1:0]; imm8[7:3] are ignored.
The register destination of VCVTPS2PH is ModRM.r/m (VEX.128 zeroing of bits 255:64 / 255:128). With
an unmasked exception VCVTPS2PH raises #XM (or #UD) before its store.
-/
namespace X86
namespace Avx2
open Vex

/-! ## 256-bit helpers -/

/-- `v` with element `k` of `bits` width (counted over all 256 bits) replaced. -/
def setLane256 (v : V256) (bits k : Nat) (x : UInt64) : V256 :=
  let n := 128 / bits
  if k < n then { v with lo := v.lo.setLane bits k x } else { v with hi := v.hi.setLane bits (k - n) x }

/-- `v` with every bit at position ≥ `w` cleared. -/
def keepLow (v : V256) (w : Nat) : V256 :=
  let m := fun (s : Nat) => if w ≥ s + 64 then 0xFFFFFFFFFFFFFFFF
    else if w ≤ s then 0 else ((1 : UInt64) <<< (w - s).toUInt64) - 1
  { lo := { lo := v.lo.lo &&& m 0, hi := v.lo.hi &&& m 64 },
    hi := { lo := v.hi.lo &&& m 128, hi := v.hi.hi &&& m 192 } }

/-! ## Kernels -/

/-- VPMOVSX/VPMOVZX: `n` elements of `fb` bits from the low bits of `src`, extended to `tb` bits. -/
def pmovx (src : V128) (fb tb n : Nat) (signed : Bool) : V256 :=
  V256.ofLanes tb ((Array.range n).map fun k =>
    let x := src.lane fb k
    if signed then lenc tb (lsx fb x) else x)

/-- VPERMD/VPERMPS: dword k is dword `idx[k][2:0]` of `data`. -/
def permd (idx data : V256) : V256 :=
  V256.ofLanes 32 ((Array.range 8).map fun k => data.lane 32 (idx.lane 32 k &&& 7).toNat)

/-- VPERMQ/VPERMPD: qword k is qword `imm8[2k+1:2k]` of `s`. -/
def permq (imm : UInt32) (s : V256) : V256 :=
  V256.ofLanes 64 ((Array.range 4).map fun k => s.lane 64 ((imm >>> (2 * k).toUInt32) &&& 3).toNat)

/-- VPBLENDD: dword k (k < n) from `b` if imm8[k], else from `a`. -/
def blendd (imm n : Nat) (a b : V256) : V256 :=
  V256.ofLanes 32 ((Array.range n).map fun k => if (imm >>> k) % 2 == 1 then b.lane 32 k else a.lane 32 k)

/-- Variable shifts of `n` elements of `bits` width: kind 0 logical right (VPSRLV), 1 arithmetic
right (VPSRAVD), 2 left (VPSLLV); the count is the whole corresponding element of `cnt` (unsigned):
a count ≥ `bits` gives 0, or the sign fill for the arithmetic shift. -/
def varShift (bits kind n : Nat) (a cnt : V256) : V256 :=
  V256.ofLanes bits ((Array.range n).map fun k =>
    let x := a.lane bits k
    let c := cnt.lane bits k
    if kind == 1 then
      let s := if c ≥ bits.toUInt64 then bits - 1 else c.toNat
      lenc bits (lsx bits x / (2^s : Nat))
    else if c ≥ bits.toUInt64 then 0
    else if kind == 0 then x >>> c
    else lenc bits ((x <<< c).toNat))

/-- The shift kind and element width of a shift by an XMM count (0F D1..D3, E1, E2, F1..F3). -/
def shiftByXmm? (b0 : UInt8) : Option (Nat × Nat) :=
  match b0 with
  | 0xD1 => some (16, 0) | 0xD2 => some (32, 0) | 0xD3 => some (64, 0)
  | 0xE1 => some (16, 1) | 0xE2 => some (32, 1)
  | 0xF1 => some (16, 2) | 0xF2 => some (32, 2) | 0xF3 => some (64, 2)
  | _ => none

/-- VMPSADBW per lane: the low lane with imm8[2:0], the high lane (VEX.256) with imm8[5:3]. -/
def mpsadbw256 (imm : Nat) (a b : V256) : V256 :=
  { lo := Sse.mpsadbw a.lo b.lo imm, hi := Sse.mpsadbw a.hi b.hi (imm >>> 3) }

/-! ## FMA kernels -/

/-- The operands (x, y, z) of `x·y + z` for the FMA3 forms 132 (`form` 0), 213 (1), 231 (2), from
op1 = ModRM.reg, op2 = VEX.vvvv, op3 = ModRM.r/m (SDM vol. 1, 14.5.1; AMD APM vol. 4 VFMADD132PS). -/
@[inline] def fmaOps (form : Nat) (o1 o2 o3 : UInt64) : UInt64 × UInt64 × UInt64 :=
  match form with
  | 0 => (o1, o3, o2)
  | 1 => (o2, o1, o3)
  | _ => (o2, o3, o1)

/-- Negations (product, addend) of FMA opcode low nibble `kind` (6 ADDSUB, 7 SUBADD, 8/9 MADD,
A/B MSUB, C/D NMADD, E/F NMSUB) for element `k`. -/
@[inline] def fmaNeg (kind k : Nat) : Bool × Bool :=
  match kind with
  | 6 => (false, k % 2 == 0)
  | 7 => (false, k % 2 == 1)
  | 8 | 9 => (false, false)
  | 10 | 11 => (false, true)
  | 12 | 13 => (true, false)
  | _ => (true, true)

/-- Packed FMA over `n` elements of `bits` width: element k of the result and the merged flags. -/
def fmaPacked (bits n form kind : Nat) (o1 o2 o3 : V256) (mx : UInt64) : V256 × UInt64 :=
  let f := if bits == 64 then FP.binary64 else FP.binary32
  let rs := (Array.range n).map fun k =>
    let (x, y, z) := fmaOps form (o1.lane bits k) (o2.lane bits k) (o3.lane bits k)
    let (np, na) := fmaNeg kind k
    FP.fma f x y z np na mx
  (V256.ofLanes bits (rs.map (·.1)), rs.foldl (fun acc r => acc ||| r.2) 0)

/-! ## Instruction forms -/

@[inline] def mx64 : M UInt64 := do return (← cpu).mxcsr.toUInt64

/-- VEX.256 shift by an XMM count: both lanes by the count in bits 63:0 of xmm/m128. -/
def shiftXmm (i : Inst) (bits kind : Nat) : M Unit := do
  start i true
  let a ← src1 i
  let cnt := (← rdRm i 16).lo.lo
  setV i i.reg (lanes i.vexL (fun x _ => pshift 128 bits kind cnt x) a {})

/-- VEX.256 shifts by imm8 (VEX.66.0F 71..73 /2 /3 /4 /6 /7): VEX.vvvv := shift (ModRM.r/m), per lane. -/
def shiftImm (i : Inst) (b0 : UInt8) : M Unit := do
  let bits := if b0 == 0x71 then 16 else if b0 == 0x72 then 32 else 64
  let ok := match i.reg with
    | 2 | 6 => true | 4 => b0 != 0x73 | 3 | 7 => b0 == 0x73 | _ => false
  start i (ok && !i.isMem)
  let cnt := (i.imm &&& 0xFF).toUInt64
  let s ← getY i.rm
  let f := fun (x : V128) => match i.reg with
    | 2 => pshift 128 bits 0 cnt x | 4 => pshift 128 bits 1 cnt x | 6 => pshift 128 bits 2 cnt x
    | 3 => byteShift false cnt x | _ => byteShift true cnt x
  setV i i.vvvv (lanes i.vexL (fun x _ => f x) s {})

/-- VPMOVSX/VPMOVZX (VEX.66.0F38 20..25, 30..35) of either length. -/
def pmovxOp (i : Inst) (b0 : UInt8) : M Unit := do
  start i (noV i)
  let (fb, tb) := match (b0 &&& 0xF).toNat with
    | 0 => (8, 16) | 1 => (8, 32) | 2 => (8, 64) | 3 => (16, 32) | 4 => (16, 64) | _ => (32, 64)
  let n := (if i.vexL then 256 else 128) / tb
  let s ← rdRm i (fb * n / 8).toUInt32
  setV i i.reg (pmovx s.lo fb tb n (b0 < 0x30))

/-- VPBROADCASTB/W/D/Q (`bits`), VBROADCASTSS/SD from a register: element 0 of xmm/m in every
element. -/
def broadcastOp (i : Inst) (bits : Nat) (enc : Bool) : M Unit := do
  start i (enc && w0 i && noV i)
  let s ← rdRm i (bits / 8).toUInt32
  setV i i.reg (Avx.broadcast bits (s.lo.lane bits 0))

/-- VPSLLV/VPSRLV/VPSRAV: data VEX.vvvv, counts r/m. -/
def varShiftOp (i : Inst) (kind : Nat) (enc : Bool) : M Unit := do
  start i enc
  let bits := if i.vexW then 64 else 32
  let a ← src1 i
  let c ← rdRmV i
  setV i i.reg (varShift bits kind ((if i.vexL then 256 else 128) / bits) a c)

/-- #AC for a VPMASKMOV operand: none on the EPYC 7742 (see the module documentation). -/
def maskAc (_lin : UInt32) : M Unit := pure ()

/-- VPMASKMOVD/Q load (VEX.66.0F38 8C): selected elements read in ascending order, others 0. -/
def pmaskLoad (i : Inst) : M Unit := do
  start i i.isMem
  let bits := if i.vexW then 64 else 32
  let mask ← src1 i
  let off ← fpEa i
  let n := (if i.vexL then 256 else 128) / bits
  let sz := (bits / 8).toUInt32
  let sel := Avx.maskSel bits n mask
  let mut out : Array UInt64 := Array.replicate n 0
  let mut first := true
  for k in sel do
    let lin ← segAddr i.seg (off + sz * k.toUInt32) sz false
    if first then maskAc (lin - sz * k.toUInt32)
    first := false
    out := out.set! k (← rdLin lin sz).lo
  setV i i.reg (V256.ofLanes bits out)

/-- VPMASKMOVD/Q store (VEX.66.0F38 8E): every selected element is checked (segment, page) before
the first is written; the others are not accessed. -/
def pmaskStore (i : Inst) : M Unit := do
  start i i.isMem
  let bits := if i.vexW then 64 else 32
  let mask ← src1 i
  let data ← getY i.reg
  let off ← fpEa i
  let n := (if i.vexL then 256 else 128) / bits
  let sz := (bits / 8).toUInt32
  let sel := Avx.maskSel bits n mask
  let mut lins : Array UInt32 := #[]
  for k in sel do
    let lin ← segAddr i.seg (off + sz * k.toUInt32) sz true
    if lins.isEmpty then maskAc (lin - sz * k.toUInt32)
    linProbeWr lin sz (← isUser)
    lins := lins.push lin
  for (k, lin) in sel.zip lins.toList do
    wrLin lin sz { lo := data.lane bits k }

/-! ### Gathers -/

/-- The VSIB index register: the SIB index field, where 100b (decoded as "no index") is XMM4/YMM4. -/
@[inline] def gatherIndex (i : Inst) : UInt8 := if i.index == 8 then 4 else i.index

/-- The encoding conditions of a gather (#UD otherwise): a memory operand with a VSIB byte, 32-bit
addressing, and destination (ModRM.reg), mask (VEX.vvvv) and index (VSIB.index) all different. -/
@[inline] def gatherEnc (i : Inst) : Bool :=
  i.isMem && i.rm == 4 && i.adsz == 4 && i.reg != i.vvvv && i.reg != gatherIndex i &&
    i.vvvv != gatherIndex i

/-- (data bits, index bits, number of elements) of a gather. -/
@[inline] def gatherShape (i : Inst) : Nat × Nat × Nat :=
  let db := if i.vexW then 64 else 32
  let ib := if i.byte &&& 1 == 1 then 64 else 32
  (db, ib, (if i.vexL then 256 else 128) / max db ib)

/-- The element loop of a gather over the element numbers `ks` (ascending): a selected element is
loaded into the destination register, then the element's mask element is cleared; both registers are
written after every element, so that a fault leaves the completed elements in place. `sel` is the
selection by the mask's sign bits before the instruction. -/
def gatherElems (i : Inst) (db ib : Nat) (base : UInt32) (ix : V256) (sel : Array Bool) :
    List Nat → V256 → V256 → M Unit
  | [], _, _ => pure ()
  | k :: ks, d, m => do
    let d ← if sel[k]! then do
        let sz := (db / 8).toUInt32
        let off := base + i.disp + ((ix.lane ib k).toUInt32 <<< i.scale.toUInt32)
        let lin ← segAddr i.seg off sz false
        let d := setLane256 d db k (← rdLin lin sz).lo
        setY i.reg d
        pure d
      else pure d
    let m := setLane256 m db k 0
    setY i.vvvv m
    gatherElems i db ib base ix sel ks d m

/-- VPGATHERDD/DQ/QD/QQ, VGATHERDPS/DPD/QPS/QPD (see the module documentation). -/
def gather (i : Inst) : M Unit := do
  start i (gatherEnc i)
  let (db, ib, n) := gatherShape i
  let c ← cpu
  let y := fun (r : UInt8) => V256.mk c.xmm[(r &&& 7).toNat]! c.ymmh[(r &&& 7).toNat]!
  let base := if i.base < 8 then c.getReg i.base else 0
  let sel := (Array.range n).map fun k => (y i.vvvv).lane db k >>> (db - 1).toUInt64 != 0
  gatherElems i db ib base (y (gatherIndex i)) sel (List.range n) (y i.reg) (y i.vvvv)
  setY i.reg (keepLow (← getY i.reg) (n * db))
  setY i.vvvv {}

/-! ### FMA and F16C -/

/-- FMA3 (VEX.66.0F38 96..9F, A6..AF, B6..BF). -/
def fmaOp (i : Inst) (b0 : UInt8) : M Unit := do
  let form := (b0 >>> 4).toNat - 9
  let kind := (b0 &&& 0xF).toNat
  let bits := if i.vexW then 64 else 32
  let f := if i.vexW then FP.binary64 else FP.binary32
  let scalar := kind ≥ 8 && kind % 2 == 1
  start i true
  let o1 ← getY i.reg
  let o2 ← src1 i
  let mx ← mx64
  if scalar then
    let o3 ← rdRm i (bits / 8).toUInt32
    let (x, y, z) := fmaOps form (o1.lane bits 0) (o2.lane bits 0) (o3.lane bits 0)
    let (np, na) := fmaNeg kind 0
    let (r, fl) := FP.fma f x y z np na mx
    sseStatus fl
    setX i.reg (o1.lo.setLane bits 0 r)
  else
    let o3 ← rdRmV i
    let (r, fl) := fmaPacked bits ((if i.vexL then 256 else 128) / bits) form kind o1 o2 o3 mx
    sseStatus fl
    setV i i.reg r

/-- VCVTPH2PS xmm1, xmm2/m64; ymm1, xmm2/m128. -/
def cvtph2ps (i : Inst) : M Unit := do
  start i (w0 i && noV i)
  let n := if i.vexL then 8 else 4
  let s := (← rdRm i (2 * n).toUInt32).lo
  let mx ← mx64
  let rs := (Array.range n).map fun k => FP.halfToSingle (s.lane 16 k) mx
  sseStatus (rs.foldl (fun acc r => acc ||| r.2) 0)
  setV i i.reg (V256.ofLanes 32 (rs.map (·.1)))

/-- VCVTPS2PH xmm1/m64, xmm2, imm8; xmm1/m128, ymm2, imm8 (source ModRM.reg). -/
def cvtps2ph (i : Inst) : M Unit := do
  start i (w0 i && noV i)
  let n := if i.vexL then 8 else 4
  let s ← getY i.reg
  let mx ← mx64
  let rc := if i.imm &&& 4 != 0 then (mx >>> 13) &&& 3 else (i.imm &&& 3).toUInt64
  let rs := (Array.range n).map fun k => FP.singleToHalf (s.lane 32 k) rc mx
  -- a memory destination is checked (segment, #AC, #PF) before the MXCSR flags are set and before an
  -- unmasked exception's #XM: the EPYC 7742 raises #AC first and leaves MXCSR unchanged on a #PF
  -- (native `enc_fuzz`, `avx_random`: 5 cases; was: MXCSR flags set, #XM)
  let lin? ← if i.isMem then some <$> addr i (2 * n).toUInt32 true false else pure none
  sseStatus (rs.foldl (fun acc r => acc ||| r.2) 0)
  let v := V128.ofLanes 16 (rs.map (·.1))
  match lin? with
  | some lin => wrLinV lin (2 * n).toUInt32 (V256.ofLo v)
  | none => setX i.rm v

/-! ## Maps -/

/-- VEX.0F: the VEX.256 integer forms (VEX.128 is AVX's). -/
def map1 (i : Inst) : Option (M Unit) :=
  if !i.vexL || !implemented .avx2 then none else
  let b0 := i.byte
  if i.pp == 1 then
    if isPint b0 then
      match shiftByXmm? b0 with
      | some (bits, kind) => some (shiftXmm i bits kind)
      | none => some (Avx.intOp i b0)
    else match b0 with
      | 0x70 => some (op2 i true (Avx.pshufK 1 i.imm))
      | 0x71 | 0x72 | 0x73 => some (shiftImm i b0)
      | 0xD7 => some do                              -- VPMOVMSKB r32, ymm
        start i (noV i && !i.isMem)
        setReg i.reg (Avx.signMask 8 32 (← getY i.rm))
      | _ => none
  -- VPSHUFHW (F3) / VPSHUFLW (F2) ymm; VEX.256.NP.0F 70 is no instruction (#UD: SDM vol. 2 and AMD
  -- APM vol. 4 list only the 66, F3 and F2 forms of 0F 70 with VEX), so pp = 0 must not reach
  -- `pshufK`, whose default arm is PSHUFLW
  else if b0 == 0x70 && i.pp ≥ 2 then some (op2 i true (Avx.pshufK i.pp.toNat i.imm))
  else none

/-- VEX.66.0F38 forms that are AVX2 only in their VEX.256 form (per 128-bit lane). -/
def map2L (i : Inst) (b0 : UInt8) : Option (M Unit) :=
  if !i.vexL then none else
  match b0 with
  | 0x00 => some (op3 i true (Sse.pshufb 128))
  | 0x01 => some (op3 i true (Sse.phop 128 16 Sse.phAdd))
  | 0x02 => some (op3 i true (Sse.phop 128 32 Sse.phAdd))
  | 0x03 => some (op3 i true (Sse.phop 128 16 Sse.phAddS))
  | 0x04 => some (op3 i true (Sse.pmaddubsw 128))
  | 0x05 => some (op3 i true (Sse.phop 128 16 Sse.phSub))
  | 0x06 => some (op3 i true (Sse.phop 128 32 Sse.phSub))
  | 0x07 => some (op3 i true (Sse.phop 128 16 Sse.phSubS))
  | 0x08 => some (op3 i true (Sse.psign 128 8))
  | 0x09 => some (op3 i true (Sse.psign 128 16))
  | 0x0A => some (op3 i true (Sse.psign 128 32))
  | 0x0B => some (op3 i true (Sse.pmulhrsw 128))
  | 0x1C => some (op2 i true (Sse.pabs 128 8))
  | 0x1D => some (op2 i true (Sse.pabs 128 16))
  | 0x1E => some (op2 i true (Sse.pabs 128 32))
  | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25 | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 =>
    some (pmovxOp i b0)
  | 0x28 => some (op3 i true Sse.pmuldq)
  | 0x29 => some (op3 i true Sse.pcmpeqq)
  | 0x2A => some do                                  -- VMOVNTDQA ymm, m256 (aligned)
    start i (noV i && i.isMem)
    setY i.reg (← rdVex i 32 true)
  | 0x2B => some (op3 i true Sse.packusdw)
  | 0x37 => some (op3 i true Sse.pcmpgtq)
  | 0x38 | 0x39 | 0x3A | 0x3B | 0x3C | 0x3D | 0x3E | 0x3F => some (op3 i true (Sse.pminmax b0))
  | 0x40 => some (op3 i true Sse.pmulld)
  | _ => none

/-- VEX.66.0F38. -/
def map2 (i : Inst) : Option (M Unit) :=
  if i.pp != 1 then none else
  let b0 := i.byte
  let L := i.vexL
  if 0x96 ≤ b0 && ((b0 &&& 0xF) ≥ 6) && b0 ≤ 0xBF then
    if implemented .fma then some (fmaOp i b0) else none
  else if b0 == 0x13 then
    if implemented .f16c then some (cvtph2ps i) else none
  else if !implemented .avx2 then none else
  match b0 with
  | 0x16 | 0x36 => some do                           -- VPERMPS, VPERMD
    start i (w0 i && L)
    let idx ← src1 i
    let data ← rdRm i 32
    setY i.reg (permd idx data)
  | 0x18 => if i.isMem then none else some (broadcastOp i 32 true)     -- VBROADCASTSS xmm/ymm, xmm
  | 0x19 => if i.isMem then none else some (broadcastOp i 64 L)        -- VBROADCASTSD ymm, xmm
  | 0x45 => some (varShiftOp i 0 true)               -- VPSRLVD/Q
  | 0x46 => some (varShiftOp i 1 (w0 i))             -- VPSRAVD
  | 0x47 => some (varShiftOp i 2 true)               -- VPSLLVD/Q
  | 0x58 => some (broadcastOp i 32 true)             -- VPBROADCASTD
  | 0x59 => some (broadcastOp i 64 true)             -- VPBROADCASTQ
  | 0x78 => some (broadcastOp i 8 true)              -- VPBROADCASTB
  | 0x79 => some (broadcastOp i 16 true)             -- VPBROADCASTW
  | 0x5A => some do                                  -- VBROADCASTI128 ymm, m128
    start i (w0 i && noV i && L && i.isMem)
    let v := (← rdVex i 16).lo
    setY i.reg { lo := v, hi := v }
  | 0x8C => some (pmaskLoad i)
  | 0x8E => some (pmaskStore i)
  | 0x90 | 0x91 | 0x92 | 0x93 => some (gather i)
  | _ => map2L i b0

/-- VEX.66.0F3A (imm8 in `imm`). -/
def map3 (i : Inst) : Option (M Unit) :=
  if i.pp != 1 then none else
  let b0 := i.byte
  let L := i.vexL
  let imm := (i.imm &&& 0xFF).toNat
  if b0 == 0x1D then
    if implemented .f16c then some (cvtps2ph i) else none
  else if !implemented .avx2 then none else
  match b0 with
  | 0x00 | 0x01 => some do                           -- VPERMQ, VPERMPD
    start i (L && noV i)   -- VEX.W ignored (EPYC 7742)
    setY i.reg (permq i.imm (← rdRm i 32))
  | 0x02 => some do                                  -- VPBLENDD
    start i (w0 i)
    let a ← src1 i
    let b ← rdRmV i
    setV i i.reg (blendd imm (if L then 8 else 4) a b)
  | 0x0E => if !L then none else some (op3 i true (Sse.blend 16 imm))          -- VPBLENDW ymm
  | 0x0F => if !L then none else some (op3 i true fun a b => Sse.palignr 128 a b imm)   -- VPALIGNR ymm
  | 0x38 => some do                                  -- VINSERTI128
    start i (w0 i && L)
    let a ← src1 i
    let b := (← rdRm i 16).lo
    setY i.reg (if imm % 2 == 1 then { a with hi := b } else { a with lo := b })
  | 0x39 => some do                                  -- VEXTRACTI128
    start i (w0 i && L && noV i)
    let s ← getY i.reg
    let v := if imm % 2 == 1 then s.hi else s.lo
    if i.isMem then wrVex i 16 (V256.ofLo v) else setX i.rm v
  | 0x42 => if !L then none else some do             -- VMPSADBW ymm
    start i true
    let a ← src1 i
    let b ← rdRmV i
    setY i.reg (mpsadbw256 imm a b)
  | 0x46 => some do                                  -- VPERM2I128
    start i (w0 i && L)
    let a ← src1 i
    let b ← rdRm i 32
    setY i.reg (Avx.perm2f128 i.imm a b)
  | 0x4C => if !L then none else some do             -- VPBLENDVB ymm (is4)
    start i (w0 i)
    let a ← src1 i
    let b ← rdRmV i
    let m ← getY (is4 i)
    setY i.reg { lo := Sse.blendv 8 a.lo b.lo m.lo, hi := Sse.blendv 8 a.hi b.hi m.hi }
  | _ => none

/-! ## Hook -/

/-- The AVX2, FMA and F16C instructions (see the module documentation); `none` for everything else. -/
def vex? (i : Inst) : Option (M Unit) :=
  if !implemented .avx then none else
  match i.map with
  | 1 => map1 i
  | 2 => map2 i
  | 3 => map3 i
  | _ => none

end Avx2
end X86
