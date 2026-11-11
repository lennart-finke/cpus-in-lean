import X86.Dispatch
import X86.Proofs.Basic
import X86.Proofs.ExtAvx
import Std.Tactic.BVDecide
/-!
# AVX2, FMA3, F16C (`X86/Ext/Avx2.lean`, `FP.fma`, `FP.halfToSingle`, `FP.singleToHalf`)

* Gathers: `gather_ud_overlap` (#UD when any two of destination, mask and index coincide, before
  any state is touched), `gather_ud_reg`, `gather_ud_a16` (ModRM.mod = 11b, 16-bit addressing);
  `gather_zero_mask` (with no mask element selected a gather makes no memory access, changes only the
  CPU registers and finishes by clearing the mask register); `vex?_gather` (the hook dispatches
  VEX.66.0F38 90..93 to `gather`, and AVX's hook does not take them).
* No FMA4 on Zen 2: `vexExec_fma4` (VEX.0F3A 5C..5F, 68..6F, 78..7F raise #UD).
* Per-lane AVX2: `pshufb256_lanes`, `palignr256_lanes`, `int256_lanes` (the VEX.256 packed-integer
  forms of the 0F map compute each 128-bit half from the same half of the sources), and
  `shiftXmm_count` (the shifts by an XMM count use one count for both halves).
* FMA: `fma_nan_32`/`_64` (a NaN operand gives the first NaN of x, y, z quieted, IE exactly for an
  SNaN), `fma_inf_zero_32`/`_64` (0 · ∞ with a non-NaN addend is the default NaN with IE),
  `fma_inf_zero_qnan_32` (… with a QNaN addend: that QNaN, no IE), and `fma_table` (a table of special
  and exactly rounded cases, checked by the kernel).
* F16C: `halfRoundTrip` (binary16 → binary32 → binary16 is the identity for every non-SNaN binary16
  value and quiets an SNaN, with no flags), checked exhaustively for all 65,536 encodings by the kernel
  (`decide +kernel`, no `native_decide`).
-/
namespace X86
open Vex Avx2

/-! ## Gathers -/

theorem gather_ud {i : Inst} {m : Machine} (h : gatherEnc i = false) :
    gather i m = .error (.exc Vec.UD none 0) m := by
  simp [gather, h, start, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- #UD when the destination, mask and index registers are not all different (AMD APM vol. 4
VGATHERDPS: "YMM/XMM registers specified for destination, mask, and index not unique"). -/
theorem gather_ud_overlap {i : Inst} {m : Machine}
    (h : i.reg = i.vvvv ∨ i.reg = gatherIndex i ∨ i.vvvv = gatherIndex i) :
    gather i m = .error (.exc Vec.UD none 0) m := by
  apply gather_ud
  rcases h with h | h | h <;> simp [gatherEnc, h]

/-- #UD for the register form (ModRM.mod = 11b) and without a VSIB byte (ModRM.rm ≠ 100b). -/
theorem gather_ud_reg {i : Inst} {m : Machine} (h : i.isMem = false ∨ i.rm ≠ 4) :
    gather i m = .error (.exc Vec.UD none 0) m := by
  apply gather_ud
  rcases h with h | h <;> simp [gatherEnc, h]

/-- #UD with 16-bit addressing (a 67 prefix in 32-bit code). -/
theorem gather_ud_a16 {i : Inst} {m : Machine} (h : i.adsz = 2) :
    gather i m = .error (.exc Vec.UD none 0) m := by
  apply gather_ud
  simp [gatherEnc, h]

/-- The element loop with no selected element only writes CPU registers. -/
theorem gatherElems_none (i : Inst) (db ib : Nat) (base : UInt32) (ix : V256) (sel : Array Bool) :
    ∀ (ks : List Nat) (d mk : V256) (s : Machine), (∀ k ∈ ks, sel[k]! = false) →
      ∃ c, gatherElems i db ib base ix sel ks d mk s = .ok () { s with cpu := c } := by
  intro ks
  induction ks with
  | nil => intro d mk s _; exact ⟨s.cpu, rfl⟩
  | cons k ks ih =>
    intro d mk s h
    have hk : sel[k]! = false := h k (by simp)
    have hs : ∀ k' ∈ ks, sel[k']! = false := fun k' hk' => h k' (by simp [hk'])
    obtain ⟨c, hc⟩ := ih d (setLane256 mk db k 0)
      { s with cpu := { s.cpu with sse := { s.cpu.sse with
        xmm := s.cpu.sse.xmm.set! (i.vvvv &&& 7).toNat (setLane256 mk db k 0).lo,
        ymmh := s.cpu.sse.ymmh.set! (i.vvvv &&& 7).toNat (setLane256 mk db k 0).hi } } } hs
    refine ⟨c, ?_⟩
    simp only [gatherElems, hk, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, EStateM.bind, pure, EStateM.pure, setY, modCpu] at hc ⊢
    exact hc

/-- A gather whose mask selects no element (no mask element has its sign bit set) makes no memory
access (memory, TLB and every other non-CPU state are unchanged, and it cannot fault on the memory
operand) and finishes by writing zero to the whole mask register. -/
theorem gather_zero_mask {i : Inst} {m : Machine} (henc : gatherEnc i = true)
    (hen : avxEnabled m.cpu = true) (hts : m.cpu.cr0 &&& CR0.TS = 0)
    (hz : ∀ k, (V256.mk m.cpu.xmm[(i.vvvv &&& 7).toNat]! m.cpu.ymmh[(i.vvvv &&& 7).toNat]!).lane
      (gatherShape i).1 k >>> ((gatherShape i).1 - 1).toUInt64 = 0) :
    ∃ c : Cpu, gather i m = .ok () { m with cpu := { c with sse := { c.sse with
      xmm := c.sse.xmm.set! (i.vvvv &&& 7).toNat {}, ymmh := c.sse.ymmh.set! (i.vvvv &&& 7).toNat {} } } } := by
  rcases hs : gatherShape i with ⟨db, ib, n⟩
  rw [hs] at hz
  simp only at hz
  have hsel : ∀ k ∈ List.range n, ((Array.range n).map fun k =>
      (V256.mk m.cpu.xmm[(i.vvvv &&& 7).toNat]! m.cpu.ymmh[(i.vvvv &&& 7).toNat]!).lane db k >>>
        (db - 1).toUInt64 != 0)[k]! = false := by
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    have h := hz k
    simp at h
    simp [hk', h]
  obtain ⟨c, hc⟩ := gatherElems_none i db ib
    (if i.base < 8 then m.cpu.getReg i.base else 0)
    (V256.mk m.cpu.xmm[(gatherIndex i &&& 7).toNat]! m.cpu.ymmh[(gatherIndex i &&& 7).toNat]!) _
    (List.range n) (V256.mk m.cpu.xmm[(i.reg &&& 7).toNat]! m.cpu.ymmh[(i.reg &&& 7).toNat]!)
    (V256.mk m.cpu.xmm[(i.vvvv &&& 7).toNat]! m.cpu.ymmh[(i.vvvv &&& 7).toNat]!) m hsel
  refine ⟨{ c with sse := { c.sse with
    xmm := c.sse.xmm.set! (i.reg &&& 7).toNat
      (keepLow (V256.mk c.xmm[(i.reg &&& 7).toNat]! c.ymmh[(i.reg &&& 7).toNat]!) (n * db)).lo,
    ymmh := c.sse.ymmh.set! (i.reg &&& 7).toNat
      (keepLow (V256.mk c.xmm[(i.reg &&& 7).toNat]! c.ymmh[(i.reg &&& 7).toNat]!) (n * db)).hi } }, ?_⟩
  simp only [gather, hs, henc, bind, EStateM.bind, start_ok hen hts, cpu]
  rw [hc]
  rfl

/-- VEX.66.0F38 90..93 go to the gather (AVX's hook does not take them). -/
theorem vex?_gather {i : Inst} (hm : i.op >>> 8 = 2) (hp : i.pp = 1)
    (hb : i.byte = 0x90 ∨ i.byte = 0x91 ∨ i.byte = 0x92 ∨ i.byte = 0x93) :
    Avx.vex? i = none ∧ Avx2.vex? i = some (gather i) := by
  have hm' : i.map = 2 := hm
  rcases hb with hb | hb | hb | hb <;>
    simp [Avx.vex?, Avx2.vex?, hm', hp, hb, implemented, Avx.map2, Avx2.map2]

/-! ## No FMA4 -/

/-- The opcodes of AMD's FMA4 (VEX.0F3A 5C..5F, 68..6F, 78..7F) are not Zen 2 instructions. -/
def fma4Bytes : List UInt8 := [0x5C, 0x5D, 0x5E, 0x5F, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F]

/-- No hook takes an FMA4 opcode, so `vexExec` raises #UD (with the state unchanged). -/
theorem vexExec_fma4 {i : Inst} {m : Machine} (hm : i.op >>> 8 = 3) (hb : i.byte ∈ fma4Bytes) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  have hm' : i.map = 3 := hm
  simp only [fma4Bytes, List.mem_cons, List.not_mem_nil, or_false] at hb
  have hn : Gpr.vex? i = none ∧ Avx.vex? i = none ∧ Avx2.vex? i = none := by
    rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp [Gpr.vex?, Gpr.vexBody?, Avx.vex?, Avx.map3, Avx2.vex?, Avx2.map3, hm', h, implemented]
  obtain ⟨hg, ha, h2⟩ := hn
  simp only [vexExec, cpu, bind, EStateM.bind, hg, ha, h2, hooked]
  split <;> simp_all [ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]
  split <;> simp_all [ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]

/-! ## Per-lane AVX2 -/

/-- VEX.256 VPSHUFB: each 128-bit half of the result is PSHUFB of the same halves of the sources
(no byte crosses the lane boundary). -/
theorem pshufb256_lanes {i : Inst} (hp : i.pp = 1) (hL : i.vexL = true) (hb : i.byte = 0x00) :
    Avx2.map2 i = some (op3 i true (Sse.pshufb 128)) ∧
      ∀ a b, lanes true (Sse.pshufb 128) a b = { lo := Sse.pshufb 128 a.lo b.lo, hi := Sse.pshufb 128 a.hi b.hi } := by
  refine ⟨?_, fun _ _ => rfl⟩
  simp [Avx2.map2, Avx2.map2L, hp, hb, hL, implemented]

/-- VEX.256 VPALIGNR: per lane, with the same imm8 for both halves. -/
theorem palignr256_lanes {i : Inst} (hp : i.pp = 1) (hL : i.vexL = true) (hb : i.byte = 0x0F) :
    Avx2.map3 i = some (op3 i true fun a b => Sse.palignr 128 a b (i.imm &&& 0xFF).toNat) := by
  simp [Avx2.map3, hp, hb, hL, implemented]

/-- VEX.256 of a 0F-map packed-integer opcode other than a shift by an XMM count is the per-lane
`pint` kernel (`Avx.intOp`: `op3` with `lanes`). -/
theorem int256_lanes {i : Inst} (hm : i.op >>> 8 = 1) (hp : i.pp = 1) (hL : i.vexL = true)
    (hi : isPint i.byte = true) (hs : shiftByXmm? i.byte = none) :
    Avx2.vex? i = some (Avx.intOp i i.byte) := by
  have hm' : i.map = 1 := hm
  simp [Avx2.vex?, hm', Avx2.map1, hL, hp, hi, hs, implemented]

/-- The shifts by an XMM count (VEX.256) shift both halves by the one count in bits 63:0 of the
source: the high half of the result does not depend on the high half of the count operand. -/
theorem shiftXmm_count (bits kind : Nat) (a : V256) (cnt : UInt64) :
    lanes true (fun x _ => pshift 128 bits kind cnt x) a {} =
      { lo := pshift 128 bits kind cnt a.lo, hi := pshift 128 bits kind cnt a.hi } := rfl

/-! ## FMA -/

section Fma
open FP

/-- `prepare` (DAZ) leaves a NaN unchanged. -/
theorem prepare_nan {f : Format} (hf : f.exponentMax ≠ 0) {mx a : UInt64} (h : isNaN f a = true) :
    prepare f mx a = (a, 0) := by
  have : isDenormal f a = false := by
    simp only [isNaN, Bool.and_eq_true, beq_iff_eq] at h
    simp [isDenormal, h.1, hf]
  simp [prepare, this]

/-- A NaN first operand is the result (quieted) of every FMA form, with IE exactly when an operand
(after DAZ) is an SNaN; the negations do not apply to it (SDM vol. 1 table 14-17: Q(x)). -/
theorem fma_nan_a {f : Format} (hf : f.exponentMax ≠ 0) (a b c mx : UInt64) (np na : Bool)
    (h : isNaN f a = true) :
    fma f a b c np na mx =
      (a ||| f.quietBit,
        if isSNaN f a || isSNaN f (prepare f mx b).1 || isSNaN f (prepare f mx c).1 then 1 else 0) := by
  simp [fma, prepare_nan hf h, h]

/-- A NaN second operand with a non-NaN first operand is the result: Q(y). -/
theorem fma_nan_b {f : Format} (hf : f.exponentMax ≠ 0) (a b c mx : UInt64) (np na : Bool)
    (ha : isNaN f (prepare f mx a).1 = false) (h : isNaN f b = true) :
    fma f a b c np na mx =
      (b ||| f.quietBit,
        if isSNaN f (prepare f mx a).1 || isSNaN f b || isSNaN f (prepare f mx c).1 then 1 else 0) := by
  simp [fma, prepare_nan hf h, h, ha]

/-- With non-NaN first and second operands a NaN addend is the result, Q(z), and IE is signaled
only for an SNaN: in particular `0 · ∞ + QNaN` is the QNaN without IE (SDM vol. 1 table 14-17). -/
theorem fma_nan_c {f : Format} (hf : f.exponentMax ≠ 0) (a b c mx : UInt64) (np na : Bool)
    (ha : isNaN f (prepare f mx a).1 = false) (hb : isNaN f (prepare f mx b).1 = false)
    (h : isNaN f c = true) :
    fma f a b c np na mx = (c ||| f.quietBit, if isSNaN f c then 1 else 0) := by
  have hsa : isSNaN f (prepare f mx a).1 = false := by simp [isSNaN, ha]
  have hsb : isSNaN f (prepare f mx b).1 = false := by simp [isSNaN, hb]
  simp [fma, prepare_nan hf h, h, ha, hb, hsa, hsb]

theorem exponentMax32 : binary32.exponentMax ≠ 0 := by decide
theorem exponentMax64 : binary64.exponentMax ≠ 0 := by decide

end Fma

namespace FmaTable
open FP

/-- One row of the FMA table: binary32 operands a, b, c, the negations, MXCSR, and the expected
(result, flags). -/
structure Row where
  a : UInt64
  b : UInt64
  c : UInt64
  np : Bool := false
  na : Bool := false
  mx : UInt64 := 0x1F80
  r : UInt64
  fl : UInt64

def inf : UInt64 := 0x7F800000
def ninf : UInt64 := 0xFF800000
def one : UInt64 := 0x3F800000
def mone : UInt64 := 0xBF800000
def qnan : UInt64 := 0x7FC00011
def snan : UInt64 := 0x7F800022
def indef : UInt64 := 0xFFC00000

/-- SDM vol. 1 table 14-17 and IEEE 754-2008 (5.4.1, 6.3, 7.2), binary32. -/
def rows : List Row := [
  -- 0 · ∞ + (non-NaN): invalid, default NaN
  { a := 0, b := inf, c := one, r := indef, fl := 1 },
  { a := inf, b := 0x80000000, c := ninf, r := indef, fl := 1 },
  -- 0 · ∞ + QNaN: the QNaN, no IE; + SNaN: quieted, IE
  { a := inf, b := 0, c := qnan, r := qnan, fl := 0 },
  { a := 0, b := inf, c := snan, r := snan ||| 0x400000, fl := 1 },
  -- NaN order x, y, z; no negation of NaNs
  { a := qnan, b := snan, c := 0x7FC00033, r := qnan, fl := 1 },
  { a := one, b := 0x7FC00055, c := snan, r := 0x7FC00055, fl := 1 },
  { a := qnan, b := one, c := one, np := true, na := true, r := qnan, fl := 0 },
  -- ∞ - ∞ invalid; -(∞) + -∞ = -∞
  { a := inf, b := one, c := ninf, r := indef, fl := 1 },
  { a := inf, b := one, c := ninf, np := true, r := ninf, fl := 0 },
  { a := inf, b := one, c := inf, na := true, r := indef, fl := 1 },
  -- exact zero sums: +0, in round-down -0; (-0)·1 + (-0) = -0
  { a := one, b := one, c := mone, r := 0, fl := 0 },
  { a := one, b := one, c := mone, mx := 0x3F80, r := 0x80000000, fl := 0 },
  { a := 0x80000000, b := one, c := 0x80000000, r := 0x80000000, fl := 0 },
  { a := 0x80000000, b := one, c := 0, r := 0, fl := 0 },
  -- one rounding: (1 + 2^-23)(1 - 2^-23) - 1 = -2^-46 exactly (two roundings would give 0)
  { a := 0x3F800001, b := 0x3F7FFFFE, c := mone, r := 0xA8800000, fl := 0 },
  -- no intermediate overflow: max · 2 - max = max
  { a := 0x7F7FFFFF, b := 0x40000000, c := 0xFF7FFFFF, r := 0x7F7FFFFF, fl := 0 },
  -- overflow: max · 2 + 0 = ∞ (OE, PE); toward zero: max
  { a := 0x7F7FFFFF, b := 0x40000000, c := 0, r := inf, fl := 0x28 },
  { a := 0x7F7FFFFF, b := 0x40000000, c := 0, mx := 0x7F80, r := 0x7F7FFFFF, fl := 0x28 },
  -- denormal operands: DE; with DAZ zeros (no DE)
  { a := 0x00400000, b := 0x40000000, c := 0, r := 0x00800000, fl := 2 },
  { a := 0x00400000, b := 0x40000000, c := 0, mx := 0x1FC0, r := 0, fl := 0 },
  -- an exact tiny result: no UE (masked); FTZ: zero with UE, PE
  { a := 0x00800000, b := 0x3F000000, c := 0, r := 0x00400000, fl := 0 },
  { a := 0x00800000, b := 0x3F000000, c := 0, mx := 0x9F80, r := 0, fl := 0x30 },
  -- tininess after rounding with unbounded exponent: (2^24 - 1)·2^-150 is exact in 24 bits and below
  -- 2^-126, so it is tiny although rounding up denormalizes it to the smallest normal (UE, PE)
  { a := 0x3F7FFFFF, b := 0x00800000, c := 0, mx := 0x5F80, r := 0x00800000, fl := 0x30 },
  -- … while a product just above the normal range rounding down stays normal: PE only
  { a := 0x3F800001, b := 0x00FFFFFF, c := 0, mx := 0x3F80, r := 0x01000000, fl := 0x20 }
]

def check (row : Row) : Bool := fma binary32 row.a row.b row.c row.np row.na row.mx == (row.r, row.fl)

/-- The FMA special-case table holds (checked by the kernel). -/
theorem fma_table : rows.all check = true := by decide +kernel

end FmaTable

/-! ## F16C -/

/-- binary16 → binary32 → binary16 for one encoding `h`: the identity without flags, except that an
SNaN comes back quieted and the first conversion reports IE. -/
def halfRoundTripOk (h : Nat) : Bool :=
  let x := h.toUInt64
  let (s, f1) := FP.halfToSingle x 0x1F80
  let (back, f2) := FP.singleToHalf s 0 0x1F80
  f2 == 0 && (if FP.isSNaN FP.binary16 x then back == (x ||| 0x200) && f1 == 1 else back == x && f1 == 0)

/-- Encodings 1024·k .. 1024·k + 1023. -/
def halfChunkOk (k : Nat) : Bool := (List.range 1024).all fun j => halfRoundTripOk (1024 * k + j)

/-! All 65,536 binary16 encodings, checked exhaustively by the kernel in 64 chunks (one declaration
each, so that the kernel's caches stay small). -/
theorem halfChunk0 : halfChunkOk 0 = true := by decide +kernel
theorem halfChunk1 : halfChunkOk 1 = true := by decide +kernel
theorem halfChunk2 : halfChunkOk 2 = true := by decide +kernel
theorem halfChunk3 : halfChunkOk 3 = true := by decide +kernel
theorem halfChunk4 : halfChunkOk 4 = true := by decide +kernel
theorem halfChunk5 : halfChunkOk 5 = true := by decide +kernel
theorem halfChunk6 : halfChunkOk 6 = true := by decide +kernel
theorem halfChunk7 : halfChunkOk 7 = true := by decide +kernel
theorem halfChunk8 : halfChunkOk 8 = true := by decide +kernel
theorem halfChunk9 : halfChunkOk 9 = true := by decide +kernel
theorem halfChunk10 : halfChunkOk 10 = true := by decide +kernel
theorem halfChunk11 : halfChunkOk 11 = true := by decide +kernel
theorem halfChunk12 : halfChunkOk 12 = true := by decide +kernel
theorem halfChunk13 : halfChunkOk 13 = true := by decide +kernel
theorem halfChunk14 : halfChunkOk 14 = true := by decide +kernel
theorem halfChunk15 : halfChunkOk 15 = true := by decide +kernel
theorem halfChunk16 : halfChunkOk 16 = true := by decide +kernel
theorem halfChunk17 : halfChunkOk 17 = true := by decide +kernel
theorem halfChunk18 : halfChunkOk 18 = true := by decide +kernel
theorem halfChunk19 : halfChunkOk 19 = true := by decide +kernel
theorem halfChunk20 : halfChunkOk 20 = true := by decide +kernel
theorem halfChunk21 : halfChunkOk 21 = true := by decide +kernel
theorem halfChunk22 : halfChunkOk 22 = true := by decide +kernel
theorem halfChunk23 : halfChunkOk 23 = true := by decide +kernel
theorem halfChunk24 : halfChunkOk 24 = true := by decide +kernel
theorem halfChunk25 : halfChunkOk 25 = true := by decide +kernel
theorem halfChunk26 : halfChunkOk 26 = true := by decide +kernel
theorem halfChunk27 : halfChunkOk 27 = true := by decide +kernel
theorem halfChunk28 : halfChunkOk 28 = true := by decide +kernel
theorem halfChunk29 : halfChunkOk 29 = true := by decide +kernel
theorem halfChunk30 : halfChunkOk 30 = true := by decide +kernel
theorem halfChunk31 : halfChunkOk 31 = true := by decide +kernel
theorem halfChunk32 : halfChunkOk 32 = true := by decide +kernel
theorem halfChunk33 : halfChunkOk 33 = true := by decide +kernel
theorem halfChunk34 : halfChunkOk 34 = true := by decide +kernel
theorem halfChunk35 : halfChunkOk 35 = true := by decide +kernel
theorem halfChunk36 : halfChunkOk 36 = true := by decide +kernel
theorem halfChunk37 : halfChunkOk 37 = true := by decide +kernel
theorem halfChunk38 : halfChunkOk 38 = true := by decide +kernel
theorem halfChunk39 : halfChunkOk 39 = true := by decide +kernel
theorem halfChunk40 : halfChunkOk 40 = true := by decide +kernel
theorem halfChunk41 : halfChunkOk 41 = true := by decide +kernel
theorem halfChunk42 : halfChunkOk 42 = true := by decide +kernel
theorem halfChunk43 : halfChunkOk 43 = true := by decide +kernel
theorem halfChunk44 : halfChunkOk 44 = true := by decide +kernel
theorem halfChunk45 : halfChunkOk 45 = true := by decide +kernel
theorem halfChunk46 : halfChunkOk 46 = true := by decide +kernel
theorem halfChunk47 : halfChunkOk 47 = true := by decide +kernel
theorem halfChunk48 : halfChunkOk 48 = true := by decide +kernel
theorem halfChunk49 : halfChunkOk 49 = true := by decide +kernel
theorem halfChunk50 : halfChunkOk 50 = true := by decide +kernel
theorem halfChunk51 : halfChunkOk 51 = true := by decide +kernel
theorem halfChunk52 : halfChunkOk 52 = true := by decide +kernel
theorem halfChunk53 : halfChunkOk 53 = true := by decide +kernel
theorem halfChunk54 : halfChunkOk 54 = true := by decide +kernel
theorem halfChunk55 : halfChunkOk 55 = true := by decide +kernel
theorem halfChunk56 : halfChunkOk 56 = true := by decide +kernel
theorem halfChunk57 : halfChunkOk 57 = true := by decide +kernel
theorem halfChunk58 : halfChunkOk 58 = true := by decide +kernel
theorem halfChunk59 : halfChunkOk 59 = true := by decide +kernel
theorem halfChunk60 : halfChunkOk 60 = true := by decide +kernel
theorem halfChunk61 : halfChunkOk 61 = true := by decide +kernel
theorem halfChunk62 : halfChunkOk 62 = true := by decide +kernel
theorem halfChunk63 : halfChunkOk 63 = true := by decide +kernel

theorem halfChunk_all : ∀ k, k < 64 → halfChunkOk k = true
  | 0, _ => halfChunk0
  | 1, _ => halfChunk1
  | 2, _ => halfChunk2
  | 3, _ => halfChunk3
  | 4, _ => halfChunk4
  | 5, _ => halfChunk5
  | 6, _ => halfChunk6
  | 7, _ => halfChunk7
  | 8, _ => halfChunk8
  | 9, _ => halfChunk9
  | 10, _ => halfChunk10
  | 11, _ => halfChunk11
  | 12, _ => halfChunk12
  | 13, _ => halfChunk13
  | 14, _ => halfChunk14
  | 15, _ => halfChunk15
  | 16, _ => halfChunk16
  | 17, _ => halfChunk17
  | 18, _ => halfChunk18
  | 19, _ => halfChunk19
  | 20, _ => halfChunk20
  | 21, _ => halfChunk21
  | 22, _ => halfChunk22
  | 23, _ => halfChunk23
  | 24, _ => halfChunk24
  | 25, _ => halfChunk25
  | 26, _ => halfChunk26
  | 27, _ => halfChunk27
  | 28, _ => halfChunk28
  | 29, _ => halfChunk29
  | 30, _ => halfChunk30
  | 31, _ => halfChunk31
  | 32, _ => halfChunk32
  | 33, _ => halfChunk33
  | 34, _ => halfChunk34
  | 35, _ => halfChunk35
  | 36, _ => halfChunk36
  | 37, _ => halfChunk37
  | 38, _ => halfChunk38
  | 39, _ => halfChunk39
  | 40, _ => halfChunk40
  | 41, _ => halfChunk41
  | 42, _ => halfChunk42
  | 43, _ => halfChunk43
  | 44, _ => halfChunk44
  | 45, _ => halfChunk45
  | 46, _ => halfChunk46
  | 47, _ => halfChunk47
  | 48, _ => halfChunk48
  | 49, _ => halfChunk49
  | 50, _ => halfChunk50
  | 51, _ => halfChunk51
  | 52, _ => halfChunk52
  | 53, _ => halfChunk53
  | 54, _ => halfChunk54
  | 55, _ => halfChunk55
  | 56, _ => halfChunk56
  | 57, _ => halfChunk57
  | 58, _ => halfChunk58
  | 59, _ => halfChunk59
  | 60, _ => halfChunk60
  | 61, _ => halfChunk61
  | 62, _ => halfChunk62
  | 63, _ => halfChunk63
  | k + 64, h => absurd h (by omega)

/-- binary16 → binary32 → binary16 (VCVTPH2PS, then VCVTPS2PH with imm8 = 0) is the identity on every
non-SNaN binary16 value, without flags; an SNaN comes back quieted, with IE from the first conversion
(all 65,536 encodings, checked by the kernel). -/
theorem halfRoundTrip (h : Nat) (hh : h < 65536) : halfRoundTripOk h = true := by
  have hc := halfChunk_all (h / 1024) (by omega)
  simp only [halfChunkOk, List.all_eq_true, List.mem_range] at hc
  have := hc (h % 1024) (by omega)
  rwa [show 1024 * (h / 1024) + h % 1024 = h by omega] at this

end X86
