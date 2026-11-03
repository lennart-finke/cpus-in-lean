import X64.Operand
import X64.Float
namespace X64

namespace Xmm
@[inline] def lane (v : Xmm) (bits k : Nat) : UInt64 :=
  let shift := bits*k
  let word := if shift < 64 then v.lo else v.hi
  (word >>> (shift%64).toUInt64) &&& (if bits == 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< bits.toUInt64)-1)
@[inline] def setLane (v : Xmm) (bits k : Nat) (x : UInt64) : Xmm :=
  let shift := bits*k
  let mask := if bits == 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< bits.toUInt64)-1
  let s := (shift%64).toUInt64
  let update := fun word => (word &&& ~~~(mask <<< s)) ||| ((x &&& mask) <<< s)
  if shift < 64 then { v with lo := update v.lo } else { v with hi := update v.hi }
def map2 (bits : Nat) (f : UInt64 → UInt64 → UInt64) (a b : Xmm) : Xmm := Id.run do
  let mut result : Xmm := {}
  for k in [0:128/bits] do result := result.setLane bits k (f (a.lane bits k) (b.lane bits k))
  return result
end Xmm

@[inline] def getXmm (r : UInt8) : M Xmm := fun m => .ok m.cpu.xmm[r.toNat]! m
@[inline] def setXmm (r : UInt8) (v : Xmm) : M Unit := modCpu fun c => { c with xmm := c.xmm.set! r.toNat v }

def checkSse : M Unit := do
  let c ← cpu
  if c.cr0 &&& CR0.EM != 0 || c.cr4 &&& 0x200 == 0 then ud
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM

/-- Probes the entire memory operand before a multi-part store. -/
def simdAddress (i : Inst) (size : UInt64) (aligned write : Bool) : M UInt64 := do
  let addr ← segAddr i.seg (← eaOff i) size
  if aligned && addr &&& 15 != 0 then gp 0
  if write then
    let _ ← translate addr .write ((← getCpl) == 3)
    let _ ← translate ((addr + size - 1) &&& ~~~(0xFFF : UInt64)) .write ((← getCpl) == 3)
  return addr

def rdXmmE (i : Inst) (bytes : UInt64 := 16) (aligned : Bool := false) : M Xmm := do
  if !i.isMem then getXmm i.rm
  else
    let addr ← simdAddress i bytes aligned false
    let user := (← getCpl) == 3
    let lo ← linRd addr (min bytes 8) user
    let hi ← if bytes == 16 then linRd (addr+8) 8 user else pure 0
    return { lo, hi }

def wrXmmE (i : Inst) (v : Xmm) (bytes : UInt64 := 16) (aligned : Bool := false) : M Unit := do
  if !i.isMem then setXmm i.rm v
  else
    let addr ← simdAddress i bytes aligned true
    let user := (← getCpl) == 3
    linWr addr (min bytes 8) v.lo user
    if bytes == 16 then linWr (addr+8) 8 v.hi user

/-- MXCSR exception status survives an unmasked SIMD exception; destination operands
are committed only after the exception decision. -/
def fpStatus (flags : UInt64) : M Unit := do
  let c ← cpu
  let unmasked := flags &&& ~~~(c.mxcsr >>> 7) &&& 0x3F
  -- Aggregate all lanes first. An unmasked input exception (IE/DE/ZE)
  -- suppresses output exceptions (OE/UE/PE), including those in other lanes.
  -- Intel SDM vol. 1, 11.5.3, "Generating SIMD Floating-Point Exceptions".
  let flags := if unmasked &&& 7 != 0 then flags &&& 7 else flags
  modCpu fun c => { c with mxcsr := c.mxcsr ||| flags }
  if unmasked != 0 then
    if c.cr4 &&& 0x400 != 0 then exc 19 else ud

/-- Recognize SSE/SSE2 opcode families before the scalar dispatcher. -/
def simdOpcode (op : UInt64) : Bool :=
  (0x110 ≤ op && op ≤ 0x117) || (0x128 ≤ op && op ≤ 0x12F) ||
  (0x150 ≤ op && op ≤ 0x176) || op == 0x17E || op == 0x17F ||
  op == 0x1C2 || op == 0x1C4 || op == 0x1C5 || op == 0x1C6 ||
  (0x1D1 ≤ op && op ≤ 0x1FE)

/-- SSE scalar/packed floating-point instructions, with exact-integer rounding. -/
def floating (i : Inst) : M Unit := do
  let op := i.op
  let scalar := i.rep == 0xF2 || i.rep == 0xF3
  let double := i.p66 || i.rep == 0xF2
  let f := if double then FP.binary64 else FP.binary32
  let bits := if double then 64 else 32
  let bytes := if scalar then bits/8 else 16
  let a ← getXmm i.reg
  let mxcsr := (← cpu).mxcsr
  if op == 0x12A && scalar then
    let src ← rdE i (if i.rex &&& 8 != 0 then 8 else 4)
    let (v,flags) := FP.fromInt f (toSInt (if i.rex &&& 8 != 0 then 8 else 4) src) mxcsr
    fpStatus flags
    setXmm i.reg (a.setLane bits 0 v)
    return
  if (op == 0x12C || op == 0x12D) && scalar then
    let b ← rdXmmE i (bits/8).toUInt64
    let (v,flags) := FP.toInt f (b.lane bits 0) mxcsr (if i.rex &&& 8 != 0 then 64 else 32) (op == 0x12C)
    fpStatus flags
    wrG i (if i.rex &&& 8 != 0 then 8 else 4) v
    return
  if op == 0x12E || op == 0x12F then
    let b ← rdXmmE i (bits/8).toUInt64
    let (aa,da) := FP.prepare f mxcsr (a.lane bits 0)
    let (bb,db) := FP.prepare f mxcsr (b.lane bits 0)
    let unordered := FP.isNaN f aa || FP.isNaN f bb
    let invalid := if op == 0x12F then unordered else FP.isSNaN f aa || FP.isSNaN f bb
    fpStatus (if invalid then 1 else if unordered then 0 else da ||| db)
    let cmp := FP.compare f aa bb
    setFlags Flag.arith (if unordered then 0x45 else if cmp == 0 then 0x40 else if cmp < 0 then 1 else 0)
    return
  let b ← rdXmmE i bytes.toUInt64 (!scalar)
  let mut result := a
  let mut flags : UInt64 := 0
  if op == 0x15A && scalar then
    let dst := if double then FP.binary32 else FP.binary64
    let (v,fl) := FP.convert f dst (b.lane bits 0) mxcsr
    fpStatus fl
    setXmm i.reg (a.setLane (if double then 32 else 64) 0 v)
    return
  for k in [0:if scalar then 1 else 128/bits] do
    let aa := a.lane bits k
    let bb := b.lane bits k
    let (v,fl) ←
      if op == 0x158 || op == 0x159 || op == 0x15C || op == 0x15E then
        pure (FP.binary f (if op == 0x158 then .add else if op == 0x159 then .mul else if op == 0x15C then .sub else .div) aa bb mxcsr)
      else if op == 0x151 then pure (FP.sqrt f bb mxcsr)
      else if op == 0x15D || op == 0x15F then
        let (aa,da) := FP.prepare f mxcsr aa
        let (bb,db) := FP.prepare f mxcsr bb
        let nan := FP.isNaN f aa || FP.isNaN f bb
        let cmp := FP.compare f aa bb
        pure (if !nan && (if op == 0x15D then cmp < 0 else cmp > 0) then aa else bb,
          if nan then 1 else da ||| db)
      else if op == 0x1C2 then
        let (aa,da) := FP.prepare f mxcsr aa
        let (bb,db) := FP.prepare f mxcsr bb
        let unord := FP.isNaN f aa || FP.isNaN f bb
        let pred := i.imm &&& 7
        let cmp := FP.compare f aa bb
        let yes := match pred with
          | 0 => !unord && cmp == 0 | 1 => !unord && cmp < 0 | 2 => !unord && cmp ≤ 0 | 3 => unord
          | 4 => unord || cmp != 0 | 5 => unord || cmp ≥ 0 | 6 => unord || cmp > 0 | _ => !unord
        let signaling := pred == 1 || pred == 2 || pred == 5 || pred == 6
        pure (if yes then 0xFFFFFFFFFFFFFFFF else 0,
          if (signaling && unord) || FP.isSNaN f aa || FP.isSNaN f bb then 1 else if unord then 0 else da ||| db)
      else unsupported s!"SSE floating opcode {op}"
    result := result.setLane bits k v
    flags := flags ||| fl
  fpStatus flags
  setXmm i.reg result

/-- SSE/SSE2 moves and packed integer operations. -/
def simd (i : Inst) : M Unit := do
  checkSse
  let op := i.op
  let a ← getXmm i.reg
  if ((0x160 ≤ op && op ≤ 0x16D) || (0x174 ≤ op && op ≤ 0x176) ||
      (0x1D1 ≤ op && op ≤ 0x1FE)) && !i.p66 then
    unsupported "MMX or later SIMD extension"
  if op == 0x110 || op == 0x111 || op == 0x128 || op == 0x129 || op == 0x16F || op == 0x17F then
    let scalar := (op == 0x110 || op == 0x111) && i.rep != 0
    let bytes : UInt64 := if scalar then (if i.rep == 0xF2 then 8 else 4) else 16
    let aligned := op == 0x128 || op == 0x129 || ((op == 0x16F || op == 0x17F) && i.p66)
    if (op == 0x16F || op == 0x17F) && !i.p66 && i.rep != 0xF3 then unsupported "MMX MOVQ"
    if op == 0x110 || op == 0x128 || op == 0x16F then
      let b ← rdXmmE i bytes aligned
      let v := if scalar && !i.isMem then a.setLane (bytes.toNat*8) 0 b.lo else b
      setXmm i.reg v
    else
      let old ← getXmm i.rm
      let v := if scalar && !i.isMem then old.setLane (bytes.toNat*8) 0 a.lo else a
      wrXmmE i v bytes aligned
    return
  if op == 0x16E || op == 0x17E || op == 0x1D6 then
    if op == 0x17E && i.rep == 0xF3 then
      let b ← rdXmmE i 8
      setXmm i.reg { lo := b.lo }
    else if op == 0x1D6 && i.p66 then wrXmmE i { lo := a.lo } 8
    else if i.p66 then
      let sz : Sz := if i.rex &&& 8 != 0 then 8 else 4
      if op == 0x16E then setXmm i.reg { lo := (← rdE i sz) }
      else wrE i sz a.lo
    else unsupported "MMX conversion"
    return
  if op == 0x150 || op == 0x1D7 then
    if i.isMem then ud
    let b ← getXmm i.rm
    let bits := if op == 0x1D7 then 8 else if i.p66 then 64 else 32
    let mut mask := 0
    for k in [0:128/bits] do
      mask := mask ||| (((b.lane bits k >>> (bits-1).toUInt64) &&& 1) <<< k.toUInt64)
    wrG i 4 mask
    return
  if op == 0x1C4 && i.p66 then
    let v ← rdE i 2
    setXmm i.reg (a.setLane 16 (i.imm &&& 7).toNat v)
    return
  if op == 0x1C5 && i.p66 then
    if i.isMem then ud
    let b ← getXmm i.rm
    wrG i 4 (b.lane 16 (i.imm &&& 7).toNat)
    return
  if op == 0x171 || op == 0x172 || op == 0x173 then
    if !i.p66 then unsupported "MMX shift"
    if i.isMem then ud
    let b ← getXmm i.rm
    let bits := if op == 0x171 then 16 else if op == 0x172 then 32 else 64
    let count := i.imm
    let mut r : Xmm := {}
    if op == 0x173 && (i.group == 3 || i.group == 7) then
      for k in [0:16] do
        let ix := if i.group == 3 then k + count.toNat else k - count.toNat
        if (i.group == 3 && ix < 16) || (i.group == 7 && k ≥ count.toNat) then
          r := r.setLane 8 k (b.lane 8 ix)
    else
      if i.group != 2 && i.group != 4 && i.group != 6 then ud
      if i.group == 4 && bits == 64 then ud
      for k in [0:128/bits] do
        let v := b.lane bits k
        let shifted := if i.group == 4 then
          let sv := toSInt (bits/8).toUInt8 v
          ((sv / (2^(min count.toNat (bits-1)) : Nat)) % (2^64 : Int)).toNat.toUInt64
          else if count ≥ bits.toUInt64 then 0 else if i.group == 2 then v >>> count else v <<< count
        r := r.setLane bits k shifted
    setXmm i.rm r
    return
  if op == 0x112 || op == 0x113 || op == 0x116 || op == 0x117 then
    if i.rep != 0 then unsupported "SSE3 duplicate instruction"
    if op == 0x113 || op == 0x117 then
      needMem i
      wrXmmE i { lo := if op == 0x117 then a.hi else a.lo } 8
    else
      let b ← rdXmmE i 8
      if op == 0x112 then
        setXmm i.reg { a with lo := if i.isMem then b.lo else b.hi }
      else setXmm i.reg { a with hi := b.lo }
    return
  if op == 0x12B || op == 0x1E7 then
    needMem i
    wrXmmE i a 16 true
    return
  if (op ≥ 0x12A && op ≤ 0x12F) ||
     (op ≥ 0x158 && op ≤ 0x15F) || op == 0x151 || op == 0x1C2 then
    floating i
    return
  let b ← rdXmmE i 16 true
  let mut r : Xmm := {}
  if op == 0x154 || op == 0x1DB then r := { lo := a.lo &&& b.lo, hi := a.hi &&& b.hi }
  else if op == 0x155 || op == 0x1DF then r := { lo := ~~~a.lo &&& b.lo, hi := ~~~a.hi &&& b.hi }
  else if op == 0x156 || op == 0x1EB then r := { lo := a.lo ||| b.lo, hi := a.hi ||| b.hi }
  else if op == 0x157 || op == 0x1EF then r := { lo := a.lo ^^^ b.lo, hi := a.hi ^^^ b.hi }
  else if op == 0x170 then
    if i.p66 then
      for k in [0:4] do r := r.setLane 32 k (b.lane 32 ((i.imm >>> (2*k).toUInt64) &&& 3).toNat)
    else if i.rep == 0xF2 || i.rep == 0xF3 then
      r := b
      let start := if i.rep == 0xF3 then 4 else 0
      for k in [0:4] do r := r.setLane 16 (start+k) (b.lane 16 (start+((i.imm >>> (2*k).toUInt64) &&& 3).toNat))
    else unsupported "MMX shuffle"
  else if op == 0x1C6 then
    let bits := if i.p66 then 64 else 32
    let n := 128/bits
    for k in [0:n] do
      let src := if k < n/2 then a else b
      let ix := if bits == 64 then ((i.imm >>> k.toUInt64) &&& 1).toNat else ((i.imm >>> (2*k).toUInt64) &&& 3).toNat
      r := r.setLane bits k (src.lane bits ix)
  else if op == 0x114 || op == 0x115 || (op ≥ 0x160 && op ≤ 0x162) ||
          (op ≥ 0x168 && op ≤ 0x16A) || op == 0x16C || op == 0x16D then
    let bits := if op == 0x114 || op == 0x115 then (if i.p66 then 64 else 32)
                else if op == 0x16C || op == 0x16D then 64 else 8 * 2^((op &&& 3).toNat)
    let high := op == 0x115 || (op ≥ 0x168 && op ≤ 0x16A) || op == 0x16D
    let start := if high then 64/bits else 0
    for k in [0:64/bits] do
      r := r.setLane bits (2*k) (a.lane bits (start+k))
      r := r.setLane bits (2*k+1) (b.lane bits (start+k))
  else if op ≥ 0x1F8 && op ≤ 0x1FE || op == 0x1D4 then
    let bits := if op == 0x1D4 || op == 0x1FB then 64 else 8 * 2^((op &&& 3).toNat)
    r := Xmm.map2 bits (if op < 0x1FC && op != 0x1D4 then (· - ·) else (· + ·)) a b
  else if (op ≥ 0x174 && op ≤ 0x176) || (op ≥ 0x164 && op ≤ 0x166) then
    let bits := 8 * 2^((op &&& 3).toNat)
    r := Xmm.map2 bits (fun x y => if (if op ≥ 0x174 then x == y else toSInt (bits/8).toUInt8 x > toSInt (bits/8).toUInt8 y)
      then 0xFFFFFFFFFFFFFFFF else 0) a b
  else if op == 0x1D5 then r := Xmm.map2 16 (· * ·) a b
  else if op == 0x1DA || op == 0x1DE then r := Xmm.map2 8 (if op == 0x1DA then min else max) a b
  else if op == 0x1EA || op == 0x1EE then
    r := Xmm.map2 16 (fun x y => if (toSInt 2 x < toSInt 2 y) == (op == 0x1EA) then x else y) a b
  else unsupported s!"SSE integer opcode {op}, prefix66 {i.p66}, REP {i.rep}"
  setXmm i.reg r

end X64
