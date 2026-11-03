import X64.Simd
namespace X64

/-- x87 availability and deferred exception checks, separated for FN forms. -/
def checkFpu (waiting : Bool := true) : M Unit := do
  let c ← cpu
  if c.cr0 &&& (CR0.EM ||| CR0.TS) != 0 then exc Vec.NM
  if waiting && c.fpStatus &&& 0x80 != 0 then exc 16

def fninit : M Unit := modCpu fun c => { c with
  fpControl := 0x37F, fpStatus := 0, fpTag := 0xFFFF,
  fpOpcode := 0, fpIp := 0, fpDp := 0 }

/-- Convert the full x87 physical-register tag word to FXSAVE's presence bitmap. -/
def fxTag (c : Cpu) : UInt64 := Id.run do
  let mut bits : UInt64 := 0
  for k in [0:8] do
    if (c.fpTag.toUInt64 >>> (k*2).toUInt64) &&& 3 != 3 then bits := bits ||| (1 <<< k.toUInt64)
  return bits

/-- Recover a full x87 tag from the register's 80-bit encoding. -/
def Float80.tag (v : Float80) : UInt64 :=
  let e := v.signExp &&& 0x7FFF
  if e == 0 && v.significand == 0 then 1
  else if e == 0 || e == 0x7FFF || v.significand >>> 63 == 0 then 2 else 0

/-- FXSAVE/FXRSTOR, MXCSR loads/stores, and ordered fences. The machine executes
instructions sequentially and has no write buffer, so fences need no state update. -/
def fxInstruction (i : Inst) : M Unit := do
  if !i.isMem then
    if i.modrm == 0xE8 || i.modrm == 0xF0 || i.modrm == 0xF8 then return
    ud
  if i.group == 2 || i.group == 3 then
    checkSse
    if i.group == 2 then
      let v ← rdE i 4
      if v &&& ~~~(0xFFFF : UInt64) != 0 then gp 0
      modCpu fun c => { c with mxcsr := v }
    else wrE i 4 (← cpu).mxcsr
    return
  if i.group != 0 && i.group != 1 then unsupported "XSAVE/CLFLUSH family not implemented"
  let c ← cpu
  -- CR0.EM does not inhibit FXSAVE/FXRSTOR; CR0.TS still does.
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM
  let addr ← simdAddress i 512 true (i.group == 0)
  let user := c.cpl == 3
  let wide := i.rex &&& 8 != 0
  if i.group == 0 then
    linWr addr 2 c.fpControl.toUInt64 user
    linWr (addr+2) 2 c.fpStatus.toUInt64 user
    linWr (addr+4) 1 (fxTag c) user
    linWr (addr+6) 2 c.fpOpcode.toUInt64 user
    linWr (addr+8) (if wide then 8 else 4) c.fpIp user
    linWr (addr+16) (if wide then 8 else 4) c.fpDp user
    if !wide then
      linWr (addr+12) 4 0 user
      linWr (addr+20) 4 0 user
    if c.cr4 &&& 0x200 != 0 then
      linWr (addr+24) 4 c.mxcsr user
      linWr (addr+28) 4 0xFFFF user
    let top := ((c.fpStatus.toUInt64 >>> 11) &&& 7).toNat
    for k in [0:8] do
      let v := c.fp[(top+k)%8]!
      linWr (addr+32+k.toUInt64*16) 8 v.significand user
      linWr (addr+40+k.toUInt64*16) 2 v.signExp.toUInt64 user
    if c.cr4 &&& 0x200 != 0 then
      for k in [0:16] do
        linWr (addr+160+k.toUInt64*16) 8 c.xmm[k]!.lo user
        linWr (addr+168+k.toUInt64*16) 8 c.xmm[k]!.hi user
  else
    let control ← linRd addr 2 user
    let status ← linRd (addr+2) 2 user
    let present ← linRd (addr+4) 1 user
    let opcode ← linRd (addr+6) 2 user
    let ip ← linRd (addr+8) (if wide then 8 else 4) user
    let dp ← linRd (addr+16) (if wide then 8 else 4) user
    let mxcsr ← if c.cr4 &&& 0x200 != 0 then linRd (addr+24) 4 user else pure c.mxcsr
    if mxcsr &&& ~~~(0xFFFF : UInt64) != 0 then gp 0
    let top := ((status >>> 11) &&& 7).toNat
    let mut fp := c.fp
    let mut tag : UInt64 := 0
    for k in [0:8] do
      let sig ← linRd (addr+32+k.toUInt64*16) 8 user
      let se ← linRd (addr+40+k.toUInt64*16) 2 user
      let v : Float80 := ⟨sig, se.toUInt16⟩
      let physical := (top+k)%8
      fp := fp.set! physical v
      let t := if present &&& (1 <<< physical.toUInt64) == 0 then 3 else v.tag
      tag := tag ||| (t <<< (physical*2).toUInt64)
    let mut xmm := c.xmm
    if c.cr4 &&& 0x200 != 0 then
      for k in [0:16] do
        let lo ← linRd (addr+160+k.toUInt64*16) 8 user
        let hi ← linRd (addr+168+k.toUInt64*16) 8 user
        xmm := xmm.set! k { lo, hi }
    modCpu fun c => { c with
      fpControl := control.toUInt16, fpStatus := status.toUInt16,
      fpTag := tag.toUInt16, fpOpcode := (opcode &&& 0x7FF).toUInt16, fpIp := ip, fpDp := dp,
      mxcsr, fp, xmm }

/-- Exact integer conversion to the explicit-integer-bit extended format. -/
def Float80.ofInt (n : Int) : Float80 :=
  if n == 0 then {} else
  let k := n.natAbs.log2
  { significand := (n.natAbs * 2^(63-k)).toUInt64,
    signExp := (k + 16383 + if n < 0 then 0x8000 else 0).toUInt16 }

/-- Push an extended value, including the masked/unmasked x87 stack-overflow cases. -/
def fpPush (v : Float80) : M Unit := do
  let c ← cpu
  let top := (((c.fpStatus.toUInt64 >>> 11) - 1) &&& 7).toNat
  let overflow := (c.fpTag.toUInt64 >>> (2*top).toUInt64) &&& 3 != 3
  if overflow && c.fpControl &&& 1 == 0 then
    modCpu fun c => { c with fpStatus := c.fpStatus ||| 0x82C1 }
  else
    let v := if overflow then { significand := 0xC000000000000000, signExp := 0xFFFF } else v
    let status := (c.fpStatus.toUInt64 &&& ~~~(0x3A00 : UInt64)) ||| (top.toUInt64 <<< 11) |||
      (if overflow then 0x241 else 0)
    let tag := (c.fpTag.toUInt64 &&& ~~~(3 <<< (2*top).toUInt64)) ||| (v.tag <<< (2*top).toUInt64)
    modCpu fun c => { c with fp := c.fp.set! top v, fpTag := tag.toUInt16, fpStatus := status.toUInt16 }

def x87Control (i : Inst) : M Unit := do
  let nonwaiting := (i.op == 0xDB && (i.modrm == 0xE2 || i.modrm == 0xE3)) ||
    (i.op == 0xDF && i.modrm == 0xE0) ||
    (i.isMem && ((i.op == 0xD9 && i.group == 7) || (i.op == 0xDD && i.group == 7)))
  checkFpu (!nonwaiting)
  if i.isMem && ((i.op == 0xDB && i.group == 0) || (i.op == 0xDF && (i.group == 0 || i.group == 5))) then
    let sz : Sz := if i.op == 0xDB then 4 else if i.group == 0 then 2 else 8
    let addr ← segAddr i.seg (← eaOff i) sz.toUInt64
    let v ← linRd addr sz.toUInt64 ((← getCpl) == 3)
    modCpu fun c => { c with
      fpIp := c.rip-i.len, fpDp := addr,
      fpOpcode := (((i.op &&& 7) <<< 8) ||| i.modrm.toUInt64).toUInt16 }
    fpPush (Float80.ofInt (toSInt sz v))
  else if i.op == 0xDB && i.modrm == 0xE3 then fninit
  else if i.op == 0xDB && i.modrm == 0xE2 then
    modCpu fun c => { c with fpStatus := c.fpStatus &&& 0x7F00 }
  else if i.op == 0xD9 && i.modrm == 0xD0 then pure () -- FNOP
  else if i.op == 0xDF && i.modrm == 0xE0 then wrReg 2 0 (← cpu).fpStatus.toUInt64
  else if i.isMem && i.op == 0xD9 && i.group == 5 then
    let v ← rdE i 2
    let c ← cpu
    let status := c.fpStatus &&& 0x7F7F
    let pending := status &&& ~~~v.toUInt16 &&& 0x3F != 0
    modCpu fun c => { c with
      fpControl := (v.toUInt16 &&& 0x1F3F) ||| 0x40,
      fpStatus := status ||| if pending then 0x8080 else 0 }
  else if i.isMem && i.group == 7 && (i.op == 0xD9 || i.op == 0xDD) then
    let c ← cpu
    wrE i 2 (if i.op == 0xD9 then c.fpControl.toUInt64 else c.fpStatus.toUInt64)
  else unsupported s!"x87 opcode {i.op}, ModRM {i.modrm}"

end X64
