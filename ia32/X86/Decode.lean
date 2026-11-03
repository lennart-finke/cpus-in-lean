import X86.Machine
/-!
# Instruction decoder

Decodes prefixes, the one- and two-byte (0F) opcode maps, ModRM/SIB, displacement and
immediates into an `Inst`. The memory operand is kept symbolic (base, index, scale, disp)
and its effective address is computed at execution time.
-/
namespace X86

structure Inst where
  /-- 0x000..0x0FF one-byte opcodes, 0x100..0x1FF two-byte (0F xx) opcodes. -/
  op : UInt32 := 0
  len : UInt32 := 0
  /-- Operand size (2 or 4). -/
  opsz : Sz := 4
  /-- Address size (2 or 4). -/
  adsz : Sz := 4
  /-- Segment override prefix, or 0xFF. -/
  segOvr : UInt8 := 0xFF
  /-- Segment of the ModRM memory operand (override or default). -/
  seg : UInt8 := SegN.DS
  /-- 0, 0xF2 (REPNE) or 0xF3 (REP/REPE). -/
  rep : UInt8 := 0
  lock : Bool := false
  modrm : UInt8 := 0
  isMem : Bool := false
  /-- Base register, 8 = none. -/
  base : UInt8 := 8
  /-- Index register, 8 = none. -/
  index : UInt8 := 8
  scale : UInt8 := 0
  disp : UInt32 := 0
  imm : UInt32 := 0
  imm2 : UInt32 := 0
  deriving Repr, Inhabited

namespace Inst
@[inline] def reg (i : Inst) : UInt8 := (i.modrm >>> 3) &&& 7
@[inline] def rm (i : Inst) : UInt8 := i.modrm &&& 7
@[inline] def mod (i : Inst) : UInt8 := i.modrm >>> 6
end Inst

-- Immediate kinds.
namespace Imm
def none  : UInt8 := 0
def ib    : UInt8 := 1
def iw    : UInt8 := 2
def iz    : UInt8 := 3
def moffs : UInt8 := 4
def ptr   : UInt8 := 5
def enter : UInt8 := 6
def grp3b : UInt8 := 7
def grp3v : UInt8 := 8
end Imm

/-- Opcode properties: `(immediate kind <<< 4) ||| hasModRM`. -/
def opInfo (op : UInt32) : UInt8 :=
  if op < 0x100 then
    let b := op
    if b < 0x40 then
      let lo := b &&& 7
      if lo < 4 then 0x01 else if lo == 4 then 0x10 else if lo == 5 then 0x30 else 0
    else if b < 0x60 then 0
    else if 0x70 ≤ b && b ≤ 0x7F then 0x10
    else if 0x84 ≤ b && b ≤ 0x8F then 0x01
    else if 0xB0 ≤ b && b ≤ 0xB7 then 0x10
    else if 0xB8 ≤ b && b ≤ 0xBF then 0x30
    else if 0xD0 ≤ b && b ≤ 0xD3 then 0x01
    else if 0xD8 ≤ b && b ≤ 0xDF then 0x01
    else if 0xE0 ≤ b && b ≤ 0xE7 then 0x10
    else match b with
      | 0x62 | 0x63 => 0x01
      | 0x68 => 0x30 | 0x69 => 0x31 | 0x6A => 0x10 | 0x6B => 0x11
      | 0x80 | 0x82 | 0x83 => 0x11 | 0x81 => 0x31
      | 0x9A | 0xEA => 0x50
      | 0xA0 | 0xA1 | 0xA2 | 0xA3 => 0x40
      | 0xA8 => 0x10 | 0xA9 => 0x30
      | 0xC0 | 0xC1 | 0xC6 => 0x11 | 0xC7 => 0x31
      | 0xC2 | 0xCA => 0x20
      | 0xC4 | 0xC5 => 0x01
      | 0xC8 => 0x60
      | 0xCD | 0xD4 | 0xD5 | 0xEB => 0x10
      | 0xE8 | 0xE9 => 0x30
      | 0xF6 => 0x71 | 0xF7 => 0x81
      | 0xFE | 0xFF => 0x01
      | _ => 0
  else
    let b := op - 0x100
    if b ≤ 0x03 || b == 0x0D || (0x18 ≤ b && b ≤ 0x1F) || (0x20 ≤ b && b ≤ 0x23) ||
       (0x40 ≤ b && b ≤ 0x4F) || (0x90 ≤ b && b ≤ 0x9F) then 0x01
    else if 0x80 ≤ b && b ≤ 0x8F then 0x30
    else match b with
      | 0xA3 | 0xA5 | 0xAB | 0xAD | 0xAE | 0xAF => 0x01
      | 0xA4 | 0xAC | 0xBA => 0x11
      | 0xB0 | 0xB1 | 0xB2 | 0xB3 | 0xB4 | 0xB5 | 0xB6 | 0xB7 => 0x01
      | 0xB9 | 0xBB | 0xBC | 0xBD | 0xBE | 0xBF => 0x01
      | 0xC0 | 0xC1 | 0xC7 | 0xFF => 0x01
      | _ => 0

/-- Decode the instruction at CS:EIP; returns the instruction and its length. -/
def decodeRaw : M (Inst × UInt32) := do
  let c ← cpu
  let eip0 := c.eip
  let d32 := c.cs.big
  let mut n : UInt32 := 0
  let mut opsz : Sz := if d32 then 4 else 2
  let mut adsz : Sz := if d32 then 4 else 2
  let mut segOvr : UInt8 := 0xFF
  let mut rep : UInt8 := 0
  let mut lock := false
  let mut b ← fetch8 eip0
  -- prefixes
  for _ in [0:15] do
    match b with
    | 0x26 => segOvr := SegN.ES
    | 0x2E => segOvr := SegN.CS
    | 0x36 => segOvr := SegN.SS
    | 0x3E => segOvr := SegN.DS
    | 0x64 => segOvr := SegN.FS
    | 0x65 => segOvr := SegN.GS
    | 0x66 => opsz := if d32 then 2 else 4
    | 0x67 => adsz := if d32 then 2 else 4
    | 0xF0 => lock := true
    | 0xF2 => rep := 0xF2
    | 0xF3 => rep := 0xF3
    | _ => break
    n := n + 1
    if n ≥ 15 then gp 0
    b ← fetch8 (eip0 + n)
  let mut op := b
  n := n + 1
  if b == 0x0F then
    op := 0x100 + (← fetch8 (eip0 + n))
    n := n + 1
  let info := opInfo op
  let mut i : Inst := { op, opsz, adsz, segOvr, rep, lock }
  if info &&& 1 != 0 then
    let modrm := (← fetch8 (eip0 + n)).toUInt8
    n := n + 1
    let md := modrm >>> 6
    let rm := modrm &&& 7
    i := { i with modrm }
    -- MOV to/from control/debug registers always uses the register form
    if md != 3 && !(op ≥ 0x120 && op ≤ 0x123) then
      let mut base : UInt8 := 8
      let mut index : UInt8 := 8
      let mut scale : UInt8 := 0
      let mut disp : UInt32 := 0
      let mut ss := false
      if adsz == 4 then
        if rm == 4 then
          let sib := (← fetch8 (eip0 + n)).toUInt8
          n := n + 1
          scale := sib >>> 6
          let ix := (sib >>> 3) &&& 7
          if ix != 4 then index := ix
          let bs := sib &&& 7
          if bs == 5 && md == 0 then
            disp := (← fetch8 (eip0+n)) ||| ((← fetch8 (eip0+n+1)) <<< 8) |||
                    ((← fetch8 (eip0+n+2)) <<< 16) ||| ((← fetch8 (eip0+n+3)) <<< 24)
            n := n + 4
          else
            base := bs
            ss := bs == 4 || bs == 5
        else if rm == 5 && md == 0 then
          disp := (← fetch8 (eip0+n)) ||| ((← fetch8 (eip0+n+1)) <<< 8) |||
                  ((← fetch8 (eip0+n+2)) <<< 16) ||| ((← fetch8 (eip0+n+3)) <<< 24)
          n := n + 4
        else
          base := rm
          ss := rm == 5
        if md == 1 then
          disp := sext 1 (← fetch8 (eip0 + n))
          n := n + 1
        else if md == 2 then
          disp := (← fetch8 (eip0+n)) ||| ((← fetch8 (eip0+n+1)) <<< 8) |||
                  ((← fetch8 (eip0+n+2)) <<< 16) ||| ((← fetch8 (eip0+n+3)) <<< 24)
          n := n + 4
      else
        match rm with
        | 0 => base := 3; index := 6
        | 1 => base := 3; index := 7
        | 2 => base := 5; index := 6; ss := true
        | 3 => base := 5; index := 7; ss := true
        | 4 => base := 6
        | 5 => base := 7
        | 6 => if md != 0 then base := 5; ss := true
        | _ => base := 3
        if md == 0 && rm == 6 then
          disp := (← fetch8 (eip0+n)) ||| ((← fetch8 (eip0+n+1)) <<< 8)
          n := n + 2
        else if md == 1 then
          disp := sext 1 (← fetch8 (eip0 + n))
          n := n + 1
        else if md == 2 then
          disp := (← fetch8 (eip0+n)) ||| ((← fetch8 (eip0+n+1)) <<< 8)
          n := n + 2
      let seg := if segOvr != 0xFF then segOvr else if ss then SegN.SS else SegN.DS
      i := { i with isMem := true, base, index, scale, disp, seg }
  -- immediates
  let kind := info >>> 4
  let rd (p k : UInt32) : M UInt32 := do
    if k == 1 then fetch8 p
    else if k == 2 then return (← fetch8 p) ||| ((← fetch8 (p+1)) <<< 8)
    else return (← fetch8 p) ||| ((← fetch8 (p+1)) <<< 8) |||
                ((← fetch8 (p+2)) <<< 16) ||| ((← fetch8 (p+3)) <<< 24)
  if kind != 0 then
    let k : UInt32 :=
      if kind == Imm.ib then 1 else if kind == Imm.iw then 2
      else if kind == Imm.iz then opsz.toUInt32
      else if kind == Imm.moffs then adsz.toUInt32
      else if kind == Imm.ptr then opsz.toUInt32
      else if kind == Imm.enter then 2
      else if kind == Imm.grp3b then (if i.reg < 2 then 1 else 0)
      else if kind == Imm.grp3v then (if i.reg < 2 then opsz.toUInt32 else 0)
      else 0
    if k != 0 then
      let v ← rd (eip0 + n) k
      n := n + k
      i := { i with imm := v }
    if kind == Imm.ptr then
      let v ← rd (eip0 + n) 2
      n := n + 2
      i := { i with imm2 := v }
    else if kind == Imm.enter then
      let v ← rd (eip0 + n) 1
      n := n + 1
      i := { i with imm2 := v }
  return (i, n)

/-- Decode the instruction at CS:EIP. Instructions longer than 15 bytes raise #GP(0). -/
def decode : M Inst := do
  let (i, n) ← decodeRaw
  if n > 15 then gp 0
  return { i with len := n }

end X86
