import X64.Machine
namespace X64

structure Inst where
  op : UInt64 := 0
  len : UInt64 := 0
  opsz : Sz := 4
  p66 : Bool := false
  adsz : Sz := 8
  segOvr : UInt8 := 0xFF
  seg : UInt8 := SegN.DS
  rep : UInt8 := 0
  lock : Bool := false
  rex : UInt8 := 0
  modrm : UInt8 := 0
  isMem : Bool := false
  base : UInt8 := 16
  index : UInt8 := 16
  scale : UInt8 := 0
  ripRelative : Bool := false
  disp : UInt64 := 0
  imm : UInt64 := 0
  imm2 : UInt64 := 0
  deriving Repr, Inhabited

namespace Inst
@[inline] def group (i : Inst) : UInt8 := (i.modrm >>> 3) &&& 7
@[inline] def reg (i : Inst) : UInt8 := i.group ||| ((i.rex &&& 4) <<< 1)
@[inline] def rm (i : Inst) : UInt8 := (i.modrm &&& 7) ||| ((i.rex &&& 1) <<< 3)
@[inline] def opcodeReg (i : Inst) : UInt8 := (i.op &&& 7).toUInt8 ||| ((i.rex &&& 1) <<< 3)
@[inline] def stackSize (i : Inst) : Sz := if i.opsz == 2 then 2 else 8
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
def opInfo (op : UInt64) : UInt8 :=
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
    if b == 0x70 || b == 0x71 || b == 0x72 || b == 0x73 || b == 0xC2 || b == 0xC4 || b == 0xC5 || b == 0xC6 then 0x11
    else if (0x10 ≤ b && b ≤ 0x17) || (0x28 ≤ b && b ≤ 0x2F) ||
       (0x50 ≤ b && b ≤ 0x6F) || (0x74 ≤ b && b ≤ 0x76) || b == 0x7E || b == 0x7F ||
       (0xD1 ≤ b && b ≤ 0xFE) then 0x01
    else if b ≤ 0x03 || b == 0x0D || (0x18 ≤ b && b ≤ 0x1F) || (0x20 ≤ b && b ≤ 0x23) ||
       (0x40 ≤ b && b ≤ 0x4F) || (0x90 ≤ b && b ≤ 0x9F) then 0x01
    else if 0x80 ≤ b && b ≤ 0x8F then 0x30
    else match b with
      | 0xA3 | 0xA5 | 0xAB | 0xAD | 0xAE | 0xAF => 0x01
      | 0xA4 | 0xAC | 0xBA => 0x11
      | 0xB0 | 0xB1 | 0xB2 | 0xB3 | 0xB4 | 0xB5 | 0xB6 | 0xB7 => 0x01
      | 0xB9 | 0xBB | 0xBC | 0xBD | 0xBE | 0xBF => 0x01
      | 0xC0 | 0xC1 | 0xC7 | 0xFF => 0x01
      | _ => 0


/-- Fetch with an explicit length bound, including immediate/displacement bytes. -/
def codeByte (start offset : UInt64) : M UInt64 := do
  if offset ≥ 15 then gp 0
  fetch8 (start + offset)

def codeWord (start offset n : UInt64) : M UInt64 := do
  let mut v := 0
  for k in [0:n.toNat] do
    v := v ||| ((← codeByte start (offset + k.toUInt64)) <<< (k.toUInt64 * 8))
  return v

/-- Decode in 64-bit mode: last adjacent REX wins, legacy prefixes invalidate prior
REX, and address-size override selects 32-bit addressing. -/
def decodeRaw : M Inst := do
  let start := (← cpu).rip
  let mut n : UInt64 := 0
  let mut i : Inst := {}
  let mut operand16 := false
  let mut b ← codeByte start n
  for _ in [0:15] do
    if b ≥ 0x40 && b ≤ 0x4F then i := { i with rex := b.toUInt8 }
    else
      match b with
      | 0x26 => i := { i with segOvr := SegN.ES, rex := 0 }
      | 0x2E => i := { i with segOvr := SegN.CS, rex := 0 }
      | 0x36 => i := { i with segOvr := SegN.SS, rex := 0 }
      | 0x3E => i := { i with segOvr := SegN.DS, rex := 0 }
      | 0x64 => i := { i with segOvr := SegN.FS, rex := 0 }
      | 0x65 => i := { i with segOvr := SegN.GS, rex := 0 }
      | 0x66 => operand16 := true; i := { i with rex := 0 }
      | 0x67 => i := { i with adsz := 4, rex := 0 }
      | 0xF0 => i := { i with lock := true, rex := 0 }
      | 0xF2 | 0xF3 => i := { i with rep := b.toUInt8, rex := 0 }
      | _ => break
    n := n + 1
    b ← codeByte start n
  i := { i with p66 := operand16, opsz := if i.rex &&& 8 != 0 then 8 else if operand16 then 2 else 4 }
  let mut op := b
  n := n + 1
  if b == 0x0F then
    op := 0x100 + (← codeByte start n)
    n := n + 1
  i := { i with op }
  let info := opInfo op
  if info &&& 1 != 0 then
    let modrm := (← codeByte start n).toUInt8
    n := n + 1
    i := { i with modrm }
    let md := modrm >>> 6
    let rm := modrm &&& 7
    if md != 3 && !(op ≥ 0x120 && op ≤ 0x123) then
      let mut base : UInt8 := 16
      let mut index : UInt8 := 16
      let mut scale : UInt8 := 0
      let mut dispBytes : UInt64 := 0
      let mut ripRelative := false
      if rm == 4 then
        let sib := (← codeByte start n).toUInt8
        n := n + 1
        scale := sib >>> 6
        let ix := (sib >>> 3) &&& 7
        if ix != 4 || i.rex &&& 2 != 0 then index := ix ||| ((i.rex &&& 2) <<< 2)
        let bs := sib &&& 7
        if bs == 5 && md == 0 then dispBytes := 4
        else base := bs ||| ((i.rex &&& 1) <<< 3)
      else if rm == 5 && md == 0 then
        ripRelative := true
        dispBytes := 4
      else base := i.rm
      if md == 1 then dispBytes := 1
      if md == 2 then dispBytes := 4
      let mut disp := 0
      if dispBytes != 0 then
        disp := sext dispBytes.toUInt8 (← codeWord start n dispBytes)
        n := n + dispBytes
      let seg := if i.segOvr != 0xFF then i.segOvr
                 else if base < 16 && (base &&& 7 == 4 || base &&& 7 == 5) then SegN.SS else SegN.DS
      i := { i with isMem := true, base, index, scale, disp, ripRelative, seg }
  let kind := info >>> 4
  let z : UInt64 := if i.opsz == 2 then 2 else 4
  let k : UInt64 :=
    if op ≥ 0xB8 && op ≤ 0xBF then i.opsz.toUInt64
    else if op == 0xE8 || op == 0xE9 || (op ≥ 0x180 && op ≤ 0x18F) then 4
    else if kind == Imm.ib then 1 else if kind == Imm.iw then 2
    else if kind == Imm.iz then z else if kind == Imm.moffs then i.adsz.toUInt64
    else if kind == Imm.enter then 2
    else if kind == Imm.grp3b && i.group < 2 then 1
    else if kind == Imm.grp3v && i.group < 2 then z else 0
  if k > 0 then
    let v ← codeWord start n k
    n := n + k
    let sign := k == 4 && (i.opsz == 8 || op == 0x68 || op == 0xE8 || op == 0xE9 || (op ≥ 0x180 && op ≤ 0x18F))
    i := { i with imm := if sign then sext 4 v else v }
  if kind == Imm.enter then
    i := { i with imm2 := (← codeByte start n) }
    n := n + 1
  return { i with len := n }

/-- Architectural maximum instruction length, enforced at the public decoder boundary. -/
def decode : M Inst := do
  let i ← decodeRaw
  if i.len > 15 then gp 0
  return i

end X64
