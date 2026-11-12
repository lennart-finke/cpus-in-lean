import X86.Machine
/-!
# Instruction decoder

Decodes prefixes, the opcode maps, ModRM/SIB, displacement and immediates into an `Inst`. The memory
operand is kept symbolic (base, index, scale, disp) and its effective address is computed at
execution time.

## Opcode numbering

`Inst.op = map * 0x100 + opcode byte`:

| `op`          | map | encoding                                   |
|---------------|-----|--------------------------------------------|
| 0x000..0x0FF  | 0   | one-byte opcodes                           |
| 0x100..0x1FF  | 1   | 0F xx                                      |
| 0x200..0x2FF  | 2   | 0F 38 xx (always ModRM)                    |
| 0x300..0x3FF  | 3   | 0F 3A xx (always ModRM and imm8)           |

VEX-encoded instructions use the same numbering for their map (VEX.mmmmm = 1, 2, 3) with
`Inst.vex = true`; a VEX prefix with any other map gives `op < 0x100` and #UD at execution.

## VEX (Intel SDM vol. 2A, 2.3; AMD APM vol. 3, 1.2.7)

C4 (3-byte) and C5 (2-byte) are VEX prefixes only if bits 7:6 of the following byte are 11b;
otherwise they are LES/LDS (whose ModRM must name memory). In 32-bit (and 16-bit) code the
inverted VEX.R and VEX.X are then necessarily 1, VEX.B is ignored, and so is the high bit of
VEX.vvvv (`Inst.vvvv` holds the low three bits of the non-inverted field). The decoder accepts VEX
in every mode; execution raises #UD in real and virtual-8086 mode, with a 66, F2, F3 or LOCK prefix
before the VEX prefix, and for unknown maps (`Dispatch.vexExec`). The VEX prefix replaces the 0F,
0F 38 or 0F 3A escape and the rest of the instruction (ModRM, SIB, displacement, immediates) is laid
out as in the legacy map with the same opcode (`opInfo`): e.g. VEX.0F 77 (VZEROUPPER/VZEROALL) has no
ModRM byte like EMMS, VEX.0F 70..73, C2, C4..C6 and VEX.0F3A have an imm8, and an unassigned VEX.0F
8x is laid out like Jcc rel32 (as QEMU decodes it). An unknown map has no ModRM byte (its opcode byte
ends the instruction). EVEX (62 with ModRM.mod = 11b) and XOP (8F with ModRM.reg ≠ 0) are not decoded: on
Zen 2, which has neither, they are the #UD register forms of BOUND and POP r/m.
-/
namespace X86

structure Inst where
  /-- Opcode number `map * 0x100 + byte` (see the module documentation). -/
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
  /-- 0, 0xF2 (REPNE) or 0xF3 (REP/REPE): the last of the two present. -/
  rep : UInt8 := 0
  /-- An operand-size prefix (66) was present (a mandatory prefix of SSE2 instructions). -/
  p66 : Bool := false
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
  /-- Second immediate: segment of far pointers, ENTER's level, the second imm8 of EXTRQ/INSERTQ. -/
  imm2 : UInt32 := 0
  /-- Mandatory prefix, one value for legacy and VEX encodings: 0 none, 1 = 66, 2 = F3, 3 = F2.
  Legacy: F2/F3 (the last one) take precedence over 66. VEX: VEX.pp. -/
  pp : UInt8 := 0
  /-- VEX-encoded (C4/C5). The fields below are 0/false otherwise. -/
  vex : Bool := false
  /-- VEX.vvvv as a register number (un-inverted, low three bits). -/
  vvvv : UInt8 := 0
  /-- VEX.L (256-bit vector length). -/
  vexL : Bool := false
  /-- VEX.W (always 0 with the two-byte prefix). -/
  vexW : Bool := false
  /-- Bit 3 of VEX.vvvv (decoded, i.e. set when the encoded bit is 0). Outside 64-bit mode it does not
  select a register (`vvvv` keeps bits 2:0), but the EPYC 7742 requires it to be 0 where VEX.vvvv
  must be 1111b (`Vex.noV`). -/
  vvvv3 : Bool := false
  deriving Repr, Inhabited

namespace Inst
@[inline] def reg (i : Inst) : UInt8 := (i.modrm >>> 3) &&& 7
@[inline] def rm (i : Inst) : UInt8 := i.modrm &&& 7
@[inline] def mod (i : Inst) : UInt8 := i.modrm >>> 6
/-- Opcode map: 0 one-byte, 1 = 0F, 2 = 0F 38, 3 = 0F 3A. -/
@[inline] def map (i : Inst) : UInt32 := i.op >>> 8
/-- The opcode byte within its map. -/
@[inline] def byte (i : Inst) : UInt8 := (i.op &&& 0xFF).toUInt8
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
/-- 0F 78: two imm8 (`imm`, `imm2`) with a 66 or F2 prefix (EXTRQ/INSERTQ, SSE4a), none otherwise. -/
def sse4a : UInt8 := 9
end Imm

/-- Opcode properties: `(immediate kind <<< 4) ||| hasModRM`. -/
def opInfo (op : UInt32) : UInt8 :=
  if op ≥ 0x300 then 0x11   -- 0F 3A: ModRM, imm8
  else if op ≥ 0x200 then 0x01   -- 0F 38: ModRM
  else if op < 0x100 then
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
    -- MMX/SSE/SSE2/SSE3: 10..17, 28..2F, 50..7F (except 77 EMMS, 78 and the undefined 7A, 7B),
    -- D0..FE; an imm8 with 70..73 and C2, C4, C5, C6. SSE4a: 66/F2 0F 78 have two imm8, 0F 79 ModRM.
    -- AMD APM vol. 3, table A-4 (Zen 2: no 3DNow!, so 0F 0E and 0F 0F stay undefined).
    else if (0x10 ≤ b && b ≤ 0x17) || (0x28 ≤ b && b ≤ 0x2F) || (0x50 ≤ b && b ≤ 0x6F) ||
            (0x74 ≤ b && b ≤ 0x76) || b == 0x79 || (0x7C ≤ b && b ≤ 0x7F) || (0xD0 ≤ b && b ≤ 0xFE) then 0x01
    else if (0x70 ≤ b && b ≤ 0x73) || b == 0xC2 || (0xC4 ≤ b && b ≤ 0xC6) then 0x11
    else if b == 0x78 then 0x91
    else match b with
      | 0xA3 | 0xA5 | 0xAB | 0xAD | 0xAE | 0xAF => 0x01
      | 0xA4 | 0xAC | 0xBA => 0x11
      | 0xB0 | 0xB1 | 0xB2 | 0xB3 | 0xB4 | 0xB5 | 0xB6 | 0xB7 => 0x01
      | 0xB8 | 0xB9 | 0xBB | 0xBC | 0xBD | 0xBE | 0xBF => 0x01   -- B8: F3 = POPCNT
      | 0xC0 | 0xC1 | 0xC3 | 0xC7 | 0xFF => 0x01
      | _ => 0

/-- `opInfo` for every opcode 0x000..0x3FF, precomputed. -/
def opInfoTable : ByteArray := ⟨Array.ofFn (n := 1024) fun k => opInfo k.val.toUInt32⟩

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
  -- VEX payload: 0 for legacy encodings, else 0x10000 ||| (C4 ? 0x8000) ||| last VEX byte
  let mut vx : UInt32 := 0
  -- a ModRM byte already fetched (C4/C5 that turned out to be LES/LDS), or 0x100
  let mut pre : UInt32 := 0x100
  if b == 0x0F then
    let b1 ← fetch8 (eip0 + n)
    n := n + 1
    if b1 == 0x38 || b1 == 0x3A then
      op := (if b1 == 0x38 then 0x200 else 0x300) + (← fetch8 (eip0 + n))
      n := n + 1
    else
      op := 0x100 + b1
  else if b == 0xC4 || b == 0xC5 then
    let v1 ← fetch8 (eip0 + n)
    n := n + 1
    if v1 &&& 0xC0 == 0xC0 then
      -- VEX: 2-byte C5 [R vvvv L pp], 3-byte C4 [R X B mmmmm] [W vvvv L pp]
      if b == 0xC5 then
        vx := 0x10000 ||| v1
        op := 0x100 + (← fetch8 (eip0 + n))
        n := n + 1
      else
        let v2 ← fetch8 (eip0 + n)
        let ob ← fetch8 (eip0 + n + 1)
        n := n + 2
        vx := 0x18000 ||| v2
        let map := v1 &&& 0x1F
        op := if 1 ≤ map && map ≤ 3 then map * 0x100 + ob else ob
    else
      pre := v1
  let info := if vx != 0 && op < 0x100 then 0 else opInfoTable.get! op.toNat
  let p66 := opsz != (if d32 then 4 else 2)
  let pp : UInt8 :=
    if vx != 0 then (vx &&& 3).toUInt8
    else if rep == 0xF3 then 2 else if rep == 0xF2 then 3 else if p66 then 1 else 0
  let mut i : Inst := { op, opsz, adsz, segOvr, rep, p66, lock, pp }
  if vx != 0 then
    i := { i with vex := true, vexL := vx &&& 4 != 0, vvvv := (((~~~vx) >>> 3) &&& 7).toUInt8,
                  vexW := vx &&& 0x8080 == 0x8080, vvvv3 := vx &&& 0x40 == 0 }
  if info &&& 1 != 0 then
    let modrm := (← if pre < 0x100 then pure pre else do
      let v ← fetch8 (eip0 + n)
      n := n + 1
      pure v).toUInt8
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
      else if kind == Imm.sse4a then (if pp == 1 || pp == 3 then 1 else 0)
      else 0
    if k != 0 then
      let v ← rd (eip0 + n) k
      n := n + k
      i := { i with imm := v }
    if kind == Imm.ptr then
      let v ← rd (eip0 + n) 2
      n := n + 2
      i := { i with imm2 := v }
    else if kind == Imm.enter || (kind == Imm.sse4a && k != 0) then
      let v ← rd (eip0 + n) 1
      n := n + 1
      i := { i with imm2 := v }
  return (i, n)

/-- The long-mode boundary (`X86/Ext/LongModeBase.lean`): in 64-bit mode (EFER.LMA = 1 and CS.L = 1),
which is the `x86_64` model's, nothing is fetched and the step stops. -/
@[inline] def stop64 : M Unit := fun m =>
  if m.cpu.cs.attr &&& 0x2000 != 0 && m.cpu.efer &&& EFER.LMA != 0 then .error (.unsupported "64-bit mode") m
  else .ok () m

/-- Decode the instruction at CS:EIP. Instructions longer than 15 bytes raise #GP(0). -/
def decode : M Inst := do
  stop64
  let (i, n) ← decodeRaw
  if n > 15 then gp 0
  return { i with len := n }

end X86
