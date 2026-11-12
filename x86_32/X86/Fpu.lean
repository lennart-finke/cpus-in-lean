import X86.Decode
import X86.Sys
import X86.Float80
import X86.Transcendental
/-!
# x87 FPU instructions (ESC opcodes D8..DF and WAIT)

The register stack, control/status/tag words, the last-instruction pointers, stack faults and the
exception responses (SDM vol. 1, chapter 8):

* Stack overflow (push onto a non-empty register) and underflow (an empty source) are invalid
  operations with SF set, C1 = 1 / 0. Masked, the result is the QNaN indefinite.
* An unmasked IE, DE or ZE suppresses the result (registers and TOP unchanged) — except the result
  of a comparison (EFLAGS or C3/C2/C0), which the EPYC 7742 writes anyway (`fpCompare`); unmasked
  OE / UE deliver a wrapped result to a register (beyond the wrapped range: ±∞ / ±0, FSCALE's
  "massive" case) but nothing to memory; any unmasked exception sets ES and
  B, and the next waiting x87 instruction (or WAIT) raises #MF with CR0.NE = 1. With CR0.NE = 0 the
  FERR# output drives IRQ13 (as on PC/AT compatibles) and execution continues.
* CR0.EM or CR0.TS make every ESC instruction raise #NM; WAIT raises #NM only with TS and MP.
* Non-control instructions record FIP/FCS/FOP, and FDP/FDS when they have a memory operand.

The transcendental instructions (F2XM1, FYL2X, FYL2XP1, FPTAN, FPATAN, FSIN, FCOS, FSINCOS) deliver
correctly rounded results (`X86/Transcendental.lean`).

Where the EPYC 7742's behaviour (the native campaign, `validation/README.md`, "First run") settles a
point the SDM leaves open or contradicts its pseudocode, the model follows the hardware: compare
results with unmasked exceptions, FLD ST(i)'s underflow over overflow, FXTRACT's overflow before the
operand's exceptions, the control word's reserved bits (`fcwLoad`) and the FFFFh upper halves of the
32-bit protected-mode environment image.
-/
namespace X86

namespace Cpu
@[inline] def ftop (c : Cpu) : Nat := ((c.fsw >>> 11) &&& 7).toNat
@[inline] def stIdx (c : Cpu) (i : Nat) : Nat := (c.ftop + i) % 8
@[inline] def stEmpty (c : Cpu) (i : Nat) : Bool := (c.fempty >>> (c.stIdx i).toUInt8) &&& 1 != 0
@[inline] def st (c : Cpu) (i : Nat) : F80 := c.fpr[c.stIdx i]!
/-- ST(i) as an operand: `none` if the register is empty. -/
@[inline] def stOpt (c : Cpu) (i : Nat) : Option F80 := if c.stEmpty i then none else some (c.st i)
@[inline] def setSt (c : Cpu) (i : Nat) (v : F80) : Cpu :=
  let k := c.stIdx i
  { c with fpr := c.fpr.set! k v, fempty := c.fempty &&& ~~~((1 : UInt8) <<< k.toUInt8) }
@[inline] def setTop (c : Cpu) (t : Nat) : Cpu :=
  { c with fsw := (c.fsw &&& ~~~0x3800) ||| ((t % 8).toUInt16 <<< 11) }
@[inline] def fpop (c : Cpu) : Cpu :=
  let k := c.stIdx 0
  { c with fempty := c.fempty ||| ((1 : UInt8) <<< k.toUInt8) }.setTop (c.ftop + 1)
@[inline] def fpushRaw (c : Cpu) (v : F80) : Cpu := (c.setTop (c.ftop + 7)).setSt 0 v

/-- Full two-bit tag of physical register k: valid 0, zero 1, special 2, empty 3. -/
def ftagOf (c : Cpu) (k : Nat) : UInt32 :=
  if (c.fempty >>> k.toUInt8) &&& 1 != 0 then 3 else
  let v := c.fpr[k]!
  if v.isZero then 1 else if v.exp == 0 || v.exp == 0x7FFF || v.unsupported then 2 else 0

def ftagWord (c : Cpu) : UInt32 := Id.run do
  let mut w : UInt32 := 0
  for k in [0:8] do w := w ||| (c.ftagOf k <<< (2 * k).toUInt32)
  return w
end Cpu

/-- The x87 control word as loaded by FLDCW, FLDENV, FRSTOR, FXRSTOR and XRSTOR: the reserved bits 7
and 13..15 read as 0 and bit 6 reads as 1, as the reset value 0040h has it (AMD APM vol. 2, table
14-1). Observed on the EPYC 7742 for FRSTOR (native `alignment_check`: an image with control word
1F80h, 001Fh or 8000h loads 1F40h, 005Fh, 0040h); the same register takes the other loads. Bit 12
(the 287's infinity control) is kept. -/
@[inline] def fcwLoad (v : UInt32) : UInt16 := ((v &&& 0x1F3F) ||| 0x40).toUInt16

/-- The status word as loaded by FLDENV, FRSTOR, FXRSTOR and XRSTOR: ES (bit 7) and B are cleared when
no unmasked exception flag is set (otherwise ES is loaded as stored), and B (bit 15) mirrors ES ("for
8087 compatibility only; it reflects the contents of the ES flag", SDM vol. 1, 8.1.3.1). The EPYC
7742 shows B set after its XRSTOR of a signal frame whose status word had ES = 1 and B = 0 (native
`xsave_save`, `xsave_compacted`, 36 cases). -/
@[inline] def fswLoad (sw cw : UInt16) : UInt16 :=
  if sw.toUInt32 &&& ~~~cw.toUInt32 &&& 0x3F == 0 then sw &&& 0x7F7F
  else (sw &&& 0x7FFF) ||| (if sw &&& 0x80 != 0 then 0x8000 else 0)

/-- FERR# asserts IRQ13 (the slave PIC's input 5) while an unmasked exception is pending. -/
def setFerr (on : Bool) : M Unit := modM fun m => { m with pic1 := m.pic1.setLine 5 on }.syncIntr

/-- A pending unmasked exception at a waiting instruction: #MF, or FERR# with CR0.NE = 0. -/
def fpPending : M Unit := do
  if (← cpu).cr0 &&& CR0.NE != 0 then exc Vec.MF
  -- SVM: the FERR_FREEZE intercept of a guest takes the place of the freeze (`Svm.ferrFreeze`)
  Svm.ferrFreeze
  setFerr true

/-- Device-not-available and pending-exception checks before an ESC instruction. -/
def fpCheck (wait : Bool) : M Unit := do
  let c ← cpu
  if c.cr0 &&& (CR0.EM ||| CR0.TS) != 0 then exc Vec.NM
  if wait && c.fsw &&& 0x80 != 0 then fpPending

/-- Merge status bits: the exception flags and SF accumulate; C1 is replaced; ES and B are set when
any unmasked exception flag is set. -/
def fpStatus (fl : UInt32) : M Unit := modCpu fun c =>
  let sw := (c.fsw.toUInt32 &&& ~~~FPF.C1) ||| (fl &&& (0x7F ||| FPF.C1))
  let sw := if sw &&& ~~~c.fcw.toUInt32 &&& 0x3F != 0 then sw ||| 0x8080 else sw
  { c with fsw := sw.toUInt16 }

/-- Set the condition codes C0..C3 (bits 8, 9, 10, 14 of `cc`), leaving the rest of the word. -/
def fpCC (cc : UInt32) : M Unit := modCpu fun c =>
  { c with fsw := ((c.fsw.toUInt32 &&& ~~~0x4700) ||| (cc &&& 0x4700)).toUInt16 }

@[inline] def fpUnmasked (fl : UInt32) (cw : UInt16) (which : UInt32 := FPF.IE ||| FPF.DE ||| FPF.ZE) : Bool :=
  fl &&& ~~~cw.toUInt32 &&& which != 0

def stackUnderflow : UInt32 := FPF.IE ||| FPF.SF

/-- The status reported when an unmasked IE, DE or ZE stops an instruction before its result: the
lower-priority numeric overflow, underflow and precision exceptions (and the round-up C1) of the
computation are not detected (SDM vol. 1, 4.9.2, 8.5.2); a stack fault keeps its C1. -/
@[inline] def fpStopped (fl : UInt32) : UInt32 :=
  fl &&& (FPF.IE ||| FPF.DE ||| FPF.ZE ||| FPF.SF ||| (if fl &&& FPF.SF != 0 then FPF.C1 else 0))

/-- Write a result to ST(dst) unless an unmasked IE/DE/ZE suppresses it; then pop `pops` times. -/
def fpResult (r : F80) (fl : UInt32) (dst : Nat) (pops : Nat := 0) : M Unit := do
  let cw := (← cpu).fcw
  fpStatus (if fpUnmasked fl cw then fpStopped fl else fl)
  if !fpUnmasked fl cw then
    modCpu fun c => Id.run do
      let mut c := c.setSt dst r
      for _ in [0:pops] do c := c.fpop
      return c

/-- Push a value (FLD and friends): stack overflow if the new ST(0) is in use. -/
def fpPush (v : F80) (fl : UInt32) : M Unit := do
  let c ← cpu
  if !c.stEmpty 7 then
    fpStatus (FPF.IE ||| FPF.SF ||| FPF.C1)
    if c.fcw.toUInt32 &&& FPF.IE != 0 then modCpu (·.fpushRaw F80.indefinite)
    return
  fpStatus fl
  if !fpUnmasked fl c.fcw then modCpu (·.fpushRaw v)

/-- Binary arithmetic ST(dst) := a op b (empty operands underflow), popping `pops` times. -/
def fpArith (op : F80.Op) (a b : Option F80) (dst : Nat) (pops : Nat := 0) (extra : UInt32 := 0) : M Unit := do
  let cw := (← cpu).fcw.toUInt32
  match a, b with
  | some a, some b =>
    let (r, fl) := F80.arith op a b (pcBits ((cw >>> 8) &&& 3)) cw
    fpResult r (fl ||| extra) dst pops
  | _, _ => fpResult F80.indefinite stackUnderflow dst pops

/-- Compare; condition codes (C3, C2, C0) or, with `eflags`, ZF/PF/CF. The result (unordered for an
invalid or empty operand) is written whether or not the exception is masked; an unmasked IE or DE
only suppresses the pops. The SDM's pseudocode sets "111" only when IM = 1, but the EPYC 7742 writes
the comparison result with IE or DE unmasked too, for FCOM/FUCOM/FTST/FCOMI/FUCOMI and their popping
forms (native campaign families `x87_exceptions`, `x87_random`: 895 cases); QEMU's TCG does the
same (`helper_fcomi_ST0_FT0` always sets the flags). -/
def fpCompare (a b : Option F80) (quiet eflags : Bool) (pops : Nat) (extra : UInt32 := 0) : M Unit := do
  let cw := (← cpu).fcw
  let (o, fl) := match a, b with
    | some a, some b => F80.compare a b quiet
    | _, _ => (none, stackUnderflow)
  let fl := fl ||| extra
  fpStatus (fl &&& ~~~FPF.C1)
  if eflags then
    let f : UInt32 := match o with
      | some 1 => 0 | some 0 => Flag.ZF | some _ => Flag.CF
      | none => Flag.ZF ||| Flag.PF ||| Flag.CF
    setFlags (Flag.ZF ||| Flag.PF ||| Flag.CF ||| Flag.OF ||| Flag.SF ||| Flag.AF) f
  else
    fpCC (match o with | some 1 => 0 | some 0 => 0x4000 | some _ => 0x100 | none => 0x4500)
  if fpUnmasked fl cw (FPF.IE ||| FPF.DE) then return
  modCpu fun c => Id.run do
    let mut c := c
    for _ in [0:pops] do c := c.fpop
    return c

/-! ## Memory operands -/

@[inline] def fpEa (i : Inst) : M UInt32 := fun m =>
  let c := m.cpu
  let b := if i.base < 8 then c.getReg i.base else 0
  let x := if i.index < 8 then c.getReg i.index <<< i.scale.toUInt32 else 0
  let a := b + x + i.disp
  .ok (if i.adsz == 2 then a &&& 0xFFFF else a) m

/-- Alignment of an x87 memory operand of `n` bytes for #AC (AMD APM vol. 2, table 8-7): m16 2,
m32 4, m64 8, m80 (extended real and packed BCD) 8, the 14/28-byte environment and the 94/108-byte
save area 2 or 4 (by operand size); 1 for the register part of FRSTOR's area (checked with the
environment at the start of the area). -/
def fpAlign (n : Nat) : UInt32 :=
  match n with
  | 2 => 2 | 4 => 4 | 8 => 8 | 10 => 8 | 14 => 2 | 28 => 4 | 94 => 2 | 108 => 4 | _ => 1

/-- Read `n` (≤ 10) bytes at seg:off as a natural number (little endian). -/
def fpRead (s : UInt8) (off : UInt32) (n : Nat) : M Nat := do
  let mut v : Nat := 0
  let mut k := 0
  while k < n do
    let w := if n - k ≥ 4 then 4 else if n - k ≥ 2 then 2 else 1
    -- the operand's alignment is checked once, with its first part
    let x ← rdMem s (off + k.toUInt32) w.toUInt32 (al := if k == 0 then fpAlign n else 1)
    v := v + x.toNat * 2^(8 * k)
    k := k + w
  return v

/-- Write `n` (≤ 108) bytes at seg:off; the whole range is checked before any byte is written. -/
def fpWrite (s : UInt8) (off : UInt32) (n : Nat) (v : Nat) : M Unit := do
  let lin ← segAddr s off n.toUInt32 true
  acChk lin (fpAlign n) (← isUser)
  linProbeWr lin n.toUInt32 (← isUser)
  let mut k := 0
  while k < n do
    let w := if n - k ≥ 4 then 4 else if n - k ≥ 2 then 2 else 1
    wrMem s (off + k.toUInt32) w.toUInt32 ((v / 2^(8 * k)) % 2^(8 * w)).toUInt32 (al := 1)
    k := k + w

@[inline] def f80OfNat (v : Nat) : F80 := { sig := (v % 2^64).toUInt64, se := (v / 2^64).toUInt16 }
@[inline] def f80ToNat (v : F80) : Nat := v.sig.toNat + v.se.toNat * 2^64

@[inline] def sext' (bits : Nat) (v : Nat) : Int := if v ≥ 2^(bits - 1) then (v : Int) - (2^bits : Nat) else v

/-- Memory operand of the arithmetic group: 0 m32fp, 1 m32int, 2 m64fp, 3 m16int (by D8/DA/DC/DE). -/
def fpMemOperand (i : Inst) : M (F80 × UInt32) := do
  let off ← fpEa i
  match i.op with
  -- a binary32/64 SNaN operand stays an SNaN for the NaN rules of the operation (an SNaN and a QNaN
  -- give the QNaN, with IE): the EPYC 7742 returns ST(0)'s QNaN for FADD/FMUL with an SNaN m32/m64
  -- (native campaign family open_questions, `x87_snan_memory`, 3 cases; open question F1). QEMU and
  -- Bochs quiet it first (and then pick the larger significand).
  | 0xD8 => return F80.ofIeee (← fpRead i.seg off 4).toUInt64 23 8 (quietSNaN := false)
  | 0xDC => return F80.ofIeee (← fpRead i.seg off 8).toUInt64 52 11 (quietSNaN := false)
  | 0xDA => return (F80.ofInt (sext' 32 (← fpRead i.seg off 4)), 0)
  | _ => return (F80.ofInt (sext' 16 (← fpRead i.seg off 2)), 0)

/-! ## Environment (FLDENV/FNSTENV/FRSTOR/FNSAVE) -/

/-- Store the environment (14 or 28 bytes, real-mode or protected-mode layout). -/
def fpEnvBytes (opsz : Sz) (real : Bool) (c : Cpu) : Nat × Nat :=
  let cw := c.fcw.toNat
  let sw := c.fsw.toNat
  let tw := c.ftagWord.toNat
  let fop := c.fop.toNat &&& 0x7FF
  let ws : List Nat :=
    if real then
      let ip := c.fip.toNat
      let dp := c.fdp.toNat
      if opsz == 4 then [cw, sw, tw, ip % 65536, ((ip / 65536) % 65536) * 4096 + fop, dp % 65536, ((dp / 65536) % 65536) * 4096]
      else [cw, sw, tw, ip % 65536, ((ip / 65536) % 16) * 4096 + fop, dp % 65536, ((dp / 65536) % 16) * 4096]
    -- the reserved upper halves of the control, status, tag and FDS dwords of the 32-bit protected-mode
    -- layout are stored as FFFFh (EPYC 7742: the FNSTENV and FNSAVE images of the native
    -- `alignment_check` family, 24 cases; QEMU stores 0)
    else if opsz == 4 then [cw + 0xFFFF0000, sw + 0xFFFF0000, tw + 0xFFFF0000, c.fip.toNat,
                            c.fcs.toNat + fop * 65536, c.fdp.toNat, c.fds.toNat + 0xFFFF0000]
    else [cw, sw, tw, c.fip.toNat % 65536, c.fcs.toNat, c.fdp.toNat % 65536, c.fds.toNat]
  let w := if opsz == 4 then 4 else 2
  -- the reserved upper halves of the 32-bit real-mode layout are stored as zero (no hardware evidence)
  let v := (ws.zipIdx).foldl (fun acc (x, k) => acc + x * 2^(8 * w * k)) 0
  (v, 7 * w)

def fpLoadEnv (opsz : Sz) (real : Bool) (s : UInt8) (off : UInt32) : M Unit := do
  let w := if opsz == 4 then 4 else 2
  let v ← fpRead s off (7 * w)
  let f := fun (k : Nat) => (v / 2^(8 * w * k)) % 2^(8 * w)
  let tw := f 2
  let mut empty : UInt8 := 0
  for k in [0:8] do
    if (tw / 4^k) % 4 == 3 then empty := empty ||| ((1 : UInt8) <<< k.toUInt8)
  let (ip, cs, op, dp, ds) :=
    if real then
      let hi := if opsz == 4 then 65536 else 16
      (f 3 + (f 4 / 4096 % hi) * 65536, 0, f 4 % 2048, f 5 + (f 6 / 4096 % hi) * 65536, 0)
    else if opsz == 4 then (f 3, f 4 % 65536, (f 4 / 65536) % 2048, f 5, f 6 % 65536)
    else (f 3, f 4, 0, f 5, f 6)
  -- a pending unmasked exception in the loaded status word sets ES and B (`fswLoad`)
  modCpu fun c => { c with fcw := fcwLoad (f 0).toUInt32, fsw := fswLoad (f 1).toUInt16 (fcwLoad (f 0).toUInt32),
                           fempty := empty, fip := ip.toUInt32, fcs := cs.toUInt16, fop := op.toUInt16,
                           fdp := dp.toUInt32, fds := ds.toUInt16 }

def fninit : M Unit := do
  modCpu fun c => { c with fcw := 0x37F, fsw := 0, fempty := 0xFF, fip := 0, fcs := 0, fop := 0,
                           fdp := 0, fds := 0 }
  setFerr false

/-! ## Instructions -/

/-- Control instructions: they do not wait for pending exceptions and do not update FIP/FDP/FOP. -/
def fpControl (i : Inst) : Bool :=
  if i.isMem then
    (i.op == 0xD9 && i.reg ≥ 4) || (i.op == 0xDD && (i.reg == 4 || i.reg == 6 || i.reg == 7))
  else (i.op == 0xDB && (i.modrm == 0xE0 || i.modrm == 0xE1 || i.modrm == 0xE2 || i.modrm == 0xE3 ||
                         i.modrm == 0xE4)) || (i.op == 0xDF && i.modrm == 0xE0)

/-- Record the last-instruction pointers (non-control instructions). -/
def fpNote (i : Inst) : M Unit := do
  let c ← cpu
  let ip := c.eip - i.len
  let ip := if c.cs.big then ip else ip &&& 0xFFFF
  let fop := (((i.op &&& 7) <<< 8) ||| i.modrm.toUInt32).toUInt16
  if i.isMem then
    let ea ← fpEa i
    modCpu fun c => { c with fip := ip, fcs := c.cs.sel, fop, fdp := ea, fds := (c.getSeg i.seg).sel }
  else modCpu fun c => { c with fip := ip, fcs := c.cs.sel, fop }

/-- Store ST(0) to memory with format `kind`: 0 m32fp, 1 m64fp, 2 m80fp, 3 m16int, 4 m32int,
5 m64int, 6 m80bcd; pop afterwards if `pop`. `trunc`: convert by truncation whatever FCW.RC says
(FISTTP, SSE3; SDM FISTTP). -/
def fpStore (i : Inst) (kind : Nat) (pop : Bool) (trunc : Bool := false) : M Unit := do
  let c ← cpu
  let cw := c.fcw.toUInt32 ||| (if trunc then 0xC00 else 0)
  let off ← fpEa i
  let a? := c.stOpt 0
  let size := match kind with | 0 => 4 | 1 => 8 | 3 => 2 | 4 => 4 | 5 => 8 | _ => 10
  let indef : Nat := match kind with
    | 0 => 0xFFC00000 | 1 => 0xFFF8000000000000 | 2 => f80ToNat F80.indefinite
    | 3 => 0x8000 | 4 => 0x80000000 | 5 => 0x8000000000000000 | _ => 0xFFFFC000000000000000
  let (v?, fl) : Option Nat × UInt32 := match a? with
    | none => (if cw &&& FPF.IE != 0 then some indef else none, stackUnderflow)
    | some a =>
      match kind with
      | 0 => let (v, fl) := a.toIeee 23 8 cw; (v.map (·.toNat), fl)
      | 1 => let (v, fl) := a.toIeee 52 11 cw; (v.map (·.toNat), fl)
      | 2 => (some (f80ToNat a), 0)
      | 3 => let (v, fl) := a.toInt 16 cw; (v.map (·.toNat), fl)
      | 4 => let (v, fl) := a.toInt 32 cw; (v.map (·.toNat), fl)
      | 5 => let (v, fl) := a.toInt 64 cw; (v.map (·.toNat), fl)
      | _ =>
        match a.toIntRC ((cw >>> 10) &&& 3) with
        | some (z, inexact, up) =>
          if z.natAbs ≥ 10^18 then (if cw &&& FPF.IE != 0 then some indef else none, FPF.IE)
          else
            let digits := (List.range 9).foldl (fun acc k =>
              let d := (z.natAbs / 100^k) % 100
              acc + ((d / 10) * 16 + d % 10) * 256^k) 0
            (some (digits + (if a.neg then 0x80 * 2^72 else 0)),
             (if inexact then FPF.PE else 0) ||| (if up then FPF.C1 else 0))
        | none => (if cw &&& FPF.IE != 0 then some indef else none, FPF.IE)
  -- an unmasked exception stores nothing (except a wrapped-precision-only exception)
  match v? with
  | none => fpStatus fl
  | some v =>
    if fpUnmasked fl c.fcw then fpStatus fl
    else
      fpWrite i.seg off size v
      fpStatus fl
      if pop then modCpu (·.fpop)

/-- Load ST(0) from memory (`kind` as in `fpStore`) and push it. -/
def fpLoad (i : Inst) (kind : Nat) : M Unit := do
  let off ← fpEa i
  match kind with
  | 0 => let (v, fl) := F80.ofIeee (← fpRead i.seg off 4).toUInt64 23 8; fpPush v fl
  | 1 => let (v, fl) := F80.ofIeee (← fpRead i.seg off 8).toUInt64 52 11; fpPush v fl
  | 2 => fpPush (f80OfNat (← fpRead i.seg off 10)) 0
  | 3 => fpPush (F80.ofInt (sext' 16 (← fpRead i.seg off 2))) 0
  | 4 => fpPush (F80.ofInt (sext' 32 (← fpRead i.seg off 4))) 0
  | 5 => fpPush (F80.ofInt (sext' 64 (← fpRead i.seg off 8))) 0
  | _ =>
    let v ← fpRead i.seg off 10
    let mag : Nat := (List.range 9).foldl (fun (acc k : Nat) =>
      let b := (v / 256^(8 - k)) % 256
      acc * 100 + (b / 16) * 10 + b % 16) 0
    let z : Int := if (v / 2^79) % 2 == 1 then -(mag : Int) else mag
    let r := F80.ofInt z
    fpPush (if z == 0 && (v / 2^79) % 2 == 1 then F80.zero true else r) 0

/-- One-operand operation on ST(0) (empty: underflow). -/
def fpUnary (f : F80 → F80 × UInt32) : M Unit := do
  match (← cpu).stOpt 0 with
  | some a => let (r, fl) := f a; fpResult r fl 0
  | none => fpResult F80.indefinite stackUnderflow 0

/-- ST(1) := f ST(0) ST(1), then pop (FYL2X, FYL2XP1, FPATAN); an empty operand underflows. -/
def fpBinPop (f : F80 → F80 → F80 × UInt32) : M Unit := do
  let c ← cpu
  match c.stOpt 0, c.stOpt 1 with
  | some x, some y => let (r, fl) := f x y; fpResult r fl 1 1
  | _, _ => fpResult F80.indefinite stackUnderflow 1 1

/-- A stack fault of an instruction that replaces ST(0) and pushes a second result (FXTRACT, FPTAN,
FSINCOS): an empty ST(0) underflows (C1 = 0), a full ST(7) overflows (C1 = 1); the masked response
writes the QNaN indefinite to both destinations. -/
def fpPush2Fault (fl : UInt32) : M Unit := do
  fpStatus fl
  if (← cpu).fcw.toUInt32 &&& FPF.IE != 0 then
    modCpu fun c => (c.setSt 0 F80.indefinite).fpushRaw F80.indefinite

/-- Replace ST(0) by `a` and push `b`, unless an unmasked IE/DE/ZE suppresses both. -/
def fpPush2 (a b : F80) (fl : UInt32) : M Unit := do
  let cw := (← cpu).fcw
  fpStatus (if fpUnmasked fl cw then fpStopped fl else fl)
  if !fpUnmasked fl cw then modCpu fun c => (c.setSt 0 a).fpushRaw b

@[inline] def fpSetC2 (on : Bool) : M Unit := modCpu fun c =>
  { c with fsw := (c.fsw &&& ~~~0x400) ||| (if on then 0x400 else 0) }

/-- FSIN (`which` = 0), FCOS (1), FPTAN (2) and FSINCOS (3). C2 = 1 (and nothing else changes,
C1 = 0) for an operand outside -2^63 < x < 2^63; C2 = 0 otherwise. FPTAN replaces ST(0) by tan x
and pushes 1.0; FSINCOS replaces ST(0) by sin x and pushes cos x (C1 is set if either was rounded
up). A NaN or invalid operand gives the NaN result in both destinations. -/
def fpTrig (which : Nat) : M Unit := do
  let c ← cpu
  let cw := c.fcw.toUInt32
  let two := which ≥ 2
  match c.stOpt 0 with
  | none =>
    if two then fpPush2Fault stackUnderflow else fpResult F80.indefinite stackUnderflow 0
    fpSetC2 false
  | some a =>
    if two && !c.stEmpty 7 then
      fpPush2Fault (FPF.IE ||| FPF.SF ||| FPF.C1)
      fpSetC2 false
      return
    match Trans.trigSpecial a with
    | some (v, fl) =>
      if two then fpPush2 v v fl else fpResult v fl 0
      fpSetC2 false
    | none =>
      if Trans.trigOutOfRange a then
        fpStatus 0
        fpSetC2 true
      else
        match which with
        | 2 => let (v, fl) := Trans.trigFinite 2 a cw; fpPush2 v F80.one fl
        | 3 =>
          let (s, fl1) := Trans.trigFinite 0 a cw
          let (co, fl2) := Trans.trigFinite 1 a cw
          fpPush2 s co (fl1 ||| fl2)
        | _ => let (v, fl) := Trans.trigFinite which a cw; fpResult v fl 0
        fpSetC2 false

/-- FXAM: class of ST(0) in C3, C2, C0 and its sign in C1. -/
def fxam : M Unit := do
  let c ← cpu
  let a := c.st 0
  let cls : UInt32 :=
    if c.stEmpty 0 then 0x4100
    else if a.unsupported then 0
    else if a.isNaN then 0x100
    else if a.isInf then 0x500
    else if a.isZero then 0x4000
    else if a.isDenormal then 0x4400
    else 0x400
  fpCC cls
  modCpu fun c => { c with fsw := (c.fsw &&& ~~~0x200) ||| (if a.neg then 0x200 else 0) }

/-- Load a constant (FLD1, FLDZ, FLDPI, ...) rounded in the current rounding mode. -/
def fpConstLoad (k : Nat) : M Unit := do
  let cw := (← cpu).fcw.toUInt32 ||| 0x3F
  let (n, e) := fpConst k
  let (v, _) := round80 false n 1 e 64 cw
  fpPush v 0

def fcmovCond (k : Nat) (fl : UInt32) : Bool :=
  let cf := fl &&& Flag.CF != 0
  let zf := fl &&& Flag.ZF != 0
  let pf := fl &&& Flag.PF != 0
  match k with
  | 0 => cf | 1 => zf | 2 => cf || zf | _ => pf

/-- FXCH ST(i). -/
def fxch (k : Nat) : M Unit := do
  let c ← cpu
  match c.stOpt 0, c.stOpt k with
  | some a, some b =>
    fpStatus 0
    modCpu fun c => (c.setSt 0 b).setSt k a
  | a, b =>
    fpStatus stackUnderflow
    if c.fcw.toUInt32 &&& FPF.IE != 0 then
      modCpu fun c => (c.setSt 0 (b.getD F80.indefinite)).setSt k (a.getD F80.indefinite)

/-- Register-operand forms of D9 (FLD ST(i), FXCH, FNOP and the D9 E0..FF group). -/
def x87D9reg (i : Inst) : M Unit := do
  let k := i.rm.toNat
  let c ← cpu
  let cw := c.fcw.toUInt32
  match i.reg with
  | 0 =>
    -- FLD ST(i) from an empty ST(i): stack underflow (C1 = 0) even when the destination ST(7) is in use
    -- too (EPYC 7742, native `x87_exceptions`/`x87_random`: 77 cases; the overflow's C1 = 1 is not
    -- reported); the masked response pushes the QNaN indefinite
    if c.stEmpty k then
      fpStatus stackUnderflow
      if cw &&& FPF.IE != 0 then modCpu (·.fpushRaw F80.indefinite)
    else fpPush (c.st k) 0
  | 1 => fxch k
  | 2 => if k == 0 then fpStatus (c.fsw.toUInt32 &&& FPF.C1) else ud   -- FNOP
  | 3 => -- FSTP1 (alias of FSTP ST(i))
    match c.stOpt 0 with
    | some a => fpResult a 0 k 1
    | none => fpResult F80.indefinite stackUnderflow k 1
  | _ =>
    match i.modrm with
    | 0xE0 => fpUnary fun a => (a.withNeg !a.neg, 0)
    | 0xE1 => fpUnary fun a => (a.withNeg false, 0)
    | 0xE4 => fpCompare (c.stOpt 0) (some (F80.zero false)) false false 0
    | 0xE5 => fxam
    | 0xE8 => fpPush F80.one 0
    | 0xE9 => fpConstLoad 1
    | 0xEA => fpConstLoad 2
    | 0xEB => fpConstLoad 0
    | 0xEC => fpConstLoad 3
    | 0xED => fpConstLoad 4
    | 0xEE => fpPush (F80.zero false) 0
    | 0xF4 => -- FXTRACT
      match c.stOpt 0 with
      | none => fpPush2Fault stackUnderflow
      | some a =>
        let ((ex, sg), fl) := a.xtract
        -- the stack overflow of the push (ST(7) in use) is detected before the operand's invalid,
        -- denormal and zero-divide exceptions (EPYC 7742, native `x87_exceptions`/`x87_random`: 22
        -- cases; with them unmasked the model used to report those instead)
        if !c.stEmpty 7 then fpPush2Fault (FPF.IE ||| FPF.SF ||| FPF.C1)
        else if fpUnmasked fl c.fcw then fpStatus fl
        else fpPush2 ex sg fl
    | 0xF5 | 0xF8 => -- FPREM1 / FPREM
      match c.stOpt 0, c.stOpt 1 with
      | some a, some b =>
        let ((r, q, done), fl) := F80.prem a b (i.modrm == 0xF5) cw
        fpStatus (if fpUnmasked fl c.fcw then fpStopped fl else fl)
        if !fpUnmasked fl c.fcw then
          modCpu (·.setSt 0 r)
          fpCC (if done then
                  (if q &&& 4 != 0 then 0x100 else 0) ||| (if q &&& 2 != 0 then 0x4000 else 0) |||
                  (if q &&& 1 != 0 then 0x200 else 0)
                else 0x400)
      | _, _ => fpResult F80.indefinite stackUnderflow 0
    | 0xF6 => fpStatus 0; modCpu fun c => c.setTop (c.ftop + 7)   -- FDECSTP
    | 0xF7 => fpStatus 0; modCpu fun c => c.setTop (c.ftop + 1)   -- FINCSTP
    | 0xFA => fpUnary fun a => a.sqrt (pcBits ((cw >>> 8) &&& 3)) cw
    | 0xFC => fpUnary fun a => a.roundInt cw
    | 0xFD => -- FSCALE
      match c.stOpt 0, c.stOpt 1 with
      | some a, some b => let (r, fl) := a.scale b cw; fpResult r fl 0
      | _, _ => fpResult F80.indefinite stackUnderflow 0
    | 0xF0 => fpUnary fun a => Trans.f2xm1 a cw
    | 0xF1 => fpBinPop fun x y => Trans.fyl2x x y cw
    | 0xF2 => fpTrig 2
    | 0xF3 => fpBinPop fun x y => Trans.fpatan x y cw
    | 0xF9 => fpBinPop fun x y => Trans.fyl2xp1 x y cw
    | 0xFB => fpTrig 3
    | 0xFE => fpTrig 0
    | 0xFF => fpTrig 1
    | _ => ud

/-- Arithmetic by `reg` field: 0 add, 1 mul, 2 com, 3 comp, 4 sub, 5 subr, 6 div, 7 divr, with
operands (x, y) meaning x op y. -/
def fpArithReg (r : Nat) (x y : Option F80) (dst : Nat) (pops : Nat) (extra : UInt32 := 0) : M Unit :=
  match r with
  | 0 => fpArith .add x y dst pops extra
  | 1 => fpArith .mul x y dst pops extra
  | 2 => fpCompare x y false false 0 extra
  | 3 => fpCompare x y false false 1 extra
  | 4 => fpArith .sub x y dst pops extra
  | 5 => fpArith .sub y x dst pops extra
  | 6 => fpArith .div x y dst pops extra
  | _ => fpArith .div y x dst pops extra

/-- Execute an ESC (D8..DF) instruction. -/
def x87 (i : Inst) : M Unit := do
  let ctl := fpControl i
  fpCheck (!ctl)
  if !ctl then fpNote i
  let c ← cpu
  let k := i.rm.toNat
  let r := i.reg.toNat
  if i.isMem then
    match i.op with
    | 0xD8 | 0xDA | 0xDC | 0xDE =>
      let (b, fl) ← fpMemOperand i
      fpArithReg r (c.stOpt 0) (some b) 0 0 fl
    | 0xD9 =>
      match r with
      | 0 => fpLoad i 0
      | 2 => fpStore i 0 false
      | 3 => fpStore i 0 true
      | 4 => fpLoadEnv i.opsz (!c.pe || c.vm86) i.seg (← fpEa i)
      | 5 =>
        let v ← fpRead i.seg (← fpEa i) 2
        modCpu fun c => { c with fcw := fcwLoad v.toUInt32 }
        let c ← cpu
        modCpu fun c => { c with fsw := if c.fsw.toUInt32 &&& ~~~c.fcw.toUInt32 &&& 0x3F != 0
                                         then c.fsw ||| 0x8080 else c.fsw &&& 0x7F7F }
        let _ := c
      | 6 =>
        let (v, n) := fpEnvBytes i.opsz (!c.pe || c.vm86) c
        fpWrite i.seg (← fpEa i) n v
        modCpu fun c => { c with fcw := c.fcw ||| 0x3F }
      | 7 => fpWrite i.seg (← fpEa i) 2 c.fcw.toNat
      | _ => ud
    | 0xDB =>
      match r with
      | 0 => fpLoad i 4
      | 1 => fpStore i 4 true true   -- FISTTP m32int (SSE3)
      | 2 => fpStore i 4 false
      | 3 => fpStore i 4 true
      | 5 => fpLoad i 2
      | 7 => fpStore i 2 true
      | _ => ud
    | 0xDD =>
      match r with
      | 0 => fpLoad i 1
      | 1 => fpStore i 5 true true   -- FISTTP m64int (SSE3)
      | 2 => fpStore i 1 false
      | 3 => fpStore i 1 true
      | 4 => -- FRSTOR
        let off ← fpEa i
        let w := if i.opsz == 4 then 4 else 2
        fpLoadEnv i.opsz (!c.pe || c.vm86) i.seg off
        let regs ← fpRead i.seg (off + (7 * w).toUInt32) 80
        modCpu fun c => Id.run do
          let mut c := c
          for j in [0:8] do
            let v := f80OfNat ((regs / 2^(80 * j)) % 2^80)
            let p := c.stIdx j
            c := { c with fpr := c.fpr.set! p v }
          return c
      | 6 => -- FNSAVE
        let off ← fpEa i
        let (env, n) := fpEnvBytes i.opsz (!c.pe || c.vm86) c
        let regs := (List.range 8).foldl (fun acc j => acc + f80ToNat (c.st j) * 2^(80 * j)) 0
        fpWrite i.seg off (n + 80) (env + regs * 2^(8 * n))
        fninit
      | 7 => fpWrite i.seg (← fpEa i) 2 c.fsw.toNat
      | _ => ud
    | _ => -- DF
      match r with
      | 0 => fpLoad i 3
      | 1 => fpStore i 3 true true   -- FISTTP m16int (SSE3)
      | 2 => fpStore i 3 false
      | 3 => fpStore i 3 true
      | 4 => fpLoad i 6
      | 5 => fpLoad i 5
      | 6 => fpStore i 6 true
      | 7 => fpStore i 5 true
      | _ => ud
  else
    match i.op with
    | 0xD8 => fpArithReg r (c.stOpt 0) (c.stOpt k) 0 0
    | 0xD9 => x87D9reg i
    | 0xDA =>
      if r < 4 then
        match c.stOpt 0, c.stOpt k with
        | some _, some b => fpStatus 0; if fcmovCond r c.eflags then modCpu (·.setSt 0 b)
        | _, _ => fpResult F80.indefinite stackUnderflow 0
      else if i.modrm == 0xE9 then fpCompare (c.stOpt 0) (c.stOpt 1) true false 2
      else ud
    | 0xDB =>
      if r < 4 then
        match c.stOpt 0, c.stOpt k with
        | some _, some b => fpStatus 0; if !fcmovCond r c.eflags then modCpu (·.setSt 0 b)
        | _, _ => fpResult F80.indefinite stackUnderflow 0
      else if r == 5 then fpCompare (c.stOpt 0) (c.stOpt k) true true 0
      else if r == 6 then fpCompare (c.stOpt 0) (c.stOpt k) false true 0
      else match i.modrm with
        | 0xE2 => modCpu fun c => { c with fsw := c.fsw &&& 0x7F00 }; setFerr false
        | 0xE3 => fninit
        | 0xE0 | 0xE1 | 0xE4 => pure ()
        | _ => ud
    | 0xDC =>
      -- ST(i) := ST(i) op ST(0); the sub/div pairs are reversed relative to D8
      let r' := if r ≥ 4 then r ^^^ 1 else r
      fpArithReg r' (c.stOpt k) (c.stOpt 0) k 0
    | 0xDD =>
      match r with
      | 0 => fpStatus 0; modCpu fun c => { c with fempty := c.fempty ||| ((1 : UInt8) <<< (c.stIdx k).toUInt8) }
      | 1 => fxch k
      | 2 | 3 =>
        match c.stOpt 0 with
        | some a => fpResult a 0 k (if r == 3 then 1 else 0)
        | none => fpResult F80.indefinite stackUnderflow k (if r == 3 then 1 else 0)
      | 4 => fpCompare (c.stOpt 0) (c.stOpt k) true false 0
      | 5 => fpCompare (c.stOpt 0) (c.stOpt k) true false 1
      | _ => ud
    | 0xDE =>
      if r == 2 then fpCompare (c.stOpt 0) (c.stOpt k) false false 1
      else if r == 3 then (if k == 1 then fpCompare (c.stOpt 0) (c.stOpt 1) false false 2 else ud)
      else
        let r' := if r ≥ 4 then r ^^^ 1 else r
        fpArithReg r' (c.stOpt k) (c.stOpt 0) k 1
    | _ => -- DF
      match r with
      | 0 => -- FFREEP
        fpStatus 0
        modCpu fun c => { c with fempty := c.fempty ||| ((1 : UInt8) <<< (c.stIdx k).toUInt8) }.fpop
      | 1 => fxch k
      | 2 | 3 =>
        match c.stOpt 0 with
        | some a => fpResult a 0 k 1
        | none => fpResult F80.indefinite stackUnderflow k 1
      | 4 => if k == 0 then setReg16Ax c.fsw.toUInt32 else ud
      | 5 => fpCompare (c.stOpt 0) (c.stOpt k) true true 1
      | 6 => fpCompare (c.stOpt 0) (c.stOpt k) false true 1
      | _ => ud
where
  setReg16Ax (v : UInt32) : M Unit := modCpu (·.wrReg 2 0 v)

/-- WAIT/FWAIT. -/
def fwait : M Unit := do
  let c ← cpu
  if c.cr0 &&& (CR0.TS ||| CR0.MP) == (CR0.TS ||| CR0.MP) then exc Vec.NM
  if c.fsw &&& 0x80 != 0 then fpPending

end X86
