import X64.Fpu
set_option maxHeartbeats 4000000
namespace X64
open Flag

def arithmetic (op : UInt8) (sz : Sz) (a b : UInt64) : M UInt64 := do
  let (r, f) := alu op sz a (b &&& sz.mask) (← flag CF)
  setFlags arith f.pack
  return r

def incDec (dec : Bool) (sz : Sz) (a : UInt64) : M UInt64 := do
  let (r, f) := if dec then subCore sz a 1 false else addCore sz a 1 false
  setFlags (arith &&& ~~~CF) f.pack
  return r

def shift (i : Inst) (count : UInt64) : M Unit := do
  let sz := bsz i
  let a ← rdE i sz true
  match shiftOp i.group sz a count (← flag CF) with
  | none => wrE i sz a
  | some (r, mask, f) => wrE i sz r; setFlags mask f

def imul (sz : Sz) (a b : UInt64) : UInt64 × Bool :=
  let p := toSInt sz a * toSInt sz b
  let lo := (p % (2^64 : Int)).toNat.toUInt64 &&& sz.mask
  (lo, toSInt sz lo != p)

def mulFlags (overflow : Bool) : M Unit := setFlags (CF ||| OF) (if overflow then CF ||| OF else 0)

def group3 (i : Inst) : M Unit := do
  let sz := bsz i
  let a ← rdE i sz (i.group == 2 || i.group == 3)
  match i.group with
  | 0 | 1 => setFlags arith (logicCore sz (a &&& i.imm)).2.pack
  | 2 => wrE i sz (~~~a &&& sz.mask)
  | 3 =>
    let (r, f) := subCore sz 0 a false
    wrE i sz r
    setFlags arith f.pack
  | 4 | 5 =>
    let acc ← rdReg sz 0
    let signed := i.group == 5
    let p : Int := if signed then toSInt sz acc * toSInt sz a else (mulWide sz acc a : Int)
    let bits := sz.bits.toNat
    let u := (p % (2 ^ (2 * bits) : Nat)).toNat
    let lo := u.toUInt64 &&& sz.mask
    let hi := (u / 2^bits).toUInt64 &&& sz.mask
    if sz == 1 then wrReg 2 0 u.toUInt64
    else wrReg sz 0 lo; wrReg sz 2 hi
    mulFlags (if signed then toSInt sz lo != p else hi != 0)
  | _ =>
    let bits := sz.bits.toNat
    let dividend ← if sz == 1 then pure (← rdReg 2 0).toNat
                    else pure ((← rdReg sz 0).toNat + (← rdReg sz 2).toNat * 2^bits)
    let result := if i.group == 6 then divU sz dividend a
      else
        let signed : Int := if dividend ≥ 2^(2*bits-1) then (dividend : Int) - (2^(2*bits) : Nat) else dividend
        divS sz signed (toSInt sz a)
    let some (q, r) := result | exc Vec.DE
    if sz == 1 then wrReg 2 0 ((q &&& 0xFF) ||| ((r &&& 0xFF) <<< 8))
    else wrReg sz 0 q; wrReg sz 2 r

/-- One REP iteration per architectural step, so faults restart at the instruction. -/
def stringOp (i : Inst) : M Unit := do
  let sz := bsz i
  let c ← cpu
  let count := c.rdReg i.adsz 1 true
  if i.rep != 0 && count == 0 then return
  let src := c.rdReg i.adsz 6 true
  let dst := c.rdReg i.adsz 7 true
  let seg := if i.segOvr == 0xFF then SegN.DS else i.segOvr
  let op := i.op &&& 0xFE
  if op == 0xA4 then wrMem SegN.ES dst sz.toUInt64 (← rdMem seg src sz.toUInt64)
  else if op == 0xAA then wrMem SegN.ES dst sz.toUInt64 (c.rdReg sz 0)
  else if op == 0xAC then wrReg sz 0 (← rdMem seg src sz.toUInt64)
  else
    let a ← if op == 0xA6 then rdMem seg src sz.toUInt64 else rdReg sz 0
    let b ← rdMem SegN.ES dst sz.toUInt64
    setFlags arith (subCore sz a b false).2.pack
  let delta := if c.flag DF then 0 - sz.toUInt64 else sz.toUInt64
  if op == 0xA4 || op == 0xA6 || op == 0xAC then wrReg i.adsz 6 (src + delta) true
  if op != 0xAC then wrReg i.adsz 7 (dst + delta) true
  if i.rep != 0 then
    wrReg i.adsz 1 (count - 1) true
    let zf ← flag ZF
    let again := count != 1 && (if op == 0xA6 || op == 0xAE then zf == (i.rep == 0xF3) else true)
    if again then modCpu fun c => { c with rip := c.rip - i.len }

/-- Bit-string operations use a signed bit index for memory operands. -/
def bitOp (i : Inst) (operation : UInt8) (index : UInt64) (immediate : Bool) : M Unit := do
  let sz := i.opsz
  let bitIndex := index &&& (sz.bits - 1)
  let mask : UInt64 := 1 <<< bitIndex
  let addr ← eaOff i
  let delta : UInt64 := if immediate then 0 else
    (((toSInt sz index / (sz.bits.toNat : Int)) * sz.toNat) % (2^64 : Int)).toNat.toUInt64
  let addr := addr + delta
  let old ← if i.isMem then rdMem i.seg addr sz.toUInt64 (operation != 0) else rdE i sz
  let new := if operation == 1 then old ||| mask else if operation == 2 then old &&& ~~~mask else old ^^^ mask
  if operation != 0 then
    if i.isMem then wrMem i.seg addr sz.toUInt64 new else wrE i sz new
  setFlags CF (if old &&& mask != 0 then CF else 0)

def shiftDouble (i : Inst) (left : Bool) (count : UInt64) : M Unit := do
  let sz := i.opsz
  let count := count &&& (if sz == 8 then 63 else 31)
  let dst ← rdE i sz true
  let src ← rdG i sz
  if count == 0 then wrE i sz dst; return
  if count > sz.bits then unsupported "SHLD/SHRD with architecturally undefined count"
  let result := (if left then (dst <<< count) ||| (src >>> (sz.bits - count))
                 else (dst >>> count) ||| (src <<< (sz.bits - count))) &&& sz.mask
  let carry := (if left then dst >>> (sz.bits - count) else dst >>> (count - 1)) &&& 1 != 0
  let f := { (logicCore sz result).2 with cf := carry, of := (result ^^^ dst) &&& sz.msb != 0 }
  wrE i sz result
  setFlags arith f.pack

def cpuid (leaf subleaf : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let _ := subleaf
  match leaf with
  | 0 => (1, 0x68747541, 0x444D4163, 0x69746E65) -- AuthenticAMD
  | 1 => (0xF00, 0, 0, 0x0700A179) -- FPU,PSE,TSC,MSR,PAE,CX8,PGE,CMOV,FXSR,SSE,SSE2
  | 0x80000000 => (0x80000008, 0, 0, 0)
  | 0x80000001 => (0, 0, 1, 0x24100800) -- SYSCALL, NX, 1 GiB pages, LM
  | 0x80000008 => (0x3028, 0, 0, 0) -- 40 physical, 48 virtual bits
  | _ => (0, 0, 0, 0)

def rdmsr (n : UInt64) : M UInt64 := do
  cplIs0
  let c ← cpu
  match n with
  | 0xC0000080 => return c.efer
  | 0xC0000081 => return c.star
  | 0xC0000082 => return c.lstar
  | 0xC0000083 => return c.cstar
  | 0xC0000084 => return c.sfmask
  | 0xC0000100 => return c.fsBase
  | 0xC0000101 => return c.gsBase
  | 0xC0000102 => return c.kernelGsBase
  | 0x10 => return (← getM).icount
  | 0x8B => return 0 -- No microcode patch is installed.
  | _ => gp 0

def wrmsr (n v : UInt64) : M Unit := do
  cplIs0
  match n with
  | 0xC0000080 =>
    if v &&& ~~~(0xD01 : UInt64) != 0 then gp 0
    let c ← cpu
    if c.cr0 &&& CR0.PG != 0 && (v ^^^ c.efer) &&& 0x100 != 0 then gp 0
    modCpu fun c => { c with efer := (v &&& ~~~(0x400 : UInt64)) ||| (c.efer &&& 0x400) }
  | 0xC0000081 => modCpu fun c => { c with star := v }
  | 0xC0000082 =>
    if !canonical v then gp 0
    modCpu fun c => { c with lstar := v }
  | 0xC0000083 =>
    if !canonical v then gp 0
    modCpu fun c => { c with cstar := v }
  | 0xC0000084 => modCpu fun c => { c with sfmask := v &&& 0xFFFFFFFF }
  | 0xC0000100 | 0xC0000101 | 0xC0000102 =>
    if !canonical v then gp 0
    modCpu fun c => if n == 0xC0000100 then { c with fsBase := v }
      else if n == 0xC0000101 then { c with gsBase := v } else { c with kernelGsBase := v }
  | _ => gp 0

def group7 (i : Inst) : M Unit := do
  if i.modrm == 0xF8 then
    cplIs0
    modCpu fun c => { c with gsBase := c.kernelGsBase, kernelGsBase := c.gsBase }
  else if i.modrm == 0xF9 then unsupported "RDTSCP is not advertised"
  else
    match i.group with
    | 0 | 1 =>
      needMem i
      let addr ← eaOff i
      let c ← cpu
      let base := if i.group == 0 then c.gdtBase else c.idtBase
      let limit := if i.group == 0 then c.gdtLimit else c.idtLimit
      let lin ← segAddr i.seg addr 10
      let _ ← translate lin .write (c.cpl == 3)
      let _ ← translate (lin + 9) .write (c.cpl == 3)
      wrMem i.seg addr 2 limit
      wrMem i.seg (addr + 2) 8 base
    | 2 | 3 =>
      cplIs0
      needMem i
      let addr ← eaOff i
      let limit ← rdMem i.seg addr 2
      let base ← rdMem i.seg (addr + 2) 8
      if !canonical base then gp 0
      modCpu fun c => if i.group == 2 then { c with gdtBase := base, gdtLimit := limit }
                     else { c with idtBase := base, idtLimit := limit }
    | 4 => wrE i (if i.isMem then 2 else i.opsz) (← cpu).cr0
    | 7 => cplIs0; needMem i; let _ ← segAddr i.seg (← eaOff i) 1; pure ()
    | _ => unsupported s!"system group 7 /{i.group}"

/-- The supported scalar long-mode instruction set. Unimplemented instructions stop;
they are never replaced by host execution or assumed no-ops. -/
def exec (i : Inst) : M Unit := do
  let op := i.op
  let sz := i.opsz
  let rex := i.rex != 0
  if simdOpcode op then simd i; return
  if 0xD8 ≤ op && op ≤ 0xDF then x87Control i; return
  if op < 0x40 && op &&& 7 ≤ 5 then
    let operation := ((op >>> 3) &&& 7).toUInt8
    let width := bsz i
    let form := op &&& 7
    if form < 2 then
      let r ← arithmetic operation width (← rdE i width (operation != 7)) (← rdG i width)
      if operation != 7 then wrE i width r
    else if form < 4 then
      let r ← arithmetic operation width (← rdG i width) (← rdE i width)
      if operation != 7 then wrG i width r
    else
      let r ← arithmetic operation width (← rdReg width 0) i.imm
      if operation != 7 then wrReg width 0 r
    return
  if op ≥ 0x50 && op ≤ 0x57 then push i.stackSize (← rdReg i.stackSize i.opcodeReg true); return
  if op ≥ 0x58 && op ≤ 0x5F then wrReg i.stackSize i.opcodeReg (← pop i.stackSize) true; return
  if op ≥ 0x70 && op ≤ 0x7F then
    if evalCC (← getFlags) (op &&& 15).toUInt8 then jumpTo ((← cpu).rip + sext 1 i.imm)
    return
  if op ≥ 0xB0 && op ≤ 0xBF then
    wrReg (if op < 0xB8 then 1 else sz) i.opcodeReg i.imm rex
    return
  if op ≥ 0x140 && op ≤ 0x14F then
    let v ← rdE i sz
    let old ← rdG i sz
    wrG i sz (if evalCC (← getFlags) (op &&& 15).toUInt8 then v else old)
    return
  if op ≥ 0x180 && op ≤ 0x18F then
    if evalCC (← getFlags) (op &&& 15).toUInt8 then jumpTo ((← cpu).rip + i.imm)
    return
  if op ≥ 0x190 && op ≤ 0x19F then
    wrE i 1 (b2u (evalCC (← getFlags) (op &&& 15).toUInt8))
    return
  match op with
  | 0x63 => wrG i sz (sext 4 (← rdE i 4))
  | 0x68 => push i.stackSize i.imm
  | 0x6A => push i.stackSize (sext 1 i.imm)
  | 0x69 | 0x6B =>
    let (r, ofl) := imul sz (← rdE i sz) (if op == 0x6B then sext 1 i.imm else i.imm)
    wrG i sz r
    mulFlags ofl
  | 0x80 | 0x81 | 0x83 =>
    let width := if op == 0x80 then 1 else sz
    let b := if op == 0x83 then sext 1 i.imm else i.imm
    let r ← arithmetic i.group width (← rdE i width (i.group != 7)) b
    if i.group != 7 then wrE i width r
  | 0x84 | 0x85 => setFlags arith (logicCore (bsz i) ((← rdE i (bsz i)) &&& (← rdG i (bsz i)))).2.pack
  | 0x86 | 0x87 =>
    let addr ← eaOff i
    let a ← rdE i (bsz i) true
    let b ← rdG i (bsz i)
    if i.isMem then wrMem i.seg addr (bsz i).toUInt64 b else wrE i (bsz i) b
    wrG i (bsz i) a
  | 0x88 | 0x89 => wrE i (bsz i) (← rdG i (bsz i))
  | 0x8A | 0x8B => wrG i (bsz i) (← rdE i (bsz i))
  | 0x8C =>
    if i.group > 5 then ud
    wrE i (if i.isMem then 2 else sz) ((← cpu).getSeg i.group).sel.toUInt64
  | 0x8D => needMem i; wrG i sz (← eaOff i)
  | 0x8E =>
    if i.group > 5 || i.group == SegN.CS then ud
    loadSeg i.group (← rdE i 2).toUInt16
    if i.group == SegN.SS then modCpu fun c => { c with shadow := true }
  | 0x8F =>
    if i.group != 0 then ud
    let v ← pop i.stackSize
    wrE i i.stackSize v
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 =>
    if op == 0x90 && i.opcodeReg == 0 then return
    let a ← rdReg sz 0
    let b ← rdReg sz i.opcodeReg true
    wrReg sz 0 b
    wrReg sz i.opcodeReg a true
  | 0x98 => wrReg sz 0 (sext (if sz == 8 then 4 else if sz == 4 then 2 else 1) (← getReg 0))
  | 0x99 => wrReg sz 2 (if (← rdReg sz 0) &&& sz.msb != 0 then sz.mask else 0)
  | 0x9C => push i.stackSize ((← getFlags) &&& ~~~(VM ||| RF))
  | 0x9D =>
    let c ← cpu
    let f ← pop i.stackSize
    let mask := (if sz == 2 then 0xFFFF else Flag.valid) &&& ~~~(VM ||| RF |||
      (if c.cpl > c.iopl then IF else 0) ||| (if c.cpl != 0 then IOPL else 0))
    setFlags mask f
  | 0x9E => setFlags (SF ||| ZF ||| AF ||| PF ||| CF) (((← getReg 0) >>> 8) &&& 0xFF)
  | 0x9F => wrReg 1 4 (((← getFlags) &&& 0xD5) ||| 2)
  | 0xA0 | 0xA1 | 0xA2 | 0xA3 =>
    let seg := if i.segOvr == 0xFF then SegN.DS else i.segOvr
    if op < 0xA2 then wrReg (bsz i) 0 (← rdMem seg i.imm (bsz i).toUInt64)
    else wrMem seg i.imm (bsz i).toUInt64 (← rdReg (bsz i) 0)
  | 0xA4 | 0xA5 | 0xA6 | 0xA7 | 0xAA | 0xAB | 0xAC | 0xAD | 0xAE | 0xAF => stringOp i
  | 0xA8 | 0xA9 => setFlags arith (logicCore (bsz i) ((← rdReg (bsz i) 0) &&& i.imm)).2.pack
  | 0xC0 | 0xC1 => shift i i.imm
  | 0xC2 | 0xC3 =>
    jumpTo (← pop 8)
    if op == 0xC2 then modCpu fun c => { c with rsp := c.rsp + i.imm }
  | 0xC6 | 0xC7 =>
    if i.group != 0 then ud
    wrE i (bsz i) i.imm
  | 0xC9 =>
    setReg 4 (← getReg 5)
    wrReg i.stackSize 5 (← pop i.stackSize)
  | 0xCC => deliver Vec.BP none true false
  | 0xCD => deliver i.imm.toUInt8 none true false
  | 0xCA | 0xCB => farReturn sz (if op == 0xCA then i.imm else 0)
  | 0xCF => if sz == 8 then iret else unsupported "IRET without REX.W"
  | 0xD0 | 0xD1 => shift i 1
  | 0xD2 | 0xD3 => shift i ((← getReg 1) &&& 0xFF)
  | 0xE0 | 0xE1 | 0xE2 | 0xE3 =>
    let n ← rdReg i.adsz 1 true
    let next := (n - 1) &&& i.adsz.mask
    if op != 0xE3 then wrReg i.adsz 1 next true
    let zf ← flag ZF
    let take := if op == 0xE3 then n == 0 else next != 0 &&
      (if op == 0xE0 then !zf else if op == 0xE1 then zf else true)
    if take then jumpTo ((← cpu).rip + sext 1 i.imm)
  | 0xE4 | 0xE5 | 0xE6 | 0xE7 | 0xEC | 0xED | 0xEE | 0xEF =>
    let c ← cpu
    if c.cpl > c.iopl then gp 0 -- TSS I/O bitmap support is pending
    let port := (if op < 0xE8 then i.imm &&& 0xFF else c.rdx &&& 0xFFFF).toUInt32
    let width : Sz := if op &&& 1 == 0 then 1 else if sz == 2 then 2 else 4
    if op &&& 2 == 0 then wrReg width 0 (← portIn port width)
    else portOut port width (← rdReg width 0)
  | 0xE8 =>
    let rip := (← cpu).rip
    let dest := rip + i.imm
    if !canonical dest then gp 0
    push 8 rip
    jumpTo dest
  | 0xE9 | 0xEB => jumpTo ((← cpu).rip + (if op == 0xEB then sext 1 i.imm else i.imm))
  | 0xF4 => cplIs0; modCpu fun c => { c with halted := true }
  | 0xF5 => setFlags CF ((← getFlags) ^^^ CF)
  | 0xF6 | 0xF7 => group3 i
  | 0xF8 => setFlags CF 0
  | 0xF9 => setFlags CF CF
  | 0xFA | 0xFB =>
    let c ← cpu
    if c.cpl > c.iopl then gp 0
    if op == 0xFB && !c.flag IF then modCpu fun c => { c with shadow := true }
    setFlags IF (if op == 0xFB then IF else 0)
  | 0xFC => setFlags DF 0
  | 0xFD => setFlags DF DF
  | 0xFE | 0xFF =>
    if i.group < 2 then wrE i (if op == 0xFE then 1 else sz) (← incDec (i.group == 1) (if op == 0xFE then 1 else sz) (← rdE i (if op == 0xFE then 1 else sz) true))
    else if op == 0xFE then ud
    else if i.group == 2 || i.group == 4 then
      let t ← rdE i 8
      if !canonical t then gp 0
      if i.group == 2 then push 8 (← cpu).rip
      jumpTo t
    else if i.group == 6 then push i.stackSize (← rdE i i.stackSize)
    else if i.group == 3 || i.group == 5 then
      needMem i
      let addr ← eaOff i
      let ip ← rdMem i.seg addr 8
      let sel ← rdMem i.seg (addr+8) 2
      farTransfer sel.toUInt16 ip (i.group == 3)
    else ud
  | 0x100 =>
    match i.group with
    | 0 => wrE i (if i.isMem then 2 else sz) (← cpu).ldtr.sel.toUInt64
    | 1 => wrE i (if i.isMem then 2 else sz) (← cpu).tr.sel.toUInt64
    | 2 | 3 => loadSystemSeg (← rdE i 2).toUInt16 (i.group == 3)
    | _ => unsupported "VERR/VERW"
  | 0x101 => group7 i
  | 0x105 => syscall
  | 0x107 => if sz == 8 then sysret else unsupported "SYSRET to compatibility mode"
  | 0x106 => cplIs0; modCpu fun c => { c with cr0 := c.cr0 &&& ~~~CR0.TS }
  | 0x108 | 0x109 => cplIs0
  | 0x10B => ud
  | 0x10D => needMem i -- PREFETCH/PREFETCHW: advisory, no architectural data access.
  | 0x118 | 0x119 | 0x11A | 0x11B | 0x11C | 0x11D | 0x11E | 0x11F => pure ()
  | 0x120 =>
    cplIs0
    let c ← cpu
    let v ← match i.reg with
      | 0 => pure c.cr0 | 2 => pure c.cr2 | 3 => pure c.cr3 | 4 => pure c.cr4 | _ => ud
    setReg i.rm v
  | 0x121 | 0x123 =>
    cplIs0
    let c ← cpu
    let mut dr := i.reg
    if dr > 7 then ud
    if dr == 4 || dr == 5 then
      if c.cr4 &&& 8 != 0 then ud
      dr := dr + 2
    if c.dr7 &&& 0x2000 != 0 then
      modCpu fun c => { c with dr6 := c.dr6 ||| 0x2000, dr7 := c.dr7 &&& ~~~(0x2000 : UInt64) }
      exc Vec.DB
    if op == 0x121 then
      setReg i.rm (match dr with
        | 0 => c.dr0 | 1 => c.dr1 | 2 => c.dr2 | 3 => c.dr3 | 6 => c.dr6 | _ => c.dr7)
    else
      let v ← getReg i.rm
      if dr < 4 && !canonical v then gp 0
      if dr ≥ 6 && v >>> 32 != 0 then gp 0
      if dr == 7 && v &&& 0xFF != 0 then unsupported "enabling hardware breakpoints"
      modCpu fun c => match dr with
        | 0 => { c with dr0 := v } | 1 => { c with dr1 := v }
        | 2 => { c with dr2 := v } | 3 => { c with dr3 := v }
        | 6 => { c with dr6 := (v &&& 0xE00F) ||| 0xFFFF0FF0 }
        | _ => { c with dr7 := (v &&& 0xFFFF23FF) ||| 0x400 }
  | 0x122 =>
    cplIs0
    let v ← getReg i.rm
    match i.reg with
    | 0 =>
      if v &&& (CR0.PG ||| CR0.PE) != CR0.PG ||| CR0.PE then unsupported "leaving long mode"
      modCpu fun c => { c with cr0 := v }
    | 2 => modCpu fun c => { c with cr2 := v }
    | 3 =>
      if v &&& 0xFFFFFF0000000000 != 0 then gp 0
      modCpu fun c => { c with cr3 := v }
    | 4 =>
      if v &&& 0x20 == 0 then gp 0
      if v &&& ~~~(0x6FF : UInt64) != 0 then unsupported "unimplemented CR4 feature"
      modCpu fun c => { c with cr4 := v }
    | _ => ud
  | 0x130 => wrmsr ((← getReg 1) &&& 0xFFFFFFFF) (((← getReg 0) &&& 0xFFFFFFFF) ||| ((← getReg 2) <<< 32))
  | 0x132 =>
    let v ← rdmsr ((← getReg 1) &&& 0xFFFFFFFF)
    wrReg 4 0 v
    wrReg 4 2 (v >>> 32)
  | 0x131 =>
    let c ← cpu
    if c.cr4 &&& CR4.TSD != 0 && c.cpl != 0 then gp 0
    let t := (← getM).icount
    wrReg 4 0 t
    wrReg 4 2 (t >>> 32)
  | 0x1AE => fxInstruction i
  | 0x177 => checkFpu; modCpu fun c => { c with fpTag := 0xFFFF }
  | 0x9B =>
    let c ← cpu
    if c.cr0 &&& (CR0.TS ||| CR0.MP) == CR0.TS ||| CR0.MP then exc Vec.NM
    if c.fpStatus &&& 0x80 != 0 then exc 16
  | 0x1A2 =>
    let (a,b,c,d) := cpuid ((← getReg 0) &&& 0xFFFFFFFF) ((← getReg 1) &&& 0xFFFFFFFF)
    wrReg 4 0 a; wrReg 4 3 b; wrReg 4 1 c; wrReg 4 2 d
  | 0x1A3 | 0x1AB | 0x1B3 | 0x1BB =>
    bitOp i (if op == 0x1A3 then 0 else if op == 0x1AB then 1 else if op == 0x1B3 then 2 else 3) (← rdG i sz) false
  | 0x1BA =>
    if i.group < 4 then ud
    bitOp i (i.group - 4) i.imm true
  | 0x1A4 | 0x1A5 | 0x1AC | 0x1AD =>
    let count ← if op &&& 1 == 0 then pure i.imm else rdReg 1 1
    shiftDouble i (op < 0x1AC) count
  | 0x1A0 | 0x1A8 => push i.stackSize ((← cpu).getSeg (if op == 0x1A0 then SegN.FS else SegN.GS)).sel.toUInt64
  | 0x1A1 | 0x1A9 =>
    let v ← pop i.stackSize
    loadSeg (if op == 0x1A1 then SegN.FS else SegN.GS) v.toUInt16
  | 0x1AF =>
    let (r, ofl) := imul sz (← rdG i sz) (← rdE i sz)
    wrG i sz r
    mulFlags ofl
  | 0x1B0 | 0x1B1 =>
    let width := bsz i
    let a ← rdReg width 0
    let b ← rdE i width true
    let src ← rdG i width
    if i.isMem || a == b then wrE i width (if a == b then src else b)
    setFlags arith (subCore width a b false).2.pack
    if a != b then wrReg width 0 b
  | 0x1B6 | 0x1B7 | 0x1BE | 0x1BF =>
    let width : Sz := if op &&& 1 == 0 then 1 else 2
    let v ← rdE i width
    wrG i sz (if op ≥ 0x1BE then sext width v else v)
  | 0x1BC | 0x1BD =>
    let v ← rdE i sz
    if v == 0 then setFlags ZF ZF
    else
      setFlags ZF 0
      let mut result : UInt64 := 0
      for k in [0:sz.bits.toNat] do
        let idx := if op == 0x1BC then sz.bits.toNat - 1 - k else k
        if v >>> idx.toUInt64 &&& 1 != 0 then result := idx.toUInt64
      wrG i sz result
  | 0x1C0 | 0x1C1 =>
    let addr ← eaOff i
    let width := bsz i
    let a ← rdE i width true
    let b ← rdG i width
    let (r, f) := addCore width a b false
    if i.isMem then
      wrMem i.seg addr width.toUInt64 r
      wrG i width a
    else
      wrG i width a
      wrE i width r
    setFlags arith f.pack
  | 0x1C7 =>
    if i.group != 1 then ud
    needMem i
    if sz == 8 then unsupported "CMPXCHG16B is not advertised"
    let addr ← eaOff i
    let old ← rdMem i.seg addr 8 true
    let c ← cpu
    let expected := (c.rax &&& 0xFFFFFFFF) ||| (c.rdx <<< 32)
    let replacement := (c.rbx &&& 0xFFFFFFFF) ||| (c.rcx <<< 32)
    wrMem i.seg addr 8 (if expected == old then replacement else old)
    setFlags ZF (if expected == old then ZF else 0)
    if expected != old then wrReg 4 0 old; wrReg 4 2 (old >>> 32)
  | 0x1C8 | 0x1C9 | 0x1CA | 0x1CB | 0x1CC | 0x1CD | 0x1CE | 0x1CF =>
    if sz == 2 then unsupported "BSWAP with undefined 16-bit operand size"
    let v ← rdReg sz i.opcodeReg true
    let mut r := 0
    for k in [0:sz.toNat] do r := (r <<< 8) ||| ((v >>> (k.toUInt64 * 8)) &&& 0xFF)
    wrReg sz i.opcodeReg r true
  | 0x06 | 0x07 | 0x0E | 0x16 | 0x17 | 0x1E | 0x1F | 0x27 | 0x2F | 0x37 | 0x3F |
    0x60 | 0x61 | 0x62 | 0x82 | 0x9A | 0xCE | 0xD4 | 0xD5 | 0xD6 | 0xEA => ud
  | _ => unsupported s!"opcode {op}, ModRM {i.modrm}, operand size {sz}"

end X64
