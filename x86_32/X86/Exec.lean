import X86.Decode
import X86.Alu
import X86.Sys
import X86.Fpu
import X86.Simd
import X86.Cpuid
/-!
# Instruction semantics

`exec i` executes a decoded instruction. On entry EIP already points to the next
instruction (`execInstr` advances it before calling `exec`). Most faults roll CPU
registers back; POPA retains the general-register loads completed before a fault.
Each individual memory write checks its whole range before committing, while
multi-write instructions can retain earlier stores when a later access faults.
-/
namespace X86
open Flag

/-! ## Operand access -/

@[inline] def eaOff (i : Inst) : M UInt32 := fun m =>
  let c := m.cpu
  let b := if i.base < 8 then c.getReg i.base else 0
  let x := if i.index < 8 then c.getReg i.index <<< i.scale.toUInt32 else 0
  let a := b + x + i.disp
  .ok (if i.adsz == 2 then a &&& 0xFFFF else a) m

@[inline] def rdE (i : Inst) (sz : Sz) : M UInt32 := do
  if i.isMem then rdMem i.seg (← eaOff i) sz.toUInt32 else rdReg sz i.rm

@[inline] def wrE (i : Inst) (sz : Sz) (v : UInt32) : M Unit := do
  if i.isMem then wrMem i.seg (← eaOff i) sz.toUInt32 v else wrReg sz i.rm v

/-- Read-modify-write of the ModRM operand; `f` returns the value to write back, if any. -/
@[inline] def rmwE (i : Inst) (sz : Sz) (f : UInt32 → M (Option UInt32)) (write : Bool := true) : M Unit := do
  if i.isMem then
    let off ← eaOff i
    let v ← rdMem i.seg off sz.toUInt32 write
    match ← f v with
    | some r => wrMem i.seg off sz.toUInt32 r
    | none => pure ()
  else
    let v ← rdReg sz i.rm
    match ← f v with
    | some r => wrReg sz i.rm r
    | none => pure ()

@[inline] def needMem (i : Inst) : M Unit := if i.isMem then pure () else ud

/-- Byte operand for even opcodes, operand size otherwise. -/
@[inline] def bsz (i : Inst) : Sz := if i.op &&& 1 == 0 then 1 else i.opsz

@[inline] def cplIs0 : M Unit := do if (← getCpl) != 0 then gp 0

/-! ## Control transfer helpers -/

def jumpTo (opsz : Sz) (t : UInt32) : M Unit := do
  let t := if opsz == 2 then t &&& 0xFFFF else t
  let c ← cpu
  if t > c.cs.limit then gp 0
  setEip t

@[inline] def jumpRel (i : Inst) (rel : UInt32) : M Unit := do
  jumpTo i.opsz ((← getEip) + rel)

/-! ## Arithmetic helpers -/

@[inline] def doAlu (op : UInt8) (sz : Sz) (a b : UInt32) : M (Option UInt32) := do
  let f ← getFlags
  let (r, fl) := alu op sz a b (f &&& CF != 0)
  setFlags arith fl
  return (if op == 7 then none else some r)

def aluEG (op : UInt8) (i : Inst) : M Unit := do
  let sz := bsz i
  rmwE i sz (write := op != 7) fun a => do doAlu op sz a (← rdReg sz i.reg)

def aluGE (op : UInt8) (i : Inst) : M Unit := do
  let sz := bsz i
  let b ← rdE i sz
  let a ← rdReg sz i.reg
  if let some r ← doAlu op sz a b then wrReg sz i.reg r

def aluAI (op : UInt8) (i : Inst) : M Unit := do
  let sz := bsz i
  let a ← rdReg sz 0
  if let some r ← doAlu op sz a (i.imm &&& sz.mask) then wrReg sz 0 r

def incDec (dec : Bool) (sz : Sz) (a : UInt32) : M UInt32 := do
  let (r, fl) := if dec then subF sz a 1 0 else addF sz a 1 0
  setFlags (arith &&& ~~~CF) fl
  return r

@[inline] def sext64 (sz : Sz) (x : UInt32) : UInt64 :=
  let s := sext sz x
  if s &&& 0x80000000 != 0 then s.toUInt64 ||| 0xFFFFFFFF00000000 else s.toUInt64

/-- Signed multiply of two `sz`-sized values; returns the 2×`sz` product (as 64 bits) and overflow flag. -/
def imulCore (sz : Sz) (a b : UInt32) : UInt64 × Bool :=
  let p := sext64 sz a * sext64 sz b
  let lo := p.toUInt32 &&& sz.mask
  (p, sext64 sz lo != p)

def setMulFlags (sz : Sz) (ovf : Bool) (lo : UInt32) : M Unit :=
  setFlags arith (szp sz lo ||| (if ovf then CF ||| OF else 0))

def grp3 (i : Inst) : M Unit := do
  let sz := bsz i
  match i.reg with
  | 0 | 1 => -- TEST
    let a ← rdE i sz
    setFlags arith (logicF sz (a &&& i.imm &&& sz.mask)).2
  | 2 => rmwE i sz fun a => pure (some (~~~a &&& sz.mask))
  | 3 => rmwE i sz fun a => do
      let (r, fl) := subF sz 0 a 0
      setFlags arith fl
      return some r
  | 4 => -- MUL
    let b ← rdE i sz
    if sz == 1 then
      let r := ((← rdReg 1 0) * b) &&& 0xFFFF
      wrReg 2 0 r
      setMulFlags 1 (r >>> 8 != 0) (r &&& 0xFF)
    else if sz == 2 then
      let r := (← rdReg 2 0) * b
      wrReg 2 0 r
      wrReg 2 2 (r >>> 16)
      setMulFlags 2 (r >>> 16 != 0) (r &&& 0xFFFF)
    else
      let r := (← getReg 0).toUInt64 * b.toUInt64
      setReg 0 r.toUInt32
      setReg 2 (r >>> 32).toUInt32
      setMulFlags 4 (r >>> 32 != 0) r.toUInt32
  | 5 => -- IMUL (one operand)
    let b ← rdE i sz
    let a ← rdReg sz 0
    let (p, ovf) := imulCore sz a b
    if sz == 1 then wrReg 2 0 p.toUInt32
    else if sz == 2 then
      wrReg 2 0 p.toUInt32
      wrReg 2 2 (p.toUInt32 >>> 16)
    else
      setReg 0 p.toUInt32
      setReg 2 (p >>> 32).toUInt32
    setMulFlags sz ovf (p.toUInt32 &&& sz.mask)
  | 6 => -- DIV
    let b ← rdE i sz
    let a : UInt64 ←
      if sz == 1 then pure (← rdReg 2 0).toUInt64
      else if sz == 2 then pure ((← rdReg 2 0) ||| ((← rdReg 2 2) <<< 16)).toUInt64
      else pure ((← getReg 0).toUInt64 ||| ((← getReg 2).toUInt64 <<< 32))
    let some (q, r) := divU sz a b | exc Vec.DE
    if sz == 1 then wrReg 2 0 (q ||| (r <<< 8))
    else
      wrReg sz 0 q
      wrReg sz 2 r
  | _ => -- IDIV
    let b ← rdE i sz
    let (a, w) : Int × Nat ←
      if sz == 1 then pure (toSInt 2 (← rdReg 2 0), 8)
      else if sz == 2 then pure (toSInt 4 ((← rdReg 2 0) ||| ((← rdReg 2 2) <<< 16)), 16)
      else
        let v := (← getReg 0).toUInt64 ||| ((← getReg 2).toUInt64 <<< 32)
        pure (if v >>> 63 != 0 then (v.toNat : Int) - (2^64 : Nat) else (v.toNat : Int), 32)
    let some (q, r) := divS w a (toSInt sz b) | exc Vec.DE
    let qu := (q % (2^32 : Int)).toNat.toUInt32 &&& sz.mask
    let ru := (r % (2^32 : Int)).toNat.toUInt32 &&& sz.mask
    if sz == 1 then wrReg 2 0 (qu ||| (ru <<< 8))
    else
      wrReg sz 0 qu
      wrReg sz 2 ru

def shiftGrp (i : Inst) (cnt : UInt32) : M Unit := do
  let sz := bsz i
  let f ← getFlags
  -- a zero count changes nothing, but the destination is still written back (RMW)
  rmwE i sz fun a =>
    match shiftOp i.reg sz a cnt (f &&& CF != 0) with
    | some (r, mask, fl) => do setFlags mask fl; return some r
    | none => return some a

def shiftD (i : Inst) (left : Bool) (cnt : UInt32) : M Unit := do
  let sz := i.opsz
  let src ← rdReg sz i.reg
  rmwE i sz fun a =>
    match shiftDouble left sz a src cnt with
    | some (r, fl) => do setFlags arith fl; return some r
    | none => return some a

/-- Bit test family: kind 0 BT, 1 BTS, 2 BTR, 3 BTC. -/
def bitOp (i : Inst) (kind : UInt8) (bitoff : UInt32) (immForm : Bool) : M Unit := do
  let sz := i.opsz
  let bits := sz.bits
  let b := bitoff &&& (bits - 1)
  let apply := fun (v : UInt32) => do
    let cf := (v >>> b) &&& 1 != 0
    setFlags CF (if cf then CF else 0)
    let m := (1 : UInt32) <<< b
    return (match kind with
      | 1 => some (v ||| m)
      | 2 => some (v &&& ~~~m)
      | 3 => some (v ^^^ m)
      | _ => none)
  if !i.isMem then
    let v ← rdReg sz i.rm
    if let some r ← apply v then wrReg sz i.rm r
  else
    let ea ← eaOff i
    let adj : UInt32 :=
      if immForm then 0
      else if sz == 4 then
        let s := if bitoff &&& 0x80000000 != 0 then (bitoff >>> 5) ||| 0xF8000000 else bitoff >>> 5
        s <<< 2
      else
        let w := sext 2 bitoff
        let s := if w &&& 0x80000000 != 0 then (w >>> 4) ||| 0xF0000000 else w >>> 4
        s <<< 1
    let off := ea + adj
    let off := if i.adsz == 2 then off &&& 0xFFFF else off
    let v ← rdMem i.seg off sz.toUInt32 (kind != 0)
    if let some r ← apply v then wrMem i.seg off sz.toUInt32 r

/-! ## Flags instructions -/

def popf (opsz : Sz) : M Unit := do
  let c ← cpu
  if c.vm86 && c.iopl < 3 then gp 0
  let v ← pop opsz
  let mut mask : UInt32 := CF ||| PF ||| AF ||| ZF ||| SF ||| TF ||| DF ||| OF ||| NT
  if opsz == 4 then mask := mask ||| AC ||| ID
  if c.cpl == 0 then mask := mask ||| IOPL ||| IF
  else if c.cpl ≤ c.iopl then mask := mask ||| IF
  modCpu fun c => { c with eflags := ((c.eflags &&& ~~~mask) ||| (v &&& mask)) ||| 2 }

/-! ## String instructions -/

/-- Kinds: 0 MOVS, 1 CMPS, 2 STOS, 3 LODS, 4 SCAS, 5 INS, 6 OUTS. -/
def ioCheck (port : UInt32) (sz : Sz) : M Unit := do
  let c ← cpu
  if c.pe && (c.cpl > c.iopl || c.vm86) then
    let tr := c.tr
    if tr.typ &&& 8 == 0 || tr.limit < 0x67 then gp 0
    let base ← sysRd (tr.base + 0x66) 2
    let off := base + port / 8
    if off + 1 > tr.limit then gp 0
    let bm ← sysRd (tr.base + off) 2
    if bm &&& ((((1 : UInt32) <<< sz.toUInt32) - 1) <<< (port &&& 7)) != 0 then gp 0

/-- One iteration of a string instruction. Returns `false` if a REPE/REPNE condition ends the loop. -/
@[inline] def strIter (i : Inst) (kind : UInt8) (sz : Sz) : M Bool := do
  let c ← cpu
  let a32 := i.adsz == 4
  let n := sz.toUInt32
  let si := if a32 then c.esi else c.esi &&& 0xFFFF
  let di := if a32 then c.edi else c.edi &&& 0xFFFF
  let d : UInt32 := if c.eflags &&& DF != 0 then 0 - n else n
  let src := if i.segOvr != 0xFF then i.segOvr else SegN.DS
  let upd := fun (r : UInt32) => if a32 then r + d else (r &&& 0xFFFF0000) ||| ((r + d) &&& 0xFFFF)
  match kind with
  | 0 =>
    let v ← rdMem src si n
    wrMem SegN.ES di n v
    modCpu fun c => { c with esi := upd c.esi, edi := upd c.edi }
    return true
  | 1 =>
    let a ← rdMem src si n
    let b ← rdMem SegN.ES di n
    setFlags arith (subF sz a b 0).2
    modCpu fun c => { c with esi := upd c.esi, edi := upd c.edi }
    let zf := (← getFlags) &&& ZF != 0
    return (if i.rep == 0xF3 then zf else if i.rep == 0xF2 then !zf else true)
  | 2 =>
    wrMem SegN.ES di n (c.rdReg sz 0)
    modCpu fun c => { c with edi := upd c.edi }
    return true
  | 3 =>
    let v ← rdMem src si n
    modCpu fun c => { (c.wrReg sz 0 v) with esi := upd c.esi }
    return true
  | 4 =>
    let b ← rdMem SegN.ES di n
    setFlags arith (subF sz (c.rdReg sz 0) b 0).2
    modCpu fun c => { c with edi := upd c.edi }
    let zf := (← getFlags) &&& ZF != 0
    return (if i.rep == 0xF3 then zf else if i.rep == 0xF2 then !zf else true)
  | 5 =>
    let port := c.edx &&& 0xFFFF
    ioCheck port sz
    let _ ← translate (← segAddr SegN.ES di n true) true (c.cpl == 3)
    let v ← portIn port sz
    wrMem SegN.ES di n v
    modCpu fun c => { c with edi := upd c.edi }
    return true
  | _ =>
    let port := c.edx &&& 0xFFFF
    ioCheck port sz
    let v ← rdMem src si n
    portOut port sz v
    modCpu fun c => { c with esi := upd c.esi }
    return true

/-- Maximum iterations of a REP string instruction per step (interrupts are
recognised between steps; EIP stays on the instruction until it completes). -/
def repChunk : Nat := 4096

def stringOp (i : Inst) (kind : UInt8) : M Unit := do
  let sz := bsz i
  if i.rep == 0 then
    let _ ← strIter i kind sz
    return
  let a32 := i.adsz == 4
  let cnt := fun (c : Cpu) => if a32 then c.ecx else c.ecx &&& 0xFFFF
  let decCnt := fun (c : Cpu) =>
    if a32 then { c with ecx := c.ecx - 1 }
    else { c with ecx := (c.ecx &&& 0xFFFF0000) ||| ((c.ecx - 1) &&& 0xFFFF) }
  let start := (← getEip) - i.len
  let start := if (← cpu).cs.big then start else start &&& 0xFFFF
  -- Single-step traps, debug breakpoints and TSO observe each REP iteration separately.
  let chunk := if (← getM).tso.isSome || (← flag TF) || (← cpu).bpOn then 1 else repChunk
  let mut k := 0
  repeat
    if cnt (← cpu) == 0 then break
    if k ≥ chunk then
      -- interrupted between iterations: RF suppresses instruction breakpoints on resumption
      setEip start
      setFlags RF RF
      break
    -- A fault after the first iteration commits the completed iterations and
    -- restarts the instruction, which then raises the fault from a consistent state.
    let r ← if k == 0 then some <$> strIter i kind sz
            else tryCatch (some <$> strIter i kind sz) (fun _ => pure none)
    match r with
    | none =>
      setEip start
      break
    | some cont =>
      modCpu decCnt
      k := k + 1
      if !cont then break
  modM fun m => { m with icount := m.icount + k.toUInt64 }

/-! ## BCD -/

def daaDas (sub : Bool) : M Unit := do
  let c ← cpu
  let al := c.eax &&& 0xFF
  let cf := c.eflags &&& CF != 0
  let af := c.eflags &&& AF != 0
  let (al1, af1, cf1) :=
    if (al &&& 0xF) > 9 || af then
      (if sub then (al - 6) &&& 0xFF else (al + 6) &&& 0xFF, true,
       cf || (if sub then al < 6 else al + 6 > 0xFF))
    else (al, false, cf)
  let (al2, cf2) :=
    if al > 0x99 || cf then ((if sub then al1 - 0x60 else al1 + 0x60) &&& 0xFF, true)
    else (al1, if sub then cf1 else false)
  let cf2 := if sub then cf2 || cf1 else cf2
  wrReg 1 0 al2
  setFlags arith (szp 1 al2 ||| (if af1 then AF else 0) ||| (if cf2 then CF else 0))

def aaaAas (sub : Bool) : M Unit := do
  let c ← cpu
  let al := c.eax &&& 0xFF
  if (al &&& 0xF) > 9 || c.eflags &&& AF != 0 then
    -- SDM: AAA: AX := AX + 106H;  AAS: AX := AX - 6; AH := AH - 1
    let ax := c.eax &&& 0xFFFF
    let ax := if sub then (ax - 6 - 0x100) &&& 0xFFFF else (ax + 0x106) &&& 0xFFFF
    wrReg 2 0 (ax &&& 0xFF0F)
    setFlags (AF ||| CF) (AF ||| CF)
  else
    wrReg 1 0 (al &&& 0xF)
    setFlags (AF ||| CF) 0

/-! ## Model-specific registers

RDMSR/WRMSR look an MSR up in `Dispatch.msr?`: first `coreMsr?` (below), then the `msr?` hook of
every extension module (`X86/Ext/*.lean`). -/

/-- What RDMSR and WRMSR do with one MSR (after the CPL check; an MSR without an `MsrImpl` is #GP(0)). -/
structure MsrImpl where
  rd : M UInt64
  wr : UInt64 → M Unit

/-- An MSR kept in `Cpu.msrs` (reads 0 until written); WRMSR stores `v &&& mask` (mask 0: the
write is accepted and the MSR reads 0). -/
def MsrImpl.stored (n : UInt32) (mask : UInt64) : MsrImpl where
  rd := do return (((← cpu).msrs.find? (·.1 == n)).map (·.2)).getD 0
  wr v := modCpu fun c => { c with msrs := (n, v &&& mask) :: c.msrs.filter (·.1 != n) }

/-- MSRs of the core model kept in `Cpu.msrs`, with their write masks: 0x17 platform id
(read-only), 0x8B microcode revision, 0xC1/0xC2 performance counters (40 bits), 0x186/0x187 event
selects, 0x1D9 debug control. -/
def msrInfo (n : UInt32) : Option UInt64 :=
  match n with
  | 0x17 => some 0
  | 0x8B => some 0xFFFFFFFFFFFFFFFF
  | 0xC1 | 0xC2 => some 0xFFFFFFFFFF
  | 0x186 | 0x187 => some 0xFFFFFFFF
  | 0x1D9 => some 0x7F
  | _ => none

/-- IA32_EFER: WRMSR accepts `Cpuid.eferWritable` and flushes the TLB. LMA is read-only: the value
written must equal it, and LME cannot change while paging is enabled (`LongMode.eferOk`). -/
def eferMsr : MsrImpl where
  rd := do return (← cpu).efer.toUInt64
  wr v := do
    if v &&& ~~~(Cpuid.eferWritable ||| EFER.LMA).toUInt64 != 0 then gp 0
    if !LongMode.eferOk (← cpu) v.toUInt32 then gp 0
    modCpu fun c => { c with efer := v.toUInt32 }
    flushTlbAll

/-- IA32_APIC_BASE: base, global enable (bit 11), x2APIC mode (bit 10), boot processor (bit 8); the
rules are `Machine.apicBaseWr` (SMP workstream, `X86/Io.lean`). -/
def apicBaseMsr : MsrImpl where
  rd := do return (← getM).apicBaseRd
  wr v := do
    match (← getM).apicBaseWr v with
    | some m => set m
    | none => gp 0

/-- The MSRs of the core model. -/
def coreMsr? (n : UInt32) : Option MsrImpl :=
  if n == EFER.msr then some eferMsr
  else if n == 0x1B then some apicBaseMsr
  else (msrInfo n).map (MsrImpl.stored n)

/-- RDMSR of MSR `n`, looked up with `look`. -/
def rdmsrWith (look : UInt32 → Option MsrImpl) (n : UInt32) : M UInt64 := do
  cplIs0
  match look n with
  | some m => m.rd
  | none => gp 0

/-- WRMSR of MSR `n`, looked up with `look`. -/
def wrmsrWith (look : UInt32 → Option MsrImpl) (n : UInt32) (v : UInt64) : M Unit := do
  cplIs0
  match look n with
  | some m => m.wr v
  | none => gp 0

/-! ## System instructions -/

def movToCr (n : UInt8) (v : UInt32) : M Unit := do
  cplIs0
  let c ← cpu
  let pae := c.cr4 &&& CR4.PAE != 0
  match n with
  | 0 =>
    let v := (v &&& 0xE005003F) ||| CR0.ET
    if v &&& CR0.PG != 0 && v &&& CR0.PE == 0 then gp 0
    -- long-mode consistency checks; with EFER.LME, PG = 1 activates long mode (EFER.LMA)
    if !LongMode.cr0Ok c v then gp 0
    -- enabling PAE paging (or changing CD/NW with it on) loads the PDPTE registers (not in long mode)
    if v &&& CR0.PG != 0 && pae && c.efer &&& EFER.LME == 0 &&
       (c.cr0 &&& CR0.PG == 0 || (v ^^^ c.cr0) &&& 0x60000000 != 0) then
      let p ← readPdptes c.cr3
      modCpu fun c => { c with pdpte := p }
    LongMode.setCr0 v
  | 2 => modCpu fun c => { c with cr2 := v }
  | 3 =>
    if c.cr0 &&& CR0.PG != 0 && pae && !LongMode.lma c then
      let p ← readPdptes v
      modCpu fun c => { c with pdpte := p }
    modCpu fun c => { c with cr3 := v }
    flushTlb
  | 4 =>
    if v &&& ~~~Cpuid.cr4Writable != 0 then gp 0
    if !LongMode.cr4Ok c v then gp 0
    if c.cr0 &&& CR0.PG != 0 && v &&& CR4.PAE != 0 && !LongMode.lma c &&
       (v ^^^ c.cr4) &&& (CR4.PAE ||| CR4.PGE ||| CR4.PSE) != 0 then
      let p ← readPdptes c.cr3
      modCpu fun c => { c with pdpte := p }
    modCpu fun c => { c with cr4 := v }
    if (v ^^^ c.cr4) &&& (CR4.PSE ||| CR4.PGE ||| CR4.PAE) != 0 then flushTlbAll
  | _ => ud

def movFromCr (n : UInt8) : M UInt32 := do
  cplIs0
  let c ← cpu
  match n with
  | 0 => return c.cr0
  | 2 => return c.cr2
  | 3 => return c.cr3
  | 4 => return c.cr4
  | _ => ud

/-- Debug-register number for MOV DR (DR4/DR5 alias DR6/DR7 unless CR4.DE). With DR7.GD set, any
debug-register access is a #DB fault with DR6.BD (the `addr` of the fault carries the DR6 bits). -/
def drIndex (n : UInt8) : M UInt8 := do
  cplIs0
  if (← cpu).dr7 &&& 0x2000 != 0 then throw (.exc Vec.DB none DR6.BD)
  if n == 4 || n == 5 then
    if (← cpu).cr4 &&& CR4.DE != 0 then ud
    return n + 2
  return n

/-- UMIP (AMD APM vol. 2, chapter 6, "User Mode Instruction Prevention (UMIP)"): with CR4.UMIP = 1, SGDT, SIDT,
SLDT, SMSW and STR "become available only at CPL=0. Any attempt to execute them with CPL>0 results in
a #GP fault with error code 0" (also in virtual-8086 mode, CPL 3; also the SMSW register form). The
check comes after the #UD checks of the form and before any memory access. -/
@[inline] def umipCheck : M Unit := do
  let c ← cpu
  if c.cr4 &&& CR4.UMIP != 0 && c.cpl != 0 then gp 0

/-- The time-stamp counter: the instruction count plus the offset set by WRMSR 0x10. -/
@[inline] def tsc : M UInt64 := fun m => .ok (m.icount + m.cpu.sysx.tscOff) m

def grp6 (i : Inst) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then ud
  match i.reg with
  | 0 =>
    umipCheck
    if i.isMem then wrE i 2 c.ldtr.sel.toUInt32 else wrReg i.opsz i.rm c.ldtr.sel.toUInt32
  | 1 =>
    umipCheck
    if i.isMem then wrE i 2 c.tr.sel.toUInt32 else wrReg i.opsz i.rm c.tr.sel.toUInt32
  | 2 => -- LLDT
    cplIs0
    let sel := (← rdE i 2).toUInt16
    if sel &&& 0xFFFC == 0 then
      modCpu fun c => { c with ldtr := { sel, base := 0, limit := 0, attr := 0 } }
    else
      if sel &&& 4 != 0 then gp (sel.toUInt32 &&& 0xFFFC)
      let (d, _) ← readDesc sel
      if d.isSeg || d.sysType != 2 then gp (sel.toUInt32 &&& 0xFFFC)
      if !d.present then exc Vec.NP (some (sel.toUInt32 &&& 0xFFFC))
      modCpu fun c => { c with ldtr := d.toSeg sel }
  | 3 => -- LTR
    cplIs0
    let sel := (← rdE i 2).toUInt16
    if sel &&& 0xFFFC == 0 then gp 0
    if sel &&& 4 != 0 then gp (sel.toUInt32 &&& 0xFFFC)
    let (d, addr) ← readDesc sel
    -- a 16-bit TSS (type 1) is illegal in long mode (APM vol. 2, table 4-6); compatibility mode reads
    -- the 8-byte descriptor (4.8.3)
    if d.isSeg || !(d.sysType == 9 || (d.sysType == 1 && !LongMode.lma c)) then gp (sel.toUInt32 &&& 0xFFFC)
    if !d.present then exc Vec.NP (some (sel.toUInt32 &&& 0xFFFC))
    let d := { d with hi := d.hi ||| 0x200 }
    sysWr (addr + 4) 4 d.hi
    modCpu fun c => { c with tr := d.toSeg sel }
  | 4 | 5 => -- VERR / VERW
    let sel := (← rdE i 2).toUInt16
    let ok ← tryCatch (do
        if sel &&& 0xFFFC == 0 then return false
        let (d, _) ← readDesc sel
        if !d.isSeg then return false
        let priv := (d.isCode && d.conforming) ||
                    (d.dpl ≥ c.cpl && d.dpl ≥ (sel.toUInt32 &&& 3))
        if !priv then return false
        if i.reg == 4 then return (!d.isCode || d.readWrite)
        else return (!d.isCode && d.readWrite)) (fun _ => pure false)
    setFlags ZF (if ok then ZF else 0)
  | _ => ud

/-- LAR (`lsl = false`) / LSL. -/
def larLsl (i : Inst) (lsl : Bool) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then ud
  let sel := (← rdE i 2).toUInt16
  let r ← tryCatch (do
      if sel &&& 0xFFFC == 0 then return none
      let (d, _) ← readDesc sel
      let okType :=
        if d.isSeg then true
        else
          let t := d.sysType
          -- long mode: LDT, 64-bit TSS and (LAR) 64-bit call gates only (APM vol. 3 LAR, LSL)
          if LongMode.lma c then t == 2 || t == 9 || t == 11 || (!lsl && t == 12)
          else if lsl then t == 1 || t == 2 || t == 3 || t == 9 || t == 11
          else t == 1 || t == 2 || t == 3 || t == 4 || t == 5 || t == 9 || t == 11 || t == 12
      if !okType then return none
      -- a long-mode call gate is valid for LAR only with bits 12:8 of its dword +12 clear
      if LongMode.lma c && !d.isSeg && d.sysType == 12 then
        let (_, _, a) ← LongMode.readSel sel 0 16
        if (← sysRd (a + 12) 4) &&& 0x1F00 != 0 then return none
      let conf := d.isCode && d.conforming
      if !conf && (d.dpl < c.cpl || d.dpl < (sel.toUInt32 &&& 3)) then return none
      return some (if lsl then d.limit else d.hi &&& 0x00F0FF00)) (fun _ => pure none)
  match r with
  | some v =>
    setFlags ZF ZF
    wrReg i.opsz i.reg v
  | none => setFlags ZF 0

def grp7 (i : Inst) : M Unit := do
  match i.reg with
  | 0 | 1 => -- SGDT / SIDT
    needMem i
    umipCheck
    let c ← cpu
    let (b, l) := if i.reg == 0 then (c.gdtBase, c.gdtLimit) else (c.idtBase, c.idtLimit)
    let off ← eaOff i
    wrMem i.seg off 2 l
    wrMem i.seg (off + 2) 4 (if i.opsz == 2 then b &&& 0xFFFFFF else b)
  | 2 | 3 => -- LGDT / LIDT
    needMem i
    cplIs0
    let off ← eaOff i
    let l ← rdMem i.seg off 2
    let b ← rdMem i.seg (off + 2) 4
    let b := if i.opsz == 2 then b &&& 0xFFFFFF else b
    if i.reg == 2 then modCpu fun c => { c with gdtBase := b, gdtLimit := l }
    else modCpu fun c => { c with idtBase := b, idtLimit := l }
  | 4 => -- SMSW
    umipCheck
    let c ← cpu
    if i.isMem then wrE i 2 c.cr0 else wrReg i.opsz i.rm c.cr0
  | 6 => -- LMSW
    cplIs0
    let v ← rdE i 2
    let c ← cpu
    let nv := (c.cr0 &&& ~~~(0xE : UInt32)) ||| (v &&& 0xF) ||| (c.cr0 &&& 1)
    modCpu fun c => { c with cr0 := nv }
  | 7 => -- INVLPG
    needMem i
    cplIs0
    let off ← eaOff i
    let sr := (← cpu).getSeg i.seg
    flushTlbPage (sr.base + off)
  | _ => ud

/-! ## Dispatch -/

def pushSeg (s : UInt8) (i : Inst) : M Unit := do
  push i.opsz ((← cpu).getSeg s).sel.toUInt32

def popSeg (s : UInt8) (i : Inst) : M Unit := do
  let v ← peek i.opsz 0
  loadSeg s v.toUInt16
  addSp i.opsz.toUInt32
  if s == SegN.SS then modCpu fun c => { c with shadow := true }

/-- Load a far pointer `seg:off` from memory into segment `s` and register G (LDS/LES/LSS/LFS/LGS). -/
def loadFarPtr (s : UInt8) (i : Inst) : M Unit := do
  needMem i
  let off ← eaOff i
  let o ← rdMem i.seg off i.opsz.toUInt32
  let sel ← rdMem i.seg (off + i.opsz.toUInt32) 2
  loadSeg s sel.toUInt16
  wrReg i.opsz i.reg o
  if s == SegN.SS then modCpu fun c => { c with shadow := true }

/-- Opcodes defined by ranges. -/
def execRange (op : Nat) : Inst → M Unit :=
  if 0x40 ≤ op && op ≤ 0x47 then fun i => do
    let r := (i.op &&& 7).toUInt8
    wrReg i.opsz r (← incDec false i.opsz (← rdReg i.opsz r))
  else if 0x48 ≤ op && op ≤ 0x4F then fun i => do
    let r := (i.op &&& 7).toUInt8
    wrReg i.opsz r (← incDec true i.opsz (← rdReg i.opsz r))
  else if 0x50 ≤ op && op ≤ 0x57 then fun i => do
    push i.opsz (← rdReg i.opsz (i.op &&& 7).toUInt8)
  else if 0x58 ≤ op && op ≤ 0x5F then fun i => do
    let v ← pop i.opsz
    wrReg i.opsz (i.op &&& 7).toUInt8 v
  else if 0x70 ≤ op && op ≤ 0x7F then fun i => do
    if evalCC (← getFlags) (i.op &&& 0xF).toUInt8 then jumpRel i (sext 1 i.imm)
  else if 0xB0 ≤ op && op ≤ 0xB7 then fun i => wrReg 1 (i.op &&& 7).toUInt8 i.imm
  else if 0xB8 ≤ op && op ≤ 0xBF then fun i => wrReg i.opsz (i.op &&& 7).toUInt8 i.imm
  else if 0x118 ≤ op && op ≤ 0x11F then fun _ => pure ()
  else if 0x140 ≤ op && op ≤ 0x14F then fun i => do
    let v ← rdE i i.opsz
    if evalCC (← getFlags) (i.op &&& 0xF).toUInt8 then wrReg i.opsz i.reg v
  else if 0x180 ≤ op && op ≤ 0x18F then fun i => do
    if evalCC (← getFlags) (i.op &&& 0xF).toUInt8 then jumpRel i i.imm
  else if 0x190 ≤ op && op ≤ 0x19F then fun i => do
    wrE i 1 (if evalCC (← getFlags) (i.op &&& 0xF).toUInt8 then 1 else 0)
  else fun _ => ud

set_option maxHeartbeats 4000000 in
def execOp00 (op : Nat) : Inst → M Unit :=
  match op with
  | 0x00 | 0x01 => aluEG 0 | 0x02 | 0x03 => aluGE 0 | 0x04 | 0x05 => aluAI 0
  | 0x08 | 0x09 => aluEG 1 | 0x0A | 0x0B => aluGE 1 | 0x0C | 0x0D => aluAI 1
  | 0x10 | 0x11 => aluEG 2 | 0x12 | 0x13 => aluGE 2 | 0x14 | 0x15 => aluAI 2
  | 0x18 | 0x19 => aluEG 3 | 0x1A | 0x1B => aluGE 3 | 0x1C | 0x1D => aluAI 3
  | 0x20 | 0x21 => aluEG 4 | 0x22 | 0x23 => aluGE 4 | 0x24 | 0x25 => aluAI 4
  | 0x28 | 0x29 => aluEG 5 | 0x2A | 0x2B => aluGE 5 | 0x2C | 0x2D => aluAI 5
  | 0x30 | 0x31 => aluEG 6 | 0x32 | 0x33 => aluGE 6 | 0x34 | 0x35 => aluAI 6
  | 0x38 | 0x39 => aluEG 7 | 0x3A | 0x3B => aluGE 7 | 0x3C | 0x3D => aluAI 7
  | 0x06 => pushSeg SegN.ES | 0x07 => popSeg SegN.ES
  | 0x0E => pushSeg SegN.CS
  | 0x16 => pushSeg SegN.SS | 0x17 => popSeg SegN.SS
  | 0x1E => pushSeg SegN.DS | 0x1F => popSeg SegN.DS
  | 0x27 => fun _ => daaDas false
  | 0x2F => fun _ => daaDas true
  | 0x37 => fun _ => aaaAas false
  | 0x3F => fun _ => aaaAas true
  | _ => execRange op

set_option maxHeartbeats 4000000 in
def execOp60 (op : Nat) : Inst → M Unit :=
  match op with
  | 0x60 => fun i => do
    let c ← cpu
    let sz := i.opsz
    -- Check segment capacity, then translate/store in architectural push order.
    -- Earlier stores remain visible when a later push faults.
    let n := 8 * sz.toUInt32
    let sp := if c.ss.big then c.esp - n else (c.esp - n) &&& 0xFFFF
    let _ ← segAddr SegN.SS sp n true
    for r in [0, 1, 2, 3] do push sz (c.rdReg sz r)
    push sz (c.rdReg sz 4)
    for r in [5, 6, 7] do push sz (c.rdReg sz r)
  | 0x61 => fun i => do
    let sz := i.opsz
    for r in [7, 6, 5] do wrReg sz r (← pop sz)
    addSp sz.toUInt32 -- the saved SP slot is skipped, not read
    for r in [3, 2, 1, 0] do wrReg sz r (← pop sz)
  | 0x62 => fun i => do -- BOUND
    needMem i
    let sz := i.opsz
    let off ← eaOff i
    let lo := toSInt sz (← rdMem i.seg off sz.toUInt32)
    let hi := toSInt sz (← rdMem i.seg (off + sz.toUInt32) sz.toUInt32)
    let v := toSInt sz (← rdReg sz i.reg)
    if v < lo || v > hi then exc Vec.BR
  | 0x63 => fun i => do -- ARPL
    let c ← cpu
    if !c.pe || c.vm86 then ud
    let src ← rdReg 2 i.reg
    rmwE i 2 fun d => do
      if d &&& 3 < src &&& 3 then
        setFlags ZF ZF
        return some ((d &&& 0xFFFC) ||| (src &&& 3))
      else
        setFlags ZF 0
        return some d
  | 0x68 => fun i => push i.opsz i.imm
  | 0x6A => fun i => push i.opsz (sext 1 i.imm &&& i.opsz.mask)
  | 0x69 | 0x6B => fun i => do
    let sz := i.opsz
    let b := if i.op == 0x6B then sext 1 i.imm &&& sz.mask else i.imm
    let a ← rdE i sz
    let (p, ovf) := imulCore sz a b
    let lo := p.toUInt32 &&& sz.mask
    wrReg sz i.reg lo
    setMulFlags sz ovf lo
  | 0x6C | 0x6D => fun i => stringOp i 5
  | 0x6E | 0x6F => fun i => stringOp i 6
  | 0x80 | 0x82 => fun i => rmwE i 1 (write := i.reg != 7) fun a => doAlu i.reg 1 a (i.imm &&& 0xFF)
  | 0x81 => fun i => rmwE i i.opsz (write := i.reg != 7) fun a => doAlu i.reg i.opsz a i.imm
  | 0x83 => fun i => rmwE i i.opsz (write := i.reg != 7) fun a => doAlu i.reg i.opsz a (sext 1 i.imm &&& i.opsz.mask)
  | 0x84 | 0x85 => fun i => do
    let sz := bsz i
    let a ← rdE i sz
    let b ← rdReg sz i.reg
    setFlags arith (logicF sz (a &&& b)).2
  | 0x86 | 0x87 => fun i => do
    let sz := bsz i
    let g ← rdReg sz i.reg
    rmwE i sz fun e => do
      wrReg sz i.reg e
      return some g
    -- register form: rmwE wrote E after G, which is correct even if E = G
  | 0x88 | 0x89 => fun i => do let sz := bsz i; wrE i sz (← rdReg sz i.reg)
  | 0x8A | 0x8B => fun i => do let sz := bsz i; wrReg sz i.reg (← rdE i sz)
  | 0x8C => fun i => do
    if i.reg > 5 then ud
    let v := ((← cpu).getSeg i.reg).sel.toUInt32
    if i.isMem then wrE i 2 v else wrReg i.opsz i.rm v
  | 0x8D => fun i => do
    needMem i
    wrReg i.opsz i.reg (← eaOff i)
  | 0x8E => fun i => do
    if i.reg > 5 || i.reg == SegN.CS then ud
    let v ← rdE i 2
    loadSeg i.reg v.toUInt16
    if i.reg == SegN.SS then modCpu fun c => { c with shadow := true }
  | 0x8F => fun i => do
    if i.reg != 0 then ud
    let v ← pop i.opsz
    wrE i i.opsz v
  | 0x90 => fun _ => pure ()
  | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 => fun i => do
    let r := (i.op &&& 7).toUInt8
    let a ← rdReg i.opsz 0
    let b ← rdReg i.opsz r
    wrReg i.opsz 0 b
    wrReg i.opsz r a
  | 0x98 => fun i => do
    if i.opsz == 2 then wrReg 2 0 (sext 1 (← rdReg 1 0))
    else setReg 0 (sext 2 (← rdReg 2 0))
  | 0x99 => fun i => do
    let a ← rdReg i.opsz 0
    wrReg i.opsz 2 (if a &&& i.opsz.msb != 0 then i.opsz.mask else 0)
  | 0x9A => fun i => farJump i.imm2.toUInt16 i.imm true i.opsz
  | 0x9B => fun _ => fwait
  | 0x9C => fun i => do
    let c ← cpu
    if c.vm86 && c.iopl < 3 then gp 0
    push i.opsz ((c.eflags &&& ~~~(VM ||| RF)) &&& i.opsz.mask)
  | 0x9D => fun i => popf i.opsz
  | 0x9E => fun _ => do
    let ah := ((← getReg 0) >>> 8) &&& 0xFF
    setFlags (SF ||| ZF ||| AF ||| PF ||| CF) ah
  | 0x9F => fun _ => do
    let f ← getFlags
    wrReg 1 4 ((f &&& 0xD5) ||| 2)
  | _ => execRange op

set_option maxHeartbeats 4000000 in
def execOpA0 (op : Nat) : Inst → M Unit :=
  match op with
  | 0xA0 | 0xA1 => fun i => do
    let sz := bsz i
    let s := if i.segOvr != 0xFF then i.segOvr else SegN.DS
    wrReg sz 0 (← rdMem s i.imm sz.toUInt32)
  | 0xA2 | 0xA3 => fun i => do
    let sz := bsz i
    let s := if i.segOvr != 0xFF then i.segOvr else SegN.DS
    wrMem s i.imm sz.toUInt32 (← rdReg sz 0)
  | 0xA4 | 0xA5 => fun i => stringOp i 0
  | 0xA6 | 0xA7 => fun i => stringOp i 1
  | 0xA8 | 0xA9 => fun i => do
    let sz := bsz i
    setFlags arith (logicF sz ((← rdReg sz 0) &&& i.imm &&& sz.mask)).2
  | 0xAA | 0xAB => fun i => stringOp i 2
  | 0xAC | 0xAD => fun i => stringOp i 3
  | 0xAE | 0xAF => fun i => stringOp i 4
  | 0xC0 | 0xC1 => fun i => shiftGrp i i.imm
  | 0xC2 => fun i => do
    let t ← pop i.opsz
    jumpTo i.opsz t
    addSp i.imm
  | 0xC3 => fun i => do jumpTo i.opsz (← pop i.opsz)
  | 0xC4 => loadFarPtr SegN.ES
  | 0xC5 => loadFarPtr SegN.DS
  | 0xC6 | 0xC7 => fun i => do
    if i.reg != 0 then ud
    wrE i (bsz i) i.imm
  | 0xC8 => fun i => do -- ENTER
    let sz := i.opsz
    let n := sz.toUInt32
    let level := i.imm2 &&& 31
    let big := (← cpu).ss.big
    push sz (← rdReg sz 5)
    let frame := (← getReg 4)
    if level > 0 then
      for _ in [1:level.toNat] do
        let bp := (← getReg 5)
        let nbp := if big then bp - n else (bp &&& 0xFFFF0000) ||| ((bp - n) &&& 0xFFFF)
        if sz == 4 then setReg 5 nbp else wrReg 2 5 nbp
        push sz (← rdMem SegN.SS (if big then nbp else nbp &&& 0xFFFF) n)
      push sz frame
    wrReg (if big then 4 else 2) 5 frame
    let sp ← getReg 4
    if big then setReg 4 (sp - i.imm) else wrReg 2 4 (sp - i.imm)
    -- ENTER checks write permission at the final stack byte even though the
    -- allocation does not store there. Earlier frame stores survive this fault.
    let finalSp ← getReg 4
    let lin ← segAddr SegN.SS (if big then finalSp else finalSp &&& 0xFFFF) 1 true
    let _ ← translate lin true (← isUser)
  | 0xC9 => fun i => do -- LEAVE
    let big := (← cpu).ss.big
    if big then setReg 4 (← getReg 5) else wrReg 2 4 (← rdReg 2 5)
    wrReg i.opsz 5 (← pop i.opsz)
  | 0xCA => fun i => farRet i.opsz i.imm
  | 0xCB => fun i => farRet i.opsz 0
  | 0xCC => fun _ => deliver Vec.BP none true false
  | 0xCD => fun i => do
    -- INT n is IOPL-sensitive in virtual-8086 mode (INT3 and INTO are not)
    let c ← cpu
    if c.vm86 && c.iopl < 3 then gp 0
    deliver i.imm.toUInt8 none true false
  | 0xCE => fun _ => do if (← flag OF) then deliver Vec.OF none true false
  | 0xCF => fun i => iret i.opsz
  | 0xD0 | 0xD1 => fun i => shiftGrp i 1
  | 0xD2 | 0xD3 => fun i => do shiftGrp i ((← getReg 1) &&& 0xFF)
  | 0xD4 => fun i => do -- AAM
    let b := i.imm &&& 0xFF
    if b == 0 then exc Vec.DE
    let al := (← getReg 0) &&& 0xFF
    let r := al % b
    wrReg 2 0 (((al / b) <<< 8) ||| r)
    setFlags arith (szp 1 r)
  | 0xD5 => fun i => do -- AAD
    let ax ← rdReg 2 0
    let al := ((ax &&& 0xFF) + (ax >>> 8) * (i.imm &&& 0xFF)) &&& 0xFF
    wrReg 2 0 al
    setFlags arith (szp 1 al)
  | 0xD6 => fun _ => do wrReg 1 0 (if (← flag CF) then 0xFF else 0)
  | 0xD7 => fun i => do
    let s := if i.segOvr != 0xFF then i.segOvr else SegN.DS
    let b ← getReg 3
    let off := b + ((← getReg 0) &&& 0xFF)
    let off := if i.adsz == 2 then off &&& 0xFFFF else off
    wrReg 1 0 (← rdMem s off 1)
  | 0xD8 | 0xD9 | 0xDA | 0xDB | 0xDC | 0xDD | 0xDE | 0xDF => x87
  | 0xE0 | 0xE1 | 0xE2 => fun i => do
    let c ← cpu
    let a32 := i.adsz == 4
    let n := (if a32 then c.ecx else c.ecx &&& 0xFFFF) - 1
    let n := if a32 then n else n &&& 0xFFFF
    if a32 then setReg 1 n else wrReg 2 1 n
    let zf := c.eflags &&& ZF != 0
    let take := n != 0 && (if i.op == 0xE0 then !zf else if i.op == 0xE1 then zf else true)
    if take then jumpRel i (sext 1 i.imm)
  | 0xE3 => fun i => do
    let c ← cpu
    let n := if i.adsz == 4 then c.ecx else c.ecx &&& 0xFFFF
    if n == 0 then jumpRel i (sext 1 i.imm)
  | 0xE4 | 0xE5 => fun i => do
    let sz := bsz i
    ioCheck (i.imm &&& 0xFF) sz
    wrReg sz 0 (← portIn (i.imm &&& 0xFF) sz)
  | 0xE6 | 0xE7 => fun i => do
    let sz := bsz i
    ioCheck (i.imm &&& 0xFF) sz
    portOut (i.imm &&& 0xFF) sz (← rdReg sz 0)
  | 0xEC | 0xED => fun i => do
    let sz := bsz i
    let p := (← getReg 2) &&& 0xFFFF
    ioCheck p sz
    wrReg sz 0 (← portIn p sz)
  | 0xEE | 0xEF => fun i => do
    let sz := bsz i
    let p := (← getReg 2) &&& 0xFFFF
    ioCheck p sz
    portOut p sz (← rdReg sz 0)
  | 0xE8 => fun i => do
    let ret ← getEip
    let t := ret + i.imm
    let t := if i.opsz == 2 then t &&& 0xFFFF else t
    if t > (← cpu).cs.limit then gp 0
    push i.opsz ret
    setEip t
  | 0xE9 => fun i => jumpRel i i.imm
  | 0xEA => fun i => farJump i.imm2.toUInt16 i.imm false i.opsz
  | 0xEB => fun i => jumpRel i (sext 1 i.imm)
  | 0xF1 => fun _ => deliver Vec.DB none false false
  | 0xF4 => fun _ => do
    cplIs0
    modCpu fun c => { c with halted := true }
  | 0xF5 => fun _ => modCpu fun c => { c with eflags := c.eflags ^^^ CF }
  | 0xF6 | 0xF7 => grp3
  | 0xF8 => fun _ => setFlags CF 0
  | 0xF9 => fun _ => setFlags CF CF
  | 0xFA => fun _ => do
    let c ← cpu
    if c.pe && c.cpl > c.iopl then gp 0
    setFlags IF 0
  | 0xFB => fun _ => do
    let c ← cpu
    if c.pe && c.cpl > c.iopl then gp 0
    if c.eflags &&& IF == 0 then modCpu fun c => { c with shadow := true }
    setFlags IF IF
  | 0xFC => fun _ => setFlags DF 0
  | 0xFD => fun _ => setFlags DF DF
  | 0xFE => fun i => do
    if i.reg > 1 then ud
    rmwE i 1 fun a => do return some (← incDec (i.reg == 1) 1 a)
  | 0xFF => fun i => do
    let sz := i.opsz
    match i.reg with
    | 0 | 1 => rmwE i sz fun a => do return some (← incDec (i.reg == 1) sz a)
    | 2 =>
      let t ← rdE i sz
      let ret ← getEip
      let t := if sz == 2 then t &&& 0xFFFF else t
      if t > (← cpu).cs.limit then gp 0
      push sz ret
      setEip t
    | 3 | 5 =>
      needMem i
      let off ← eaOff i
      let o ← rdMem i.seg off sz.toUInt32
      let sel ← rdMem i.seg (off + sz.toUInt32) 2
      farJump sel.toUInt16 o (i.reg == 3) sz
    | 4 => do jumpTo sz (← rdE i sz)
    | 6 => do push sz (← rdE i sz)
    | _ => ud
  -- two-byte opcodes
  | _ => execRange op

set_option maxHeartbeats 4000000 in
def execOp0F (op : Nat) : Inst → M Unit :=
  match op with
  | 0x100 => grp6
  | 0x101 => grp7
  | 0x102 => fun i => larLsl i false
  | 0x103 => fun i => larLsl i true
  | 0x106 => fun _ => do
    cplIs0
    modCpu fun c => { c with cr0 := c.cr0 &&& ~~~CR0.TS }
  | 0x108 | 0x109 => fun _ => cplIs0
  | 0x10D => fun _ => pure ()
  | 0x120 => fun i => do setReg i.rm (← movFromCr i.reg)
  | 0x122 => fun i => do movToCr i.reg (← getReg i.rm)
  | 0x121 => fun i => do
    let n ← drIndex i.reg
    let c ← cpu
    let v := match n with
      | 0 => c.dr0 | 1 => c.dr1 | 2 => c.dr2 | 3 => c.dr3 | 6 => c.dr6 | _ => c.dr7
    setReg i.rm v
  | 0x123 => fun i => do
    let n ← drIndex i.reg
    let v ← getReg i.rm
    modCpu fun c => match n with
      | 0 => { c with dr0 := v } | 1 => { c with dr1 := v } | 2 => { c with dr2 := v }
      | 3 => { c with dr3 := v } | 6 => { c with dr6 := v ||| 0xFFFF0FF0 }
      | _ => c.setDr7 (v ||| 0x400)
  | 0x131 => fun _ => do
    let c ← cpu
    if c.cr4 &&& CR4.TSD != 0 && c.cpl != 0 then gp 0
    let t ← tsc
    setReg 0 t.toUInt32
    setReg 2 (t >>> 32).toUInt32
  | 0x1AA => fun _ => rsm
  | 0x1A0 => pushSeg SegN.FS | 0x1A1 => popSeg SegN.FS
  | 0x1A8 => pushSeg SegN.GS | 0x1A9 => popSeg SegN.GS
  | 0x1A2 => fun _ => do
    let (a, b, c, d) := cpuid (← cpu) (← getReg 0) (← getReg 1)
    setReg 0 a; setReg 3 b; setReg 1 c; setReg 2 d
  | 0x1A3 => fun i => do bitOp i 0 (← rdReg i.opsz i.reg) false
  | 0x1AB => fun i => do bitOp i 1 (← rdReg i.opsz i.reg) false
  | 0x1B3 => fun i => do bitOp i 2 (← rdReg i.opsz i.reg) false
  | 0x1BB => fun i => do bitOp i 3 (← rdReg i.opsz i.reg) false
  | 0x1BA => fun i => do
    if i.reg < 4 then ud
    bitOp i (i.reg - 4) (i.imm &&& 0xFF) true
  | 0x1A4 => fun i => shiftD i true i.imm
  | 0x1A5 => fun i => do shiftD i true ((← getReg 1) &&& 0xFF)
  | 0x1AC => fun i => shiftD i false i.imm
  | 0x1AD => fun i => do shiftD i false ((← getReg 1) &&& 0xFF)
  | 0x1AF => fun i => do
    let sz := i.opsz
    let (p, ovf) := imulCore sz (← rdReg sz i.reg) (← rdE i sz)
    let lo := p.toUInt32 &&& sz.mask
    wrReg sz i.reg lo
    setMulFlags sz ovf lo
  | 0x1B0 | 0x1B1 => fun i => do
    let sz := bsz i
    let src ← rdReg sz i.reg
    let acc ← rdReg sz 0
    let mut old := 0
    if i.isMem then
      let off ← eaOff i
      old ← rdMem i.seg off sz.toUInt32 true
      setFlags arith (subF sz acc old 0).2
      wrMem i.seg off sz.toUInt32 (if acc == old then src else old)
    else
      old ← rdReg sz i.rm
      setFlags arith (subF sz acc old 0).2
      if acc == old then wrReg sz i.rm src
    if acc != old then wrReg sz 0 old
  | 0x1B2 => loadFarPtr SegN.SS
  | 0x1B4 => loadFarPtr SegN.FS
  | 0x1B5 => loadFarPtr SegN.GS
  | 0x1B6 => fun i => do wrReg i.opsz i.reg (← rdE i 1)
  | 0x1B7 => fun i => do wrReg i.opsz i.reg (← rdE i 2)
  | 0x1BE => fun i => do wrReg i.opsz i.reg (sext 1 (← rdE i 1) &&& i.opsz.mask)
  | 0x1BF => fun i => do wrReg i.opsz i.reg (sext 2 (← rdE i 2) &&& i.opsz.mask)
  | 0x1BC | 0x1BD => fun i => do
    let sz := i.opsz
    let v ← rdE i sz
    if v == 0 then setFlags ZF ZF
    else
      setFlags ZF 0
      let mut k : UInt32 := 0
      if i.op == 0x1BC then
        while (v >>> k) &&& 1 == 0 do k := k + 1
      else
        k := sz.bits - 1
        while (v >>> k) &&& 1 == 0 do k := k - 1
      wrReg sz i.reg k
  | 0x1C0 | 0x1C1 => fun i => do
    let sz := bsz i
    let src ← rdReg sz i.reg
    if i.isMem then
      let off ← eaOff i
      let d ← rdMem i.seg off sz.toUInt32 true
      let (r, fl) := addF sz d src 0
      wrMem i.seg off sz.toUInt32 r
      setFlags arith fl
      wrReg sz i.reg d
    else
      let d ← rdReg sz i.rm
      let (r, fl) := addF sz d src 0
      setFlags arith fl
      wrReg sz i.reg d
      wrReg sz i.rm r
  | 0x1C7 => fun i => do
    if i.reg != 1 then ud
    needMem i
    let off ← eaOff i
    let _ ← segAddr i.seg off 8 true
    -- Both halves require write access before either half can be committed.
    -- Reading in address order also reports the first byte of a faulting page.
    let lo ← rdMem i.seg off 4 true (al := 8)
    let hi ← rdMem i.seg (off + 4) 4 true
    let eax ← getReg 0
    let edx ← getReg 2
    if eax == lo && edx == hi then
      wrMem i.seg off 4 (← getReg 3)
      wrMem i.seg (off + 4) 4 (← getReg 1)
      setFlags ZF ZF
    else
      wrMem i.seg off 4 lo
      wrMem i.seg (off + 4) 4 hi
      setReg 0 lo
      setReg 2 hi
      setFlags ZF 0
  | 0x1C8 | 0x1C9 | 0x1CA | 0x1CB | 0x1CC | 0x1CD | 0x1CE | 0x1CF => fun i => do
    let r := (i.op &&& 7).toUInt8
    let v ← getReg r
    setReg r ((v <<< 24) ||| ((v &&& 0xFF00) <<< 8) ||| ((v >>> 8) &&& 0xFF00) ||| (v >>> 24))
  | _ => if op ≥ 0x100 && isSimdOp (op - 0x100) then simd else execRange op

/-- The core model's semantics of the one-byte and 0F maps (0x000..0x1FF), before the hooks of
`X86/Dispatch.lean` (which also handles RDMSR/WRMSR and the 0F 38 / 0F 3A / VEX maps). -/
def execBase (op : Nat) : Inst → M Unit :=
  if op < 0x60 then execOp00 op else if op < 0xA0 then execOp60 op
  else if op < 0x100 then execOpA0 op else execOp0F op

end X86
