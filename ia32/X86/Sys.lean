import X86.Io
/-!
# System architecture

Stack operations, descriptor tables and segment loads, far control transfers,
interrupt/exception delivery through the IDT, and IRET.

Not modelled (stop the simulation with `Fault.unsupported`): hardware task switching
(task gates, `NT`-flag IRET, far jumps to TSS), call gates, and virtual-8086 mode.
-/
namespace X86

/-! ## Stack -/

def push (sz : Sz) (v : UInt32) : M Unit := do
  let c ← cpu
  let big := c.ss.big
  let n := sz.toUInt32
  let sp := if big then c.esp - n else (c.esp - n) &&& 0xFFFF
  wrMem SegN.SS sp n v
  modCpu fun c => { c with esp := if big then sp else (c.esp &&& 0xFFFF0000) ||| sp }

def pop (sz : Sz) : M UInt32 := do
  let c ← cpu
  let big := c.ss.big
  let n := sz.toUInt32
  let sp := if big then c.esp else c.esp &&& 0xFFFF
  let v ← rdMem SegN.SS sp n
  let nsp := sp + n
  modCpu fun c => { c with esp := if big then nsp else (c.esp &&& 0xFFFF0000) ||| (nsp &&& 0xFFFF) }
  return v

/-- Read the stack `k` bytes above the top without popping. -/
def peek (sz : Sz) (k : UInt32) : M UInt32 := do
  let c ← cpu
  let sp := if c.ss.big then c.esp + k else (c.esp + k) &&& 0xFFFF
  rdMem SegN.SS sp sz.toUInt32

def addSp (k : UInt32) : M Unit := modCpu fun c =>
  if c.ss.big then { c with esp := c.esp + k }
  else { c with esp := (c.esp &&& 0xFFFF0000) ||| ((c.esp + k) &&& 0xFFFF) }

/-! ## Descriptors -/

structure Desc where
  lo : UInt32
  hi : UInt32
  deriving Repr, Inhabited

namespace Desc
@[inline] def base (d : Desc) : UInt32 := (d.lo >>> 16) ||| ((d.hi &&& 0xFF) <<< 16) ||| (d.hi &&& 0xFF000000)
@[inline] def limit (d : Desc) : UInt32 :=
  let raw := (d.lo &&& 0xFFFF) ||| (d.hi &&& 0xF0000)
  if d.hi &&& 0x800000 != 0 then (raw <<< 12) ||| 0xFFF else raw
@[inline] def attr (d : Desc) : UInt32 := (d.hi >>> 8) &&& 0xF0FF
@[inline] def dpl (d : Desc) : UInt32 := (d.hi >>> 13) &&& 3
@[inline] def present (d : Desc) : Bool := d.hi &&& 0x8000 != 0
/-- Code or data (S = 1) descriptor. -/
@[inline] def isSeg (d : Desc) : Bool := d.hi &&& 0x1000 != 0
@[inline] def isCode (d : Desc) : Bool := d.hi &&& 0x1800 == 0x1800
@[inline] def conforming (d : Desc) : Bool := d.hi &&& 0x400 != 0
@[inline] def readWrite (d : Desc) : Bool := d.hi &&& 0x200 != 0
/-- System descriptor type (S = 0). -/
@[inline] def sysType (d : Desc) : UInt32 := (d.hi >>> 8) &&& 0x1F
def toSeg (d : Desc) (sel : UInt16) : SegReg :=
  { sel, base := d.base, limit := d.limit, attr := d.attr }
end Desc

/-- Read the descriptor of a non-null selector. Returns the descriptor and its linear address. -/
def readDesc (sel : UInt16) (ext : UInt32 := 0) : M (Desc × UInt32) := do
  let c ← cpu
  let idx := sel.toUInt32 &&& 0xFFF8
  let err := (sel.toUInt32 &&& 0xFFFC) ||| ext
  let (base, limit) ←
    if sel &&& 4 != 0 then
      if !c.ldtr.present then gp err
      pure (c.ldtr.base, c.ldtr.limit)
    else pure (c.gdtBase, c.gdtLimit)
  if idx + 7 > limit then gp err
  let lo ← sysRd (base + idx) 4
  let hi ← sysRd (base + idx + 4) 4
  return ({ lo, hi }, base + idx)

/-- Set the accessed bit of a code/data descriptor in memory. -/
def setAccessed (d : Desc) (addr : UInt32) : M Desc := do
  if d.hi &&& 0x100 == 0 then
    let hi := d.hi ||| 0x100
    sysWr (addr + 4) 4 hi
    return { d with hi }
  else return d

/-- Compute the descriptor cache for loading `sel` into data/stack segment register `s`
at privilege level `cpl` (protected mode), with all checks. -/
def segFor (s : UInt8) (sel : UInt16) (cpl : UInt32) : M SegReg := do
  let rpl := sel.toUInt32 &&& 3
  let err := sel.toUInt32 &&& 0xFFFC
  if err == 0 then
    if s == SegN.SS then gp 0
    return { sel, base := 0, limit := 0, attr := 0 }
  let (d, addr) ← readDesc sel
  if !d.isSeg then gp err
  if s == SegN.SS then
    if rpl != cpl || d.isCode || !d.readWrite || d.dpl != cpl then gp err
    if !d.present then exc Vec.SS (some err)
  else
    if d.isCode && !d.readWrite then gp err
    if (!d.isCode || !d.conforming) && (rpl > d.dpl || cpl > d.dpl) then gp err
    if !d.present then exc Vec.NP (some err)
  let d ← setAccessed d addr
  return d.toSeg sel

/-- Load a data or stack segment register (MOV/POP Sreg, LDS etc.). -/
def loadSeg (s : UInt8) (sel : UInt16) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then
    let sr := c.getSeg s
    let sr := if c.vm86 then { sel, base := sel.toUInt32 <<< 4, limit := 0xFFFF, attr := 0xF3 }
              else { sr with sel, base := sel.toUInt32 <<< 4 }
    modCpu (·.setSeg s sr)
  else
    let sr ← segFor s sel c.cpl
    modCpu (·.setSeg s sr)

/-- Check a code segment descriptor as a far JMP/CALL target (no gates). Returns the CS cache. -/
def codeForJump (sel : UInt16) (off : UInt32) : M SegReg := do
  let c ← cpu
  let cpl := c.cpl
  let err := sel.toUInt32 &&& 0xFFFC
  if err == 0 then gp 0
  let (d, addr) ← readDesc sel
  if !d.isSeg then
    unsupported s!"far transfer through system descriptor (type {d.sysType}) selector {sel}"
  if !d.isCode then gp err
  if d.conforming then
    if d.dpl > cpl then gp err
  else if (sel.toUInt32 &&& 3) > cpl || d.dpl != cpl then gp err
  if !d.present then exc Vec.NP (some err)
  if off > d.limit then gp 0
  let d ← setAccessed d addr
  return d.toSeg ((sel &&& 0xFFFC) ||| cpl.toUInt16)

/-- Far JMP (`call = false`) or far CALL to `sel:off`. `next` is the return EIP. -/
def farJump (sel : UInt16) (off : UInt32) (call : Bool) (opsz : Sz) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then
    if call then
      push opsz c.cs.sel.toUInt32
      push opsz c.eip
    modCpu fun c => { c with cs := { c.cs with sel, base := sel.toUInt32 <<< 4 }, eip := off }
  else
    let cs ← codeForJump sel off
    if call then
      push opsz c.cs.sel.toUInt32
      push opsz c.eip
    modCpu fun c => { c with cs, eip := off }

/-- Null data segment registers that are not accessible at the new (outer) privilege level. -/
def nullInaccessible (cpl : UInt32) : M Unit := modCpu fun c =>
  let fix := fun (sr : SegReg) =>
    let dataOrNc := !sr.isCode || sr.attr &&& 4 == 0
    if sr.present && dataOrNc && sr.dpl < cpl then { sr with sel := 0, attr := 0 } else sr
  { c with es := fix c.es, ds := fix c.ds, fs := fix c.fs, gs := fix c.gs }

/-- Code segment check for a return (RETF / IRET) to selector `sel` with RPL ≥ CPL. -/
def codeForReturn (sel : UInt16) : M SegReg := do
  let c ← cpu
  let rpl := sel.toUInt32 &&& 3
  let err := sel.toUInt32 &&& 0xFFFC
  if err == 0 then gp 0
  if rpl < c.cpl then gp err
  let (d, addr) ← readDesc sel
  if !d.isCode then gp err
  if d.conforming then
    if d.dpl > rpl then gp err
  else if d.dpl != rpl then gp err
  if !d.present then exc Vec.NP (some err)
  let d ← setAccessed d addr
  return d.toSeg sel

/-- Far RET with `imm` bytes of parameters. -/
def farRet (opsz : Sz) (imm : UInt32) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then
    let ip ← pop opsz
    let cs ← pop opsz
    addSp imm
    modCpu fun c => { c with eip := ip, cs := { c.cs with sel := cs.toUInt16, base := (cs &&& 0xFFFF) <<< 4 } }
  else
    let ip ← peek opsz 0
    let csel := (← peek opsz opsz.toUInt32).toUInt16
    let cs ← codeForReturn csel
    let rpl := csel.toUInt32 &&& 3
    if rpl == c.cpl then
      if ip > cs.limit then gp 0
      addSp (2 * opsz.toUInt32 + imm)
      modCpu fun c => { c with cs, eip := ip }
    else
      let o := 2 * opsz.toUInt32 + imm
      let nsp ← peek opsz o
      let nss := (← peek opsz (o + opsz.toUInt32)).toUInt16
      let ss ← segFor SegN.SS nss rpl
      if ip > cs.limit then gp 0
      modCpu fun c => { c with cs, eip := ip, ss,
                               esp := if ss.big then nsp + imm else (nsp + imm) &&& 0xFFFF }
      nullInaccessible rpl

/-! ## Interrupts and exceptions -/

/-- Deliver interrupt/exception `vec`. `soft` marks INT n / INT3 / INTO (gate DPL is checked);
`ext` marks an external event (sets the EXT bit of error codes). EIP must already hold
the return address. -/
def deliver (vec : UInt8) (err : Option UInt32) (soft ext : Bool) : M Unit := do
  let c ← cpu
  let v := vec.toUInt32
  if !c.pe then
    let ent := c.idtBase + v * 4
    if ent + 3 > c.idtBase + c.idtLimit then gp 0
    let ip ← sysRd ent 2
    let seg ← sysRd (ent + 2) 2
    push 2 (c.eflags &&& 0xFFFF)
    push 2 c.cs.sel.toUInt32
    push 2 (c.eip &&& 0xFFFF)
    modCpu fun c => { c with
      eflags := c.eflags &&& ~~~(Flag.IF ||| Flag.TF ||| Flag.AC ||| Flag.RF)
      cs := { c.cs with sel := seg.toUInt16, base := seg <<< 4 }
      eip := ip }
    return
  if c.vm86 then unsupported "interrupt in virtual-8086 mode"
  let extB : UInt32 := if ext then 1 else 0
  let gerr := v * 8 + 2 + extB
  if v * 8 + 7 > c.idtLimit then gp gerr
  let lo ← sysRd (c.idtBase + v * 8) 4
  let hi ← sysRd (c.idtBase + v * 8 + 4) 4
  let gtype := (hi >>> 8) &&& 0x1F
  if gtype == 0x05 then unsupported s!"task gate for vector {vec}"
  if !(gtype == 0x06 || gtype == 0x07 || gtype == 0x0E || gtype == 0x0F) then gp gerr
  let gdpl := (hi >>> 13) &&& 3
  if soft && gdpl < c.cpl then gp gerr
  if hi &&& 0x8000 == 0 then exc Vec.NP (some gerr)
  let g32 := gtype &&& 8 != 0
  let gsz : Sz := if g32 then 4 else 2
  let sel := (lo >>> 16).toUInt16
  let off := if g32 then (lo &&& 0xFFFF) ||| (hi &&& 0xFFFF0000) else lo &&& 0xFFFF
  let serr := (sel.toUInt32 &&& 0xFFFC) ||| extB
  if sel &&& 0xFFFC == 0 then gp extB
  let (d, daddr) ← readDesc sel extB
  if !d.isCode || d.dpl > c.cpl then gp serr
  if !d.present then exc Vec.NP (some serr)
  let d ← setAccessed d daddr
  if off > d.limit then gp extB
  let oldFlags := c.eflags
  let oldCs := c.cs.sel.toUInt32
  let oldEip := c.eip
  if !d.conforming && d.dpl < c.cpl then
    -- inter-privilege: fetch the inner stack from the TSS
    let ndpl := d.dpl
    let tr := c.tr
    let tss32 := tr.typ &&& 8 != 0
    let (spOff, ssOff, w) := if tss32 then (4 + ndpl * 8, 8 + ndpl * 8, 4) else (2 + ndpl * 4, 4 + ndpl * 4, 2)
    if ssOff + 1 > tr.limit || spOff + w - 1 > tr.limit then
      exc Vec.TS (some ((tr.sel.toUInt32 &&& 0xFFFC) ||| extB))
    let nesp ← sysRd (tr.base + spOff) w
    let nssSel := (← sysRd (tr.base + ssOff) 2).toUInt16
    let ssErr := (nssSel.toUInt32 &&& 0xFFFC) ||| extB
    if nssSel &&& 0xFFFC == 0 then exc Vec.TS (some extB)
    let (sd, saddr) ← readDesc nssSel extB
    if (nssSel.toUInt32 &&& 3) != ndpl || sd.dpl != ndpl || sd.isCode || !sd.isSeg || !sd.readWrite then
      exc Vec.TS (some ssErr)
    if !sd.present then exc Vec.SS (some ssErr)
    let sd ← setAccessed sd saddr
    let nss := sd.toSeg nssSel
    let oldSs := c.ss.sel.toUInt32
    let oldEsp := c.esp
    modCpu fun c => { c with ss := nss, esp := nesp,
                             cs := d.toSeg ((sel &&& 0xFFFC) ||| ndpl.toUInt16) }
    push gsz oldSs
    push gsz oldEsp
  else if d.conforming || d.dpl == c.cpl then
    modCpu fun c => { c with cs := d.toSeg ((sel &&& 0xFFFC) ||| c.cpl.toUInt16) }
  else gp serr
  push gsz oldFlags
  push gsz oldCs
  push gsz oldEip
  if let some e := err then push gsz e
  let clr := Flag.TF ||| Flag.NT ||| Flag.RF ||| Flag.VM ||| (if gtype &&& 1 == 0 then Flag.IF else 0)
  modCpu fun c => { c with eip := off, eflags := c.eflags &&& ~~~clr }

/-- IRET / IRETD. -/
def iret (opsz : Sz) : M Unit := do
  let c ← cpu
  if !c.pe then
    let ip ← pop opsz
    let cs ← pop opsz
    let fl ← pop opsz
    let keep := if opsz == 4 then Flag.VM else 0xFFFF0000
    let mask := Flag.valid &&& ~~~keep
    modCpu fun c => { c with eip := ip, cs := { c.cs with sel := cs.toUInt16, base := (cs &&& 0xFFFF) <<< 4 },
                             eflags := ((c.eflags &&& ~~~mask) ||| (fl &&& mask)) ||| 2 }
    return
  if c.vm86 then unsupported "IRET in virtual-8086 mode"
  if c.eflags &&& Flag.NT != 0 then unsupported "IRET with NT set (task return)"
  let ip ← peek opsz 0
  let csel := (← peek opsz opsz.toUInt32).toUInt16
  let fl ← peek opsz (2 * opsz.toUInt32)
  if opsz == 4 && fl &&& Flag.VM != 0 && c.cpl == 0 then unsupported "IRET to virtual-8086 mode"
  let cs ← codeForReturn csel
  let rpl := csel.toUInt32 &&& 3
  let cpl := c.cpl
  -- flags that may change
  let mut mask : UInt32 := Flag.CF ||| Flag.PF ||| Flag.AF ||| Flag.ZF ||| Flag.SF ||| Flag.TF |||
                           Flag.DF ||| Flag.OF ||| Flag.NT
  if opsz == 4 then mask := mask ||| Flag.RF ||| Flag.AC ||| Flag.ID
  if cpl ≤ c.iopl then mask := mask ||| Flag.IF
  if cpl == 0 then mask := mask ||| Flag.IOPL
  let newFlags := (c.eflags &&& ~~~mask) ||| (fl &&& mask)
  if ip > cs.limit then gp 0
  if rpl == cpl then
    addSp (3 * opsz.toUInt32)
    modCpu fun c => { c with cs, eip := ip, eflags := newFlags }
  else
    let nsp ← peek opsz (3 * opsz.toUInt32)
    let nss := (← peek opsz (4 * opsz.toUInt32)).toUInt16
    let ss ← segFor SegN.SS nss rpl
    modCpu fun c => { c with cs, eip := ip, eflags := newFlags, ss,
                             esp := if ss.big then nsp else (c.esp &&& 0xFFFF0000) ||| (nsp &&& 0xFFFF) }
    nullInaccessible rpl

end X86
