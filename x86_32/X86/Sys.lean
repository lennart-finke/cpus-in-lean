import X86.Ext.LongModeBase
import X86.Ext.SvmBase
/-!
# System architecture

Stack operations, descriptor tables and segment loads, far control transfers (including call
gates with inner-stack switch and parameter copying), hardware task switching (JMP/CALL to a TSS
or task gate, task gates in the IDT, IRET with NT), interrupt/exception delivery through the IDT,
and IRET. Virtual-8086 mode: entry by IRET from CPL 0 or by a task switch, interrupts and exceptions
to ring-0 handlers, IOPL-sensitive INT n and IRET (PUSHF, POPF, CLI and STI are in `Exec`), and the
CR4.VME/PVI extensions (system workstream B). System-management mode: SMI entry and RSM.

Long mode (EFER.LMA = 1) differs at the places marked `LongMode.` (`X86/Ext/LongModeBase.lean`):
64-bit IDT and call gates, no task switches, returns to 64-bit code.
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

/-- Segment register cache in virtual-8086 mode: base = selector × 16, 64 KiB, DPL 3, writable. -/
@[inline] def vm86Seg (sel : UInt32) : SegReg :=
  { sel := sel.toUInt16, base := (sel &&& 0xFFFF) <<< 4, limit := 0xFFFF, attr := 0xF3 }

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

/-! ## Hardware task switching

A task switch saves the dynamic state of the current task in its TSS (TR), and loads the state of
the new task from its TSS: CR3 (32-bit TSS with paging on), EFLAGS, EIP, the general registers,
the segment selectors and LDTR. It is caused by JMP or CALL to a TSS descriptor or task gate, by an
interrupt or exception through a task gate in the IDT, and by IRET with EFLAGS.NT set (return to the
task in the previous-task link). CALL and interrupts nest: they write the link field of the new TSS,
set the new task's NT flag and leave the old TSS busy; JMP and IRET clear the old task's busy flag.

Once TR has been loaded the switch has committed (SDM 7.3, step 10): a fault while loading the new
task's segment registers is delivered in the context of the new task. `keepCpu` tells `execInstr`
and `raiseExc` not to roll the CPU state back for such faults. -/

inductive TaskSrc where
  | jmp | call | iret | int
  deriving BEq, Inhabited

/-- Read a descriptor for a task switch: table-limit violations raise #TS instead of #GP. -/
def tsDesc (sel : UInt16) (ext : UInt32) : M (Desc × UInt32) :=
  tryCatch (readDesc sel ext) fun f => match f with
    | .exc 13 _ _ => exc Vec.TS (some ((sel.toUInt32 &&& 0xFFFC) ||| ext))
    | f => throw f

/-- Load a code/data segment register of the new task (protected mode, CPL `cpl`), with the task
switch checks: #TS for invalid selectors or descriptors, #NP (#SS for SS) if not present. -/
def tsLoadSeg (s : UInt8) (sel : UInt16) (cpl ext : UInt32) : M Unit := do
  let rpl := sel.toUInt32 &&& 3
  let err := (sel.toUInt32 &&& 0xFFFC) ||| ext
  if sel &&& 0xFFFC == 0 then
    if s == SegN.CS || s == SegN.SS then exc Vec.TS (some err)
    modCpu (·.setSeg s { sel, base := 0, limit := 0, attr := 0 })
    return
  let (d, addr) ← tsDesc sel ext
  if !d.isSeg then exc Vec.TS (some err)
  if s == SegN.CS then
    if !d.isCode then exc Vec.TS (some err)
    if (d.conforming && d.dpl > rpl) || (!d.conforming && d.dpl != rpl) then exc Vec.TS (some err)
    if !d.present then exc Vec.NP (some err)
  else if s == SegN.SS then
    if rpl != cpl || d.isCode || !d.readWrite || d.dpl != cpl then exc Vec.TS (some err)
    if !d.present then exc Vec.SS (some err)
  else
    if d.isCode && !d.readWrite then exc Vec.TS (some err)
    if (!d.isCode || !d.conforming) && (d.dpl < cpl || d.dpl < rpl) then exc Vec.TS (some err)
    if !d.present then exc Vec.NP (some err)
  let d ← setAccessed d addr
  modCpu (·.setSeg s (d.toSeg sel))

/-- Mark the instruction's remaining faults as belonging to the new task (see above). -/
@[inline] def commitTask : M Unit := modM fun m => { m with keepCpu := true }

/-- Switch to the task whose (non-busy for JMP/CALL/INT, busy for IRET) TSS descriptor `d` at
linear address `daddr` is selected by `sel`. EIP must hold the old task's resume address. `ext`
is the EXT bit for error codes of faults raised by the switch. -/
def taskSwitch (sel : UInt16) (d : Desc) (daddr : UInt32) (src : TaskSrc) (ext : UInt32 := 0)
    (errc : Option UInt32 := none) : M Unit := do
  let c ← cpu
  let err := (sel.toUInt32 &&& 0xFFFC) ||| ext
  let t32 := d.sysType &&& 8 != 0
  if !d.present then exc Vec.NP (some err)
  if d.limit < (if t32 then 0x67 else 0x2B) then exc Vec.TS (some err)
  let otr := c.tr
  let o32 := otr.typ &&& 8 != 0
  if otr.limit < (if o32 then 0x67 else 0x2B) then
    exc Vec.TS (some ((otr.sel.toUInt32 &&& 0xFFFC) ||| ext))
  -- SVM task-switch intercept: after the incoming TSS (and task gate) checks, before the switch
  -- (AMD APM vol. 2, 15.14.1); `errc` the error code the new task would get
  Svm.taskSwitch sel (src == .iret) (src == .jmp) errc
  -- the new task's state: read once before modifying anything (so that its faults leave the old task
  -- intact) and again after the old state has been saved (SDM 7.3 steps 8 and 12: an IRET to the
  -- current task itself loads the state it has just saved)
  let nb := d.base
  let w : UInt32 := if t32 then 4 else 2
  let rdw := fun (o32off o16off : UInt32) => sysRd (nb + (if t32 then o32off else o16off)) w
  let readNew : M (UInt32 × UInt32 × UInt32 × Array UInt32 × Array UInt16 × UInt16 × Bool) := do
    let ncr3 ← if t32 then sysRd (nb + 0x1C) 4 else pure c.cr3
    let neip ← rdw 0x20 0x0E
    let nefl ← rdw 0x24 0x10
    let mut nregs : Array UInt32 := #[]
    for k in [0:8] do
      let v ← rdw (0x28 + 4 * k.toUInt32) (0x12 + 2 * k.toUInt32)
      nregs := nregs.push v
    let mut nsegs : Array UInt16 := #[]   -- ES CS SS DS FS GS
    for k in [0:6] do
      let v ← if t32 then sysRd (nb + 0x48 + 4 * k.toUInt32) 2
              else if k < 4 then sysRd (nb + 0x22 + 2 * k.toUInt32) 2 else pure 0
      nsegs := nsegs.push v.toUInt16
    let nldt := (← sysRd (nb + (if t32 then 0x60 else 0x2A)) 2).toUInt16
    let ntrap ← if t32 then pure ((← sysRd (nb + 0x64) 2) &&& 1 != 0) else pure false
    return (ncr3, neip, nefl, nregs, nsegs, nldt, ntrap)
  let _ ← readNew
  -- JMP / IRET: the old task is no longer busy
  if src == .jmp || src == .iret then
    let (od, oaddr) ← readDesc otr.sel
    sysWr (oaddr + 4) 4 (od.hi &&& ~~~0x200)
  -- save the old task's state
  let oefl := if src == .iret then c.eflags &&& ~~~Flag.NT else c.eflags
  let ob := otr.base
  let wro := fun (o32off o16off v : UInt32) =>
    if o32 then sysWr (ob + o32off) 4 v else sysWr (ob + o16off) 2 v
  wro 0x20 0x0E c.eip
  wro 0x24 0x10 oefl
  for k in [0:8] do wro (0x28 + 4 * k.toUInt32) (0x12 + 2 * k.toUInt32) (c.getReg k.toUInt8)
  for k in [0:6] do
    let s := (c.getSeg k.toUInt8).sel.toUInt32
    if o32 then sysWr (ob + 0x48 + 4 * k.toUInt32) 2 s
    else if k < 4 then sysWr (ob + 0x22 + 2 * k.toUInt32) 2 s
  let (ncr3, neip, nefl, nregs, nsegs, nldt, ntrap) ← readNew
  -- nesting: back link and NT
  let nefl := if src == .call || src == .int then nefl ||| Flag.NT else nefl
  if src == .call || src == .int then sysWr nb 2 otr.sel.toUInt32
  let d := if src != .iret then { d with hi := d.hi ||| 0x200 } else d
  if src != .iret then sysWr (daddr + 4) 4 d.hi
  -- commit: load TR, set CR0.TS
  modCpu fun c => { c with tr := d.toSeg sel, cr0 := c.cr0 ||| CR0.TS }
  commitTask
  if t32 && c.cr0 &&& CR0.PG != 0 then
    if c.cr4 &&& CR4.PAE != 0 then
      let p ← readPdptes ncr3
      modCpu fun c => { c with pdpte := p }
    modCpu fun c => { c with cr3 := ncr3 }
    flushTlb
  let nefl := if t32 then (nefl &&& Flag.valid) ||| 2
              else (c.eflags &&& 0xFFFF0000) ||| (nefl &&& 0xFFFF) ||| 2
  let neip := if t32 then neip else neip &&& 0xFFFF
  modCpu fun c => Id.run do
    -- local breakpoint enables are cleared on every task switch
    let mut c := { c.setDr7 (c.dr7 &&& ~~~0x55) with eflags := nefl, eip := neip }
    -- a 16-bit TSS loads only the low halves (the upper halves keep their values, as on QEMU)
    for k in [0:8] do
      let v := if t32 then nregs[k]! else (c.getReg k.toUInt8 &&& 0xFFFF0000) ||| nregs[k]!
      c := c.setReg k.toUInt8 v
    -- selectors first, with unusable caches: a fault below leaves them loaded (SDM 7.3)
    for k in [0:6] do c := c.setSeg k.toUInt8 { sel := nsegs[k]!, base := 0, limit := 0, attr := 0 }
    return { c with ldtr := { sel := nldt, base := 0, limit := 0, attr := 0 } }
  -- LDTR
  let lerr := (nldt.toUInt32 &&& 0xFFFC) ||| ext
  if nldt &&& 0xFFFC != 0 then
    if nldt &&& 4 != 0 then exc Vec.TS (some lerr)
    let (ld, _) ← tsDesc nldt ext
    if ld.isSeg || ld.sysType != 2 then exc Vec.TS (some lerr)
    if !ld.present then exc Vec.TS (some lerr)
    modCpu fun c => { c with ldtr := ld.toSeg nldt }
  -- segment registers
  if nefl &&& Flag.VM != 0 then
    modCpu fun c => Id.run do
      let mut c := c
      for k in [0:6] do
        let s := nsegs[k]!
        c := c.setSeg k.toUInt8 { sel := s, base := s.toUInt32 <<< 4, limit := 0xFFFF, attr := 0xF3 }
      return c
  else
    let cpl := nsegs[1]!.toUInt32 &&& 3
    tsLoadSeg SegN.CS nsegs[1]! cpl ext
    tsLoadSeg SegN.SS nsegs[2]! cpl ext
    for s in [SegN.ES, SegN.DS, SegN.FS, SegN.GS] do
      tsLoadSeg s nsegs[s.toNat]! cpl ext
  if neip > (← cpu).cs.limit then exc Vec.GP (some ext)
  -- T flag of the new TSS: debug trap (DR6.BT) before its first instruction
  if ntrap then modM fun m => { m with dbPend := m.dbPend ||| DR6.BT }

/-- Resolve the TSS of a task gate (in the GDT, available) for JMP/CALL/INT through the gate. -/
def taskGateTss (g : Desc) (ext : UInt32) : M (UInt16 × Desc × UInt32) := do
  let tsel := (g.lo >>> 16).toUInt16
  let terr := (tsel.toUInt32 &&& 0xFFFC) ||| ext
  if tsel &&& 4 != 0 || tsel &&& 0xFFFC == 0 then gp terr
  let (td, taddr) ← readDesc tsel ext
  if td.isSeg || !(td.sysType == 1 || td.sysType == 9) then gp terr
  if !td.present then exc Vec.NP (some terr)
  return (tsel, td, taddr)

/-- Inner-level stack (SS selector, cache and ESP) for privilege level `ndpl`, from the current TSS,
with the checks of an inter-privilege CALL or interrupt (#TS, #SS). -/
def innerStack (ndpl extB : UInt32) : M (UInt16 × SegReg × UInt32) := do
  let tr := (← cpu).tr
  let tss32 := tr.typ &&& 8 != 0
  let (spOff, ssOff, w) := if tss32 then (4 + ndpl * 8, 8 + ndpl * 8, 4) else (2 + ndpl * 4, 4 + ndpl * 4, 2)
  if ssOff + 1 > tr.limit || spOff + w - 1 > tr.limit then
    exc Vec.TS (some ((tr.sel.toUInt32 &&& 0xFFFC) ||| extB))
  let nesp ← sysRd (tr.base + spOff) w
  let nssSel := (← sysRd (tr.base + ssOff) 2).toUInt16
  let ssErr := (nssSel.toUInt32 &&& 0xFFFC) ||| extB
  if nssSel &&& 0xFFFC == 0 then exc Vec.TS (some extB)
  let (sd, saddr) ← tsDesc nssSel extB   -- beyond the table limit: #TS (SDM CALL, INT)
  if (nssSel.toUInt32 &&& 3) != ndpl || sd.dpl != ndpl || sd.isCode || !sd.isSeg || !sd.readWrite then
    exc Vec.TS (some ssErr)
  if !sd.present then exc Vec.SS (some ssErr)
  let sd ← setAccessed sd saddr
  return (nssSel, sd.toSeg nssSel, nesp)

/-! ## Far control transfers -/

/-- Check a code segment descriptor `d` (selected by `sel`) as a direct far JMP/CALL target.
Returns the CS cache. -/
def codeForJump (sel : UInt16) (d : Desc) (addr off : UInt32) : M SegReg := do
  let cpl := (← cpu).cpl
  let err := sel.toUInt32 &&& 0xFFFC
  if !d.isCode || LongMode.reservedCode (← cpu) d.hi then gp err
  if d.conforming then
    if d.dpl > cpl then gp err
  else if (sel.toUInt32 &&& 3) > cpl || d.dpl != cpl then gp err
  if !d.present then exc Vec.NP (some err)
  if !LongMode.limitOk (← cpu) (d.toSeg sel) off then gp 0
  let d ← setAccessed d addr
  return d.toSeg ((sel &&& 0xFFFC) ||| cpl.toUInt16)

/-- Far CALL or JMP through the call gate `g` (selected by `gsel`). A CALL to a more privileged
non-conforming segment switches to the inner stack from the TSS and copies the gate's parameter
count of words/dwords from the old stack. Pushes have the gate's size. -/
def callGate (gsel : UInt16) (g : Desc) (call : Bool) : M Unit := do
  let c ← cpu
  let cpl := c.cpl
  let gerr := gsel.toUInt32 &&& 0xFFFC
  if g.dpl < cpl || g.dpl < (gsel.toUInt32 &&& 3) then gp gerr
  if !g.present then exc Vec.NP (some gerr)
  let tsel := (g.lo >>> 16).toUInt16
  let terr := tsel.toUInt32 &&& 0xFFFC
  if terr == 0 then gp 0
  let (d, daddr) ← readDesc tsel
  if !d.isCode || d.dpl > cpl then gp terr
  if !call && !d.conforming && d.dpl != cpl then gp terr
  if !d.present then exc Vec.NP (some terr)
  let g32 := g.sysType &&& 8 != 0
  let gsz : Sz := if g32 then 4 else 2
  let off := if g32 then (g.lo &&& 0xFFFF) ||| (g.hi &&& 0xFFFF0000) else g.lo &&& 0xFFFF
  if call && !d.conforming && d.dpl < cpl then
    let ndpl := d.dpl
    let (nssSel, nss, nesp) ← innerStack ndpl 0
    let pc := (g.hi &&& 0x1F).toNat
    -- the new stack must have room for the whole frame (old SS:ESP, parameters, return address):
    -- #SS(new SS selector) before anything is pushed and before the offset check (SDM CALL)
    for j in [1:pc + 5] do
      let o := nesp - j.toUInt32 * gsz.toUInt32
      if !segAllowed nss (if nss.big then o else o &&& 0xFFFF) gsz.toUInt32 true then
        exc Vec.SS (some (nssSel.toUInt32 &&& 0xFFFC))
    -- the parameters are read from the caller's stack at the caller's CPL (before CS changes), as
    -- QEMU does; neither manual's CALL pseudocode says at which privilege (visible only with SMAP)
    let mut params : Array UInt32 := #[]
    for k in [0:pc] do params := params.push (← peek gsz (k.toUInt32 * gsz.toUInt32))
    if off > d.limit then gp 0
    let d ← setAccessed d daddr
    modCpu fun c => { c with ss := nss, esp := nesp,
                             cs := d.toSeg ((tsel &&& 0xFFFC) ||| ndpl.toUInt16) }
    push gsz c.ss.sel.toUInt32
    push gsz c.esp
    for k in [0:pc] do push gsz params[pc - 1 - k]!
    push gsz c.cs.sel.toUInt32
    push gsz c.eip
    setEip off
  else
    if off > d.limit then gp 0
    let d ← setAccessed d daddr
    if call then
      push gsz c.cs.sel.toUInt32
      push gsz c.eip
    modCpu fun c => { c with cs := d.toSeg ((tsel &&& 0xFFFC) ||| cpl.toUInt16), eip := off }

/-- Far JMP (`call = false`) or far CALL to `sel:off`: to a code segment, through a call gate, or to
another task (TSS descriptor or task gate). EIP holds the return address. -/
def farJump (sel : UInt16) (off : UInt32) (call : Bool) (opsz : Sz) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then
    if call then
      push opsz c.cs.sel.toUInt32
      push opsz c.eip
    modCpu fun c => { c with cs := { c.cs with sel, base := sel.toUInt32 <<< 4 }, eip := off }
    return
  let err := sel.toUInt32 &&& 0xFFFC
  if err == 0 then gp 0
  let (d, addr) ← readDesc sel
  if d.isSeg then
    let cs ← codeForJump sel d addr off
    if call then
      push opsz c.cs.sel.toUInt32
      push opsz c.eip
    modCpu fun c => { c with cs, eip := off }
    if LongMode.lma c && LongMode.lBit cs then LongMode.enter64 0 (if call then "far CALL" else "far JMP")
  else if LongMode.lma c then LongMode.gateLong sel d.lo d.hi addr call
  else
    let t := d.sysType
    let rpl := sel.toUInt32 &&& 3
    if t == 4 || t == 0xC then callGate sel d call
    else if t == 1 || t == 9 then
      -- TSS descriptors live only in the GDT: one reached through the LDT is a #GP (SDM 7.2.2)
      if sel &&& 4 != 0 then gp err
      if d.dpl < c.cpl || d.dpl < rpl then gp err
      taskSwitch sel d addr (if call then .call else .jmp)
    else if t == 5 then
      if d.dpl < c.cpl || d.dpl < rpl then gp err
      if !d.present then exc Vec.NP (some err)
      let (tsel, td, taddr) ← taskGateTss d 0
      taskSwitch tsel td taddr (if call then .call else .jmp)
    else gp err

/-- Null data segment registers that are not accessible at the new (outer) privilege level. A register
holding a null selector (with any RPL) also becomes 0: IRET's pseudocode tests `SegmentSelector = NULL`
explicitly, and for RET the hidden part of such a register describes no segment (DPL 0 < CPL). -/
def nullInaccessible (cpl : UInt32) : M Unit := modCpu fun c =>
  let fix := fun (sr : SegReg) =>
    let dataOrNc := !sr.isCode || sr.attr &&& 4 == 0
    if sr.sel &&& 0xFFFC == 0 || (sr.present && dataOrNc && sr.dpl < cpl) then { sr with sel := 0, attr := 0 }
    else sr
  { c with es := fix c.es, ds := fix c.ds, fs := fix c.fs, gs := fix c.gs }

/-- Code segment check for a return (RETF / IRET) to selector `sel` with RPL ≥ CPL. -/
def codeForReturn (sel : UInt16) : M SegReg := do
  let c ← cpu
  let rpl := sel.toUInt32 &&& 3
  let err := sel.toUInt32 &&& 0xFFFC
  if err == 0 then gp 0
  if rpl < c.cpl then gp err
  let (d, addr) ← readDesc sel
  if !d.isCode || LongMode.reservedCode c d.hi then gp err
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
      if !LongMode.limitOk c cs ip then gp 0
      addSp (2 * opsz.toUInt32 + imm)
      modCpu fun c => { c with cs, eip := ip }
    else
      let o := 2 * opsz.toUInt32 + imm
      let nsp ← peek opsz o
      let nss := (← peek opsz (o + opsz.toUInt32)).toUInt16
      let ss ← if LongMode.nullSsOk c cs nss rpl then pure (LongMode.nullSs nss rpl) else segFor SegN.SS nss rpl
      if !LongMode.limitOk c cs ip then gp 0
      -- to 64-bit code the stack pointer is 64 bits wide and SS.B is ignored (AMD APM vol. 2, 2.4.5;
      -- vol. 3 RET (Far) "RSP.s = temp_RSP + temp_IMM"): RSP = the popped (zero-extended) value + imm;
      -- otherwise a 16-bit outer stack receives only SP: ESP[31:16] keep their value, as for IRET
      let r := nsp.toUInt64 + imm.toUInt64
      let to64 := LongMode.lma c && LongMode.lBit cs
      modCpu fun c => { c with cs, eip := ip, ss,
                               esp := if ss.big || to64 then nsp + imm else (c.esp &&& 0xFFFF0000) ||| ((nsp + imm) &&& 0xFFFF),
                               lmx := if to64 then { c.lmx with rspHi := (r >>> 32).toUInt32 } else c.lmx }
      nullInaccessible rpl
    if LongMode.lma c && LongMode.lBit cs then LongMode.enter64 0 "far RET"

/-! ## Interrupts and exceptions -/

/-- The state in which an interrupt or exception from virtual-8086 mode pushes its frame: the ring-0
stack and handler CS loaded and EFLAGS.VM cleared, so that the pushes are made at CPL 0
(`leaveV86_cpl`, `Proofs/ExtSysB.lean`). -/
@[inline] def Cpu.leaveV86 (c : Cpu) (ss : SegReg) (esp : UInt32) (cs : SegReg) : Cpu :=
  { c with ss, esp, cs, eflags := c.eflags &&& ~~~Flag.VM }

/-- Deliver interrupt/exception `vec`. `soft` marks INT n / INT3 / INTO (gate DPL is checked);
`ext` marks an external event (sets the EXT bit of error codes). EIP must already hold
the return address. -/
def deliver (vec : UInt8) (err : Option UInt32) (soft ext : Bool) : M Unit := do
  let c ← cpu
  if LongMode.lma c then return ← LongMode.deliverLong vec err soft ext
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
  let extB : UInt32 := if ext then 1 else 0
  let gerr := v * 8 + 2 + extB
  if v * 8 + 7 > c.idtLimit then gp gerr
  let lo ← sysRd (c.idtBase + v * 8) 4
  let hi ← sysRd (c.idtBase + v * 8 + 4) 4
  let gtype := (hi >>> 8) &&& 0x1F
  if !(gtype == 0x05 || gtype == 0x06 || gtype == 0x07 || gtype == 0x0E || gtype == 0x0F) then gp gerr
  let gdpl := (hi >>> 13) &&& 3
  if soft && gdpl < c.cpl then gp gerr
  if hi &&& 0x8000 == 0 then exc Vec.NP (some gerr)
  if gtype == 0x05 then
    -- task gate: switch tasks (nesting), then push the error code on the new task's stack
    let (tsel, td, taddr) ← taskGateTss { lo, hi } extB
    taskSwitch tsel td taddr .int extB err
    if let some e := err then push (if td.sysType &&& 8 != 0 then 4 else 2) e
    return
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
  let clr := Flag.TF ||| Flag.NT ||| Flag.RF ||| Flag.VM ||| (if gtype &&& 1 == 0 then Flag.IF else 0)
  if c.vm86 then
    -- from virtual-8086 mode: only to a non-conforming ring-0 handler, on the ring-0 stack; the
    -- data segment registers are saved on the stack and nulled. VM is cleared before the pushes:
    -- they are made at CPL 0, i.e. supervisor accesses (not user accesses, no #AC; SDM vol. 3,
    -- INT pseudocode INTERRUPT-FROM-VIRTUAL-8086-MODE: "VM ← 0; ... CPL ← 0" before "Push(GS)";
    -- AMD APM vol. 2, 8.9.3; SDM vol. 3, 4.6: accesses made while CPL < 3 are supervisor accesses).
    -- The pushed EFLAGS image is the one before the event (VM = 1).
    if d.conforming || d.dpl != 0 then gp serr
    let (_, nss, nesp) ← innerStack 0 extB
    modCpu fun c => c.leaveV86 nss nesp (d.toSeg (sel &&& 0xFFFC))
    for sr in [c.gs, c.fs, c.ds, c.es] do push gsz sr.sel.toUInt32
    push gsz c.ss.sel.toUInt32
    push gsz c.esp
    push gsz c.eflags
    push gsz c.cs.sel.toUInt32
    push gsz c.eip
    if let some e := err then push gsz e
    let null : SegReg := { sel := 0, base := 0, limit := 0, attr := 0 }
    modCpu fun c => { c with eip := off, eflags := c.eflags &&& ~~~clr,
                             es := null, ds := null, fs := null, gs := null }
    return
  let oldFlags := c.eflags
  let oldCs := c.cs.sel.toUInt32
  let oldEip := c.eip
  if !d.conforming && d.dpl < c.cpl then
    -- inter-privilege: fetch the inner stack from the TSS
    let ndpl := d.dpl
    let (_, nss, nesp) ← innerStack ndpl extB
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
  modCpu fun c => { c with eip := off, eflags := c.eflags &&& ~~~clr }

/-! ## Virtual-8086 mode extensions and protected-mode virtual interrupts

CR4.VME (AMD APM vol. 2, 8.10.1; vol. 3 CLI, STI, PUSHF, POPF, IRET, INT; SDM vol. 3, 23.3) changes
the IOPL-sensitive instructions of virtual-8086 code running with IOPL < 3: CLI and STI clear and
set the virtual interrupt flag VIF instead of IF (STI with VIP = 1 is #GP(0)); the 16-bit PUSHF
pushes FLAGS with VIF in the IF position and IOPL = 3; the 16-bit POPF and IRET load FLAGS except IF
and IOPL and copy the popped IF into VIF, and raise #GP(0) if the popped TF is 1 or the popped IF is 1
while VIP = 1; their 32-bit forms stay #GP(0). INT n (CD) consults the interrupt redirection bitmap
(IRB, the 32 bytes below the I/O permission bitmap in the TSS; AMD table 8-11): with the vector's
bit clear it is redirected to the 8086 handler of the real-mode vector table at linear 0 (with any
IOPL), with the bit set it is handled as without VME (#GP(0) with IOPL < 3). INT3, INTO and INT1 are
never redirected. CR4.PVI (AMD 8.10.2) makes CLI and STI at CPL 3 in protected mode with IOPL < 3
work on VIF the same way; nothing else changes. The processor never sets VIP; VIF and VIP are loaded
by IRETD at CPL 0, IRET to virtual-8086 mode, task switches and RSM (`Flag.valid`). Where the AMD
manuals do not say (the TSS limit for the IRB), the IRB bytes are read like the I/O map base: an
offset beyond the TSS limit is #GP(0) (AMD 12.2.2), also for a 16-bit TSS (AMD's INT pseudocode
reads the IRB through the I/O map base word at offset 102 for any TSS). -/

/-- VME applies to an IOPL-sensitive instruction: virtual-8086 mode with CR4.VME and IOPL < 3. -/
@[inline] def Cpu.vmeActive (c : Cpu) : Bool := c.vm86 && c.cr4 &&& CR4.VME != 0 && c.iopl < 3

/-- CLI/STI work on VIF: VME (`vmeActive`), or PVI at CPL 3 in protected mode with IOPL < 3. -/
@[inline] def Cpu.virtualIf (c : Cpu) : Bool :=
  c.vmeActive || (c.pe && !c.vm86 && c.cr4 &&& CR4.PVI != 0 && c.cpl == 3 && c.iopl < 3)

/-- The FLAGS image that PUSHF and a redirected INT n push under VME with IOPL < 3: VIF in the IF
position, IOPL = 3 (AMD APM vol. 3 PUSHF, INT). -/
def vmeFlagsImage (fl : UInt32) : UInt32 :=
  ((fl &&& 0xFFFF &&& ~~~(Flag.IF ||| Flag.IOPL)) ||| (if fl &&& Flag.VIF != 0 then Flag.IF else 0)) ||| Flag.IOPL

/-- POPF and IRET under VME raise #GP(0) for a popped image with TF = 1, or IF = 1 while VIP = 1. -/
@[inline] def vmePopFault (old v : UInt32) : Bool :=
  v &&& Flag.TF != 0 || (v &&& Flag.IF != 0 && old &&& Flag.VIP != 0)

/-- EFLAGS after a 16-bit POPF or IRET under VME: FLAGS[15:0] from the image except IF and IOPL,
VIF = the image's IF, bits 31:16 otherwise unchanged. -/
def vmePopFlags (old v : UInt32) : UInt32 :=
  let keep : UInt32 := 0xFFFF0000 ||| Flag.IF ||| Flag.IOPL
  let r := (old &&& keep &&& ~~~Flag.VIF) ||| (v &&& Flag.valid &&& 0xFFFF &&& ~~~keep)
  (r ||| (if v &&& Flag.IF != 0 then Flag.VIF else 0)) ||| 2

/-- EFLAGS after a redirected INT n: TF and RF cleared, and IF (IOPL = 3) or VIF (IOPL < 3). -/
def vmeIntFlags (fl : UInt32) : UInt32 :=
  fl &&& ~~~(Flag.TF ||| Flag.RF ||| (if (fl >>> 12) &&& 3 == 3 then Flag.IF else Flag.VIF))

/-- Whether INT `n` in virtual-8086 mode with CR4.VME is redirected: bit `n` of the IRB is clear. -/
def vmeRedirected (n : UInt8) : M Bool := do
  let tr := (← cpu).tr
  if 0x67 > tr.limit then gp 0
  let iomap ← sysRd (tr.base + 0x66) 2
  let off := iomap - 32 + (n.toUInt32 >>> 3)
  if off > tr.limit then gp 0
  let b ← sysRd (tr.base + off) 1
  return (b >>> (n.toUInt32 &&& 7)) &&& 1 == 0

/-- INT n redirected to the 8086 handler (AMD APM vol. 3 INT, "virtual-8086 mode with VME"): the
vector's CS:IP from linear address 4n (a user-mode read through paging, no limit check), then FLAGS
(with VIF as IF and IOPL = 3 if IOPL < 3), CS and IP pushed with 16-bit pushes, as in real mode.
EIP holds the return address. -/
def vmeInt (n : UInt8) : M Unit := do
  let c ← cpu
  let ip ← linRd (n.toUInt32 * 4) 2 true
  let cs ← linRd (n.toUInt32 * 4 + 2) 2 true
  push 2 (if c.iopl < 3 then vmeFlagsImage c.eflags else c.eflags &&& 0xFFFF)
  push 2 c.cs.sel.toUInt32
  push 2 (c.eip &&& 0xFFFF)
  modCpu fun c => { c with eip := ip, cs := vm86Seg cs, eflags := vmeIntFlags c.eflags }

/-- IRET / IRETD. (An IRET that completes also ends the blocking of NMIs:
`Step.iretUnblock`.) -/
def iret (opsz : Sz) : M Unit := do
  let c ← cpu
  if !c.pe then
    let ip ← pop opsz
    let cs ← pop opsz
    let fl ← pop opsz
    -- real-address mode: VM, VIF and VIP are not loaded (SDM IRET: "(EFLAGS AND 1A0000H)")
    let keep := if opsz == 4 then Flag.VM ||| Flag.VIF ||| Flag.VIP else 0xFFFF0000
    let mask := Flag.valid &&& ~~~keep
    modCpu fun c => { c with eip := ip, cs := { c.cs with sel := cs.toUInt16, base := (cs &&& 0xFFFF) <<< 4 },
                             eflags := ((c.eflags &&& ~~~mask) ||| (fl &&& mask)) ||| 2 }
    return
  if c.vm86 then
    -- IOPL-sensitive; at IOPL 3 a real-mode style return that cannot change VM, IOPL, VIF or VIP
    if c.iopl < 3 then
      -- CR4.VME: the 16-bit IRET works on VIF (see `vmePopFlags`)
      if c.cr4 &&& CR4.VME == 0 || opsz == 4 then gp 0
      let ip ← peek 2 0
      let cs ← peek 2 2
      let fl ← peek 2 4
      if vmePopFault c.eflags fl then gp 0
      addSp 6
      modCpu fun c => { c with eip := ip, cs := vm86Seg cs, eflags := vmePopFlags c.eflags fl }
      return
    let ip ← peek opsz 0
    let cs ← peek opsz opsz.toUInt32
    let fl ← peek opsz (2 * opsz.toUInt32)
    if ip > 0xFFFF then gp 0
    addSp (3 * opsz.toUInt32)
    let mask := (if opsz == 4 then Flag.valid else Flag.valid &&& 0xFFFF) &&& ~~~(Flag.VM ||| Flag.IOPL ||| Flag.VIF ||| Flag.VIP)
    modCpu fun c => { c with eip := ip, cs := vm86Seg cs,
                             eflags := ((c.eflags &&& ~~~mask) ||| (fl &&& mask)) ||| 2 }
    return
  if c.eflags &&& Flag.NT != 0 then
    -- no task switches in long mode (APM vol. 3 IRET: #GP(0))
    if LongMode.lma c then gp 0
    -- return to the task in the previous-task link of the current TSS
    let link := (← sysRd c.tr.base 2).toUInt16
    let lerr := link.toUInt32 &&& 0xFFFC
    if link &&& 4 != 0 || lerr == 0 then exc Vec.TS (some lerr)
    let (d, addr) ← tsDesc link 0
    if d.isSeg || !(d.sysType == 3 || d.sysType == 0xB) then exc Vec.TS (some lerr)
    taskSwitch link d addr .iret
    return
  let ip ← peek opsz 0
  let csel := (← peek opsz opsz.toUInt32).toUInt16
  let fl ← peek opsz (2 * opsz.toUInt32)
  if opsz == 4 && fl &&& Flag.VM != 0 && c.cpl == 0 && !LongMode.lma c then
    -- return to virtual-8086 mode: the frame also holds ESP, SS, ES, DS, FS, GS
    let mut v : Array UInt32 := #[]
    for k in [3:9] do v := v.push (← peek 4 (4 * k.toUInt32))
    if ip > 0xFFFF then gp 0
    modCpu fun c => { c with eip := ip, eflags := (fl &&& Flag.valid) ||| 2, cs := vm86Seg csel.toUInt32,
                             esp := v[0]!, ss := vm86Seg v[1]!, es := vm86Seg v[2]!, ds := vm86Seg v[3]!,
                             fs := vm86Seg v[4]!, gs := vm86Seg v[5]! }
    return
  let cs ← codeForReturn csel
  let rpl := csel.toUInt32 &&& 3
  let cpl := c.cpl
  -- flags that may change
  let mut mask : UInt32 := Flag.CF ||| Flag.PF ||| Flag.AF ||| Flag.ZF ||| Flag.SF ||| Flag.TF |||
                           Flag.DF ||| Flag.OF ||| Flag.NT
  if opsz == 4 then mask := mask ||| Flag.RF ||| Flag.AC ||| Flag.ID
  if cpl ≤ c.iopl then mask := mask ||| Flag.IF
  if cpl == 0 then mask := mask ||| Flag.IOPL
  -- VIF and VIP are loaded only by IRETD at CPL 0 (AMD APM vol. 3 IRET: "VIF,VIP,IOPL only changed
  -- if old_CPL == 0"; SDM IRET: "IF OperandSize = 32 THEN EFLAGS(VIF, VIP)")
  if cpl == 0 && opsz == 4 then mask := mask ||| Flag.VIF ||| Flag.VIP
  let newFlags := (c.eflags &&& ~~~mask) ||| (fl &&& mask)
  if !LongMode.limitOk c cs ip then gp 0
  if rpl == cpl then
    addSp (3 * opsz.toUInt32)
    modCpu fun c => { c with cs, eip := ip, eflags := newFlags }
  else
    let nsp ← peek opsz (3 * opsz.toUInt32)
    let nss := (← peek opsz (4 * opsz.toUInt32)).toUInt16
    let ss ← if LongMode.nullSsOk c cs nss rpl then pure (LongMode.nullSs nss rpl) else segFor SegN.SS nss rpl
    -- to 64-bit code RSP is the popped value, whatever SS.B (APM vol. 3 IRET "RSP.s = temp_RSP"; in 64-bit
    -- mode the stack size is 64 bits, vol. 2, 2.4.5); otherwise a 16-bit stack receives only SP
    let to64 := LongMode.lma c && LongMode.lBit cs
    modCpu fun c => { c with cs, eip := ip, eflags := newFlags, ss,
                             esp := if ss.big || to64 then nsp else (c.esp &&& 0xFFFF0000) ||| (nsp &&& 0xFFFF),
                             lmx := if to64 then { c.lmx with rspHi := 0 } else c.lmx }
    nullInaccessible rpl
  if LongMode.lma c && LongMode.lBit cs then LongMode.enter64 0 "IRET"

/-! ## System-management mode

An SMI (here: a write to the APM control port 0xB2, as on PIIX4/ICH chipsets with APMC SMIs
enabled) is taken at an instruction boundary. The processor saves its state in the SMRAM state-save
area at `smbase + FE00h..FFFFh` and enters SMM at `smbase:8000` in a real-mode-like environment with
4 GiB segment limits (AMD APM vol. 2, table 10-3: CR0.PE/EM/TS/PG, CR4, EFER and DR7 cleared or
reset); RSM restores the saved state. SMRAM protection belongs to the chipset and is not modelled.
SMM entry blocks NMIs; RSM restores the NMI blocking state of the interrupted context, and an IRET in
SMM unblocks them.

**State-save map.** AMD64 processors use the AMD64 save-state map of APM vol. 2, table 10-1 in every
mode ("This 64-bit save-state map is used in all modes, regardless of mode", vol. 3 RSM; "the legacy
SMM state-save area format ... Implementations of the AMD64 architecture do not use this format",
vol. 2, 10.2.3), so the model, an AMD64 processor, uses it also for SMIs from legacy mode, and SMM can
be entered from long mode. Offsets from SMBASE: ES, CS, SS, DS, FS, GS at FE00h + 10h·k (selector
word, attributes word, limit dword, base qword), GDTR FE64h/FE68h, LDTR FE70h, IDTR FE84h/FE88h, TR
FE90h, EFER FED0h, revision FEFCh, SMBASE FF00h, CR4 FF48h, CR3 FF50h, CR0 FF58h, DR7 FF60h, DR6
FF68h, RFLAGS FF70h, RIP FF78h, R15..R8 FF80h..FFB8h, RDI, RSI, RBP, RSP, RBX, RDX, RCX, RAX FFC0h..FFF8h.
The attribute word holds descriptor bits 47:40 and 55:52 as `SegReg.attr` (the APM does not define
its layout; QEMU's AMD64 map uses this one). Not saved (10.2): CR2, CR8, DR0–DR3, x87/SSE state,
MSRs. The I/O-restart fields and the auto-halt restart byte are written as 0 (the model's SMIs come
from an OUT that has completed, and HLT is not restarted); the SVM fields (SVM Guest, VMCB address,
virtual interrupt, guest PAT, host EFER/CR4/CR0, nCR3) as `Svm.smmSave` says. The model keeps no
high halves of the general registers in compatibility mode: RAX..R15 are saved zero-extended, except
R11 (`LongModeState.r11`) and RIP/RSP (`ripHi`, `rspHi`). QEMU's qemu-system-i386, which has no long
mode, uses Intel's 32-bit map instead; `qemu-system-x86_64` with a long-mode CPU uses the AMD64 map
(with revision 20064h). -/

/-- SMM revision identifier (APM vol. 2, 10.2.4): bits 15:0 = 0064h (the AMD64 map), bit 16 I/O
instruction restart and bit 17 SMBASE relocation ("always set to 1" by AMD64 implementations). -/
def smmRevision : UInt32 := 0x00030064

/-- Offset (from SMBASE + 8000h) of the save-map slot of segment register `k` (ES, CS, SS, DS, FS, GS). -/
@[inline] def smmSegOff (k : UInt32) : UInt32 := 0x7E00 + 0x10 * k

/-- The 64-bit base of FS (`k` = 4) or GS (5): bits 63:32 from FS_BASE/GS_BASE if the cache is the one
WRMSR produced (`LongModeState.fsBase`), else the cache's 32-bit base. -/
def segBase64 (c : Cpu) (k : UInt8) (sr : SegReg) : UInt64 :=
  let saved := if k == SegN.FS then c.lmx.fsBase else if k == SegN.GS then c.lmx.gsBase else none
  match saved with
  | some (cache, b) => if cache == sr then b else sr.base.toUInt64
  | none => sr.base.toUInt64

/-- Enter SMM: save the state and load the SMM execution environment (APM vol. 2, 10.3, table 10-3). -/
def smmEnter : M Unit := do
  let c ← cpu
  let sb := c.smbase + 0x8000
  let w := fun (o v : UInt32) => physWr (sb + o).toUInt64 4 v
  let w2 := fun (o v : UInt32) => physWr (sb + o).toUInt64 2 (v &&& 0xFFFF)
  let w8 := fun (o : UInt32) (v : UInt64) => do w o v.toUInt32; w (o + 4) (v >>> 32).toUInt32
  for k in [0:6] do
    let s := c.getSeg k.toUInt8
    let o := smmSegOff k.toUInt32
    w2 o s.sel.toUInt32
    w2 (o + 2) s.attr
    w (o + 4) s.limit
    w8 (o + 8) (segBase64 c k.toUInt8 s)
  w 0x7E60 0; w2 0x7E64 c.gdtLimit; w2 0x7E66 0; w8 0x7E68 c.gdtBase.toUInt64
  w2 0x7E70 c.ldtr.sel.toUInt32; w2 0x7E72 c.ldtr.attr; w 0x7E74 c.ldtr.limit; w8 0x7E78 c.ldtr.base.toUInt64
  w 0x7E80 0; w2 0x7E84 c.idtLimit; w2 0x7E86 0; w8 0x7E88 c.idtBase.toUInt64
  w2 0x7E90 c.tr.sel.toUInt32; w2 0x7E92 c.tr.attr; w 0x7E94 c.tr.limit; w8 0x7E98 c.tr.base.toUInt64
  -- I/O restart RIP/RCX/RSI/RDI, I/O restart dword and bytes, auto-halt: none
  for k in [0:12] do w (0x7EA0 + 4 * k.toUInt32) 0
  w8 0x7ED0 c.efer.toUInt64
  -- SVM fields: guest mode, VMCB, virtual interrupt, nested-paging context (`Svm.smmSave`, 15.22)
  for (o, v) in Svm.smmSave c do w8 o v
  w 0x7EFC smmRevision
  w 0x7F00 c.smbase
  w8 0x7F48 c.cr4.toUInt64
  w8 0x7F50 c.cr3.toUInt64
  w8 0x7F58 c.cr0.toUInt64
  w8 0x7F60 c.dr7.toUInt64
  w8 0x7F68 c.dr6.toUInt64
  w8 0x7F70 c.eflags.toUInt64
  w8 0x7F78 (LongMode.rip c)
  -- R15 .. R8 (only R11 is kept by the model)
  for k in [0:8] do w8 (0x7F80 + 8 * k.toUInt32) (if k == 4 then c.lmx.r11 else 0)
  -- RDI, RSI, RBP, RSP, RBX, RDX, RCX, RAX
  let regs : List UInt64 := [c.edi.toUInt64, c.esi.toUInt64, c.ebp.toUInt64, LongMode.rsp c, c.ebx.toUInt64,
                             c.edx.toUInt64, c.ecx.toUInt64, c.eax.toUInt64]
  for (v, k) in regs.zip (List.range 8) do w8 (0x7FC0 + 8 * k.toUInt32) v
  let flat (sel : UInt16) (base : UInt32) : SegReg := { sel, base, limit := 0xFFFFFFFF, attr := 0x8093 }
  modCpu fun c => { c with
    smm := true, halted := false, shadow := false,
    -- SMM entry blocks NMIs (an NMI arriving in SMM stays latched); RSM restores the blocking state
    sysbx := { c.sysbx with smmNmiBlocked := c.sysbx.nmiBlocked, nmiBlocked := true },
    eflags := 2, eip := 0x8000,
    cr0 := c.cr0 &&& ~~~(CR0.PE ||| CR0.EM ||| CR0.TS ||| CR0.PG), cr4 := 0, dr7 := 0x400, bpOn := false,
    -- EFER = 0 (table 10-3), so LMA = 0: SMM code runs in legacy real or protected mode; SVME is kept,
    -- as RSM cannot change it (vol. 3 RSM: "RSM cannot modify EFER.SVME"): the interrupted host (or
    -- guest, 15.22) gets its SVME back
    efer := c.efer &&& EFER.SVME,
    cs := flat (c.smbase >>> 4).toUInt16 c.smbase,
    ds := flat 0 0, es := flat 0 0, ss := flat 0 0, fs := flat 0 0, gs := flat 0 0,
    lmx := { c.lmx with ripHi := 0, rspHi := 0, fsBase := none, gsBase := none } }
  flushTlbAll

/-- EFER after RSM from the saved image `e` (APM vol. 2, 10.4): LMA = the saved LME ∧ CR0.PG ∧
CR4.PAE ("The EFER.LMA register bit is set to the value obtained by logically ANDing the SMRAM values
of EFER.LME, CR0.PG, and CR4.PAE"), and SVME stays as it is (`cur`; vol. 3 RSM: "RSM cannot modify
EFER.SVME"). -/
def rsmEfer (e cur cr0 cr4 : UInt32) : UInt32 :=
  -- LMA (bit 10) = LME (bit 8) ∧ PG (CR0 bit 31) ∧ PAE (CR4 bit 5)
  let lma := ((e >>> 8) &&& (cr0 >>> 31) &&& (cr4 >>> 5) &&& 1) <<< 10
  (e &&& ~~~(EFER.LMA ||| EFER.SVME)) ||| (cur &&& EFER.SVME) ||| lma

/-- The saved state is invalid and RSM shuts the processor down (APM vol. 2, 10.4): CR0.PE = 0 with
PG = 1 unless EFER.SVME = 1 (`svme`, the EFER.SVME RSM leaves: paged real mode is legal with SVM
enabled, vol. 2 15.19, vol. 3 RSM; an SMI in a paged-real-mode guest returns to it), CR0.NW = 1 with CD = 0, CR0 bits 63:32, a reserved CR4 bit (every bit MOV CR4 accepts is valid:
an SMI taken while it is set must be able to return), DR6/DR7 bits 63:32, an unsupported EFER bit,
EFER.LME ∧ CR0.PG with CR4.PAE = 0, or with CS.L = CS.D = 1. -/
def rsmInvalid (cr0 cr4 dr6 dr7 efer : UInt64) (csAttr : UInt32) (svme : Bool := false) : Bool :=
  let c0 := cr0.toUInt32
  (c0 &&& CR0.PG != 0 && c0 &&& CR0.PE == 0 && !svme) || (c0 &&& CR0.NW != 0 && c0 &&& CR0.CD == 0) ||
  cr0 >>> 32 != 0 || cr4 &&& ~~~Cpuid.cr4Writable.toUInt64 != 0 || dr6 >>> 32 != 0 || dr7 >>> 32 != 0 ||
  efer &&& ~~~(Cpuid.eferWritable ||| EFER.LMA).toUInt64 != 0 ||
  (efer.toUInt32 &&& EFER.LME != 0 && c0 &&& CR0.PG != 0 &&
    (cr4.toUInt32 &&& CR4.PAE == 0 || csAttr &&& 0x6000 == 0x6000))

/-- Canonical form of a 48-bit virtual address (bits 63:48 copies of bit 47). -/
@[inline] def canon48 (v : UInt64) : UInt64 :=
  if v &&& 0x800000000000 != 0 then v ||| 0xFFFF000000000000 else v &&& 0x0000FFFFFFFFFFFF

/-- RSM: #UD outside SMM; otherwise restore the saved state of the AMD64 map (a relocated SMBASE takes
effect for the next SMI). An invalid saved state (`rsmInvalid`, or a changed revision identifier)
shuts the processor down; EFER.LMA is recomputed (`rsmEfer`), RFLAGS.VM = VM ∧ CR0.PE ∧ ¬LMA, FS/GS
bases are canonicalized, and the PDPTEs are reloaded for legacy PAE paging (10.4). -/
def rsm : M Unit := do
  let c ← cpu
  if !c.smm then ud
  let sb := c.smbase + 0x8000
  let r := fun (o : UInt32) => physRd (sb + o).toUInt64 4
  let r2 := fun (o : UInt32) => physRd (sb + o).toUInt64 2
  let r8 := fun (o : UInt32) => do
    let lo ← r o
    let hi ← r (o + 4)
    return (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let cr0q ← r8 0x7F58
  let cr4q ← r8 0x7F48
  let cr3q ← r8 0x7F50
  let dr6q ← r8 0x7F68
  let dr7q ← r8 0x7F60
  let eferq ← r8 0x7ED0
  let csAttr ← r2 (smmSegOff 1 + 2)
  let rev ← r 0x7EFC
  if rsmInvalid cr0q cr4q dr6q dr7q eferq csAttr (c.efer &&& EFER.SVME != 0) || rev != smmRevision then
    throw (.shutdown "RSM: invalid saved state")
  -- CR3 above 4 GiB (bits 51:32) cannot be held by the model's 32-bit CR3
  if cr3q >>> 32 != 0 then unsupported "RSM: CR3 above 4 GiB"
  let cr0 := cr0q.toUInt32 ||| CR0.ET
  let cr4 := cr4q.toUInt32
  let cr3 := cr3q.toUInt32
  let efer := rsmEfer eferq.toUInt32 c.efer cr0 cr4
  let lma := efer &&& EFER.LMA != 0
  let rfl ← r8 0x7F70
  let rip ← r8 0x7F78
  let mut regs : Array UInt64 := #[]
  for k in [0:8] do regs := regs.push (← r8 (0x7FC0 + 8 * k.toUInt32))
  let r11 ← r8 0x7FA0
  let seg := fun (sel attr limit : UInt32) (base : UInt64) =>
    ({ sel := sel.toUInt16, base := base.toUInt32, limit, attr := attr &&& 0xF0FF } : SegReg)
  let tr := seg (← r2 0x7E90) (← r2 0x7E92) (← r 0x7E94) (← r8 0x7E98)
  let ldtr := seg (← r2 0x7E70) (← r2 0x7E72) (← r 0x7E74) (← r8 0x7E78)
  let gdtLimit ← r2 0x7E64
  let gdtBase := (← r8 0x7E68).toUInt32
  let idtLimit ← r2 0x7E84
  let idtBase := (← r8 0x7E88).toUInt32
  let mut segs : Array (SegReg × UInt64) := #[]
  for k in [0:6] do
    let o := smmSegOff k.toUInt32
    let b ← r8 (o + 8)
    segs := segs.push (seg (← r2 o) (← r2 (o + 2)) (← r (o + 4)) b, b)
  let nsb ← if rev &&& 0x20000 != 0 then r 0x7F00 else pure c.smbase
  let fl := (rfl.toUInt32 &&& Flag.valid) ||| 2
  let fl := if cr0 &&& CR0.PE == 0 || lma then fl &&& ~~~Flag.VM else fl
  -- RIP/RSP bits 63:32 are kept only for a return to 64-bit mode (the model's invariant: 0 elsewhere)
  let in64 := lma && segs[1]!.1.attr &&& 0x2000 != 0
  let fsb := canon48 segs[4]!.2
  let gsb := canon48 segs[5]!.2
  modCpu fun c => Id.run do
    let c0 := c.setDr7 dr7q.toUInt32
    let mut c := { c0 with smm := false, smbase := nsb, cr0 := cr0, cr3 := cr3, cr4 := cr4, efer := efer }
    c := { c with eflags := fl, eip := rip.toUInt32, dr6 := dr6q.toUInt32, tr, ldtr, gdtBase, gdtLimit,
                  idtBase, idtLimit, sysbx := { c.sysbx with nmiBlocked := c.sysbx.smmNmiBlocked } }
    -- RDI, RSI, RBP, RSP, RBX, RDX, RCX, RAX
    let order : List UInt8 := [7, 6, 5, 4, 3, 2, 1, 0]
    for (reg, k) in order.zip (List.range 8) do c := c.setReg reg regs[k]!.toUInt32
    for k in [0:6] do c := c.setSeg k.toUInt8 segs[k]!.1
    -- FS/GS bases above 4 GiB as FS_BASE/GS_BASE would set them
    c := { c with lmx := { c.lmx with
      ripHi := if in64 then (rip >>> 32).toUInt32 else 0,
      rspHi := if in64 then (regs[3]! >>> 32).toUInt32 else 0,
      r11,
      fsBase := if fsb >>> 32 != 0 then some (c.fs, fsb) else none,
      gsBase := if gsb >>> 32 != 0 then some (c.gs, gsb) else none } }
    return c
  if cr0 &&& CR0.PG != 0 && cr4 &&& CR4.PAE != 0 && !lma then
    let p ← tryCatch (readPdptes cr3) fun _ => throw (.shutdown "RSM: invalid PDPTEs")
    modCpu fun c => { c with pdpte := p }
  flushTlbAll

end X86
