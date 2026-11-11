import X86.Io
/-!
# System architecture

Stack operations, descriptor tables and segment loads, far control transfers (including call
gates with inner-stack switch and parameter copying), hardware task switching (JMP/CALL to a TSS
or task gate, task gates in the IDT, IRET with NT), interrupt/exception delivery through the IDT,
and IRET. Virtual-8086 mode (without the CR4.VME extensions): entry by IRET from CPL 0 or by a task
switch, interrupts and exceptions to ring-0 handlers, IOPL-sensitive INT n and IRET (PUSHF, POPF,
CLI and STI are in `Exec`). System-management mode: SMI entry and RSM.
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
def taskSwitch (sel : UInt16) (d : Desc) (daddr : UInt32) (src : TaskSrc) (ext : UInt32 := 0) : M Unit := do
  let c ← cpu
  let err := (sel.toUInt32 &&& 0xFFFC) ||| ext
  let t32 := d.sysType &&& 8 != 0
  if !d.present then exc Vec.NP (some err)
  if d.limit < (if t32 then 0x67 else 0x2B) then exc Vec.TS (some err)
  let otr := c.tr
  let o32 := otr.typ &&& 8 != 0
  if otr.limit < (if o32 then 0x67 else 0x2B) then
    exc Vec.TS (some ((otr.sel.toUInt32 &&& 0xFFFC) ||| ext))
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
  if !d.isCode then gp err
  if d.conforming then
    if d.dpl > cpl then gp err
  else if (sel.toUInt32 &&& 3) > cpl || d.dpl != cpl then gp err
  if !d.present then exc Vec.NP (some err)
  if off > d.limit then gp 0
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
      -- a 16-bit outer stack receives only SP: ESP[31:16] keep their value, as for IRET
      modCpu fun c => { c with cs, eip := ip, ss,
                               esp := if ss.big then nsp + imm else (c.esp &&& 0xFFFF0000) ||| ((nsp + imm) &&& 0xFFFF) }
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
    taskSwitch tsel td taddr .int extB
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
    -- data segment registers are saved on the stack and nulled
    if d.conforming || d.dpl != 0 then gp serr
    let (_, nss, nesp) ← innerStack 0 extB
    modCpu fun c => { c with ss := nss, esp := nesp, cs := d.toSeg (sel &&& 0xFFFC) }
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
  if c.vm86 then
    -- IOPL-sensitive; at IOPL 3 a real-mode style return that cannot change VM or IOPL
    if c.iopl < 3 then gp 0
    let ip ← peek opsz 0
    let cs ← peek opsz opsz.toUInt32
    let fl ← peek opsz (2 * opsz.toUInt32)
    if ip > 0xFFFF then gp 0
    addSp (3 * opsz.toUInt32)
    let mask := (if opsz == 4 then Flag.valid else 0xFFFF) &&& ~~~(Flag.VM ||| Flag.IOPL)
    modCpu fun c => { c with eip := ip, cs := vm86Seg cs,
                             eflags := ((c.eflags &&& ~~~mask) ||| (fl &&& mask)) ||| 2 }
    return
  if c.eflags &&& Flag.NT != 0 then
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
  if opsz == 4 && fl &&& Flag.VM != 0 && c.cpl == 0 then
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

/-! ## System-management mode

An SMI (here: a write to the APM control port 0xB2, as on PIIX4/ICH chipsets with APMC SMIs
enabled) is taken at an instruction boundary. The processor saves its state in the 32-bit SMRAM
state-save map at `smbase + 0xFE00..0xFFFF` and enters SMM at `smbase:8000` in a real-mode-like
environment with 4 GiB segment limits; RSM restores the saved state (SDM 32.4-32.5). The SDM leaves
the save locations of hidden state (descriptor caches, table registers, CR4) implementation-specific;
they follow QEMU's 32-bit layout, with descriptor attributes stored like `SegReg.attr`. SMRAM
protection belongs to the chipset and is not modelled; NMIs do not exist in this model. -/

/-- SMM revision identifier: SMBASE relocation supported (bit 17), no I/O instruction restart. -/
def smmRevision : UInt32 := 0x00020000

/-- Offset in the state-save map of the cache (attr, limit, base) of segment register `k`. -/
@[inline] def smmSegOff (k : UInt32) : UInt32 := if k < 3 then 0x7F84 + 12 * k else 0x7F2C + 12 * (k - 3)

/-- Enter SMM: save the state and load the SMM execution environment. -/
def smmEnter : M Unit := do
  let c ← cpu
  let sb := c.smbase + 0x8000
  let w := fun (o v : UInt32) => physWr (sb + o).toUInt64 4 v
  w 0x7FFC c.cr0
  w 0x7FF8 c.cr3
  w 0x7FF4 c.eflags
  w 0x7FF0 c.eip
  for k in [0:8] do w (0x7FD0 + 4 * k.toUInt32) (c.getReg k.toUInt8)
  w 0x7FCC c.dr6
  w 0x7FC8 c.dr7
  w 0x7FC4 c.tr.sel.toUInt32
  w 0x7F64 c.tr.base
  w 0x7F60 c.tr.limit
  w 0x7F5C c.tr.attr
  w 0x7FC0 c.ldtr.sel.toUInt32
  w 0x7F80 c.ldtr.base
  w 0x7F7C c.ldtr.limit
  w 0x7F78 c.ldtr.attr
  w 0x7F74 c.gdtBase
  w 0x7F70 c.gdtLimit
  w 0x7F58 c.idtBase
  w 0x7F54 c.idtLimit
  for k in [0:6] do
    let s := c.getSeg k.toUInt8
    let k32 := k.toUInt32
    w (0x7FA8 + 4 * k32) s.sel.toUInt32
    w (smmSegOff k32) s.attr
    w (smmSegOff k32 + 4) s.limit
    w (smmSegOff k32 + 8) s.base
  w 0x7F14 c.cr4
  w 0x7EFC smmRevision
  w 0x7EF8 c.smbase
  let flat (sel : UInt16) (base : UInt32) : SegReg := { sel, base, limit := 0xFFFFFFFF, attr := 0x8093 }
  modCpu fun c => { c with
    smm := true, halted := false, shadow := false,
    eflags := 2, eip := 0x8000,
    cr0 := c.cr0 &&& ~~~(CR0.PE ||| CR0.EM ||| CR0.TS ||| CR0.PG), cr4 := 0, dr7 := 0x400, bpOn := false,
    cs := flat (c.smbase >>> 4).toUInt16 c.smbase,
    ds := flat 0 0, es := flat 0 0, ss := flat 0 0, fs := flat 0 0, gs := flat 0 0 }
  flushTlb

/-- RSM: #UD outside SMM; otherwise restore the saved state (a relocated SMBASE takes effect for the
next SMI). An inconsistent saved state (paging without protection) shuts the processor down. -/
def rsm : M Unit := do
  let c ← cpu
  if !c.smm then ud
  let sb := c.smbase + 0x8000
  let r := fun (o : UInt32) => physRd (sb + o).toUInt64 4
  let cr0 := ((← r 0x7FFC) &&& 0xE005003F) ||| CR0.ET
  let cr4 ← r 0x7F14
  if cr0 &&& CR0.PG != 0 && cr0 &&& CR0.PE == 0 then throw (.shutdown "RSM: invalid saved CR0")
  if cr4 &&& ~~~(0x01FC : UInt32) != 0 then throw (.shutdown "RSM: invalid saved CR4")
  let cr3 ← r 0x7FF8
  let efl ← r 0x7FF4
  let eip ← r 0x7FF0
  let mut regs : Array UInt32 := #[]
  for k in [0:8] do regs := regs.push (← r (0x7FD0 + 4 * k.toUInt32))
  let dr6 ← r 0x7FCC
  let dr7 ← r 0x7FC8
  let seg := fun (sel base limit attr : UInt32) =>
    ({ sel := sel.toUInt16, base, limit, attr := attr &&& 0xF0FF } : SegReg)
  let tr := seg (← r 0x7FC4) (← r 0x7F64) (← r 0x7F60) (← r 0x7F5C)
  let ldtr := seg (← r 0x7FC0) (← r 0x7F80) (← r 0x7F7C) (← r 0x7F78)
  let gdtBase ← r 0x7F74
  let gdtLimit := (← r 0x7F70) &&& 0xFFFF
  let idtBase ← r 0x7F58
  let idtLimit := (← r 0x7F54) &&& 0xFFFF
  let mut segs : Array SegReg := #[]
  for k in [0:6] do
    let k32 := k.toUInt32
    segs := segs.push (seg (← r (0x7FA8 + 4 * k32)) (← r (smmSegOff k32 + 8)) (← r (smmSegOff k32 + 4))
                            (← r (smmSegOff k32)))
  let rev ← r 0x7EFC
  let nsb ← if rev &&& 0x20000 != 0 then r 0x7EF8 else pure c.smbase
  modCpu fun c => Id.run do
    let mut c := { c.setDr7 dr7 with smm := false, smbase := nsb, cr0, cr3, cr4, eflags := (efl &&& Flag.valid) ||| 2,
                                     eip, dr6, tr, ldtr, gdtBase, gdtLimit, idtBase, idtLimit }
    for k in [0:8] do c := c.setReg k.toUInt8 regs[k]!
    for k in [0:6] do c := c.setSeg k.toUInt8 segs[k]!
    return c
  if cr0 &&& CR0.PG != 0 && cr4 &&& CR4.PAE != 0 then
    let p ← tryCatch (readPdptes cr3) fun _ => throw (.shutdown "RSM: invalid PDPTEs")
    modCpu fun c => { c with pdpte := p }
  flushTlb

end X86
