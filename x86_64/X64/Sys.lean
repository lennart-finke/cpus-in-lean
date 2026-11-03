import X64.Io
namespace X64

def cplIs0 : M Unit := do if (← getCpl) != 0 then gp 0

def jumpTo (t : UInt64) : M Unit := do
  if !canonical t then gp 0
  modCpu fun c => { c with rip := t }

def push (sz : Sz) (v : UInt64) : M Unit := do
  let sp := (← cpu).rsp - sz.toUInt64
  wrMem SegN.SS sp sz.toUInt64 v
  modCpu fun c => { c with rsp := sp }

def peek (sz : Sz) (offset : UInt64) : M UInt64 := do
  rdMem SegN.SS ((← cpu).rsp + offset) sz.toUInt64

def pop (sz : Sz) : M UInt64 := do
  let v ← peek sz 0
  modCpu fun c => { c with rsp := c.rsp + sz.toUInt64 }
  return v

structure Desc where
  raw : UInt64
  addr : UInt64
  deriving Inhabited
namespace Desc
@[inline] def base (d : Desc) : UInt64 := ((d.raw >>> 16) &&& 0xFFFFFF) ||| ((d.raw >>> 32) &&& 0xFF000000)
@[inline] def attr (d : Desc) : UInt64 := (d.raw >>> 40) &&& 0xF0FF
@[inline] def limit (d : Desc) : UInt64 :=
  let n := (d.raw &&& 0xFFFF) ||| ((d.raw >>> 32) &&& 0xF0000)
  if d.raw &&& 0x80000000000000 != 0 then (n <<< 12) ||| 0xFFF else n
@[inline] def dpl (d : Desc) : UInt64 := (d.raw >>> 45) &&& 3
@[inline] def present (d : Desc) : Bool := d.raw &&& 0x800000000000 != 0
@[inline] def code (d : Desc) : Bool := d.raw &&& 0x180000000000 == 0x180000000000
@[inline] def conforming (d : Desc) : Bool := d.raw &&& 0x40000000000 != 0
@[inline] def long (d : Desc) : Bool := d.attr &&& 0x6000 == 0x2000
@[inline] def toSeg (d : Desc) (sel : UInt16) : SegReg := { sel, base := d.base, limit := d.limit, attr := d.attr }
end Desc

def readDesc (sel : UInt16) : M Desc := do
  let c ← cpu
  let index := sel.toUInt64 &&& 0xFFF8
  let (base, limit) := if sel &&& 4 != 0 then (c.ldtr.base, c.ldtr.limit) else (c.gdtBase, c.gdtLimit)
  if index + 7 > limit || (sel &&& 4 != 0 && !c.ldtr.present) then gp (sel.toUInt64 &&& 0xFFFC)
  return { raw := (← sysRd (base + index) 8), addr := base + index }

def markAccessed (d : Desc) : M Desc := do
  let raw := d.raw ||| 0x10000000000
  if raw != d.raw then sysWr d.addr 8 raw
  return { d with raw }

def loadSeg (s : UInt8) (sel : UInt16) : M Unit := do
  let c ← cpu
  let err := sel.toUInt64 &&& 0xFFFC
  let rpl := sel.toUInt64 &&& 3
  if err == 0 then
    if s == SegN.SS && (c.cpl == 3 || rpl != c.cpl) then gp 0
    modCpu (·.setSeg s { sel, attr := 0 })
    if s == SegN.FS then modCpu fun c => { c with fsBase := 0 }
    if s == SegN.GS then modCpu fun c => { c with gsBase := 0 }
    return
  let d ← readDesc sel
  if d.attr &&& 0x10 == 0 then gp err
  if s == SegN.SS then
    if d.code || d.attr &&& 2 == 0 || d.dpl != c.cpl || rpl != c.cpl then gp err
    if !d.present then exc Vec.SS (some err)
  else
    if d.code && d.attr &&& 2 == 0 then gp err
    if (!d.code || !d.conforming) && (c.cpl > d.dpl || rpl > d.dpl) then gp err
    if !d.present then exc Vec.NP (some err)
  let d ← markAccessed d
  modCpu (·.setSeg s (d.toSeg sel))
  if s == SegN.FS then modCpu fun c => { c with fsBase := d.base }
  if s == SegN.GS then modCpu fun c => { c with gsBase := d.base }

def loadSystemSeg (sel : UInt16) (task : Bool) : M Unit := do
  cplIs0
  if sel &&& 4 != 0 then gp (sel.toUInt64 &&& 0xFFFC)
  if sel &&& 0xFFF8 == 0 then
    if task then gp 0
    modCpu fun c => { c with ldtr := { attr := 0 } }
    return
  let d ← readDesc sel
  let err := sel.toUInt64 &&& 0xFFFC
  if d.attr &&& 0x1F != (if task then 9 else 2) then gp err
  if (sel.toUInt64 &&& 0xFFF8) + 15 > (← cpu).gdtLimit then gp err
  if !d.present then exc Vec.NP (some err)
  let hi ← sysRd (d.addr + 8) 8
  if hi >>> 32 != 0 then gp err
  let base := d.base ||| (hi <<< 32)
  if !canonical base then gp err
  let sr := { d.toSeg sel with base, attr := d.attr ||| (if task then 2 else 0) }
  if task then
    sysWr d.addr 8 (d.raw ||| 0x20000000000)
    modCpu fun c => { c with tr := sr }
  else modCpu fun c => { c with ldtr := sr }

/-- 16-byte IA-32e interrupt/trap gates and 64-bit TSS stacks, including IST.
The full frame is probed before storing any frame bytes. -/
def deliver (vec : UInt8) (err : Option UInt64) (soft ext : Bool) : M Unit := do
  let c ← cpu
  let offset := vec.toUInt64 * 16
  let ge := vec.toUInt64 * 8 + 2 + (if ext then 1 else 0)
  if offset + 15 > c.idtLimit then gp ge
  let lo ← sysRd (c.idtBase + offset) 8
  let hi ← sysRd (c.idtBase + offset + 8) 8
  let typ := (lo >>> 40) &&& 0x1F
  if (typ != 14 && typ != 15) || hi >>> 32 != 0 || lo &&& 0xF800000000 != 0 then gp ge
  if soft && c.cpl > (lo >>> 45) &&& 3 then gp ge
  if lo &&& 0x800000000000 == 0 then exc Vec.NP (some ge)
  let sel := (lo >>> 16).toUInt16
  let se := sel.toUInt64 &&& 0xFFFC
  if se == 0 then gp 0
  let d ← readDesc sel
  if !d.code || !d.long || d.dpl > c.cpl then gp se
  if !d.present then exc Vec.NP (some se)
  let ip := (lo &&& 0xFFFF) ||| ((lo >>> 32) &&& 0xFFFF0000) ||| (hi <<< 32)
  if !canonical ip then gp 0
  let ndpl := if d.conforming then c.cpl else d.dpl
  let ist := (lo >>> 32) &&& 7
  let change := ist != 0 || ndpl < c.cpl
  let mut sp := c.rsp
  if change then
    let off := if ist != 0 then 36 + 8 * (ist - 1) else 4 + 8 * ndpl
    if !c.tr.present || off + 7 > c.tr.limit then exc Vec.TS (some (c.tr.sel.toUInt64 &&& 0xFFFC))
    sp ← sysRd (c.tr.base + off) 8
  sp := sp &&& ~~~(15 : UInt64)
  let frameBytes := if err.isSome then 48 else 40
  if !canonical (sp - frameBytes) || !canonical (sp - 1) then exc Vec.SS (some 0)
  let _ ← translate (sp - frameBytes) .write (ndpl == 3)
  let _ ← translate (sp - 1) .write (ndpl == 3)
  let d ← markAccessed d
  modCpu fun c => { c with
    cs := d.toSeg ((sel &&& 0xFFFC) ||| ndpl.toUInt16), rsp := sp,
    ss := if change then { sel := ndpl.toUInt16, attr := 0 } else c.ss }
  push 8 c.ss.sel.toUInt64
  push 8 c.rsp
  push 8 c.rflags
  push 8 c.cs.sel.toUInt64
  push 8 c.rip
  if let some e := err then push 8 e
  modCpu fun c => { c with rip := ip, rflags := c.rflags &&& ~~~(Flag.TF ||| Flag.NT ||| Flag.RF |||
    (if typ == 14 then Flag.IF else 0)) }

/-- IRETQ always pops SS:RSP in 64-bit mode, including same-privilege returns. -/
def iret : M Unit := do
  let c ← cpu
  if c.rflags &&& Flag.NT != 0 then gp 0
  let ip ← peek 8 0
  let sel := (← peek 8 8).toUInt16
  let fl ← peek 8 16
  let sp ← peek 8 24
  let ss := (← peek 8 32).toUInt16
  let rpl := sel.toUInt64 &&& 3
  let err := sel.toUInt64 &&& 0xFFFC
  if err == 0 || rpl < c.cpl then gp err
  let d ← readDesc sel
  if !d.code || (!d.conforming && d.dpl != rpl) || (d.conforming && d.dpl > rpl) then gp err
  if !d.long then unsupported "IRET to compatibility mode"
  if !d.present then exc Vec.NP (some err)
  if !canonical ip || !canonical sp then gp 0
  -- Check the destination SS using the destination privilege level.
  modCpu fun c => { c with cs := d.toSeg sel }
  loadSeg SegN.SS ss
  let mask := Flag.arith ||| Flag.TF ||| Flag.DF ||| Flag.NT ||| Flag.RF ||| Flag.AC ||| Flag.ID |||
    (if c.cpl == 0 then Flag.IOPL else 0) ||| (if c.cpl ≤ c.iopl then Flag.IF else 0)
  modCpu fun c => { c with rip := ip, rsp := sp, rflags := (c.rflags &&& ~~~mask) ||| (fl &&& mask) ||| 2 }

/-- Far return to a 64-bit code segment, including privilege-stack restoration. -/
def farReturn (sz : Sz) (extra : UInt64) : M Unit := do
  let c ← cpu
  let ip ← peek sz 0
  let sel := (← peek sz sz.toUInt64).toUInt16
  let rpl := sel.toUInt64 &&& 3
  let err := sel.toUInt64 &&& 0xFFFC
  if err == 0 || rpl < c.cpl then gp err
  let d ← readDesc sel
  if !d.code || (!d.conforming && d.dpl != rpl) || (d.conforming && d.dpl > rpl) then gp err
  if !d.present then exc Vec.NP (some err)
  if !d.long then unsupported "far return to compatibility mode"
  if !canonical ip then gp 0
  let mut sp := c.rsp + 2*sz.toUInt64 + extra
  let mut ss := c.ss.sel
  if rpl > c.cpl then
    sp ← peek sz (2*sz.toUInt64 + extra)
    ss := (← peek sz (3*sz.toUInt64 + extra)).toUInt16
    sp := sp + extra
    if !canonical sp then gp 0
  let d ← markAccessed d
  modCpu fun c => { c with cs := d.toSeg sel }
  if rpl > c.cpl then loadSeg SegN.SS ss
  modCpu fun c => { c with rip := ip, rsp := sp }

/-- Direct far transfer through an ordinary code descriptor. System gates stop explicitly. -/
def farTransfer (sel : UInt16) (ip : UInt64) (call : Bool) : M Unit := do
  let c ← cpu
  let err := sel.toUInt64 &&& 0xFFFC
  if err == 0 then gp 0
  let d ← readDesc sel
  if d.attr &&& 0x10 == 0 then unsupported "far transfer through system gate"
  if !d.code || (if d.conforming then d.dpl > c.cpl else d.dpl != c.cpl || sel.toUInt64 &&& 3 > c.cpl) then gp err
  if !d.present then exc Vec.NP (some err)
  if !d.long then unsupported "far transfer to compatibility mode"
  if !canonical ip then gp 0
  let d ← markAccessed d
  if call then
    push 8 c.cs.sel.toUInt64
    push 8 c.rip
  modCpu fun c => { c with cs := d.toSeg ((sel &&& 0xFFFC) ||| c.cpl.toUInt16), rip := ip }

def syscall : M Unit := do
  let c ← cpu
  if c.efer &&& 1 == 0 then ud
  if !canonical c.lstar then gp 0
  let cs := (c.star >>> 32).toUInt16 &&& 0xFFFC
  modCpu fun c => { c with
    rcx := c.rip, r11 := c.rflags &&& ~~~Flag.RF, rip := c.lstar,
    rflags := c.rflags &&& ~~~(c.sfmask ||| Flag.RF),
    cs := { sel := cs, attr := 0xA09B, limit := 0xFFFFFFFF },
    ss := { sel := cs + 8, attr := 0xC093, limit := 0xFFFFFFFF } }

def sysret : M Unit := do
  cplIs0
  let c ← cpu
  if c.efer &&& 1 == 0 then ud
  if !canonical c.rcx then gp 0
  let sel := (c.star >>> 48).toUInt16
  modCpu fun c => { c with
    rip := c.rcx, rflags := (c.r11 &&& 0x3C7FD7) ||| 2,
    cs := { sel := (sel + 16) ||| 3, attr := 0xA0FB, limit := 0xFFFFFFFF },
    ss := { sel := (sel + 8) ||| 3, attr := 0xC0F3, limit := 0xFFFFFFFF } }

end X64
