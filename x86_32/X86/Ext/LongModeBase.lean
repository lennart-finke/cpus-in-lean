import X86.Io
/-!
# Long mode: activation, compatibility mode and the 64-bit boundary

Owner: the long-mode workstream (with `X86/Ext/LongMode.lean`, which holds the instruction and MSR
hooks). This file comes before `X86/Sys.lean` in the import order, because the core descriptor,
far-transfer and interrupt code calls into it at the places where long mode differs from legacy
protected mode. Sources: AMD64 APM vol. 2 rev. 3.43 (24593) chapters 1, 4, 5, 8, 12, 14 and vol. 3
rev. 3.39 (24594) instruction pseudocode; the Intel SDM where AMD is silent (marked).

## Modes

EFER.LMA = 1 (long mode active) is maintained by the processor as LME ∧ CR0.PG (APM vol. 2, 14.6.1;
`withLma`). With LMA = 1 the processor is in *compatibility mode* while CS.L = 0, and in *64-bit
mode* while CS.L = 1 (CS.D = 0; L = D = 1 is reserved and refused when CS is loaded). In
compatibility mode, 32- and 16-bit code runs as in legacy protected mode (CS.D selects the default
sizes; segmentation, the 32-bit registers and linear addresses), with these differences, all
modelled:

* paging is the 4-level long-mode paging (`Machine.walkLong`), with 1 GiB pages;
* interrupts and exceptions go through 16-byte 64-bit IDT gates to 64-bit handlers (`deliverLong`):
  task gates and 16-bit gates are #GP, the stack frame has 8-byte slots, always holds SS:RSP, is
  aligned to 16 bytes, and an inner stack (RSPn of the 64-bit TSS, with a null SS) or an IST stack is
  used;
* far CALL/JMP through call gates use 16-byte 64-bit call gates whose target must be 64-bit code;
  16-bit call gates, task gates and TSS descriptors as far-transfer targets are #GP(selector), and
  IRET with EFLAGS.NT = 1 is #GP(0): there is no hardware task switching in long mode (APM vol. 2,
  12.1, 4.8.4; vol. 3 CALL, JMP, IRET); IRET cannot enter virtual-8086 mode (EFLAGS.VM is not loaded);
* far RET and IRET may return to 64-bit code, then with a null SS at CPL < 3;
* SYSCALL enters 64-bit mode at CSTAR with RCX/R11 (`syscallLong`); SYSENTER and SYSEXIT are #UD
  (AMD); SYSRET from compatibility mode is the legacy-mode SYSRET (vol. 3 SYSRET_NON_64BIT_MODE);
* LTR accepts only a 32/64-bit TSS (type 9; type 1 is illegal in long mode); LTR and LLDT read
  8-byte descriptors in compatibility mode (APM vol. 2, 4.8.3: the 16-byte form is loaded "only from
  64-bit mode"); LAR/LSL accept the long-mode system types (vol. 3 LAR, LSL);
* SWAPGS and RDFSBASE/RDGSBASE/WRFSBASE/WRGSBASE are #UD (64-bit mode only); FS_BASE, GS_BASE and
  KernelGSbase are MSRs.

## The 64-bit boundary

The model executes no instruction in 64-bit mode: `decodeRaw` stops with
`Fault.unsupported "64-bit mode"` before fetching when EFER.LMA = 1 and CS.L = 1 (theorems
`decode_64bit`, `execInstr_64bit` in `X86/Proofs/ExtLongMode.lean`). Every control transfer *into*
64-bit mode is executed completely by the model, including every check and memory access that
precedes the first 64-bit instruction:

* far JMP/CALL to a 64-bit code segment or through a 64-bit call gate (descriptor and gate checks,
  the inner stack from the TSS, the 8-byte pushes with their #SS/#PF);
* far RET / IRET to a 64-bit code segment (all checks of the return);
* SYSCALL from compatibility mode;
* every interrupt and exception while EFER.LMA = 1 (IDT and gate checks, target code segment
  checks, IST/RSPn, the 16-byte-aligned 8-byte frame pushes, RFLAGS update).

Faults raised by these checks are delivered (again through the 64-bit IDT) as on hardware. The
transfer leaves the machine at the instruction boundary before the first 64-bit instruction:
CS holds the 64-bit code segment, RIP = `LongModeState.ripHi`:EIP, RSP = `rspHi`:ESP, R11 = `r11`
after SYSCALL, and `entry` names the transfer; the other general registers have their 32-bit values
with bits 63:32 zero (the model does not keep the high halves; QEMU zero-extends 32-bit results in
every mode; the APM leaves the high halves undefined outside 64-bit mode), R8–R15 are zero. The next
step stops there (an interrupt or debug trap pending at that boundary is delivered first, from
64-bit mode, as on hardware). This state is exactly what a 64-bit executor needs to resume; the
bridge in `validation/` (`BridgeMain.lean`) maps it to the `x86_64` model's state.

SMM: SMIs are taken in long mode too; the AMD64 state-save map holds EFER, RIP/RSP and R11, and RSM
recomputes LMA = LME ∧ PG ∧ PAE (`Sys.lean`, `rsmEfer`).

Not modelled (stop with `Fault.unsupported`): a #PF at a linear address ≥ 4 GiB during a transfer
(an inner stack above 4 GiB: CR2 is 32 bits in the model), RSM to a CR3 above 4 GiB.
-/
namespace X86
namespace LongMode

/-- Long mode is active (EFER.LMA). -/
@[inline] def lma (c : Cpu) : Bool := c.efer &&& EFER.LMA != 0

/-- The L bit of a segment cache (`SegReg.attr` bit 13). -/
@[inline] def lBit (s : SegReg) : Bool := s.attr &&& 0x2000 != 0

/-- 64-bit mode: EFER.LMA = 1 and CS.L = 1. -/
@[inline] def in64 (c : Cpu) : Bool := lBit c.cs && lma c

/-- RIP and RSP as 64-bit values (`LongModeState.ripHi`, `rspHi`; zero outside 64-bit mode). -/
@[inline] def rip (c : Cpu) : UInt64 := (c.lmx.ripHi.toUInt64 <<< 32) ||| c.eip.toUInt64
@[inline] def rsp (c : Cpu) : UInt64 := (c.lmx.rspHi.toUInt64 <<< 32) ||| c.esp.toUInt64

/-- Canonical 48-bit virtual address: bits 63:47 all equal (APM vol. 2, 5.3.1; 48 virtual-address
bits, CPUID Fn8000_0008_EAX[15:8] = 0x30 on the 7742). -/
@[inline] def canonical (v : UInt64) : Bool :=
  let hi := v >>> 47
  hi == 0 || hi == 0x1FFFF

/-! ## Activation (APM vol. 2, 14.6) -/

/-- EFER with LMA recomputed for EFER = `efer` and CR0 = `cr0`: LMA = LME ∧ PG ("When paging is
enabled after LME is set to 1, the processor sets the EFER.LMA bit to 1"; clearing PG clears it,
14.7). -/
@[inline] def withLma (efer cr0 : UInt32) : UInt32 :=
  if efer &&& EFER.LME != 0 && cr0 &&& CR0.PG != 0 then efer ||| EFER.LMA else efer &&& ~~~EFER.LMA

/-- The state change of MOV CR0 = `v` once its checks have passed: CR0 = `v`, EFER.LMA = LME ∧ PG,
and a TLB flush (global entries included) if PG, WP or PE change. -/
def setCr0 (v : UInt32) : M Unit := fun m =>
  let c := m.cpu
  let m' := { m with cpu := { c with cr0 := v, efer := withLma c.efer v } }
  if (v ^^^ c.cr0) &&& (CR0.PG ||| CR0.WP ||| CR0.PE) != 0 then flushTlbAll m' else .ok () m'

/-- MOV CR0 = `v` passes the long-mode consistency checks of table 14-5: enabling paging (PG 0 → 1)
with EFER.LME = 1 needs CR4.PAE = 1 and CS.L = 0. (Disabling paging from 64-bit mode would be #GP on
Intel, but the model never executes in 64-bit mode.) -/
@[inline] def cr0Ok (c : Cpu) (v : UInt32) : Bool :=
  !(c.cr0 &&& CR0.PG == 0 && v &&& CR0.PG != 0 && c.efer &&& EFER.LME != 0 &&
    (c.cr4 &&& CR4.PAE == 0 || lBit c.cs))

/-- MOV CR4 = `v` passes table 14-5: PAE cannot be cleared while long mode is active. -/
@[inline] def cr4Ok (c : Cpu) (v : UInt32) : Bool := !(lma c && v &&& CR4.PAE == 0)

/-- WRMSR EFER = `v` passes the long-mode checks: LME cannot change while paging is enabled
(table 14-5), and the LMA bit written must equal the processor's (APM vol. 2, 3.1.7: "An attempt to
write a value that differs from the state determined by hardware results in a #GP fault"). -/
@[inline] def eferOk (c : Cpu) (v : UInt32) : Bool :=
  !(c.cr0 &&& CR0.PG != 0 && (v ^^^ c.efer) &&& EFER.LME != 0) && (v ^^^ c.efer) &&& EFER.LMA == 0

/-! ## Linear accesses of 64-bit transfers -/

/-- Translate a 64-bit linear address for a write by a transfer into 64-bit mode. Below 4 GiB the
ordinary translation (with the TLB) is used. Above, the long-mode walk without filling the TLB (a
TLB may decline to cache a translation); a #PF there cannot be represented (CR2 is 32 bits in the
model) and stops the simulation. -/
def xlate64 (lin : UInt64) (user : Bool) : M UInt64 := fun m =>
  if lin >>> 32 == 0 then translate lin.toUInt32 true user false false m
  else if m.cpu.cr0 &&& CR0.PG == 0 then .ok lin m
  else match walkLong lin true user false false m with
    | .ok (p, _, _) m => .ok p m
    | .error (.exc 14 _ _) m => .error (.unsupported "64-bit mode: page fault at a linear address above 4 GiB") m
    | .error f m => .error f m

/-- Write the 8 bytes `v` at the 64-bit linear address `lin` (a slot of a 64-bit stack frame): #SS(0)
if the address is not canonical, then paging (both pages are checked before anything is written). -/
def wr64 (lin v : UInt64) (user : Bool) : M Unit := do
  if !canonical lin || !canonical (lin + 7) then exc Vec.SS (some 0)
  if user && lin &&& 7 != 0 then acCheck
  dbData lin.toUInt32 8 true
  let p0 ← xlate64 lin user
  let p1 ← xlate64 ((lin + 7) &&& ~~~0xFFF) user
  for k in [0:8] do
    let a := lin + k.toUInt64
    let p := if a &&& ~~~0xFFF == lin &&& ~~~0xFFF then p0 + k.toUInt64 else p1 + (a &&& 0xFFF)
    physWr p 1 (v >>> (8 * k.toUInt64)).toUInt32

/-- Push 8 bytes on a 64-bit stack: the new RSP. -/
@[inline] def push64 (rsp v : UInt64) (user : Bool) : M UInt64 := do
  let n := rsp - 8
  wr64 n v user
  return n

/-- The two 8-byte pushes (`a`, then `b`) of a same-privilege CALL through a 64-bit call gate. In the
APM's pseudocode (vol. 3 CALL (Far), CALLF_CALLGATE) they come after CS is loaded with the 64-bit
target ("PUSH.v old_CS; PUSH.v next_RIP" with v = 8), and WRITE_MEM tests the mode at the access: in
64-bit mode the SS base and limit are not used, a non-canonical address is #SS(0) (vol. 3, 2.5.3
WRITE_MEM; vol. 2, 4.12 and 2.4.5). So the pushes go to the flat linear addresses RSP − 8 and
RSP − 16 (with paging and #AC at CPL 3). The stack pointer is then updated at the stack size the
instruction started with (pseudocode "RSP.s = RSP − 8", S fixed at the start of the instruction):
ESP for a 32-bit SS, SP for a 16-bit one. QEMU does the same (`helper_lcall_protected`: `PUSHQ` on
the unmasked RSP, `SET_ESP` with the old SS mask). -/
def pushGate8 (a b : UInt64) : M Unit := do
  let c ← cpu
  let user := c.cpl == 3
  let r := rsp c
  wr64 (r - 8) a user
  wr64 (r - 16) b user
  let n := (r - 16).toUInt32
  modCpu fun c => if c.ss.big then { c with esp := n, lmx := { c.lmx with rspHi := 0 } }
                   else { c with esp := (c.esp &&& 0xFFFF0000) ||| (n &&& 0xFFFF) }

/-! ## Descriptors -/

/-- Read the 8-byte descriptor of a non-null selector from the GDT/LDT (`n` = 16: check that a
16-byte system descriptor fits the table): (low dword, high dword, linear address). #GP(selector |
ext) beyond the limit or through an unusable LDT. -/
def readSel (sel : UInt16) (ext : UInt32) (n : UInt32 := 8) : M (UInt32 × UInt32 × UInt32) := do
  let c ← cpu
  let idx := sel.toUInt32 &&& 0xFFF8
  let err := (sel.toUInt32 &&& 0xFFFC) ||| ext
  let (base, limit) ←
    if sel &&& 4 != 0 then
      if !c.ldtr.present then gp err
      pure (c.ldtr.base, c.ldtr.limit)
    else pure (c.gdtBase, c.gdtLimit)
  if idx + (n - 1) > limit then gp err
  let lo ← sysRd (base + idx) 4
  let hi ← sysRd (base + idx + 4) 4
  return (lo, hi, base + idx)

/-- Segment cache of a code/data descriptor (as `Desc.toSeg`). -/
@[inline] def toSeg (sel : UInt16) (lo hi : UInt32) : SegReg :=
  let raw := (lo &&& 0xFFFF) ||| (hi &&& 0xF0000)
  { sel, base := (lo >>> 16) ||| ((hi &&& 0xFF) <<< 16) ||| (hi &&& 0xFF000000),
    limit := if hi &&& 0x800000 != 0 then (raw <<< 12) ||| 0xFFF else raw,
    attr := (hi >>> 8) &&& 0xF0FF }

/-- Set the accessed bit of a code/data descriptor (high dword `hi` at `addr + 4`). -/
def setA (hi addr : UInt32) : M UInt32 := do
  if hi &&& 0x100 == 0 then
    sysWr (addr + 4) 4 (hi ||| 0x100)
    return hi ||| 0x100
  else return hi

/-- A code descriptor (high dword `hi`) with L = 1 and D = 1, reserved in long mode: loading it into
CS is #GP(selector) (APM vol. 2, 4.8.1 "reserved for future use"; the Intel SDM's JMP/CALL/RET/IRET
pseudocode raises #GP(selector) for it in IA-32e mode). -/
@[inline] def reservedCode (c : Cpu) (hi : UInt32) : Bool := lma c && hi &&& 0x600000 == 0x600000

/-- A 64-bit code segment (L = 1, D = 0) as required of the target of a long-mode gate (4.8.4). -/
@[inline] def code64 (hi : UInt32) : Bool := hi &&& 0x1800 == 0x1800 && hi &&& 0x600000 == 0x200000

/-- The limit check of a far transfer or return to code segment cache `cs` at offset `ip`: not made
for a 64-bit code segment in long mode (the 16/32-bit offset, zero-extended, is canonical; vol. 3
pseudocode "(!64BIT_MODE) && (temp_RIP > CS.limit)"). -/
@[inline] def limitOk (c : Cpu) (cs : SegReg) (ip : UInt32) : Bool := ip ≤ cs.limit || (lma c && lBit cs)

/-- Returning to 64-bit code at CPL `rpl` < 3 with a null SS selector loads it without a descriptor
(APM vol. 2, 8.9.5 "Nested IRETs to 64-Bit Mode Procedures"; vol. 3 RET (Far): #GP only if "the
return mode was non-64-bit mode or CPL was 3"). -/
@[inline] def nullSsOk (c : Cpu) (cs : SegReg) (ss : UInt16) (rpl : UInt32) : Bool :=
  lma c && lBit cs && rpl != 3 && ss &&& 0xFFFC == 0

/-- The SS cache for a null selector with RPL `rpl` loaded in long mode (unusable; DPL = RPL). -/
@[inline] def nullSs (sel : UInt16) (rpl : UInt32) : SegReg := { sel, base := 0, limit := 0, attr := rpl <<< 5 }

/-- Record a transfer into 64-bit mode: RIP bits 63:32 and the entry name (RSP's are set by the
caller where a 64-bit stack pointer is loaded). -/
@[inline] def enter64 (ripHi : UInt32) (what : String) : M Unit := modCpu fun c =>
  { c with lmx := { c.lmx with ripHi, entry := what } }

/-! ## Interrupts and exceptions (APM vol. 2, 8.9; vol. 3 INT pseudocode) -/

/-- The inner stack pointer for `ist` (1..7: ISTn) or, if 0, RSPn for CPL `ncpl`, from the 64-bit
TSS (vol. 3 READ_INNER_LEVEL_SP): #TS(TR selector) if it lies beyond the TSS limit. -/
def innerRsp (ncpl ist extB : UInt32) : M UInt64 := do
  let tr := (← cpu).tr
  let off := if ist != 0 then 0x1C + ist * 8 else 4 + ncpl * 8
  if off + 7 > tr.limit then exc Vec.TS (some ((tr.sel.toUInt32 &&& 0xFFFC) ||| extB))
  let lo ← sysRd (tr.base + off) 4
  let hi ← sysRd (tr.base + off + 4) 4
  return (hi.toUInt64 <<< 32) ||| lo.toUInt64

/-- Deliver interrupt/exception `vec` in long mode through the 64-bit IDT (arguments as `deliver`:
EIP holds the return address; `soft` = INT n/INT3/INTO, `ext` = external event). The handler is
always 64-bit code, so the model stops at its first instruction (see the module documentation).

Order (vol. 3 INT_N_PROTECTED, READ_IDT, READ_DESCRIPTOR, READ_INNER_LEVEL_SP): the 16-byte gate
must lie within the IDT limit (#GP(vector·8 + 2 + EXT)); type 0Eh/0Fh only (task gates and 16-bit
gates are #GP, 8.9.1); gate DPL ≥ CPL for software interrupts; present (#NP); the target selector is
non-null (#GP(EXT)), within its table, a 64-bit code segment (L = 1, D = 0; #GP(selector)) with
DPL ≤ CPL, present (#NP(selector)); the new stack: IST, or RSPn on a privilege change (#TS), aligned
to 16 bytes; the pushes of SS, RSP, RFLAGS, CS, RIP and the error code (8 bytes each, #SS(0) if not
canonical, #PF); the target RIP must be canonical (#GP(0), checked after the pushes as in the APM's
pseudocode). The error code for a target that is not 64-bit code is the selector, as in the
pseudocode's READ_DESCRIPTOR (4.8.4's prose says "the interrupt vector number"; QEMU and the Intel
SDM use the selector). -/
def deliverLong (vec : UInt8) (err : Option UInt32) (soft ext : Bool) : M Unit := do
  let c ← cpu
  let v := vec.toUInt32
  let extB : UInt32 := if ext then 1 else 0
  let gerr := v * 8 + 2 + extB
  if v * 16 + 15 > c.idtLimit then gp gerr
  let ent := c.idtBase + v * 16
  let lo ← sysRd ent 4
  let hi ← sysRd (ent + 4) 4
  let gtype := (hi >>> 8) &&& 0x1F
  if gtype != 0x0E && gtype != 0x0F then gp gerr
  if soft && (hi >>> 13) &&& 3 < c.cpl then gp gerr
  if hi &&& 0x8000 == 0 then exc Vec.NP (some gerr)
  let offHi ← sysRd (ent + 8) 4
  let target : UInt64 := (offHi.toUInt64 <<< 32) ||| ((hi &&& 0xFFFF0000) ||| (lo &&& 0xFFFF)).toUInt64
  let ist := hi &&& 7
  let sel := (lo >>> 16).toUInt16
  let serr := (sel.toUInt32 &&& 0xFFFC) ||| extB
  if sel &&& 0xFFFC == 0 then gp extB
  let (dlo, dhi, daddr) ← readSel sel extB
  let ddpl := (dhi >>> 13) &&& 3
  if !code64 dhi || ddpl > c.cpl then gp serr
  if dhi &&& 0x8000 == 0 then exc Vec.NP (some serr)
  let dhi ← setA dhi daddr
  let conforming := dhi &&& 0x400 != 0
  let ncpl := if conforming then c.cpl else ddpl
  let change := ncpl != c.cpl
  let newRsp ←
    if ist != 0 || change then innerRsp ncpl ist extB
    else pure (rsp c)
  let user := ncpl == 3
  let mut sp := newRsp &&& ~~~0xF
  sp ← push64 sp c.ss.sel.toUInt64 user
  sp ← push64 sp (rsp c) user
  sp ← push64 sp c.eflags.toUInt64 user
  sp ← push64 sp c.cs.sel.toUInt64 user
  sp ← push64 sp (rip c) user
  if let some e := err then sp ← push64 sp e.toUInt64 user
  if !canonical target then gp 0
  let clr := Flag.TF ||| Flag.NT ||| Flag.RF ||| Flag.VM ||| (if gtype == 0x0E then Flag.IF else 0)
  let ncs := toSeg ((sel &&& 0xFFFC) ||| ncpl.toUInt16) dlo dhi
  let nsp := sp
  modCpu fun c => { c with
    cs := ncs, ss := if change then nullSs ncpl.toUInt16 ncpl else c.ss,
    esp := nsp.toUInt32, eip := target.toUInt32, eflags := c.eflags &&& ~~~clr,
    lmx := { c.lmx with rspHi := (nsp >>> 32).toUInt32, ripHi := (target >>> 32).toUInt32,
                        entry := s!"interrupt {vec}" } }

/-! ## Far transfers through gates (APM vol. 2, 4.8.4; vol. 3 CALL (Far), JMP (Far)) -/

/-- Far CALL (`call`) or JMP in long mode to the system descriptor (`lo`, `hi` at `addr`) selected by
`gsel`: only a 64-bit call gate (type 0Ch) is legal; 16-bit call gates, task gates and TSS
descriptors are #GP(selector) (no task switches in long mode). The gate: DPL ≥ CPL and ≥ RPL
(#GP(gate)), present (#NP(gate)), its upper 8 bytes within the table and with bits 12:8 of dword +12
clear (#GP(gate)); the target: non-null (#GP(0)), a 64-bit code segment with DPL ≤ CPL (#GP(target)),
for JMP a non-conforming one with DPL = CPL, present (#NP(target)); the 64-bit offset canonical
(#GP(0)). A CALL to a more privileged segment switches to RSPn of the 64-bit TSS with a null SS and
pushes SS, RSP, CS, RIP as 8 bytes each on it (no parameters are copied); a CALL at the same
privilege pushes CS and RIP (8 bytes each, `pushGate8`). The target is 64-bit code: the model stops
there. -/
def gateLong (gsel : UInt16) (lo hi addr : UInt32) (call : Bool) : M Unit := do
  let c ← cpu
  let cpl := c.cpl
  let gerr := gsel.toUInt32 &&& 0xFFFC
  let t := (hi >>> 8) &&& 0x1F
  if t != 0x0C then gp gerr
  if (hi >>> 13) &&& 3 < cpl || (hi >>> 13) &&& 3 < (gsel.toUInt32 &&& 3) then gp gerr
  if hi &&& 0x8000 == 0 then exc Vec.NP (some gerr)
  -- the upper half of the 16-byte gate
  let _ ← readSel gsel 0 16
  let up0 ← sysRd (addr + 8) 4
  let up1 ← sysRd (addr + 12) 4
  if up1 &&& 0x1F00 != 0 then gp gerr
  let target : UInt64 := (up0.toUInt64 <<< 32) ||| ((hi &&& 0xFFFF0000) ||| (lo &&& 0xFFFF)).toUInt64
  let tsel := (lo >>> 16).toUInt16
  let terr := tsel.toUInt32 &&& 0xFFFC
  if terr == 0 then gp 0
  let (dlo, dhi, daddr) ← readSel tsel 0
  let ddpl := (dhi >>> 13) &&& 3
  let conforming := dhi &&& 0x400 != 0
  if !code64 dhi || ddpl > cpl then gp terr
  if !call && !conforming && ddpl != cpl then gp terr
  if dhi &&& 0x8000 == 0 then exc Vec.NP (some terr)
  if !canonical target then gp 0
  let dhi ← setA dhi daddr
  let ncpl := if conforming then cpl else ddpl
  let ret := rip c
  if call && ncpl != cpl then
    let nrsp ← innerRsp ncpl 0 0
    let user := ncpl == 3
    let mut sp := nrsp
    sp ← push64 sp c.ss.sel.toUInt64 user
    sp ← push64 sp (rsp c) user
    sp ← push64 sp c.cs.sel.toUInt64 user
    sp ← push64 sp ret user
    let nsp := sp
    modCpu fun c => { c with ss := nullSs ncpl.toUInt16 ncpl, esp := nsp.toUInt32,
                             lmx := { c.lmx with rspHi := (nsp >>> 32).toUInt32 } }
  else if call then pushGate8 c.cs.sel.toUInt64 ret
  modCpu fun c => { c with cs := toSeg ((tsel &&& 0xFFFC) ||| ncpl.toUInt16) dlo dhi, eip := target.toUInt32 }
  enter64 (target >>> 32).toUInt32 (if call then "far CALL through a call gate" else "far JMP through a call gate")

/-! ## SYSCALL (vol. 3 SYSCALL_LONG_MODE) -/

/-- SYSCALL in compatibility mode (EFER.SCE checked by the caller): RCX = the next RIP, R11 = RFLAGS
(RF clear), CS = STAR[47:32] & FFFCh as a flat 64-bit DPL-0 code segment, SS = STAR[47:32] + 8 as a
flat DPL-0 stack segment (its RPL is not cleared, as in legacy mode), RFLAGS &= ~SFMASK, RF = 0,
RIP = CSTAR: 64-bit mode, where the model stops. -/
def syscallLong : M Unit := do
  let c ← cpu
  let sel := (c.sysx.star >>> 32).toUInt32 &&& 0xFFFF
  let cstar := c.sysx.cstar
  modCpu fun c => { c with
    ecx := c.eip, eip := cstar.toUInt32,
    cs := { sel := (sel &&& 0xFFFC).toUInt16, base := 0, limit := 0xFFFFFFFF, attr := 0xA09B },
    ss := { sel := ((sel + 8) &&& 0xFFFF).toUInt16, base := 0, limit := 0xFFFFFFFF, attr := 0xC093 },
    eflags := c.eflags &&& ~~~(c.sysx.sfmask ||| Flag.RF),
    lmx := { c.lmx with r11 := (c.eflags &&& ~~~Flag.RF).toUInt64 } }
  enter64 (cstar >>> 32).toUInt32 "SYSCALL"

end LongMode
end X86
