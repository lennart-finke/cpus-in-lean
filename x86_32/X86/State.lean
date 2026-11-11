import X86.Word
import X86.Float80
/-!
# Architectural CPU state

A segment register consists of the visible selector and the hidden descriptor cache
(base, scaled limit, attributes).  `attr` holds bits 8..23 of the descriptor's high
dword, with the limit[19:16] nibble cleared:

* bits 0..3  type, bit 4 S, bits 5..6 DPL, bit 7 P
* bit 12 AVL, bit 13 L, bit 14 D/B, bit 15 G

A segment register whose cache has `P = 0` is *unusable* (e.g. after loading a null
selector); any memory reference through it raises #GP.
-/
namespace X86

structure SegReg where
  sel   : UInt16 := 0
  base  : UInt32 := 0
  limit : UInt32 := 0xFFFF
  attr  : UInt32 := 0x93
  deriving Repr, Inhabited, BEq

namespace SegReg
@[inline] def present (s : SegReg) : Bool := s.attr &&& 0x80 != 0
@[inline] def dpl (s : SegReg) : UInt32 := (s.attr >>> 5) &&& 3
@[inline] def big (s : SegReg) : Bool := s.attr &&& 0x4000 != 0
@[inline] def isCode (s : SegReg) : Bool := s.attr &&& 0x18 == 0x18
@[inline] def typ (s : SegReg) : UInt32 := s.attr &&& 0xF
end SegReg

-- Segment register numbers as encoded in instructions.
namespace SegN
def ES : UInt8 := 0
def CS : UInt8 := 1
def SS : UInt8 := 2
def DS : UInt8 := 3
def FS : UInt8 := 4
def GS : UInt8 := 5
end SegN

/-- A 128-bit XMM register. -/
structure V128 where
  lo : UInt64 := 0
  hi : UInt64 := 0
  deriving Repr, Inhabited, BEq

/-- SSE registers XMM0..XMM7 and the SIMD control/status register MXCSR (reset value 0x1F80: all
exceptions masked, round to nearest). Kept in one field of `Cpu`, so that the many `Cpu` updates of
integer instructions do not copy them.

`ymmh` holds bits 255:128 of YMM0..YMM7 (AVX); YMMk = `ymmh[k]` : `xmm[k]`. Legacy SSE instructions
leave it unchanged, VEX.128 instructions zero it (SDM vol. 1, 14.1.2). Nothing writes it yet. -/
structure SseState where
  xmm : Array V128 := Array.replicate 8 {}
  mxcsr : UInt32 := 0x1F80
  ymmh : Array V128 := Array.replicate 8 {}
  deriving Repr, Inhabited

/-! Per-owner state. Each extension module (`X86/Ext/*.lean`, see `EXTENDING.md`) that needs new
architectural CPU state adds fields to its own structure below, so that parallel work does not edit
the same lines. They are fields of `CpuExt` (not copied by integer-instruction updates). -/

/-- State of `X86/Ext/Gpr.lean` (see its module documentation). -/
structure GprState where
  /-- The monitor hardware of MONITOR/MONITORX: the physical address of the armed 64-byte line
  (`none`: not armed) and the line's 16 dwords when it was armed. -/
  monLine : Option UInt64 := none
  monData : Array UInt32 := #[]
  /-- The deterministic entropy source of RDRAND/RDSEED: the SplitMix64 state. -/
  rng : UInt64 := 0
  /-- TSC_AUX (MSR C000_0103h), read by RDTSCP and RDPID; bits 63:32 are reserved. -/
  tscAux : UInt32 := 0
  /-- HWCR (MSR C001_0015h) bit 10, MonMwaitUserEn: MONITOR/MWAIT allowed at CPL > 0. -/
  monMwaitUserEn : Bool := false
  /-- MPERF and APERF (MSRs E7h, E8h, read by RDPRU) as offsets from the instruction count. -/
  mperfOff : UInt64 := 0
  aperfOff : UInt64 := 0
  /-- Core performance counters PerfCtr0..5 (48 bits) and their event selects PerfEvtSel0..5. -/
  perfCtr : Array UInt64 := Array.replicate 6 0
  perfEvtSel : Array UInt64 := Array.replicate 6 0
  deriving Repr, Inhabited

/-- State of `X86/Ext/Sys.lean` (SYSENTER/SYSCALL MSRs, TSC offset, PAT, MTRRs, ...). -/
structure SysState where
  deriving Repr, Inhabited

/-- State of `X86/Ext/Svm.lean` (VM_HSAVE_PA, GIF, ...). -/
structure SvmState where
  deriving Repr, Inhabited

/-- State of `X86/Ext/LongMode.lean`. -/
structure LongModeState where
  deriving Repr, Inhabited

/-- CPU state beyond the integer core: x87, EFER, PAE registers, SMM. Integer code never touches it,
so it is one (parent) field of `Cpu`: the many `Cpu` updates of integer instructions do not copy
these fields, and symbolic proofs carry a single constant instead of a dozen. -/
structure CpuExt where
  /-- x87 physical registers R0..R7 (ST(i) is R((TOP + i) mod 8)). -/
  fpr : Array F80 := Array.replicate 8 {}
  /-- x87 control word, status word (TOP in bits 11..13), and empty-register bits (bit k: Rk empty;
  the other tag values are derived from register contents). -/
  fcw : UInt16 := 0x37F
  fsw : UInt16 := 0
  fempty : UInt8 := 0xFF
  /-- Last non-control x87 instruction: pointer (CS:EIP), opcode (11 bits), data operand (DS:offset). -/
  fip : UInt32 := 0
  fcs : UInt16 := 0
  fop : UInt16 := 0
  fdp : UInt32 := 0
  fds : UInt16 := 0
  /-- IA32_EFER; the writable bits are `Cpuid.eferWritable` (only NXE, bit 11, today). -/
  efer : UInt32 := 0
  /-- XCR0 (XFEATURE_ENABLED_MASK, written by XSETBV); reset value 1 (x87 only), SDM vol. 1, 13.3. -/
  xcr0 : UInt64 := 1
  /-- IA32_XSS (MSR 0xDA0, supervisor state components of XSAVES/XRSTORS); reset 0. -/
  xss : UInt64 := 0
  /-- PAE page-directory-pointer-table registers, loaded from CR3 by MOV CR0/CR3/CR4 and task
  switches while PAE paging is (being) enabled; translation uses these, not memory. -/
  pdpte : Array UInt64 := #[0, 0, 0, 0]
  /-- System-management mode, entered on an SMI and left by RSM. -/
  smm : Bool := false
  /-- SMRAM base: SMM is entered at `smbase + 0x8000`, the state is saved at `smbase + 0xFE00..0xFFFF`. -/
  smbase : UInt32 := 0x30000
  /-- Some breakpoint of DR7 is enabled (L0..3/G0..3 not all clear), cached from `dr7`: set wherever
  DR7 is written (`Cpu.setDr7`). Checked on every instruction and data access. -/
  bpOn : Bool := false
  gprx : GprState := {}
  sysx : SysState := {}
  svmx : SvmState := {}
  lmx : LongModeState := {}
  deriving Repr, Inhabited

structure Cpu extends CpuExt where
  eax : UInt32 := 0
  ecx : UInt32 := 0
  edx : UInt32 := 0
  ebx : UInt32 := 0
  esp : UInt32 := 0
  ebp : UInt32 := 0
  esi : UInt32 := 0
  edi : UInt32 := 0
  eip : UInt32 := 0
  eflags : UInt32 := 2
  es : SegReg := {}
  cs : SegReg := { attr := 0x9B }
  ss : SegReg := {}
  ds : SegReg := {}
  fs : SegReg := {}
  gs : SegReg := {}
  ldtr : SegReg := { attr := 0x82 }
  tr : SegReg := { attr := 0x8B }
  gdtBase : UInt32 := 0
  gdtLimit : UInt32 := 0xFFFF
  idtBase : UInt32 := 0
  idtLimit : UInt32 := 0x3FF
  cr0 : UInt32 := 0x10
  cr2 : UInt32 := 0
  cr3 : UInt32 := 0
  cr4 : UInt32 := 0
  dr0 : UInt32 := 0
  dr1 : UInt32 := 0
  dr2 : UInt32 := 0
  dr3 : UInt32 := 0
  dr6 : UInt32 := 0xFFFF0FF0
  dr7 : UInt32 := 0x400
  /-- Model-specific registers that have been written (see `Exec.coreMsr?`). -/
  msrs : List (UInt32 × UInt64) := []
  halted : Bool := false
  /-- Interrupts are inhibited for one instruction after STI / MOV SS / POP SS. -/
  shadow : Bool := false
  /-- SSE state (`Cpu.xmm`, `Cpu.mxcsr`). The MMX registers MM0..MM7 are the significands of `fpr`. -/
  sse : SseState := {}
  deriving Repr, Inhabited

namespace Cpu

/-- Write DR7 and its cached breakpoint-enable flag. -/
@[inline] def setDr7 (c : Cpu) (v : UInt32) : Cpu := { c with dr7 := v, bpOn := v &&& 0xFF != 0 }

@[inline] def xmm (c : Cpu) : Array V128 := c.sse.xmm
@[inline] def mxcsr (c : Cpu) : UInt32 := c.sse.mxcsr
@[inline] def ymmh (c : Cpu) : Array V128 := c.sse.ymmh

@[inline] def getReg (c : Cpu) (r : UInt8) : UInt32 :=
  match r with
  | 0 => c.eax | 1 => c.ecx | 2 => c.edx | 3 => c.ebx
  | 4 => c.esp | 5 => c.ebp | 6 => c.esi | _ => c.edi

@[inline] def setReg (c : Cpu) (r : UInt8) (v : UInt32) : Cpu :=
  match r with
  | 0 => { c with eax := v } | 1 => { c with ecx := v }
  | 2 => { c with edx := v } | 3 => { c with ebx := v }
  | 4 => { c with esp := v } | 5 => { c with ebp := v }
  | 6 => { c with esi := v } | _ => { c with edi := v }

@[inline] def getSeg (c : Cpu) (s : UInt8) : SegReg :=
  match s with
  | 0 => c.es | 1 => c.cs | 2 => c.ss | 3 => c.ds | 4 => c.fs | _ => c.gs

@[inline] def setSeg (c : Cpu) (s : UInt8) (v : SegReg) : Cpu :=
  match s with
  | 0 => { c with es := v } | 1 => { c with cs := v } | 2 => { c with ss := v }
  | 3 => { c with ds := v } | 4 => { c with fs := v } | _ => { c with gs := v }

/-- Read a register of size `sz` (for size 1, registers 4..7 are AH, CH, DH, BH). -/
@[inline] def rdReg (c : Cpu) (sz : Sz) (r : UInt8) : UInt32 :=
  if sz == 4 then c.getReg r
  else if sz == 2 then c.getReg r &&& 0xFFFF
  else if r < 4 then c.getReg r &&& 0xFF
  else (c.getReg (r - 4) >>> 8) &&& 0xFF

@[inline] def wrReg (c : Cpu) (sz : Sz) (r : UInt8) (v : UInt32) : Cpu :=
  if sz == 4 then c.setReg r v
  else if sz == 2 then c.setReg r ((c.getReg r &&& 0xFFFF0000) ||| (v &&& 0xFFFF))
  else if r < 4 then c.setReg r ((c.getReg r &&& 0xFFFFFF00) ||| (v &&& 0xFF))
  else
    let hi := r - 4
    let old : UInt32 := c.getReg hi
    c.setReg hi ((old &&& 0xFFFF00FF) ||| ((v &&& 0xFF) <<< (8 : UInt32)))

@[inline] def pe (c : Cpu) : Bool := c.cr0 &&& CR0.PE != 0
@[inline] def vm86 (c : Cpu) : Bool := c.eflags &&& Flag.VM != 0

/-- Current privilege level. -/
@[inline] def cpl (c : Cpu) : UInt32 :=
  if !c.pe then 0 else if c.vm86 then 3 else c.cs.sel.toUInt32 &&& 3

@[inline] def iopl (c : Cpu) : UInt32 := (c.eflags >>> 12) &&& 3

@[inline] def flag (c : Cpu) (f : UInt32) : Bool := c.eflags &&& f != 0

/-- Replace the flags selected by `mask` with the bits of `v`. -/
@[inline] def setFlags (c : Cpu) (mask v : UInt32) : Cpu :=
  { c with eflags := (c.eflags &&& ~~~mask) ||| (v &&& mask) }

end Cpu

-- Exception vectors.
namespace Vec
def DE : UInt8 := 0
def DB : UInt8 := 1
def BP : UInt8 := 3
def OF : UInt8 := 4
def BR : UInt8 := 5
def UD : UInt8 := 6
def NM : UInt8 := 7
def DF : UInt8 := 8
def TS : UInt8 := 10
def NP : UInt8 := 11
def SS : UInt8 := 12
def GP : UInt8 := 13
def PF : UInt8 := 14
def MF : UInt8 := 16
def AC : UInt8 := 17
/-- SIMD floating-point exception. -/
def XM : UInt8 := 19
end Vec

/-- Abnormal termination of an instruction. -/
inductive Fault where
  /-- A processor exception; `err` is the pushed error code, if any; `addr` is the CR2 value for #PF. -/
  | exc (vec : UInt8) (err : Option UInt32) (addr : UInt32)
  /-- Shutdown (triple fault). -/
  | shutdown (why : String)
  /-- Behaviour outside the scope of this model; stops the simulation. -/
  | unsupported (what : String)
  deriving Repr, Inhabited

end X86
