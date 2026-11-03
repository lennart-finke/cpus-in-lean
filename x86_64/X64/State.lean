import X64.Word
/-!
# Architectural CPU state

A segment register consists of the visible selector and the hidden descriptor cache
(base, scaled limit, attributes).  `attr` holds bits 8..23 of the descriptor's high
dword, with the limit[19:16] nibble cleared:

* bits 0..3  type, bit 4 S, bits 5..6 DPL, bit 7 P
* bit 12 AVL, bit 13 L, bit 14 D/B, bit 15 G

In 64-bit mode ordinary data accesses ignore segment limits and DS/ES/SS bases;
FS/GS bases come from their architectural base registers. Descriptor loads still
check type and privilege.
-/
namespace X64

structure SegReg where
  sel   : UInt16 := 0
  base  : UInt64 := 0
  limit : UInt64 := 0xFFFF
  attr  : UInt64 := 0x93
  deriving Repr, Inhabited, BEq

namespace SegReg
@[inline] def present (s : SegReg) : Bool := s.attr &&& 0x80 != 0
@[inline] def dpl (s : SegReg) : UInt64 := (s.attr >>> 5) &&& 3
@[inline] def big (s : SegReg) : Bool := s.attr &&& 0x4000 != 0
@[inline] def isCode (s : SegReg) : Bool := s.attr &&& 0x18 == 0x18
@[inline] def typ (s : SegReg) : UInt64 := s.attr &&& 0xF
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

/-- 128-bit SSE register, represented as two architectural 64-bit halves. -/
structure Xmm where
  lo : UInt64 := 0
  hi : UInt64 := 0
  deriving Repr, BEq, Inhabited

structure Float80 where
  significand : UInt64 := 0
  signExp : UInt16 := 0
  deriving Repr, BEq, Inhabited

structure Cpu where
  xmm : Array Xmm := Array.replicate 16 {}
  mxcsr : UInt64 := 0x1F80
  fpControl : UInt16 := 0x37F
  fpStatus : UInt16 := 0
  fpTag : UInt16 := 0xFFFF
  fpOpcode : UInt16 := 0
  fpIp : UInt64 := 0
  fpDp : UInt64 := 0
  fp : Array Float80 := Array.replicate 8 {}

  rax : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rbx : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  r8 : UInt64 := 0
  r9 : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  efer : UInt64 := 0
  fsBase : UInt64 := 0
  gsBase : UInt64 := 0
  kernelGsBase : UInt64 := 0
  star : UInt64 := 0
  lstar : UInt64 := 0
  cstar : UInt64 := 0
  sfmask : UInt64 := 0
  rip : UInt64 := 0
  rflags : UInt64 := 2
  es : SegReg := {}
  cs : SegReg := { attr := 0x9B }
  ss : SegReg := {}
  ds : SegReg := {}
  fs : SegReg := {}
  gs : SegReg := {}
  ldtr : SegReg := { attr := 0x82 }
  tr : SegReg := { attr := 0x8B }
  gdtBase : UInt64 := 0
  gdtLimit : UInt64 := 0xFFFF
  idtBase : UInt64 := 0
  idtLimit : UInt64 := 0x3FF
  cr0 : UInt64 := 0x10
  cr2 : UInt64 := 0
  cr3 : UInt64 := 0
  cr4 : UInt64 := 0
  dr0 : UInt64 := 0
  dr1 : UInt64 := 0
  dr2 : UInt64 := 0
  dr3 : UInt64 := 0
  dr6 : UInt64 := 0xFFFF0FF0
  dr7 : UInt64 := 0x400
  /-- Model-specific registers that have been written (for future MSR extensions). -/
  msrs : List (UInt64 × UInt64) := []
  halted : Bool := false
  /-- Interrupts are inhibited for one instruction after STI / MOV SS / POP SS. -/
  shadow : Bool := false
  deriving Repr, Inhabited

namespace Cpu

@[inline] def getReg (c : Cpu) (r : UInt8) : UInt64 :=
  match r with
  | 0 => c.rax | 1 => c.rcx | 2 => c.rdx | 3 => c.rbx
  | 4 => c.rsp | 5 => c.rbp | 6 => c.rsi | 7 => c.rdi
  | 8 => c.r8
  | 9 => c.r9
  | 10 => c.r10
  | 11 => c.r11
  | 12 => c.r12
  | 13 => c.r13
  | 14 => c.r14
  | _ => c.r15

@[inline] def setReg (c : Cpu) (r : UInt8) (v : UInt64) : Cpu :=
  match r with
  | 0 => { c with rax := v } | 1 => { c with rcx := v }
  | 2 => { c with rdx := v } | 3 => { c with rbx := v }
  | 4 => { c with rsp := v } | 5 => { c with rbp := v }
  | 6 => { c with rsi := v } | 7 => { c with rdi := v }
  | 8 => { c with r8 := v }
  | 9 => { c with r9 := v }
  | 10 => { c with r10 := v }
  | 11 => { c with r11 := v }
  | 12 => { c with r12 := v }
  | 13 => { c with r13 := v }
  | 14 => { c with r14 := v }
  | _ => { c with r15 := v }

@[inline] def getSeg (c : Cpu) (s : UInt8) : SegReg :=
  match s with
  | 0 => c.es | 1 => c.cs | 2 => c.ss | 3 => c.ds | 4 => c.fs | _ => c.gs

@[inline] def setSeg (c : Cpu) (s : UInt8) (v : SegReg) : Cpu :=
  match s with
  | 0 => { c with es := v } | 1 => { c with cs := v } | 2 => { c with ss := v }
  | 3 => { c with ds := v } | 4 => { c with fs := v } | _ => { c with gs := v }

/-- Encoded byte registers 4..7 mean AH..BH only in the absence of REX. -/
@[inline] def rdReg (c : Cpu) (sz : Sz) (r : UInt8) (rex : Bool := false) : UInt64 :=
  if sz == 1 && !rex && 4 ≤ r && r < 8 then (c.getReg (r - 4) >>> 8) &&& 0xFF
  else c.getReg r &&& sz.mask

/-- A 32-bit write clears the upper half; 8/16-bit writes preserve other bits. -/
@[inline] def wrReg (c : Cpu) (sz : Sz) (r : UInt8) (v : UInt64) (rex : Bool := false) : Cpu :=
  if sz == 8 then c.setReg r v
  else if sz == 4 then c.setReg r (v &&& 0xFFFFFFFF)
  else if sz == 1 && !rex && 4 ≤ r && r < 8 then
    let h := r - 4
    c.setReg h ((c.getReg h &&& ~~~(0xFF00 : UInt64)) ||| ((v &&& 0xFF) <<< 8))
  else c.setReg r ((c.getReg r &&& ~~~sz.mask) ||| (v &&& sz.mask))

@[inline] def long (c : Cpu) : Bool := c.efer &&& 0x400 != 0 && c.cs.attr &&& 0x2000 != 0

@[inline] def pe (c : Cpu) : Bool := c.cr0 &&& CR0.PE != 0
@[inline] def vm86 (c : Cpu) : Bool := c.rflags &&& Flag.VM != 0

/-- Current privilege level. -/
@[inline] def cpl (c : Cpu) : UInt64 :=
  if !c.pe then 0 else if c.vm86 then 3 else c.cs.sel.toUInt64 &&& 3

@[inline] def iopl (c : Cpu) : UInt64 := (c.rflags >>> 12) &&& 3

@[inline] def flag (c : Cpu) (f : UInt64) : Bool := c.rflags &&& f != 0

/-- Replace the flags selected by `mask` with the bits of `v`. -/
@[inline] def setFlags (c : Cpu) (mask v : UInt64) : Cpu :=
  { c with rflags := (c.rflags &&& ~~~mask) ||| (v &&& mask) }

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
end Vec

/-- Abnormal termination of an instruction. -/
inductive Fault where
  /-- A processor exception; `err` is the pushed error code, if any; `addr` is the CR2 value for #PF. -/
  | exc (vec : UInt8) (err : Option UInt64) (addr : UInt64)
  /-- Shutdown (triple fault). -/
  | shutdown (why : String)
  /-- Behaviour outside the scope of this model; stops the simulation. -/
  | unsupported (what : String)
  deriving Repr, Inhabited

end X64
