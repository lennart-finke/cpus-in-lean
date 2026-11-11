import X86.Ext.Gpr
import X86.Ext.Sse
import X86.Ext.Crypto
import X86.Ext.Xsave
import X86.Ext.Avx
import X86.Ext.Avx2
import X86.Ext.Sys
import X86.Ext.Svm
import X86.Ext.LongMode
import X86.Ext.Smp
/-!
# Instruction dispatch

`exec i` runs a decoded instruction: the core semantics `Exec.execBase` for the one-byte and 0F
maps, with hooks into the extension modules `X86/Ext/*.lean` at fixed places. A hook returns
`none` when its module does not implement the instruction form; then the next hook of the chain, or
the fallback, runs. Only the opcodes listed in `execOne` go through hooks, so the other one-byte and
0F instructions run exactly as before at the cost of a table lookup.

This file is written once (by the foundation work) and is not edited by the workstreams: each
owns its module's hooks (see each module's documentation and `x86_32/EXTENDING.md`).
-/
namespace X86

/-- Run the action of a hook, or `fallback` if no hook took the instruction. -/
@[inline] def hooked (h : Option (M Unit)) (fallback : M Unit) : M Unit :=
  match h with
  | some a => a
  | none => fallback

/-- MSR lookup: the core MSRs, then each module's (owners: see the modules). -/
def msr? (n : UInt32) : Option MsrImpl :=
  coreMsr? n <|> Gpr.msr? n <|> Sys.msr? n <|> Xsave.msr? n <|> Svm.msr? n <|> LongMode.msr? n <|>
    Smp.msr? n

def rdmsr (n : UInt32) : M UInt64 := rdmsrWith msr? n
def wrmsr (n : UInt32) (v : UInt64) : M Unit := wrmsrWith msr? n v

/-- 0F 01 register forms other than SMSW (/4) and LMSW (/6): MONITOR/MWAIT, CLAC/STAC,
XGETBV/XSETBV, the SVM instructions, SWAPGS, RDTSCP, MONITORX/MWAITX, CLZERO, RDPRU. -/
def grp7Reg (i : Inst) : M Unit :=
  hooked (Gpr.op0F? i <|> Sys.op0F? i <|> Xsave.op0F? i <|> Svm.op0F? i <|> LongMode.op0F? i) ud

/-- 0F AE forms handled by the core (`Simd.grp15`): no mandatory prefix, and FXSAVE, FXRSTOR,
LDMXCSR, STMXCSR (memory /0../3) or LFENCE, MFENCE, SFENCE (register /5../7). -/
@[inline] def grp15Core (i : Inst) : Bool :=
  i.pp == 0 && (if i.isMem then i.reg ≤ 3 else i.reg ≥ 5)

/-- One-byte and 0F-map opcode `op` with its hooks. -/
def execOne (op : Nat) : Inst → M Unit :=
  let base := execBase op
  match op with
  -- system: SYSCALL, SYSRET, SYSENTER, SYSEXIT (Sys)
  | 0x105 | 0x107 | 0x134 | 0x135 => fun i => hooked (Sys.op0F? i) (base i)
  -- PREFETCH/PREFETCHW, prefetch hints, RDPMC (Gpr)
  | 0x10D | 0x118 | 0x133 => fun i => hooked (Gpr.op0F? i) (base i)
  -- F3 0F 09 WBNOINVD (Gpr)
  | 0x109 => fun i => if i.rep == 0xF3 then hooked (Gpr.op0F? i) (base i) else base i
  -- F3 0F B8 POPCNT (Gpr)
  | 0x1B8 => fun i => hooked (Gpr.op0F? i) (base i)
  -- F3 0F BC/BD TZCNT/LZCNT (Gpr); without them BSF/BSR
  | 0x1BC | 0x1BD => fun i => if i.rep == 0xF3 then hooked (Gpr.op0F? i) (base i) else base i
  -- SSE3 and SSE4a forms of the 0F map (Sse)
  | 0x112 | 0x116 | 0x12B => fun i => if i.pp ≥ 2 then hooked (Sse.op0F? i) (base i) else base i
  | 0x178 | 0x179 | 0x17C | 0x17D | 0x1D0 => fun i => hooked (Sse.op0F? i) (base i)
  | 0x1F0 => fun i => if i.pp == 3 then hooked (Sse.op0F? i) (base i) else base i
  -- LOCK MOV CR0 = MOV CR8 (AltMovCr8, Sys)
  | 0x120 | 0x122 => fun i => if i.lock then hooked (Sys.op0F? i) (base i) else base i
  -- 0F 01 register forms (Gpr, Sys, Xsave, Svm, LongMode)
  | 0x101 => fun i => if i.isMem || i.reg == 4 || i.reg == 6 then base i else grp7Reg i
  -- 0F AE beyond FXSAVE..STMXCSR and the fences (Xsave, Gpr, LongMode)
  | 0x1AE => fun i => if grp15Core i then base i
                      else hooked (Xsave.op0F? i <|> Gpr.op0F? i <|> LongMode.op0F? i) ud
  -- 0F C7 beyond CMPXCHG8B (Xsave, Gpr)
  | 0x1C7 => fun i => if i.reg == 1 then base i else hooked (Xsave.op0F? i <|> Gpr.op0F? i) (base i)
  -- WRMSR, RDMSR
  | 0x130 => fun _ => do wrmsr (← getReg 1) ((← getReg 0).toUInt64 ||| ((← getReg 2).toUInt64 <<< 32))
  | 0x132 => fun _ => do
    let v ← rdmsr (← getReg 1)
    setReg 0 v.toUInt32
    setReg 2 (v >>> 32).toUInt32
  | _ =>
    if op < 0x200 then base
    -- 0F 38 and 0F 3A (Sse, Crypto, Gpr)
    else if op < 0x300 then fun i => hooked (Sse.map2? i <|> Crypto.map2? i <|> Gpr.map2? i) ud
    else fun i => hooked (Sse.map3? i <|> Crypto.map3? i) ud

/-- Dispatch table of the legacy encodings, indexed by `Inst.op` (0x000..0x3FF). -/
def execTable : Array (Inst → M Unit) := Array.ofFn (n := 1024) fun k => execOne k.val

/-- VEX-encoded instructions, keyed on (map, `pp`, opcode) = (`op >>> 8`, `pp`, `op &&& 0xFF`):
#UD in real and virtual-8086 mode (SDM vol. 2A, 2.3; the decoder recognises VEX in every mode),
with a 66, F2, F3 or LOCK prefix before VEX (SDM vol. 2A, 2.3.2) and for maps other than 0F, 0F 38,
0F 3A; then BMI1/BMI2 (Gpr), AVX (Avx), AVX2/FMA/F16C (Avx2). -/
def vexExec (i : Inst) : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 then ud
  if i.lock || i.rep != 0 || i.p66 || i.op < 0x100 then ud
  hooked (Gpr.vex? i <|> Avx.vex? i <|> Avx2.vex? i) ud

@[inline] def exec (i : Inst) : M Unit :=
  if i.vex then vexExec i else execTable[i.op.toNat]! i

end X86
