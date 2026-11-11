import X86.Exec
/-!
# Long mode (entry and compatibility mode): instruction and MSR hooks

Owner: the long-mode workstream. The architecture (activation, compatibility mode, 4-level paging,
the 64-bit boundary) is described in `X86/Ext/LongModeBase.lean`, which the core descriptor,
far-transfer and interrupt code calls; the 4-level walk is `walkLong` in `X86/Machine.lean`; state:
`LongModeState` in `X86/State.lean`.

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for 0F 01 register forms other than SMSW/LMSW (this module owns F8, SWAPGS)
  and for the 0F AE forms other than FXSAVE/FXRSTOR/LDMXCSR/STMXCSR and the fences (this module owns
  F3 0F AE register /0../3: RDFSBASE, RDGSBASE, WRFSBASE, WRGSBASE). All of them exist only in 64-bit
  mode, where the model does not execute: #UD (APM vol. 3 SWAPGS: "#UD ... not in 64-bit mode";
  RDFSBASE..WRGSBASE: "#UD ... not in 64-bit mode", checked before CR4.FSGSBASE).
* `msr?`: FS_BASE, GS_BASE, KernelGSbase (C000_0100h..C000_0102h; LSTAR, CSTAR and SFMASK are
  system A's, `Sys.msr?`). WRMSR of a non-canonical address is #GP(0) (APM vol. 2, 4.5.3 and the
  WRMSR exception list). They exist with CPUID Fn8000_0001_EDX[LM]; RDMSR/WRMSR work in every mode at
  CPL 0. FS_BASE/GS_BASE write bits 31:0 into the segment cache's base (all that legacy and
  compatibility-mode addressing uses) and keep bits 63:32 (`LongModeState.fsBase`).
-/
namespace X86
namespace LongMode

def op0F? (i : Inst) : Option (M Unit) :=
  if !implemented .lm then none
  else if i.op == 0x101 && i.modrm == 0xF8 then some ud
  else if i.op == 0x1AE && !i.isMem && i.pp == 2 && i.reg ≤ 3 then some ud
  else none

/-- FS_BASE (`s` = FS) or GS_BASE: the 64-bit base, if WRMSR set it and the cache is unchanged. -/
def segBaseRd (s : UInt8) : M UInt64 := do
  let c ← cpu
  let sr := c.getSeg s
  let saved := if s == SegN.FS then c.lmx.fsBase else c.lmx.gsBase
  match saved with
  | some (cache, b) => return if cache == sr then b else sr.base.toUInt64
  | none => return sr.base.toUInt64

def segBaseWr (s : UInt8) (v : UInt64) : M Unit := do
  if !canonical v then gp 0
  modCpu fun c =>
    let sr := { c.getSeg s with base := v.toUInt32 }
    let c := c.setSeg s sr
    if s == SegN.FS then { c with lmx := { c.lmx with fsBase := some (sr, v) } }
    else { c with lmx := { c.lmx with gsBase := some (sr, v) } }

def msr? (n : UInt32) : Option MsrImpl :=
  if !implemented .lm then none
  else if n == 0xC0000100 then some { rd := segBaseRd SegN.FS, wr := segBaseWr SegN.FS }
  else if n == 0xC0000101 then some { rd := segBaseRd SegN.GS, wr := segBaseWr SegN.GS }
  else if n == 0xC0000102 then
    some { rd := do return (← cpu).lmx.kernelGsBase
           wr := fun v => do
             if !canonical v then gp 0
             modCpu fun c => { c with lmx := { c.lmx with kernelGsBase := v } } }
  else none

end LongMode
end X86
