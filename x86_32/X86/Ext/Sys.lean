import X86.Exec
/-!
# System extensions (system workstream A)

Owner: the system workstream A. SYSENTER/SYSEXIT, legacy-mode SYSCALL/SYSRET (STAR, EFER.SCE),
CLAC/STAC, AltMovCr8 (LOCK MOV CR0 = CR8) and the model-specific registers of the module (TSC,
SYSENTER/SYSCALL linkage, PAT, MTRRs, machine check, speculation control, AMD configuration MSRs).
State: `SysState` in `X86/State.lean` (hot MSRs) and `Cpu.msrs` (the others). The paging features of
the workstream (SMEP/SMAP, global pages, PSE-36, MAXPHYADDR 48) are in `X86/Machine.lean`, UMIP and
the TSC read in `X86/Exec.lean`, alignment checking (#AC) in `X86/Machine.lean` (`acChk`) and at the
multi-part operands (`Fpu.fpRead`/`fpWrite`, `Simd.vecAddr`, CMPXCHG8B).

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for
  - 0F 05 (SYSCALL), 0F 07 (SYSRET), 0F 34 (SYSENTER), 0F 35 (SYSEXIT) (fallback #UD);
  - LOCK 0F 20 / LOCK 0F 22 (AltMovCr8: MOV from/to CR8; fallback: the core behaviour; `lockOk` in
    `X86/Step.lean` admits LOCK on them once `altMovCr8` is implemented);
  - 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns CA (CLAC) and
    CB (STAC).
* `msr?`: the MSRs listed at `msr?` (looked up after the core MSRs of `Exec.coreMsr?`).

Sources: AMD64 APM vol. 2 rev. 3.46 (24593) and vol. 3 rev. 3.39 (24594). Where AMD's documents are
silent the Intel SDM is followed, and where the AMD family 17h PPR would be needed (it was not
available) values are marked UNCONFIRMED.
-/
namespace X86
namespace Sys

/-! ## SYSENTER / SYSEXIT, SYSCALL / SYSRET

The four instructions load CS and SS with fixed flat caches instead of reading descriptors: base 0,
limit 4 GiB, 32-bit, CS execute/read, SS read/write expand-up, accessed (as `SegReg.attr`). -/

/-- Flat 32-bit code segment cache with privilege `dpl` (attributes as `SegReg.attr`: G, D, P, DPL,
S, type 1011b). -/
@[inline] def flatCode (sel : UInt32) (dpl : UInt32) : SegReg :=
  { sel := sel.toUInt16, base := 0, limit := 0xFFFFFFFF, attr := 0xC09B ||| (dpl <<< 5) }

/-- Flat 32-bit stack segment cache with privilege `dpl` (type 0011b). -/
@[inline] def flatStack (sel : UInt32) (dpl : UInt32) : SegReg :=
  { sel := sel.toUInt16, base := 0, limit := 0xFFFFFFFF, attr := 0xC093 ||| (dpl <<< 5) }

/-- SYSENTER (AMD APM vol. 3, SYSENTER; vol. 2, 6.1.2). #UD in real mode (vol. 3's exception table;
its text says #GP, as does the Intel SDM, and QEMU raises #UD: real hardware unconfirmed); #GP(0)
if SYSENTER_CS is a null selector (bits 15:2 zero). CS = SYSENTER_CS with RPL 0, SS = CS + 8, both
flat at CPL 0; ESP = SYSENTER_ESP, EIP = SYSENTER_EIP; EFLAGS.VM and IF cleared (RF is already
clear while an instruction executes). Also from virtual-8086 mode. -/
def sysenter : M Unit := do
  let c ← cpu
  if !c.pe then ud
  let cs := c.sysx.sysenterCs &&& 0xFFFC
  if cs == 0 then gp 0
  modCpu fun c => { c with
    cs := flatCode cs 0, ss := flatStack ((cs + 8) &&& 0xFFFF) 0,
    esp := c.sysx.sysenterEsp, eip := c.sysx.sysenterEip,
    eflags := c.eflags &&& ~~~(Flag.VM ||| Flag.IF ||| Flag.RF) }

/-- SYSEXIT (AMD APM vol. 3, SYSEXIT): #GP(0) outside protected mode (real and virtual-8086 mode),
at CPL > 0 and if SYSENTER_CS is null. CS = (SYSENTER_CS + 16) | 3, SS = (SYSENTER_CS + 24) | 3,
both flat at CPL 3; ESP = ECX, EIP = EDX. -/
def sysexit : M Unit := do
  let c ← cpu
  if !c.pe || c.vm86 || c.cpl != 0 then gp 0
  let sc := c.sysx.sysenterCs
  if sc &&& 0xFFFC == 0 then gp 0
  modCpu fun c => { c with
    cs := flatCode (((sc + 16) &&& 0xFFFC) ||| 3) 3, ss := flatStack (((sc + 24) &&& 0xFFFC) ||| 3) 3,
    esp := c.ecx, eip := c.edx, eflags := c.eflags &&& ~~~Flag.RF }

/-- Legacy-mode SYSCALL (AMD APM vol. 3, SYSCALL, SYSCALL_LEGACY_MODE; unlike Intel, valid outside
64-bit mode): #UD if EFER.SCE = 0, no other check ("no permission checks based on the CPL, real mode,
or virtual-8086 mode"). ECX = the next EIP; CS = STAR[47:32] with RPL 0, flat 32-bit code at CPL 0;
SS = STAR[47:32] + 8 (the pseudocode does not clear its RPL; QEMU does), flat stack; EFLAGS.VM, IF
and RF cleared; EIP = STAR[31:0]. -/
def syscall : M Unit := do
  let c ← cpu
  if c.efer &&& EFER.SCE == 0 then ud
  let sel := (c.sysx.star >>> 32).toUInt32 &&& 0xFFFF
  modCpu fun c => { c with
    ecx := c.eip, eip := c.sysx.star.toUInt32,
    cs := flatCode (sel &&& 0xFFFC) 0, ss := flatStack ((sel + 8) &&& 0xFFFF) 0,
    eflags := c.eflags &&& ~~~(Flag.VM ||| Flag.IF ||| Flag.RF) }

/-- Legacy-mode SYSRET (AMD APM vol. 3, SYSRET, SYSRET_NON_64BIT_MODE): #UD if EFER.SCE = 0, #GP(0)
outside protected mode or at CPL > 0. CS = STAR[63:48] | 3, flat 32-bit code at CPL 3; SS's selector
becomes STAR[63:48] + 8 while its base, limit and attributes are unchanged (AMD; QEMU loads a flat
CPL 3 cache and forces the RPL to 3); EFLAGS.IF set; EIP = ECX. -/
def sysret : M Unit := do
  let c ← cpu
  if c.efer &&& EFER.SCE == 0 then ud
  if !c.pe || c.vm86 || c.cpl != 0 then gp 0
  let sel := (c.sysx.star >>> 48).toUInt32
  modCpu fun c => { c with
    cs := flatCode (sel ||| 3) 3, ss := { c.ss with sel := ((sel + 8) &&& 0xFFFF).toUInt16 },
    eip := c.ecx, eflags := (c.eflags ||| Flag.IF) &&& ~~~Flag.RF }

/-! ## CLAC / STAC, AltMovCr8 -/

/-- CLAC (`set = false`) and STAC (AMD APM vol. 3): #UD in virtual-8086 mode and at CPL > 0 (and with
LOCK, which `Step.lockOk` rejects); otherwise clear or set EFLAGS.AC. Valid in real mode. -/
def clacStac (set : Bool) : M Unit := do
  let c ← cpu
  if c.vm86 || c.cpl != 0 then ud
  setFlags Flag.AC (if set then Flag.AC else 0)

/-- AltMovCr8 (CPUID Fn8000_0001_ECX[AltMovCr8]): LOCK MOV CR0 accesses CR8, the task-priority
register TPR[7:4] of the local APIC (AMD APM vol. 2, 3.1.5, 8.5.2; vol. 3, MOV CRn). LOCK with another
control register is #UD (as on QEMU; the APM defines only CR0). Then #GP(0) at CPL > 0 (as MOV CRn),
and for a write with any of bits 31:4 set (CR8 bits 63:4 are reserved, MBZ). Reads return TPR[7:4];
writes set TPR to `v << 4`, which is how CR8 and the APIC's TPR alias (QEMU does the same). -/
def movCr8 (i : Inst) : M Unit := do
  if i.reg != 0 then ud
  cplIs0
  if i.op == 0x120 then
    setReg i.rm (((← getM).apic.tpr >>> 4) &&& 0xF)
  else
    let v ← getReg i.rm
    if v &&& ~~~(0xF : UInt32) != 0 then gp 0
    modM fun m => m.apicWrite 0x80 (v <<< 4)

def op0F? (i : Inst) : Option (M Unit) :=
  match i.op with
  | 0x105 => if implemented .syscall then some syscall else none
  | 0x107 => if implemented .syscall then some sysret else none
  | 0x134 => if implemented .sep then some sysenter else none
  | 0x135 => if implemented .sep then some sysexit else none
  | 0x120 | 0x122 => if i.lock && implemented .altMovCr8 then some (movCr8 i) else none
  | 0x101 =>
    if i.isMem || !implemented .smap then none
    else if i.modrm == 0xCA then some (clacStac false)
    else if i.modrm == 0xCB then some (clacStac true)
    else none
  | _ => none

/-! ## Model-specific registers -/

/-- An MSR kept in `Cpu.msrs` with reset value `dflt`. -/
@[inline] def rdStore (n : UInt32) (dflt : UInt64 := 0) : M UInt64 := do
  return (((← cpu).msrs.find? (·.1 == n)).map (·.2)).getD dflt

@[inline] def wrStore (n : UInt32) (v : UInt64) : M Unit :=
  modCpu fun c => { c with msrs := (n, v) :: c.msrs.filter (·.1 != n) }

/-- A read/write MSR in `Cpu.msrs` with reset value `dflt`: WRMSR with a bit outside `mask` set is
#GP(0) (reserved, MBZ). -/
def checked (n : UInt32) (mask : UInt64) (dflt : UInt64 := 0) : MsrImpl where
  rd := rdStore n dflt
  wr v := do
    if v &&& ~~~mask != 0 then gp 0
    wrStore n v

/-- A read/write MSR in `Cpu.msrs` whose bits outside `mask` read as zero and ignore writes. -/
def masked (n : UInt32) (mask : UInt64) (dflt : UInt64 := 0) : MsrImpl where
  rd := rdStore n dflt
  wr v := wrStore n (v &&& mask)

/-- A read-only MSR: WRMSR is #GP(0). -/
def readOnly (v : UInt64) : MsrImpl where
  rd := return v
  wr _ := gp 0

/-- A counter that advances with the instruction count (TSC-like), stored as an offset in
`Cpu.msrs`. -/
def counter (n : UInt32) : MsrImpl where
  rd := do return (← getM).icount + (← rdStore n)
  wr v := do wrStore n (v - (← getM).icount)

/-- The memory types an MTRR may hold (AMD APM vol. 2, table 7-6: UC, WC, WT, WP, WB). A reserved
type is #GP(0) as in the Intel SDM (vol. 3, 11.11.2); the APM does not say. -/
@[inline] def mtrrType (t : UInt64) : Bool := t == 0 || t == 1 || t == 4 || t == 5 || t == 6

/-- PAT (AMD APM vol. 2, 7.8.1): eight PA fields of 3 bits in bits 8k+2:8k; writing a reserved bit
or an unsupported type (2, 3) is #GP(0). -/
def patOk (v : UInt64) : Bool :=
  (List.range 8).all fun k =>
    let b := (v >>> (8 * k).toUInt64) &&& 0xFF
    b &&& 0xF8 == 0 && b != 2 && b != 3

/-- Machine-check banks: BANK_CNT of MCG_CAP. UNCONFIRMED: the family 17h PPR's MCG_CAP count was
not available; 23 (the core's legacy MCi view, MCG_CTL present: MCG_CAP = 0x117) is assumed. -/
def mcBanks : UInt32 := 23

def hwcrMsr : UInt32 := 0xC0010015
def syscfgMsr : UInt32 := 0xC0010010

/-- SYSCFG[MtrrFixDramModEn] (bit 19): the RdMem/WrMem bits (4:3 of each type field) of the
fixed-range MTRRs are readable and writable (AMD APM vol. 2, 7.9.1). -/
def fixModEn : M Bool := do return (← rdStore syscfgMsr 0x20601) &&& 0x80000 != 0

/-- RdMem/WrMem bits of the eight type fields of a fixed-range MTRR. -/
def rdWrMem : UInt64 := 0x1818181818181818

/-- Fixed-range MTRR (AMD APM vol. 2, 7.7.2, 7.9.1): eight type fields; bits 7:5 of a field are
reserved (#GP(0)), a reserved type is #GP(0); RdMem/WrMem read as 0 and are not changed by writes
while SYSCFG[MtrrFixDramModEn] = 0. Writes invalidate the TLB (5.5.3). -/
def fixedMtrr (n : UInt32) : MsrImpl where
  rd := do
    let v ← rdStore n
    return if ← fixModEn then v else v &&& ~~~rdWrMem
  wr v := do
    let ok := (List.range 8).all fun k =>
      let b := (v >>> (8 * k).toUInt64) &&& 0xFF
      b &&& 0xE0 == 0 && mtrrType (b &&& 7)
    if !ok then gp 0
    let old ← rdStore n
    wrStore n (if ← fixModEn then v else (v &&& ~~~rdWrMem) ||| (old &&& rdWrMem))
    flushTlbAll

/-- An MTRR with reserved bits outside `mask` and (if `typed`) a type in bits 7:0; writes invalidate
the TLB including global pages (AMD APM vol. 2, 5.5.3). -/
def mtrr (n : UInt32) (mask : UInt64) (typed : Bool) : MsrImpl where
  rd := rdStore n
  wr v := do
    if v &&& ~~~mask != 0 || (typed && !mtrrType (v &&& 0xFF)) then gp 0
    wrStore n v
    flushTlbAll

/-- Physical-address bits 47:12 (MAXPHYADDR = 48). -/
def physMask : UInt64 := 0xFFFFFFFFF000

/-- Machine-check bank register `n` (0x400 + 4·bank + k; AMD APM vol. 2, 9.3.2): CTL, ADDR, MISC
are stored; MCi_STATUS accepts only zero unless HWCR[McStatusWrEn] (bit 18) is set, as on AMD
processors (the bit Linux's mce-inject sets; PPR UNCONFIRMED). -/
def mcBank (n : UInt32) : MsrImpl where
  rd := rdStore n
  wr v := do
    if (n - 0x400) &&& 3 == 1 && v != 0 && (← rdStore hwcrMsr 0x01000010) &&& 0x40000 == 0 then gp 0
    wrStore n v

/-- Canonical 48-bit linear address (bits 63:47 equal), for LSTAR/CSTAR (AMD APM vol. 2, 6.1.1:
"If the RIP written to either of the MSRs is not in canonical form, a #GP fault is generated"). -/
@[inline] def canonical (v : UInt64) : Bool :=
  let hi := v >>> 47
  hi == 0 || hi == 0x1FFFF

/-- The MSRs of this module. Each is present only with its feature. Values marked UNCONFIRMED are
plausible Zen 2 values that could not be checked against the family 17h PPR.

* 0x10 TSC: `icount + tscOff`, writes set all 64 bits.
* 0x48 SPEC_CTRL: IBRS (0), STIBP (1), SSBD (2) read/write, other bits #GP (APM vol. 2, 3.2.9).
* 0x49 PRED_CMD: write-only; bit 0 IBPB (no effect: the model has no predictors), other bits and
  RDMSR #GP.
* 0xE7 MPERF, 0xE8 APERF (CPUID 6:ECX[EffFreq]): count instructions (constant frequency).
* 0xFE MTRRcap: read-only 0x508 (8 variable ranges, fixed ranges, WC; APM table A-3 reset value).
* 0x174..0x176 SYSENTER_CS/ESP/EIP: bits 15:0 / 31:0 kept, upper bits ignored (UNCONFIRMED).
* 0x179 MCG_CAP read-only, 0x17A MCG_STATUS (bits 2:0), 0x17B MCG_CTL, 0x400.. MCi banks.
* 0x200..0x20F variable MTRRs, 0x250/0x258/0x259/0x268..0x26F fixed MTRRs, 0x2FF MTRRdefType,
  0x277 PAT.
* C000_0081..84 STAR, LSTAR, CSTAR (canonical, else #GP), SFMASK (bits 63:32 RAZ).
* C001_0010 SYSCFG (reset 0x20601, bits 63:27 MBZ), C001_0015 HWCR (reset 0x01000010, bit 24
  TscFreqSel read-only; UNCONFIRMED), C001_0016..19 IORRs, C001_001A TOP_MEM (reset 0x4000000),
  C001_001D TOP_MEM2, C001_001F NB_CFG, C001_0074 CPU watchdog timer (bits 6:0), C001_0140/0141
  OSVW_ID_Length/OSVW_Status (0: no OS-visible errata), C001_1004/1005 CPUID override MSRs (read
  the reported CPUID feature words; writes are stored but do not change CPUID: an approximation),
  C001_1020 LS_CFG, C001_1029 DE_CFG (stored; UNCONFIRMED reserved bits).
* Not present: VIRT_SPEC_CTRL (C001_011F; only for guests, CPUID 8000_0008:EBX[25] = 0 on the 7742),
  TSC_AUX (owned by the RDTSCP work), PATCH_LEVEL 0x8B (core, `Exec.msrInfo`). -/
def msr? (n : UInt32) : Option MsrImpl :=
  if n == 0x10 then
    if !implemented .tsc then none else
    some { rd := tsc
           wr := fun v m => .ok () { m with cpu := { m.cpu with sysx := { m.cpu.sysx with tscOff := v - m.icount } } } }
  else if n == 0x48 then
    if implemented .ibrs then some (checked n 0x7) else none
  else if n == 0x49 then
    if !implemented .ibpb then none else
    some { rd := gp 0, wr := fun v => if v &&& ~~~1 != 0 then gp 0 else pure () }
  else if n == 0xE7 || n == 0xE8 then
    if implemented .effFreq then some (counter n) else none
  else if n == 0xFE then
    if implemented .mtrr then some (readOnly 0x508) else none
  else if n == 0x174 || n == 0x175 || n == 0x176 then
    if !implemented .sep then none else
    some {
      rd := do
        let s := (← cpu).sysx
        return (if n == 0x174 then s.sysenterCs else if n == 0x175 then s.sysenterEsp else s.sysenterEip).toUInt64
      wr := fun v => modCpu fun c =>
        let s := c.sysx
        { c with sysx := if n == 0x174 then { s with sysenterCs := v.toUInt32 &&& 0xFFFF }
                         else if n == 0x175 then { s with sysenterEsp := v.toUInt32 }
                         else { s with sysenterEip := v.toUInt32 } } }
  else if n == 0x179 then
    if implemented .mca then some (readOnly (0x100 ||| mcBanks.toUInt64)) else none
  else if n == 0x17A then
    if implemented .mca then some (masked n 7) else none
  else if n == 0x17B then
    if implemented .mca then some (masked n 0xFFFFFFFFFFFFFFFF) else none
  else if 0x400 ≤ n && n < 0x400 + 4 * mcBanks then
    if implemented .mca then some (mcBank n) else none
  else if 0x200 ≤ n && n ≤ 0x20F then
    if !implemented .mtrr then none
    else if n &&& 1 == 0 then some (mtrr n (physMask ||| 0xFF) true)   -- PhysBase: 47:12, type
    else some (mtrr n (physMask ||| 0x800) false)                         -- PhysMask: 47:12, V
  else if n == 0x250 || n == 0x258 || n == 0x259 || (0x268 ≤ n && n ≤ 0x26F) then
    if implemented .mtrr then some (fixedMtrr n) else none
  else if n == 0x2FF then
    if implemented .mtrr then some (mtrr n 0xCFF true) else none          -- E, FE, type
  else if n == 0x277 then
    if !implemented .pat then none else
    some { rd := do return (← cpu).sysx.pat
           wr := fun v => do
             if !patOk v then gp 0
             modCpu fun c => { c with sysx := { c.sysx with pat := v } } }
  else if 0xC0000081 ≤ n && n ≤ 0xC0000084 then
    if !implemented .syscall then none else
    some {
      rd := do
        let s := (← cpu).sysx
        return if n == 0xC0000081 then s.star else if n == 0xC0000082 then s.lstar
               else if n == 0xC0000083 then s.cstar else s.sfmask.toUInt64
      wr := fun v => do
        if (n == 0xC0000082 || n == 0xC0000083) && !canonical v then gp 0
        modCpu fun c =>
          let s := c.sysx
          { c with sysx := if n == 0xC0000081 then { s with star := v }
                           else if n == 0xC0000082 then { s with lstar := v }
                           else if n == 0xC0000083 then { s with cstar := v }
                           else { s with sfmask := v.toUInt32 } } }
  else if n == syscfgMsr then some (checked n 0x7FFFFFF 0x20601)
  else if n == hwcrMsr then
    some { rd := rdStore n 0x01000010
           wr := fun v => wrStore n ((v &&& ~~~0x01000000) ||| 0x01000000) }
  else if n == 0xC0010016 || n == 0xC0010018 then some (checked n (physMask ||| 0x18))  -- IORRBase
  else if n == 0xC0010017 || n == 0xC0010019 then some (checked n (physMask ||| 0x800)) -- IORRMask
  else if n == 0xC001001A then some (checked n 0xFFFFFF800000 0x4000000)                -- TOP_MEM
  else if n == 0xC001001D then some (checked n 0xFFFFFF800000)                          -- TOP_MEM2
  else if n == 0xC001001F || n == 0xC0011020 || n == 0xC0011029 then
    some (masked n 0xFFFFFFFFFFFFFFFF)
  else if n == 0xC0010074 then
    if implemented .wdt then some (masked n 0x7F) else none
  else if n == 0xC0010140 || n == 0xC0010141 then
    if implemented .osvw then some (masked n 0xFFFFFFFFFFFFFFFF) else none
  else if n == 0xC0011004 || n == 0xC0011005 then
    some { rd := do
             let c ← cpu
             let (_, _, ecx, edx) := cpuid c (if n == 0xC0011004 then 1 else 0x80000001) 0
             rdStore n ((ecx.toUInt64 <<< 32) ||| edx.toUInt64)
           wr := fun v => wrStore n v }
  else none

end Sys
end X86
