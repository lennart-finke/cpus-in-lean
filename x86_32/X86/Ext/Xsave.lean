import X86.Exec
/-!
# XSAVE

Owner: the XSAVE workstream. XCR0 (`Cpu.xcr0`, reset 1), IA32_XSS (`Cpu.xss`), XGETBV/XSETBV,
XSAVE/XRSTOR/XSAVEOPT/XSAVEC/XSAVES/XRSTORS, CPUID leaf 0xD (`Cpuid.leafD`, with the component
table `Cpuid.xcomp`, `xcr0Supported`, `xssSupported`, `xsaveSize`, `compactSize` in
`X86/Cpuid.lean`), CR4.OSXSAVE (accepted by MOV CR4, `Cpuid.cr4Writable`; mirrored in
CPUID 1:ECX[27], `Cpuid.osxsave`).

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for
  - 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns D0 (XGETBV) and D1
    (XSETBV);
  - 0F AE forms other than FXSAVE/FXRSTOR/LDMXCSR/STMXCSR and the fences (fallback #UD): this
    module owns memory /4 (XSAVE), /5 (XRSTOR), /6 (XSAVEOPT) without prefix;
  - 0F C7 forms other than /1 (fallback #UD): this module owns memory /3 (XRSTORS), /4 (XSAVEC),
    /5 (XSAVES) without prefix.
* `msr?`: IA32_XSS (0xDA0).

Sources: Intel SDM vol. 1, chapter 13 and vol. 2 (XSAVE, XSAVEOPT, XSAVEC, XSAVES, XRSTOR,
XRSTORS, XGETBV, XSETBV; their pseudocode is followed step by step); AMD APM vol. 2, 11.5 and vol. 4
(the same instructions). Where they differ, AMD wins (error pointers, below).

## State components

The model has x87 (0), SSE (1: XMM0..7; MXCSR is handled separately, as the SDM does) and AVX
(2: YMM0..7 bits 255:128, `SseState.ymmh`), in 32-bit mode only (XMM8..15/YMM_Hi8..15 do not exist;
AMD APM vol. 2, 11.5.10). The legacy region uses the 32-bit FXSAVE layout, written and read by the
FXSAVE/FXRSTOR pieces of `X86/Simd.lean` (`fxsaveEnv`, `fxsaveRegs`, `fxsaveXmm`, `fxrstorEnv`,
`fxrstorRegs`, `Cpu.loadFxX87`); MXCSR_MASK is `mxcsrMask`. Bytes the instructions do not write are
left alone: 464..511 (SDM 13.4.1), the reserved bytes of the legacy region (5, 14..15, 22..23 are
written as zero together with their fields, as FXSAVE does; bytes 10..15 of each x87 register slot are
written as zero, as the EPYC 7742 does (native `xsave_padding`); 288..463 are not written), the header
beyond XSTATE_BV (XSAVE, XSAVEOPT) or XCOMP_BV (XSAVEC, XSAVES), and the areas of components that are
not saved.

**Error pointers**: the 7742 reports CPUID Fn8000_0008_EBX[2] (XSaveErPtr; "FXSAVE, XSAVE, FXSAVEOPT,
XSAVEC, XSAVES always save error pointers and FXRSTOR, XRSTOR, XRSTORS always restore error pointers",
AMD APM vol. 3, appendix E), but its FXSAVE and XSAVE write FOP, FIP, FCS, FDP and FDS only when
FSW.ES = 1 and zeros otherwise, while the restoring instructions always load them (native
`fpu_pointers`, 16 images; open questions F5, X6). The model follows the hardware for the whole family
(XSAVEC/XSAVES not observed). (The model wrote them always before the extended run.)

## Tracking: init and modified optimizations (SDM vol. 1, 13.6, 13.8.3)

Hardware has latitude: XINUSE[i] = 0 only if component i is in its initial configuration, but may
be 1 in it; XMODIFIED[i] = 0 only if component i has not been modified since the last
XRSTOR/XRSTORS, but may be 1. The model defines them exactly:

* **XINUSE** (`xinuse`) = `XsaveState.inuse` OR the components not in their initial configuration.
  `inuse[i]` is set by XRSTOR/XRSTORS loading component i and cleared by XRSTOR/XRSTORS initializing
  it (as their pseudocode sets XINUSE[i] := 1 / 0), and is 0 after reset. Initial configurations
  (SDM 13.6; AMD APM vol. 2, table 11-3): x87 — FCW = 037FH, FSW = 0, all registers empty, FOP,
  FIP, FCS, FDP, FDS = 0, ST0..ST7 = 0 (FOP is included, which only makes XINUSE[0] = 1 more often);
  SSE — XMM0..7 = 0 (not MXCSR); AVX — YMM0..7[255:128] = 0. So a component that software has
  returned to its initial values (e.g. FNINIT and zeroed registers, PXOR) reads as not in use, unless
  the last XRSTOR loaded it.
* **XMODIFIED** / **XRSTOR_INFO** (`unmodified`): XRSTOR/XRSTORS record XRSTOR_INFO (CPL, the linear
  address of the area, the XCOMP_BV value: 0 for the standard form) with their RFBM and the
  instruction count. XMODIFIED[i] = 0 exactly for the components in that RFBM and only for the
  instruction directly following the XRSTOR/XRSTORS (no instruction in between can have modified
  them; interrupt and exception delivery do not touch this state); afterwards every bit is 1. So
  XSAVEOPT/XSAVES skip a component only when they directly follow an XRSTOR/XRSTORS with the same
  CPL, address and XCOMP_BV (XSAVEOPT: 0; XSAVES: its own compaction mask). There is no VMX; SVM
  guest mode (the AMD "virtualization mode" of XRSTOR_INFO) does not exist yet.

QEMU (TCG) does not track XINUSE (all ones), so XSAVE/XSAVEOPT set XSTATE_BV[i] = 1 for every
component in RFBM, XSAVEOPT saves like XSAVE and XGETBV(1) returns XCR0; the system tests print
XSTATE_BV and XGETBV(1) only where every implementation must agree (components in use) and check
the model's choices in their model-only part.

## Order of checks

LOCK: #UD (`Step.lockOk`). Prefixes 66/F2/F3 ("NP" encodings): the forms are not this module's
(0F AE, 0F C7: another hook or #UD) or #UD (XGETBV/XSETBV, as QEMU). Then CR4.OSXSAVE = 0: #UD; CR0.TS:
#NM (not XGETBV/XSETBV; CR0.EM is ignored); XSAVES/XRSTORS, XSETBV: CPL > 0 #GP(0) (#UD and #NM come
first: SDM vol. 3, table 6-2 puts decode faults before execution faults); segment limit (#GP(0) or
#SS(0)) over the bytes the instruction accesses; 64-byte alignment of the linear address: #GP(0)
(alignment checking is never #AC here: the model has no #AC); every page of the accessed range is
translated before the first access (#PF at the first byte of the first inaccessible page, the
instruction has no effect); XRSTOR/XRSTORS: header checks (#GP(0)), then the components are read,
then the MXCSR reserved-bit check (#GP(0)); only then is any state changed.

**Where AMD's text differs from Intel's** (unverified on hardware; the model follows Intel where AMD
is ambiguous): APM vol. 4 XSAVE says MXCSR is saved "if either of RFBM bits 0 or 1" is set, while
APM vol. 2, 11.5.9 and the XRSTOR page tie MXCSR to XMM/YMM_HI (Intel: RFBM[1] or RFBM[2]) — the
model uses RFBM[1] or RFBM[2]; APM vol. 4 XRSTOR lists "bytes 63:16 of header are non-zero" as #GP
without naming the form — the model checks bytes 8..23 for the standard form (SDM 13.8.1, as QEMU)
and 16..63 for the compacted form; APM vol. 4 XRSTORS lists "(XSTATE_BV[i] & ~IA32_XSS[i]) = 1"
as #GP, which would forbid restoring user components — the model uses the SDM's XRSTORS checks.
The native campaign (`validation/test/native_xsave.py`) has cases for the first point.

The accessed range is the legacy region and header (576 bytes) plus the extended components the
instruction saves (XSAVE: RFBM; XSAVEOPT: RFBM ∧ XINUSE) or restores (RFBM ∧ XSTATE_BV), in the
standard or compacted layout. Whether hardware faults on pages of components it does not touch is
not documented; QEMU probes the same range.
-/
namespace X86
namespace Xsave

/-! ## Tracking -/

/-- Component 0 (x87) is in its initial configuration. -/
def x87Init (c : Cpu) : Bool :=
  c.fcw == 0x37F && c.fsw == 0 && c.fempty == 0xFF && c.fop == 0 && c.fip == 0 && c.fcs == 0 &&
  c.fdp == 0 && c.fds == 0 && c.fpr.all (· == {})

/-- Component 1 (SSE) is in its initial configuration: XMM0..7 = 0 (MXCSR is not part of it). -/
def sseInit (c : Cpu) : Bool := c.xmm.all (· == {})

/-- Component 2 (AVX) is in its initial configuration: YMM0..7[255:128] = 0. -/
def ymmInit (c : Cpu) : Bool := c.ymmh.all (· == {})

/-- XINUSE (see the module documentation). -/
def xinuse (c : Cpu) : UInt64 :=
  c.xsx.inuse ||| (if x87Init c then 0 else XCR0.X87) ||| (if sseInit c then 0 else XCR0.SSE) |||
    (if ymmInit c then 0 else XCR0.YMM)

/-- The components XSAVEOPT/XSAVES may leave unsaved because they have not been modified since the
last XRSTOR/XRSTORS (NOT XMODIFIED, restricted to a matching XRSTOR_INFO): nonzero only for the
instruction directly following that XRSTOR/XRSTORS, at `icount`. -/
def unmodified (c : Cpu) (icount : UInt64) (lin : UInt32) (comp : UInt64) : UInt64 :=
  let x := c.xsx
  if x.infoValid && x.atCount + 1 == icount && x.infoCpl == c.cpl && x.infoLaxa == lin &&
     x.infoComp == comp then x.rfbm else 0

/-! ## Memory access -/

@[inline] def edxEax (c : Cpu) : UInt64 := c.eax.toUInt64 ||| (c.edx.toUInt64 <<< 32)

@[inline] def bit (m : UInt64) (i : Nat) : Bool := (m >>> i.toUInt64) &&& 1 != 0

/-- Translate every page of `[lin, lin + n)` (n ≤ 4096) for reading or writing, in address order. -/
def probe (lin n : UInt32) (write : Bool) : M Unit := do
  let u ← isUser
  let _ ← translate lin write u
  let last := (lin + n - 1) &&& 0xFFFFF000
  if last != lin &&& 0xFFFFF000 then
    let _ ← translate last write u

/-- Linear address of the XSAVE area of the memory operand, `n` bytes of which are accessed:
64-byte alignment (#GP(0), before the segment-limit check, as the EPYC 7742 orders them: native
`enc_fuzz`, an XSAVEOPT through SS wrapping past 4 GiB), segment checks, page translation (see the module
documentation). `first`: an offset in the area that is translated before the others, as the EPYC 7742
checks its areas: the last byte for a save (FXSAVE, XSAVE, XSAVEOPT; native `fxsave_align`: an area
crossing into an unmapped page faults at its last byte, and `enc_fuzz`: an FXSAVE area wholly inside an
unmapped page too) and the first header byte (offset 512) for XRSTOR (native `fxsave_align`, 8 cases).
Areas whose both pages fault were not observed: the model reports that byte's fault. -/
def area (i : Inst) (n : UInt32) (write : Bool) (first : Option UInt32 := none) : M UInt32 := do
  let off ← fpEa i
  if (((← cpu).getSeg i.seg).base + off) &&& 63 != 0 then gp 0
  let lin ← segAddr i.seg off n write
  if let some f := first then
    let _ ← translate (lin + f) write (← isUser)
  probe lin n write
  return lin

def rd64 (lin : UInt32) : M UInt64 := do return (← rdLin lin 8).lo
def wr64 (lin : UInt32) (v : UInt64) : M Unit := wrLin lin 8 { lo := v }

/-- The x87 component (legacy region bytes 0..23 without MXCSR, ST0..ST7): the error pointers only with
FSW.ES = 1 (`fxsaveEnv`), the register slots' padding as zeros (EPYC 7742, native `xsave_padding`). -/
def saveX87 (c : Cpu) (lin : UInt32) : M Unit := do
  fxsaveEnv c lin
  fxsaveRegs c lin (pad := true)

/-- MXCSR and MXCSR_MASK (bytes 24..31). -/
def saveMxcsr (c : Cpu) (lin : UInt32) : M Unit := do
  let u ← isUser
  linWr (lin + 24) 4 c.mxcsr u
  linWr (lin + 28) 4 mxcsrMask u

/-- The AVX component (YMM0..7[255:128], 16 bytes each) at `lin`. -/
def saveYmm (c : Cpu) (lin : UInt32) : M Unit := do
  for k in [0:8] do wrLin (lin + 16 * k.toUInt32) 16 c.ymmh[k]!

def readYmm (lin : UInt32) : M (Array V128) := do
  let mut r : Array V128 := #[]
  for k in [0:8] do r := r.push (← rdLin (lin + 16 * k.toUInt32) 16)
  return r

def readXmm (lin : UInt32) : M (Array V128) := do
  let mut r : Array V128 := #[]
  for k in [0:8] do r := r.push (← rdLin (lin + 160 + 16 * k.toUInt32) 16)
  return r

/-- Offset of component i ≥ 2 in the standard (`comp = 0`) or compacted layout. -/
def compOffset (comp : UInt64) (i : Nat) : UInt32 :=
  if comp >>> 63 == 0 then ((Cpuid.xcomp i).map (·.2.1)).getD 0
  else Cpuid.compactOffset (comp &&& 0x7FFFFFFFFFFFFFFF) i

/-! ## Initial configurations -/

/-- x87 state initialized by XRSTOR (AMD APM vol. 2, table 11-3; SDM 13.6). -/
def Cpu.initX87 (c : Cpu) : Cpu :=
  { c with fcw := 0x37F, fsw := 0, fempty := 0xFF, fop := 0, fip := 0, fcs := 0, fdp := 0,
           fds := 0, fpr := Array.replicate 8 {} }

/-! ## XGETBV, XSETBV -/

/-- XGETBV: EDX:EAX := XCR[ECX]. ECX = 0: XCR0; ECX = 1 (CPUID 0xD.1:EAX[2]): XCR0 AND XINUSE, with
bit 1 also set if XCR0[1] = 1 and MXCSR ≠ 1F80H (SDM 13.6). Any CPL; #UD with CR4.OSXSAVE = 0,
#GP(0) for other ECX values. -/
def xgetbv : M Unit := do
  let c ← cpu
  if c.cr4 &&& CR4.OSXSAVE == 0 then ud
  let v ← if c.ecx == 0 then pure c.xcr0
    else if c.ecx == 1 && implemented .xgetbv1 then
      pure (c.xcr0 &&& (xinuse c ||| (if c.mxcsr != 0x1F80 then XCR0.SSE else 0)))
    else gp 0
  setReg 0 v.toUInt32
  setReg 2 (v >>> 32).toUInt32

/-- The XCR0 values XSETBV accepts (SDM vol. 2 XSETBV, AMD APM vol. 2, 11.5.2): supported bits
only, bit 0 set, not XCR0[2:1] = 10b. -/
def xcr0Valid (v : UInt64) : Bool :=
  v &&& ~~~Cpuid.xcr0Supported == 0 && v &&& XCR0.X87 != 0 && v &&& (XCR0.SSE ||| XCR0.YMM) != XCR0.YMM

/-- XSETBV: XCR[ECX] := EDX:EAX. #UD with CR4.OSXSAVE = 0; #GP(0) at CPL > 0 (also in virtual-8086
mode), for ECX ≠ 0 and for an invalid XCR0 value (`xcr0Valid`). Not serializing on AMD (APM vol. 2,
7.6.4 does not list it). The state of a component disabled in XCR0 is kept. -/
def xsetbv : M Unit := do
  Svm.icpt4 13   -- SVM XSETBV: the intercept before the exceptions (AMD APM vol. 2, table 15-7)
  let c ← cpu
  if c.cr4 &&& CR4.OSXSAVE == 0 then ud
  if c.cpl != 0 then gp 0
  let v := edxEax c
  if c.ecx != 0 || !xcr0Valid v then gp 0
  modCpu fun c => { c with xcr0 := v }

/-! ## XSAVE, XSAVEOPT, XSAVEC, XSAVES -/

/-- Checks of every XSAVE-family instruction before its memory operand: CR4.OSXSAVE (#UD), CR0.TS
(#NM), and for XSAVES/XRSTORS (`priv`) CPL 0 (#GP(0)). -/
def pre (priv : Bool) : M Unit := do
  let c ← cpu
  if c.cr4 &&& CR4.OSXSAVE == 0 then ud
  if c.cr0 &&& CR0.TS != 0 then exc Vec.NM
  if priv && c.cpl != 0 then gp 0

/-- XSAVE (`opt = false`) and XSAVEOPT (`opt = true`): the standard format (SDM vol. 2 XSAVE,
XSAVEOPT pseudocode). RFBM = XCR0 AND EDX:EAX; XSAVE saves the components in RFBM, XSAVEOPT those
in RFBM AND XINUSE, minus the unmodified ones (modified optimization); MXCSR and MXCSR_MASK are
saved if RFBM[1] or RFBM[2]; XSTATE_BV := (XSTATE_BV AND NOT RFBM) OR (XINUSE AND RFBM). -/
def xsave (i : Inst) (opt : Bool) : M Unit := do
  pre false
  let c ← cpu
  let rfbm := c.xcr0 &&& edxEax c
  let inuse := xinuse c
  let save := if opt then rfbm &&& inuse else rfbm
  let lin ← area i (Cpuid.xsaveSize save) true (first := some (Cpuid.xsaveSize save - 1))
  let icount := (← getM).icount
  let save := if opt then save &&& ~~~unmodified c icount lin 0 else save
  let oldBv ← rd64 (lin + 512)
  if bit save 0 then saveX87 c lin
  if rfbm &&& (XCR0.SSE ||| XCR0.YMM) != 0 then saveMxcsr c lin
  if bit save 1 then fxsaveXmm c lin
  if bit save 2 then saveYmm c (lin + compOffset 0 2)
  wr64 (lin + 512) ((oldBv &&& ~~~rfbm) ||| (inuse &&& rfbm))

/-- XSAVEC (`sup = false`) and XSAVES (`sup = true`): the compacted format (SDM vol. 2 XSAVEC,
XSAVES pseudocode). RFBM = XCR0 (XSAVES: OR IA32_XSS) AND EDX:EAX; saved: RFBM AND XINUSE (XSAVES:
minus the unmodified components), plus SSE if RFBM[1] and MXCSR ≠ 1F80H; component i ≥ 2 at its
compacted offset for RFBM; XSTATE_BV := RFBM AND XINUSE (plus bit 1 if MXCSR ≠ 1F80H and RFBM[1]),
XCOMP_BV := RFBM OR 2^63. -/
def xsavec (i : Inst) (sup : Bool) : M Unit := do
  pre sup
  let c ← cpu
  let rfbm := (if sup then c.xcr0 ||| c.xss else c.xcr0) &&& edxEax c
  let comp := rfbm ||| 0x8000000000000000
  let inuse := xinuse c
  let lin ← area i (Cpuid.compactSize rfbm) true (first := some (Cpuid.compactSize rfbm - 1))
  let mx := if c.mxcsr != 0x1F80 && bit rfbm 1 then XCR0.SSE else 0
  let icount := (← getM).icount
  let save := rfbm &&& inuse
  let save := (if sup then save &&& ~~~unmodified c icount lin comp else save) ||| mx
  if bit save 0 then saveX87 c lin
  if bit save 1 then
    saveMxcsr c lin
    fxsaveXmm c lin
  if bit save 2 then saveYmm c (lin + compOffset comp 2)
  wr64 (lin + 512) ((rfbm &&& inuse) ||| mx)
  wr64 (lin + 520) comp

/-! ## XRSTOR, XRSTORS -/

/-- XRSTOR (`sup = false`) and XRSTORS (`sup = true`), SDM vol. 2 pseudocode. RFBM = XCR0 (XRSTORS:
OR IA32_XSS) AND EDX:EAX. XCOMP_BV[63] = 0 selects the standard form (XRSTOR only; #GP(0) if
XSTATE_BV sets a bit outside XCR0 or header bytes 8..23 are not zero), 1 the compacted form (#GP(0)
without XSAVEC support, if XCOMP_BV[62:0] sets a bit outside XCR0 (XRSTORS: XCR0 OR IA32_XSS), if
XSTATE_BV sets a bit outside XCOMP_BV, or if header bytes 16..63 are not zero). Component i in RFBM
is loaded if XSTATE_BV[i] = 1 (compacted: and XCOMP_BV[i] = 1), initialized otherwise. MXCSR:
standard form, loaded whenever RFBM[1] or RFBM[2] (never initialized); compacted form, loaded with
the SSE component, set to 1F80H when SSE is initialized; #GP(0) if a reserved bit would be set
(`mxcsrMask`). XINUSE, XMODIFIED and XRSTOR_INFO as in the module documentation. -/
def xrstor (i : Inst) (sup : Bool) : M Unit := do
  pre sup
  let c ← cpu
  let enabled := if sup then c.xcr0 ||| c.xss else c.xcr0
  let rfbm := enabled &&& edxEax c
  let lin ← area i 0x240 false (first := some 512)
  let bv ← rd64 (lin + 512)
  let comp ← rd64 (lin + 520)
  let compacted := comp >>> 63 != 0
  if !compacted then
    if sup then gp 0
    -- header bytes 16..23 must be zero; read unconditionally (the area was probed by `area`, so the
    -- read cannot fault, and XRSTOR reads the whole header anyway)
    let rsv ← rd64 (lin + 528)
    if comp != 0 || rsv != 0 || bv &&& ~~~c.xcr0 != 0 then gp 0
  else
    if !implemented .xsavec then gp 0
    for k in [2:8] do
      if (← rd64 (lin + 512 + 8 * k.toUInt32)) != 0 then gp 0
    if comp &&& 0x7FFFFFFFFFFFFFFF &&& ~~~enabled != 0 || bv &&& ~~~comp != 0 then gp 0
  let format := if compacted then comp &&& 0x7FFFFFFFFFFFFFFF else enabled
  let restore := rfbm &&& bv &&& format
  let init := rfbm &&& ~~~restore
  -- the extended components that are read
  let ext := restore &&& ~~~(XCR0.X87 ||| XCR0.SSE)
  if ext != 0 then
    let _ ← area i (if compacted then Cpuid.compactSize format else Cpuid.xsaveSize ext) false
  -- read everything before changing any state
  let x87 ← if bit restore 0 then
      some <$> ((·, ·) <$> fxrstorEnv lin <*> fxrstorRegs lin) else pure none
  let xmm ← if bit restore 1 then some <$> readXmm lin else pure none
  let ymm ← if bit restore 2 then some <$> readYmm (lin + compOffset (if compacted then comp else 0) 2)
    else pure none
  let loadMx := if compacted then bit restore 1 else rfbm &&& (XCR0.SSE ||| XCR0.YMM) != 0
  let mxcsr ← if loadMx then linRd (lin + 24) 4 (← isUser)
    else pure (if compacted && bit init 1 then 0x1F80 else c.mxcsr)
  if mxcsr &&& ~~~mxcsrMask != 0 then gp 0
  let icount := (← getM).icount
  modCpu fun c =>
    let c := match x87 with
      | some (env, regs) => c.loadFxX87 env regs
      | none => if bit init 0 then Cpu.initX87 c else c
    let xmm := match xmm with
      | some v => v
      | none => if bit init 1 then Array.replicate 8 {} else c.xmm
    let ymmh := match ymm with
      | some v => v
      | none => if bit init 2 then Array.replicate 8 {} else c.ymmh
    { c with sse := { c.sse with mxcsr, xmm, ymmh },
             xsx := { inuse := (c.xsx.inuse &&& ~~~rfbm) ||| restore, infoValid := true,
                      infoCpl := c.cpl, infoLaxa := lin, infoComp := comp, rfbm, atCount := icount } }

/-! ## Hooks -/

def op0F? (i : Inst) : Option (M Unit) :=
  if i.vex || !implemented .xsave then none else
  match i.op with
  | 0x101 =>
    if i.isMem || i.reg != 2 || i.rm > 1 then none
    -- NP 0F 01 D0 / D1: a 66, F2 or F3 prefix is #UD (SDM vol. 2; QEMU does the same)
    else if i.p66 || i.rep != 0 then some ud
    else some (if i.rm == 0 then xgetbv else xsetbv)
  | 0x1AE =>
    if !i.isMem || i.pp != 0 then none
    else match i.reg with
      | 4 => some (xsave i false)
      | 5 => some (xrstor i false)
      | 6 => if implemented .xsaveopt then some (xsave i true) else none
      | _ => none
  | 0x1C7 =>
    if !i.isMem || i.pp != 0 then none
    else match i.reg with
      | 3 => if implemented .xsaves then some (xrstor i true) else none
      | 4 => if implemented .xsavec then some (xsavec i false) else none
      | 5 => if implemented .xsaves then some (xsavec i true) else none
      | _ => none
  | _ => none

/-- IA32_XSS (MSR 0DA0h, AMD APM vol. 2, 3.2.8), with XSAVES: WRMSR of a bit outside
`Cpuid.xssSupported` (all bits on the 7742) raises #GP(0). -/
def xssMsr : MsrImpl where
  rd := do return (← cpu).xss
  wr v := do
    if v &&& ~~~Cpuid.xssSupported != 0 then gp 0
    modCpu fun c => { c with xss := v }

def msr? (n : UInt32) : Option MsrImpl :=
  if n == 0xDA0 && implemented .xsaves then some xssMsr else none

end Xsave
end X86
