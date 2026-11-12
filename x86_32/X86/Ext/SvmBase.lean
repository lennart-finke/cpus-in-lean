import X86.Ext.LongModeBase
/-!
# SVM: intercept checks used by the core

Owner: the SVM workstream (with `X86/Ext/Svm.lean`, which holds VMRUN, #VMEXIT, the SVM
instructions and MSRs). This file comes before `X86/Sys.lean` in the import order: the core
instruction semantics (`Exec.lean`, `Sys.lean`, the extension modules) call these checks at the
point where AMD APM vol. 2, table 15-7 places each instruction intercept relative to the
instruction's exceptions (each call site cites its rule). An intercept raises `Fault.vmexit`: like a
fault, the guest state is the one before the instruction (`Step.execInstr` restores it), and
`Step.handleFault` performs the #VMEXIT (`Svm.vmexit`). Outside guest mode (and in SMM, where the
handler of an unintercepted SMI "is not subject to any intercepts", 15.22.3) every check is a single
test of `SvmState.guest`.

nRIP (15.7.1): every instruction intercept, IOIO and MSR intercept, and the #BP/#OF/#BR exceptions of
INT3/INTO/BOUND save the next sequential instruction pointer, which is the EIP the instruction has
already advanced to when its semantics run (`Step.execInstr`). Decode assists (15.8): MOV CRx/DRx
(EXITINFO1 = GPR number, bit 63 for MOV CRx), INTn (the vector), INVLPG (the linear address).
-/
namespace X86

namespace Vec
/-- Security exception (AMD APM vol. 2, 15.28): INIT redirected by VM_CR.R_INIT. -/
def SX : UInt8 := 30
end Vec

/-- Intercepts are active: guest mode, outside SMM. -/
@[inline] def Cpu.svmOn (c : Cpu) : Bool := c.svmx.guest && !c.smm

/-- Physical maskable interrupts are unmasked: EFLAGS.IF, or in a guest with V_INTR_MASKING the
host's EFLAGS.IF at VMRUN (AMD APM vol. 2, 15.21.1). -/
@[inline] def Cpu.physIntrOk (c : Cpu) : Bool :=
  if c.svmOn && c.svmx.vIntrMasking then c.svmx.hostIf else c.eflags &&& Flag.IF != 0

/-- A virtual interrupt is taken (15.21.4): V_IRQ pending with V_INTR_PRIO above V_TPR (or
V_IGN_TPR), guest EFLAGS.IF = 1, GIF and the virtual GIF (if enabled, 15.33.2) set, not in an
interrupt shadow. -/
@[inline] def Cpu.vintrReady (c : Cpu) : Bool :=
  let s := c.svmx
  c.svmOn && s.vIrq && s.gif && (!s.vGifEn || s.vGif) && c.eflags &&& Flag.IF != 0 && !c.shadow &&
    (s.vIgnTpr || s.vPrio > s.vTpr)

/-- The SVM state after INIT: guest mode and its controls end (EFER is cleared by INIT, and the
processor restarts at the reset vector), GIF = 1; VM_CR.SVMDIS is cleared unless VM_CR.LOCK is set
(15.30.1); the MSRs (VM_HSAVE_PA, SVM_KEY, TSC_RATIO, the other VM_CR bits) keep their values. -/
def SvmState.afterInit (s : SvmState) : SvmState :=
  { vmCr := if s.vmCr &&& 8 == 0 then s.vmCr &&& ~~~0x10 else s.vmCr,
    hsavePa := s.hsavePa, svmKey := s.svmKey, tscRatio := s.tscRatio, ignne := s.ignne }

namespace Svm

/-- Bit `b` of a 32-bit intercept vector. -/
@[inline] def bit (v : UInt32) (b : UInt32) : Bool := (v >>> b) &&& 1 != 0

/-- The #VMEXIT of an instruction intercept: EXITCODE `code`, EXITINFO1/2, nRIP = the next
instruction's EIP. -/
@[inline] def exitInstr (code : UInt64) (info1 : UInt64 := 0) (info2 : UInt64 := 0) : M α := fun m =>
  .error (.vmexit { code, info1, info2, nrip := m.cpu.eip.toUInt64 }) m

/-- Instruction intercept `b` of vector 3 (VMCB 00Ch, exit code 60h + b). -/
@[inline] def icpt3 (b : UInt32) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.i3 b then exitInstr (0x60 + b.toUInt64) 0 0 m else .ok () m

/-- Instruction intercept `b` of vector 4 (VMCB 010h, exit code 80h + b). -/
@[inline] def icpt4 (b : UInt32) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.i4 b then exitInstr (0x80 + b.toUInt64) 0 0 m else .ok () m

/-- Intercept `b` of vector 5 (VMCB 014h): bit 3 MCOMMIT (exit code A3h). -/
@[inline] def icpt5 (b : UInt32) (code : UInt64) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.i5 b then exitInstr code 0 0 m else .ok () m

/-! ## Control and debug registers (15.8.1, table 15-7) -/

/-- EXITINFO1 of a MOV CRx (decode assist): bit 63 and the GPR number. -/
@[inline] def movCrInfo (gpr : UInt8) : UInt64 := 0x8000000000000000 ||| gpr.toUInt64

/-- Read of CR`n` (exit code n): `info` = `movCrInfo gpr` for MOV from CR, 0 for SMSW. -/
@[inline] def crRead (n : UInt32) (info : UInt64) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.icr n then exitInstr n.toUInt64 info 0 m else .ok () m

/-- Write of CR`n` (exit code 10h + n): `info` = `movCrInfo gpr` for MOV to CR, 0 for LMSW/CLTS. -/
@[inline] def crWrite (n : UInt32) (info : UInt64) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.icr (16 + n) then exitInstr (0x10 + n.toUInt64) info 0 m else .ok () m

/-- A write of CR0 with `old` → `new`: the CR0 write intercept, then the selective CR0 write
intercept (exit code 65h) if a bit other than TS and MP changes, or always for LMSW (`lmsw`), which
treats it as non-selective (table 15-7). -/
@[inline] def cr0Write (old new : UInt32) (info : UInt64) (lmsw : Bool := false) : M Unit := fun m =>
  let c := m.cpu
  if !c.svmOn then .ok () m
  else if bit c.svmx.icr 16 then exitInstr 0x10 info 0 m
  else if bit c.svmx.i3 5 && (lmsw || (old ^^^ new) &&& ~~~(CR0.TS ||| CR0.MP) != 0) then exitInstr 0x65 info 0 m
  else .ok () m

/-- MOV from DR`n` (exit code 20h + n; EXITINFO1 = GPR number). -/
@[inline] def drRead (n : UInt8) (gpr : UInt8) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.idr n.toUInt32 then exitInstr (0x20 + n.toUInt64) gpr.toUInt64 0 m else .ok () m

/-- MOV to DR`n` (exit code 30h + n). -/
@[inline] def drWrite (n : UInt8) (gpr : UInt8) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.idr (16 + n.toUInt32) then exitInstr (0x30 + n.toUInt64) gpr.toUInt64 0 m else .ok () m

/-! ## I/O and MSRs (15.10, 15.11) -/

/-- The IOPM bits of an access of `sz` bytes at `port` (bit p of the 12 KiB map at IOPM_BASE_PA
for port p; ports above FFFFh of a wrapping access use the map's first bits of its third page). -/
def iopmHit (base : UInt64) (port : UInt32) (sz : Sz) (mem : ByteArray) : Bool :=
  (List.range sz.toNat).any fun k =>
    let p := port + k.toUInt32
    let a := base + (p >>> 3).toUInt64
    a >>> 32 == 0 && (rdBytes mem a.toUInt32 1 >>> (p &&& 7)) &&& 1 != 0

/-- IN/OUT/INS/OUTS: the IOIO intercept after the virtual-8086/IOPL/TSS-bitmap checks and before
every other exception (15.10.2). EXITINFO1 (figure 15-2): port (31:16), effective segment (12:10,
the default DS for OUTS, ES for INS), address size (A32 bit 8, A16 bit 7), operand size (6:4), REP
(3), STR (2), IN (0); EXITINFO2 = the next RIP. -/
def ioio (port : UInt32) (sz : Sz) (inp str rep : Bool) (seg : UInt8) (adsz : Sz) : M Unit := fun m =>
  let c := m.cpu
  if !(c.svmOn && bit c.svmx.i3 27) then .ok () m
  else if !iopmHit (c.svmx.iopm &&& ~~~0xFFF) port sz m.mem then .ok () m
  else
    let info : UInt64 := (port.toUInt64 <<< 16) ||| ((if str then seg.toUInt64 else 0) <<< 10) |||
      (if adsz == 4 then 0x100 else 0x80) |||
      (if sz == 4 then 0x40 else if sz == 2 then 0x20 else 0x10) |||
      (if rep then 8 else 0) ||| (if str then 4 else 0) ||| (if inp then 1 else 0)
    .error (.vmexit { code := 0x7B, info1 := info, info2 := c.eip.toUInt64, nrip := c.eip.toUInt64 }) m

/-- Byte offset and bit (read; write is the next bit) of MSR `n` in the MSRPM (table 15-8), or
`none` outside the covered ranges (always intercepted). -/
def msrpmPos (n : UInt32) : Option (UInt32 × UInt32) :=
  let pos := fun (off : UInt32) (k : UInt32) => some (off + (2 * k) / 8, (2 * k) % 8)
  if n ≤ 0x1FFF then pos 0 n
  else if 0xC0000000 ≤ n && n ≤ 0xC0001FFF then pos 0x800 (n - 0xC0000000)
  else if 0xC0010000 ≤ n && n ≤ 0xC0011FFF then pos 0x1000 (n - 0xC0010000)
  else none

/-- RDMSR/WRMSR: the MSR intercept after the exceptions common to all MSRs (CPL) and before the
MSR's own (15.11); EXITINFO1 = 0 for RDMSR, 1 for WRMSR. -/
def msr (n : UInt32) (write : Bool) : M Unit := fun m =>
  let c := m.cpu
  if !(c.svmOn && bit c.svmx.i3 28) then .ok () m else
  let hit := match msrpmPos n with
    | none => true
    | some (off, b) =>
      let a := (c.svmx.msrpm &&& ~~~0xFFF) + off.toUInt64
      a >>> 32 == 0 && (rdBytes m.mem a.toUInt32 1 >>> (b + (if write then 1 else 0))) &&& 1 != 0
  if hit then exitInstr 0x7C (if write then 1 else 0) 0 m else .ok () m

/-- A guest WRMSR (not intercepted) of an MSR that affects address translation (MTRRs 200h-2FFh and
2FFh, SYSCFG and the IORRs/TOP_MEM C001_0010h-C001_001Ah) flushes the TLB entries of all ASIDs
(15.16.1): the host's set-aside entries are dropped (the running ASID's by the MSR itself). -/
@[inline] def wrmsrGuest (n : UInt32) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && ((0x200 ≤ n && n ≤ 0x2FF) || (0xC0010010 ≤ n && n ≤ 0xC001001A)) then
    .ok () { m with cpu := { c with svmx := { c.svmx with hostTlb := {} } } }
  else .ok () m

/-! ## Other instruction intercepts -/

/-- INT n: the software-interrupt intercept before every exception (75h; EXITINFO1 = n). -/
@[inline] def swint (n : UInt8) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.i3 21 then exitInstr 0x75 n.toUInt64 0 m else .ok () m

/-- INVLPG: after its exceptions (79h; EXITINFO1 = the linear address). -/
@[inline] def invlpg (lin : UInt32) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.i3 25 then exitInstr 0x79 lin.toUInt64 0 m else .ok () m

/-- An exception raised by an instruction itself (INT3 #BP, INTO #OF, BOUND #BR, 15.12.4-6): the
exception intercept with the instruction's rIP and nRIP = the next instruction. -/
@[inline] def excInstr (v : UInt8) : M Unit := fun m =>
  let c := m.cpu
  if c.svmOn && bit c.svmx.iexc v.toUInt32 then exitInstr (0x40 + v.toUInt64) 0 0 m else .ok () m

/-- PAUSE (table 15-7, 15.14.4): with the PAUSE intercept, the filter count (loaded by VMRUN) is
decremented by each PAUSE and the intercept occurs when it would go below zero; with a filter
threshold, a PAUSE more than `threshold` cycles after the previous one reloads the count first (the
model's cycle count is the instruction count `icount`). A count of 0 intercepts every PAUSE. -/
def pause : M Unit := fun m =>
  let c := m.cpu
  if !(c.svmOn && bit c.svmx.i3 23) then .ok () m else
  let s := c.svmx
  let cnt := if s.pauseThresh != 0 && m.icount - s.lastPause > s.pauseThresh.toUInt64 then s.pauseFilter
    else s.pauseCount
  let m := { m with cpu := { c with svmx := { s with lastPause := m.icount } } }
  if cnt == 0 then
    let m := { m with cpu := { m.cpu with svmx := { m.cpu.svmx with pauseCount := s.pauseFilter } } }
    exitInstr 0x77 0 0 m
  else .ok () { m with cpu := { m.cpu with svmx := { m.cpu.svmx with pauseCount := cnt - 1 } } }

/-- MWAIT/MWAITX: the conditional intercept (monitor armed, 8Ch) before the unconditional one (8Bh). -/
@[inline] def mwait (armed : Bool) : M Unit := fun m =>
  let c := m.cpu
  if !c.svmOn then .ok () m
  else if armed && bit c.svmx.i4 12 then exitInstr 0x8C 0 0 m
  else if bit c.svmx.i4 11 then exitInstr 0x8B 0 0 m
  else .ok () m

/-- The task-switch intercept (15.14.1), after the incoming TSS has been checked: EXITINFO1 = the
TSS selector, EXITINFO2 = the error code (31:0) with bit 36 for IRET, 38 for a far JMP, 44 if an
error code is pushed, 48 the EFLAGS.RF the outgoing TSS would get. `iret`/`jmp`: the source. -/
def taskSwitch (sel : UInt16) (iret jmp : Bool) (err : Option UInt32) : M Unit := fun m =>
  let c := m.cpu
  if !(c.svmOn && bit c.svmx.i3 29) then .ok () m else
  let info2 : UInt64 := (err.getD 0).toUInt64 ||| (if iret then 1 <<< 36 else 0) |||
    (if jmp then 1 <<< 38 else 0) ||| (if err.isSome then 1 <<< 44 else 0) |||
    (if c.eflags &&& Flag.RF != 0 then 1 <<< 48 else 0)
  .error (.vmexit { code := 0x7D, info1 := sel.toUInt64, info2 }) m

/-! ## Event delivery (EXITINTINFO, 15.7.2) -/

/-- EXITINTINFO / EVENTINJ encoding (figure 15-1): vector, type (0 INTR, 2 NMI, 3 exception, 4
software interrupt), error code, valid. -/
@[inline] def intInfo (vec : UInt8) (ty : UInt64) (err : Option UInt32) : UInt64 :=
  vec.toUInt64 ||| (ty <<< 8) ||| 0x80000000 |||
    (match err with | some e => 0x800 ||| (e.toUInt64 <<< 32) | none => 0)

/-- The exception intercept bit of vector `v`. Vectors 2 and 9 are not implemented as exception
intercepts (15.12.3, 15.12.10). -/
@[inline] def excIntercepted (c : Cpu) (v : UInt8) : Bool :=
  c.svmOn && v < 32 && v != 2 && v != 9 && bit c.svmx.iexc v.toUInt32

/-- Run the IDT delivery `act` of an event the guest delivers on behalf of an instruction (INT n,
INT3, INTO, INT1) or an injected event, with `info` its EXITINTINFO: a #VMEXIT during the delivery
records it (unless a delivery nested inside already did), and an exception the delivery raises is
checked for its intercept before it is combined with the event (15.7.3, 15.12). -/
def deliverAs (info : UInt64) (act : M Unit) : M Unit := fun m =>
  if !m.cpu.svmOn then act m else
  match act m with
  | .error (.vmexit e) m' =>
    .error (.vmexit (if e.intInfo &&& 0x80000000 != 0 then e else { e with intInfo := info })) m'
  | .error (.exc v e a) m' =>
    if excIntercepted m'.cpu v then
      .error (.vmexit { code := 0x40 + v.toUInt64, info1 := (e.getD 0).toUInt64,
                        info2 := if v == Vec.PF then a.toUInt64 else 0, intInfo := info }) m'
    else .error (.exc v e a) m'
  | r => r

/-! ## Time-stamp counter (15.30.5) -/

/-- The TSC as a guest reads it: `t` scaled by TSC_RATIO (8.32 fixed point) plus TSC_OFFSET
(RDTSC, RDTSCP, RDMSR TSC; 15.5.1, 15.30.5); unchanged outside guest mode and in SMM. -/
@[inline] def guestTsc (c : Cpu) (t : UInt64) : UInt64 :=
  if !c.svmOn then t else
  let r := c.svmx.tscRatio
  let scaled := if r == 0x100000000 then t else ((t.toNat * r.toNat) >>> 32).toUInt64
  scaled + c.svmx.tscOffset

/-- The TSC rate as MPERF/APERF read in a guest: scaled by TSC_RATIO, without the offset (15.30.5:
"the TSC, MPERF, and MPerfReadOnly MSRs ... read via RDMSR by a guest" are scaled). -/
@[inline] def guestScaled (c : Cpu) (t : UInt64) : UInt64 :=
  if !c.svmOn || c.svmx.tscRatio == 0x100000000 then t
  else ((t.toNat * c.svmx.tscRatio.toNat) >>> 32).toUInt64

/-! ## TPR virtualization (15.21.2) -/

/-- A guest that virtualizes interrupt masking (V_INTR_MASKING): CR8 accesses use V_TPR. -/
@[inline] def vTprOn (c : Cpu) : Bool := c.svmOn && c.svmx.vIntrMasking

/-- Set V_TPR after a CR8 write in guest mode (also without V_INTR_MASKING, where the write goes
to the APIC's TPR as well). -/
@[inline] def setVTpr (v : UInt32) : M Unit := modCpu fun c =>
  if c.svmOn then { c with svmx := { c.svmx with vTpr := v &&& 0xF } } else c

/-! ## SMM (15.22) -/

/-- The virtual-interrupt quadword in the format of VMCB offset 060h (V_TPR, V_IRQ, V_GIF,
V_INTR_PRIO, V_IGN_TPR, V_INTR_MASKING, V_GIF enable, V_INTR_VECTOR in bits 39:32). -/
def vintWord (s : SvmState) : UInt64 :=
  let b (x : Bool) (k : UInt64) : UInt64 := if x then 1 <<< k else 0
  s.vTpr.toUInt64 ||| b s.vIrq 8 ||| b s.vGif 9 ||| (s.vPrio.toUInt64 <<< 16) ||| b s.vIgnTpr 20 |||
    b s.vIntrMasking 24 ||| b s.vGifEn 25 ||| (s.vVec.toUInt64 <<< 32)

/-- The SVM fields of the AMD64 SMM state-save map (APM vol. 2, table 10-1), as offsets from
SMBASE + 8000h with their quadword values, written by SMM entry (`smmEnter`). An SMI taken in guest
mode (one the guest does not intercept, 15.22) records it: SVM Guest (FED8h) = 1, the guest's VMCB
physical address (FEE0h), its virtual-interrupt state (FEE8h, the VMCB 060h format), and the nested
paging context the SMM handler needs to translate guest addresses: guest PAT (FF20h), host EFER
(FF28h), host CR4 (FF30h), nCR3 (FF38h) and host CR0 (FF40h); outside guest mode they are 0, as are
gPAT and nCR3 without nested paging. The table marks them read-only, and RSM does not read them back:
guest mode, the VMCB and the host state stay on chip across SMM (`SvmState`), so RSM returns to the
guest exactly as it was interrupted (SMM software changing these fields has no effect). FEF0h–FEF7h
(reserved) is written as 0. -/
def smmSave (c : Cpu) : List (UInt32 × UInt64) :=
  let s := c.svmx
  let g := s.guest
  let z (x : Bool) (v : UInt64) : UInt64 := if x then v else 0
  [(0x7ED8, z g 1), (0x7EE0, z g s.vmcb), (0x7EE8, z g (vintWord s)), (0x7EF0, 0),
   (0x7F20, z (g && s.np) c.sysx.pat), (0x7F28, z g s.host.efer.toUInt64), (0x7F30, z g s.host.cr4.toUInt64),
   (0x7F38, z (g && s.np) s.ncr3), (0x7F40, z g s.host.cr0.toUInt64)]

end Svm
end X86
