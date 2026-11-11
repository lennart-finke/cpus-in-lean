import X86.Exec
import X86.Ext.LongMode
/-!
# SVM (Secure Virtual Machine)

Owner: the SVM workstream. AMD's virtualization architecture as an EPYC 7742 (Zen 2) provides it,
from AMD APM vol. 2 (24593 rev. 3.43) chapter 15, appendices B and C, and vol. 3 (24594 rev. 3.39)
VMRUN, VMLOAD, VMSAVE, VMMCALL, STGI, CLGI, SKINIT, INVLPGA. State: `SvmState` (`X86/State.lean`,
part of `Cpu`, so each CPU of `MpMachine` has its own); the intercept checks of the core
instructions are `X86/Ext/SvmBase.lean`; nested paging is in `X86/Machine.lean` ("SVM nested
paging"); the event logic in guest mode and with GIF = 0 (physical and virtual interrupts, NMI, SMI,
INIT, exception intercepts, EXITINTINFO, event injection, shutdown) is in `X86/Step.lean` ("SVM").

Hooks (called by `X86/Dispatch.lean`; `none` = not handled here):

* `op0F?` is called for 0F 01 register forms other than SMSW/LMSW (fallback #UD): this module owns
  D8 (VMRUN), D9 (VMMCALL), DA (VMLOAD), DB (VMSAVE), DC (STGI), DD (CLGI), DE (SKINIT),
  DF (INVLPGA).
* `msr?`: VM_CR (C001_0114h), IGNNE (C001_0115h), SMM_CTL (C001_0116h), VM_HSAVE_PA (C001_0117h),
  SVM_KEY (C001_0118h), TSC_RATIO (C000_0104h).

## Scope

The host is legacy protected mode or compatibility mode (the model executes no 64-bit code, see
`LongModeBase.lean`): VMRUN in a 64-bit host is unreachable. Guests run in real mode (also paged real
mode, 15.19), virtual-8086 mode, 16/32-bit protected mode with or without paging (legacy, PAE) and
long-mode compatibility mode; a guest whose CS is 64-bit stops at its first instruction with
`Fault.unsupported "64-bit mode"` like every 64-bit code (VMRUN loads RIP/RSP bits 63:32 into
`LongModeState` first). VMRUN is not supported in SMM (APM: undefined): `Fault.unsupported`.

## Choices where the APM leaves room (documented, UNCONFIRMED on hardware unless stated)

* The host state is kept on chip (`SvmState.host`; allowed by 15.5.1); VM_HSAVE_PA is checked and
  kept but its page is not written. The host's segment caches are restored as saved (15.6: "if
  required, re-reads the descriptors ... depending on the implementation"). #VMEXIT restores host
  DR6 and DR7 with breakpoints disabled (bits 7:0 clear), as QEMU does; CR2 keeps the guest's value
  (VMRUN does not save it).
* VMCB Clean bits are ignored: every VMRUN loads every field from the VMCB (15.15.1: "any given
  processor implementation may ignore bits that are set to 1").
* TLB: a guest always starts with an empty TLB and its entries are dropped at #VMEXIT; the host's
  entries are set aside at VMRUN and reinstated at #VMEXIT (`SvmState.hostTlb`), so host and guest
  translations never meet (theorems in `Proofs/ExtSvm.lean`). Every TLB_CONTROL command is therefore
  honoured; 01h also drops the host's entries. A reserved TLB_CONTROL value is VMEXIT_INVALID (as
  KVM's nested SVM; the APM calls them reserved). INVLPGA invalidates in the running ASID or the
  host's set-aside entries; other ASIDs hold nothing.
* CR0 reserved bits from the VMCB read as zero (as MOV CR0); EFER.LMA is recomputed as LME ∧ PG;
  CR3 bits 63:48 are MBZ only for a long-mode guest; DR6/DR7 get their fixed bits as with MOV DRn.
* The VMCB CPL must equal CS.RPL for a protected-mode guest: the model derives the CPL from CS
  (`Cpu.cpl`), so another value stops the simulation (`Fault.unsupported`).
* Event injection: an error code is pushed only with EV = 1, also for vectors that normally have
  none (APM 15.20), and never in real mode; injected software interrupts (type 4) and #BP/#OF
  (type 3, vectors 3/4: "behaves like a trap raised by INT3 and INTO") push the VMCB's nRIP as return
  address and check the gate DPL. Type 3 with vector 2 or above 31 and reserved types are
  VMEXIT_INVALID.
* SKINIT: the CPU-state effects of vol. 3 SKINIT (INIT-like reset, flat 32-bit protected mode,
  EAX/EDX/ESP, VM_CR.DPD/R_INIT/DIS_A20M, GIF = 0, jump to the SLB entry point). The model has no
  TPM and no DMA: the SL image is not measured and SL_DEV protection protects nothing; the
  multiprocessor handshake (APs clear GIF at STARTUP after an SKINIT) is not modelled.
* VMSAVE/VMLOAD virtualization (15.33.1) "is only recognized when the hypervisor is in 64 bit
  mode": never in this model, so a guest VMLOAD/VMSAVE with the enable bit set is a #VMEXIT with its
  exit code (as the APM requires); with the bit clear it runs on the system-physical address.
* Not reported (CPUID 8000_000A:EDX): LbrVirt (the model records no branches and has no
  LastBranch*/LastInt* MSRs), AVIC, GMET (its EXITINFO1 user bit is ambiguous in the APM), and the
  dump's reserved bit 11.
-/
namespace X86
namespace Svm

/-! ## Physical VMCB access -/

@[inline] def rd8 (a : UInt64) : M UInt32 := physRd a 1
@[inline] def rd16 (a : UInt64) : M UInt32 := physRd a 2
@[inline] def rd32 (a : UInt64) : M UInt32 := physRd a 4
def rd64 (a : UInt64) : M UInt64 := do
  let lo ← physRd a 4
  let hi ← physRd (a + 4) 4
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)
@[inline] def wr8 (a : UInt64) (v : UInt32) : M Unit := physWr a 1 v
@[inline] def wr16 (a : UInt64) (v : UInt32) : M Unit := physWr a 2 v
@[inline] def wr32 (a : UInt64) (v : UInt32) : M Unit := physWr a 4 v
def wr64 (a : UInt64) (v : UInt64) : M Unit := do
  physWr a 4 v.toUInt32
  physWr (a + 4) 4 (v >>> 32).toUInt32

/-- State-save area offsets (table B-2, from VMCB offset 400h). -/
def ssEs : UInt64 := 0x400
def ssCs : UInt64 := 0x410
def ssSs : UInt64 := 0x420
def ssDs : UInt64 := 0x430
def ssFs : UInt64 := 0x440
def ssGs : UInt64 := 0x450
def ssGdtr : UInt64 := 0x460
def ssLdtr : UInt64 := 0x470
def ssIdtr : UInt64 := 0x480
def ssTr : UInt64 := 0x490

/-- VMCB segment attributes (12 bits: descriptor bits 47:40 and 55:52) ↔ `SegReg.attr`. -/
@[inline] def attrOfVmcb (a : UInt32) : UInt32 := (a &&& 0xFF) ||| ((a &&& 0xF00) <<< 4)
@[inline] def attrToVmcb (a : UInt32) : UInt32 := (a &&& 0xFF) ||| ((a >>> 4) &&& 0xF00)

/-- Sign-extend a segment base from bit 47 (canonicalization, 15.5.1). -/
@[inline] def canon (v : UInt64) : UInt64 := if v &&& 0x800000000000 != 0 then v ||| 0xFFFF000000000000 else v &&& 0xFFFFFFFFFFFF

/-- Read a segment (selector, attributes, limit, base) at `a`. -/
def rdSeg (a : UInt64) : M (SegReg × UInt64) := do
  let sel ← rd16 a
  let attr ← rd16 (a + 2)
  let limit ← rd32 (a + 4)
  let base := canon (← rd64 (a + 8))
  return ({ sel := sel.toUInt16, attr := attrOfVmcb attr, limit, base := base.toUInt32 }, base)

/-- Write a segment at `a` (`base` the full 64-bit base). -/
def wrSeg (a : UInt64) (s : SegReg) (base : UInt64) : M Unit := do
  wr16 a s.sel.toUInt32
  wr16 (a + 2) (attrToVmcb s.attr)
  wr32 (a + 4) s.limit
  wr64 (a + 8) base

/-! ## Helpers -/

@[inline] def svmx : M SvmState := fun m => .ok m.cpu.svmx m
@[inline] def modS (f : SvmState → SvmState) : M Unit := modCpu fun c => { c with svmx := f c.svmx }

/-- The maximum physical address (MAXPHYADDR 48). -/
def maxPa : UInt64 := 0x1000000000000

/-- EFER.SVME. -/
@[inline] def svme (c : Cpu) : Bool := c.efer &&& EFER.SVME != 0

/-- The #UD and #GP(0) checks common to VMRUN, VMLOAD, VMSAVE, CLGI and INVLPGA (vol. 3): #UD
without EFER.SVME or outside protected mode (real and virtual-8086 mode), #GP(0) at CPL > 0. -/
def pre : M Unit := do
  let c ← cpu
  if !svme c || !c.pe || c.vm86 then ud
  if c.cpl != 0 then gp 0

/-- STGI and SKINIT also execute with EFER.SVME = 0 when SVM-Lock or SKINIT/DEV is supported
(vol. 3 STGI, SKINIT). -/
@[inline] def svmLockOrSkinit : Bool := implemented .svmFeatures || implemented .skinit

/-- The physical address in rAX (by the address size) of VMRUN/VMLOAD/VMSAVE: #GP(0) if not 4 KiB
aligned (or beyond MAXPHYADDR, which a 32-bit rAX cannot be). -/
def raxPa (i : Inst) : M UInt64 := do
  let a ← getReg 0
  let a := if i.adsz == 2 then a &&& 0xFFFF else a
  if a &&& 0xFFF != 0 then gp 0
  return a.toUInt64

/-! ## #VMEXIT (15.6; vol. 3 VMRUN "Upon #VMEXIT") -/

/-- The guest's TLB entries are dropped and the host's set-aside entries reinstated. -/
def restoreHostTlb : M Unit := modM fun m =>
  let t := m.cpu.svmx.hostTlb
  let tag := if t.tag.size == tlbSize then t.tag else Array.replicate tlbSize 0
  let v := if t.val.size == tlbSize then t.val else Array.replicate tlbSize 0
  { m with tlbTag := tag, tlbVal := v, tlbLarge := t.large, tlbLargeRegions := t.regions,
           tlbGlobal := t.global, cpu := { m.cpu with svmx := { m.cpu.svmx with hostTlb := {} } } }

/-- SPEC_CTRL (MSR 48h) value kept in `Cpu.msrs` by `Sys.msr?`. -/
@[inline] def specCtrlOf (c : Cpu) : UInt64 := ((c.msrs.find? (·.1 == 0x48)).map (·.2)).getD 0
@[inline] def withSpecCtrl (c : Cpu) (v : UInt64) : Cpu :=
  { c with msrs := (0x48, v) :: c.msrs.filter (·.1 != 0x48) }

/-- The return to the host after the guest state has been saved: write EXITCODE, EXITINFO1/2,
EXITINTINFO and nRIP, clear EVENTINJ, clear the guest controls (intercepts, V_IRQ, V_INTR_MASKING,
TSC_OFFSET, nested paging, ASID 0), reinstate the host's TLB and reload the host state with
CR0.PE = 1, EFLAGS.VM = RF = 0, CPL 0 and DR7 breakpoints disabled; GIF = 0. A host PAE PDPTE with
reserved bits shuts the processor down. EFLAGS.TF of the host raises its #DB trap after the
completed VMRUN (15.5.1). -/
def exitToHost (e : VmExit) : M Unit := do
  let s ← svmx
  let v := s.vmcb
  wr64 (v + 0x70) e.code
  wr64 (v + 0x78) e.info1
  wr64 (v + 0x80) e.info2
  wr64 (v + 0x88) e.intInfo
  if implemented .svmFeatures then wr64 (v + 0xC8) e.nrip
  wr64 (v + 0xA8) 0
  let h := s.host
  restoreHostTlb
  modCpu fun c =>
    let c := { c with
      svmx := { c.svmx with guest := false, gif := false, icr := 0, idr := 0, iexc := 0, i3 := 0, i4 := 0,
                            i5 := 0, tscOffset := 0, asid := 0, vIrq := false, vIntrMasking := false,
                            vGifEn := false, np := false, vmsaveVirt := false, inject := 0 },
      es := h.es, cs := h.cs, ss := h.ss, ds := h.ds,
      gdtBase := h.gdtBase, gdtLimit := h.gdtLimit, idtBase := h.idtBase, idtLimit := h.idtLimit,
      efer := h.efer, cr0 := h.cr0 ||| CR0.PE, cr3 := h.cr3, cr4 := h.cr4,
      eflags := h.eflags &&& ~~~(Flag.VM ||| Flag.RF), eip := h.eip, esp := h.esp, eax := h.eax,
      dr6 := h.dr6, halted := false, shadow := false,
      lmx := { c.lmx with ripHi := 0, rspHi := 0 } }
    (withSpecCtrl c h.specCtrl).setDr7 (h.dr7 &&& ~~~0xFF)
  let c ← cpu
  -- the host's PAE PDPTEs from its CR3 (legacy PAE paging); illegal ones shut down
  if c.cr0 &&& CR0.PG != 0 && c.cr4 &&& CR4.PAE != 0 && !LongMode.lma c then
    let p ← tryCatch (readPdptes c.cr3) fun _ => throw (.shutdown "#VMEXIT: invalid host PDPTEs")
    modCpu fun c => { c with pdpte := p }
  modM fun m => { m with dbPend := if h.eflags &&& Flag.TF != 0 then DR6.BS else 0, dbHit := 0 }

/-- Guest instruction bytes for the decode assist of a nested or intercepted #PF (15.8.4): up to 15
bytes at guest CS:rIP, fewer if a fetch faults; byte 0 holds the count. -/
def guestBytes : M (UInt64 × UInt64) := fun m =>
  let c := m.cpu
  let rec go : Nat → Nat → Machine → List UInt32 × Machine
    | 0, _, m => ([], m)
    | n + 1, k, m =>
      match fetch8 (c.eip + k.toUInt32) m with
      | .ok b m => let (r, m) := go n (k + 1) m; (b :: r, m)
      | .error _ m => ([], m)
  let (bs, m) := go 15 0 m
  let all := (bs.length.toUInt32) :: bs
  let byteAt := fun (k : Nat) => (all.getD k 0).toUInt64 &&& 0xFF
  let lo := (List.range 8).foldl (fun a k => a ||| (byteAt k <<< (8 * k).toUInt64)) 0
  let hi := (List.range 8).foldl (fun a k => a ||| (byteAt (k + 8) <<< (8 * k).toUInt64)) 0
  .ok (lo, hi) { m with cpu := c }

/-- #VMEXIT from guest mode with `e`: save the guest state in the VMCB (segments ES/CS/SS/DS, GDTR,
IDTR, EFER, CR0, CR2, CR3, CR4, gPAT with nested paging, RFLAGS, RIP, RSP, RAX, DR6, DR7, CPL, the
interrupt shadow, V_TPR, V_IRQ, VGIF, SPEC_CTRL), the decode-assist instruction bytes for #PF and NPF
exits, then `exitToHost`. -/
def vmexit (e : VmExit) : M Unit := do
  let c ← cpu
  let s := c.svmx
  let v := s.vmcb
  -- decode assists (15.8.4): bytes for data #PF / NPF; other exits clear the count byte
  let fetchFault := match e.code with
    | 0x4E => e.info1 &&& 0x10 != 0
    | 0x400 => e.info1 &&& 0x10 != 0 && e.info1 &&& npfFinal != 0
    | _ => true
  if (e.code == 0x4E || e.code == 0x400) && !fetchFault && implemented .svmFeatures then
    let (lo, hi) ← guestBytes
    wr64 (v + 0xD0) lo
    wr64 (v + 0xD8) hi
  else wr8 (v + 0xD0) 0
  let c ← cpu
  wrSeg (v + ssEs) c.es c.es.base.toUInt64
  wrSeg (v + ssCs) c.cs c.cs.base.toUInt64
  wrSeg (v + ssSs) c.ss c.ss.base.toUInt64
  wrSeg (v + ssDs) c.ds c.ds.base.toUInt64
  wr32 (v + ssGdtr + 4) c.gdtLimit
  wr64 (v + ssGdtr + 8) c.gdtBase.toUInt64
  wr32 (v + ssIdtr + 4) c.idtLimit
  wr64 (v + ssIdtr + 8) c.idtBase.toUInt64
  wr8 (v + 0x4CB) c.cpl
  wr64 (v + 0x4D0) c.efer.toUInt64
  wr64 (v + 0x548) c.cr4.toUInt64
  wr64 (v + 0x550) c.cr3.toUInt64
  wr64 (v + 0x558) c.cr0.toUInt64
  wr64 (v + 0x560) c.dr7.toUInt64
  wr64 (v + 0x568) c.dr6.toUInt64
  wr64 (v + 0x570) c.eflags.toUInt64
  wr64 (v + 0x578) ((c.lmx.ripHi.toUInt64 <<< 32) ||| c.eip.toUInt64)
  wr64 (v + 0x5D8) ((c.lmx.rspHi.toUInt64 <<< 32) ||| c.esp.toUInt64)
  wr64 (v + 0x5F8) c.eax.toUInt64
  wr64 (v + 0x640) c.cr2.toUInt64
  if s.np then wr64 (v + 0x668) c.sysx.pat
  if implemented .svmFeatures then wr64 (v + 0x6E0) (specCtrlOf c)
  -- V_TPR (7:0), V_IRQ (8), VGIF (9) of 060h; the other control bits are not written
  let w ← rd32 (v + 0x60)
  wr32 (v + 0x60) ((w &&& ~~~0x3FF) ||| s.vTpr ||| (if s.vIrq then 0x100 else 0) ||| (if s.vGif then 0x200 else 0))
  let st ← rd32 (v + 0x68)
  wr32 (v + 0x68) ((st &&& ~~~1) ||| (if c.shadow then 1 else 0))
  -- with nested paging the host's PAT register was replaced by gPAT
  if s.np then modCpu fun c => { c with sysx := { c.sysx with pat := s.hostPat } }
  exitToHost e

/-- `vmexit` as a machine transition (for `Step`): an exception while reloading the host state shuts
the processor down (15.6). -/
def vmexitM (m : Machine) (e : VmExit) : Machine :=
  match vmexit e { m with keepCpu := false } with
  | .ok _ m => m
  | .error (.shutdown w) m => { m with fatal := some (.shutdown w) }
  | .error f m => { m with fatal := some (.shutdown s!"#VMEXIT: {repr f}") }

/-! ## VMRUN (15.5; vol. 3 VMRUN) -/

/-- The PAT memory types a G_PAT entry may hold (UC, WC, WT, WP, WB, UC-; APM vol. 2, 7.8.1). -/
@[inline] def patOk (v : UInt64) : Bool :=
  (List.range 8).all fun k =>
    let t := (v >>> (8 * k).toUInt64) &&& 0xFF
    t == 0 || t == 1 || t == 4 || t == 5 || t == 6 || t == 7

/-- EVENTINJ is legal (15.20): reserved types and type 3 (exception) with vector 2 or > 31 are not. -/
@[inline] def injOk (e : UInt64) : Bool :=
  if e &&& 0x80000000 == 0 then true else
  let ty := (e >>> 8) &&& 7
  let vec := e &&& 0xFF
  (ty == 0 || ty == 2 || ty == 3 || ty == 4) && !(ty == 3 && (vec == 2 || vec > 31))

/-- VMRUN: checks (#UD, #GP), the VMRUN intercept, then save the host state, load the control area
and the guest state, check them (VMEXIT_INVALID on an illegal combination), execute TLB_CONTROL,
set GIF and enter guest mode; an event in EVENTINJ is taken before the first guest instruction
(`Step`). EIP already holds the instruction after VMRUN (the host's resume point). -/
def vmrun (i : Inst) : M Unit := do
  pre
  let v ← raxPa i
  icpt4 0
  let c ← cpu
  if c.smm then unsupported "VMRUN in SMM (undefined)"
  -- save the host state (hidden on-chip, see the module documentation)
  let host : SvmHost := {
    es := c.es, cs := c.cs, ss := c.ss, ds := c.ds,
    gdtBase := c.gdtBase, gdtLimit := c.gdtLimit, idtBase := c.idtBase, idtLimit := c.idtLimit,
    efer := c.efer, cr0 := c.cr0, cr3 := c.cr3, cr4 := c.cr4,
    eflags := c.eflags, eip := c.eip, esp := c.esp, eax := c.eax, dr6 := c.dr6, dr7 := c.dr7,
    specCtrl := specCtrlOf c }
  modS fun s => { s with vmcb := v, host }
  -- the control area
  let icr ← rd32 v
  let idr ← rd32 (v + 4)
  let iexc ← rd32 (v + 8)
  let i3 ← rd32 (v + 0xC)
  let i4 ← rd32 (v + 0x10)
  let i5 ← rd32 (v + 0x14)
  let pthr ← rd16 (v + 0x3C)
  let pcnt ← rd16 (v + 0x3E)
  let iopm := (← rd64 (v + 0x40)) &&& ~~~0xFFF
  let msrpm := (← rd64 (v + 0x48)) &&& ~~~0xFFF
  let tscOff ← rd64 (v + 0x50)
  let asid ← rd32 (v + 0x58)
  let tlbCtl ← rd8 (v + 0x5C)
  let vint ← rd64 (v + 0x60)
  let intState ← rd64 (v + 0x68)
  let npCtl ← rd64 (v + 0x90)
  let inj ← rd64 (v + 0xA8)
  let ncr3 ← rd64 (v + 0xB0)
  let virtCtl ← rd64 (v + 0xB8)
  let nrip ← rd64 (v + 0xC8)
  -- the guest state
  let (es, _) ← rdSeg (v + ssEs)
  let (cs, _) ← rdSeg (v + ssCs)
  let (ss, _) ← rdSeg (v + ssSs)
  let (ds, _) ← rdSeg (v + ssDs)
  let gdtLimit ← rd32 (v + ssGdtr + 4)
  let gdtBase ← rd64 (v + ssGdtr + 8)
  let idtLimit ← rd32 (v + ssIdtr + 4)
  let idtBase ← rd64 (v + ssIdtr + 8)
  let cpl ← rd8 (v + 0x4CB)
  let efer ← rd64 (v + 0x4D0)
  let cr4 ← rd64 (v + 0x548)
  let cr3 ← rd64 (v + 0x550)
  let cr0 ← rd64 (v + 0x558)
  let dr7 ← rd64 (v + 0x560)
  let dr6 ← rd64 (v + 0x568)
  let rflags ← rd64 (v + 0x570)
  let rip ← rd64 (v + 0x578)
  let rsp ← rd64 (v + 0x5D8)
  let rax ← rd64 (v + 0x5F8)
  let cr2 ← rd64 (v + 0x640)
  let gpat ← rd64 (v + 0x668)
  let gspec ← rd64 (v + 0x6E0)
  let np := npCtl &&& 1 != 0 && implemented .svmFeatures
  let lme := efer &&& EFER.LME.toUInt64 != 0
  let pg := cr0 &&& CR0.PG.toUInt64 != 0
  let pae := cr4 &&& CR4.PAE.toUInt64 != 0
  let lBitCs := cs.attr &&& 0x2000 != 0
  let dBitCs := cs.attr &&& 0x4000 != 0
  -- consistency checks (15.5.1 "Canonicalization and Consistency Checks", 15.25.4, 15.20)
  let invalid :=
    efer &&& EFER.SVME.toUInt64 == 0 ||
    efer &&& ~~~(Cpuid.eferWritable ||| EFER.LMA).toUInt64 != 0 ||
    (cr0 &&& CR0.CD.toUInt64 == 0 && cr0 &&& CR0.NW.toUInt64 != 0) ||
    cr0 >>> 32 != 0 ||
    (lme && pg && cr3 >>> 48 != 0) ||
    cr4 &&& ~~~Cpuid.cr4Writable.toUInt64 != 0 ||
    dr6 >>> 32 != 0 || dr7 >>> 32 != 0 ||
    (lme && pg && !pae) ||
    (lme && pg && cr0 &&& CR0.PE.toUInt64 == 0) ||
    (lme && pg && pae && lBitCs && dBitCs) ||
    i4 &&& 1 == 0 ||
    msrpm + 0x1FFF ≥ maxPa || iopm + 0x2FFF ≥ maxPa ||
    !injOk inj ||
    asid == 0 ||
    !(tlbCtl == 0 || tlbCtl == 1 || tlbCtl == 3 || tlbCtl == 7) ||
    (np && (c.cr0 &&& CR0.PG == 0 || ncr3 >>> 48 != 0 || !patOk gpat))
  if invalid then
    exitToHost { code := 0xFFFFFFFFFFFFFFFF }
    return
  -- a protected-mode guest's CPL must be CS.RPL (the model derives the CPL from CS)
  let vm := rflags &&& Flag.VM.toUInt64 != 0
  if cr0 &&& CR0.PE.toUInt64 != 0 && !vm && cpl != (cs.sel.toUInt32 &&& 3) then
    unsupported "VMRUN: VMCB CPL differs from CS.RPL"
  -- legacy PAE guest without nested paging: its PDPTEs, checked (15.5.1)
  let ncr0 := (cr0.toUInt32 &&& 0xE005003F) ||| CR0.ET
  let pdpte ← if pg && pae && !lme && !np then
      tryCatch (some <$> readPdptes cr3.toUInt32) fun _ => pure none
    else pure (some c.pdpte)
  let some pdpte := pdpte | do exitToHost { code := 0xFFFFFFFFFFFFFFFF }; return
  -- the host's paging mode for the nested tables (15.25.3)
  let nMode : UInt8 :=
    if c.cr4 &&& CR4.PAE == 0 then (if c.cr4 &&& CR4.PSE != 0 then 1 else 0)
    else if LongMode.lma c then 3 else 2
  -- the host's TLB entries are set aside (TLB_CONTROL 01h: flushed); the guest starts empty
  modM fun m =>
    let ht : SvmTlb := if tlbCtl == 1 then {} else
      { tag := m.tlbTag, val := m.tlbVal, large := m.tlbLarge, regions := m.tlbLargeRegions,
        global := m.tlbGlobal }
    { m with tlbTag := Array.replicate tlbSize 0, tlbVal := Array.replicate tlbSize 0, tlbLarge := false,
             tlbLargeRegions := #[], tlbGlobal := false, dbPend := 0, dbHit := 0,
             cpu := { m.cpu with svmx := { m.cpu.svmx with hostTlb := ht } } }
  let nefer := (efer.toUInt32 &&& ~~~EFER.LMA) ||| (if lme && pg then EFER.LMA else 0)
  let in64 := nefer &&& EFER.LMA != 0 && lBitCs
  modCpu fun c =>
    let c := { c with
      svmx := { c.svmx with
        guest := true, gif := true, icr, idr, iexc, i3, i4, i5, iopm, msrpm, tscOffset := tscOff, asid,
        pauseFilter := pcnt, pauseCount := pcnt, pauseThresh := pthr, lastPause := 0,
        vTpr := vint.toUInt32 &&& 0xF, vIrq := vint &&& 0x100 != 0, vGif := vint &&& 0x200 != 0,
        vPrio := (vint >>> 16).toUInt32 &&& 0xF, vIgnTpr := vint &&& 0x100000 != 0,
        vIntrMasking := vint &&& 0x1000000 != 0, vGifEn := vint &&& 0x2000000 != 0 && implemented .svmFeatures,
        vVec := (vint >>> 32).toUInt32 &&& 0xFF, hostIf := c.eflags &&& Flag.IF != 0,
        np, ncr3, nMode, nNxe := c.efer &&& EFER.NXE != 0,
        vmsaveVirt := virtCtl &&& 2 != 0 && implemented .svmFeatures,
        hostPat := c.sysx.pat, inject := inj, injNrip := nrip.toUInt32 },
      es, cs, ss, ds, gdtBase := gdtBase.toUInt32, gdtLimit := gdtLimit &&& 0xFFFF,
      idtBase := idtBase.toUInt32, idtLimit := idtLimit &&& 0xFFFF,
      efer := nefer, cr0 := ncr0, cr3 := cr3.toUInt32, cr4 := cr4.toUInt32, cr2 := cr2.toUInt32,
      pdpte, eflags := (rflags.toUInt32 &&& Flag.valid) ||| 2, eip := rip.toUInt32, esp := rsp.toUInt32,
      eax := rax.toUInt32, dr6 := dr6.toUInt32 ||| 0xFFFF0FF0, halted := false,
      shadow := intState &&& 1 != 0,
      lmx := { c.lmx with ripHi := if in64 then (rip >>> 32).toUInt32 else 0,
                          rspHi := if in64 then (rsp >>> 32).toUInt32 else 0 } }
    let c := if np then { c with sysx := { c.sysx with pat := gpat } } else c
    let c := if implemented .svmFeatures then withSpecCtrl c (gspec &&& 7) else c
    c.setDr7 (dr7.toUInt32 ||| 0x400)
  -- the guest's EFLAGS.RF suppresses an instruction breakpoint on its first instruction; the host's
  -- TF traps after the #VMEXIT (`exitToHost`), not here (`Step.noStepTrap`)

/-! ## VMLOAD, VMSAVE (15.5.2) -/

/-- FS or GS with its full 64-bit base (`LongModeState.fsBase`/`gsBase` while the cache is
unchanged; else the cache's 32-bit base). -/
@[inline] def segBase64 (sr : SegReg) (saved : Option (SegReg × UInt64)) : UInt64 :=
  match saved with
  | some (cache, b) => if cache == sr then b else sr.base.toUInt64
  | none => sr.base.toUInt64

/-- VMLOAD (`save = false`) and VMSAVE: FS, GS, TR, LDTR with their hidden state, KernelGsBase,
STAR, LSTAR, CSTAR, SFMASK, SYSENTER_CS/ESP/EIP at the VMCB in rAX (system-physical). In a guest
with VMSAVE/VMLOAD virtualization enabled the enable bit is not recognized (the host is never in
64-bit mode here) and the instruction exits with its intercept code (15.33.1). -/
def vmloadSave (i : Inst) (save : Bool) : M Unit := do
  pre
  let v ← raxPa i
  icpt4 (if save then 3 else 2)
  let c ← cpu
  if c.svmOn && c.svmx.vmsaveVirt then exitInstr (if save then 0x83 else 0x82)
  if save then
    wrSeg (v + ssFs) c.fs (segBase64 c.fs c.lmx.fsBase)
    wrSeg (v + ssGs) c.gs (segBase64 c.gs c.lmx.gsBase)
    wrSeg (v + ssTr) c.tr c.tr.base.toUInt64
    wrSeg (v + ssLdtr) c.ldtr c.ldtr.base.toUInt64
    wr64 (v + 0x620) c.lmx.kernelGsBase
    wr64 (v + 0x600) c.sysx.star
    wr64 (v + 0x608) c.sysx.lstar
    wr64 (v + 0x610) c.sysx.cstar
    wr64 (v + 0x618) c.sysx.sfmask.toUInt64
    wr64 (v + 0x628) c.sysx.sysenterCs.toUInt64
    wr64 (v + 0x630) c.sysx.sysenterEsp.toUInt64
    wr64 (v + 0x638) c.sysx.sysenterEip.toUInt64
  else
    let (fs, fsb) ← rdSeg (v + ssFs)
    let (gs, gsb) ← rdSeg (v + ssGs)
    let (tr, _) ← rdSeg (v + ssTr)
    let (ldtr, _) ← rdSeg (v + ssLdtr)
    let kgs := canon (← rd64 (v + 0x620))
    let star ← rd64 (v + 0x600)
    let lstar ← rd64 (v + 0x608)
    let cstar ← rd64 (v + 0x610)
    let sfmask ← rd64 (v + 0x618)
    let scs ← rd64 (v + 0x628)
    let sesp ← rd64 (v + 0x630)
    let seip ← rd64 (v + 0x638)
    modCpu fun c => { c with
      fs, gs, tr, ldtr,
      lmx := { c.lmx with kernelGsBase := kgs,
                          fsBase := if fsb >>> 32 != 0 then some (fs, fsb) else none,
                          gsBase := if gsb >>> 32 != 0 then some (gs, gsb) else none },
      sysx := { c.sysx with star, lstar, cstar, sfmask := sfmask.toUInt32,
                            sysenterCs := scs.toUInt32 &&& 0xFFFF, sysenterEsp := sesp.toUInt32,
                            sysenterEip := seip.toUInt32 } }

/-! ## STGI, CLGI, VMMCALL, INVLPGA, SKINIT -/

/-- STGI (`set`) / CLGI: GIF := 1 / 0, or the virtual GIF in a guest with VGIF enabled (15.33.2).
STGI also executes with EFER.SVME = 0 when SVM-Lock or SKINIT is supported (vol. 3 STGI). -/
def stgiClgi (set : Bool) : M Unit := do
  let c ← cpu
  if (!svme c && !(set && svmLockOrSkinit)) || !c.pe || c.vm86 then ud
  if c.cpl != 0 then gp 0
  icpt4 (if set then 4 else 5)
  modCpu fun c =>
    if c.svmOn && c.svmx.vGifEn then { c with svmx := { c.svmx with vGif := set } }
    else { c with svmx := { c.svmx with gif := set } }

/-- VMMCALL: #UD without EFER.SVME (in every mode, at every CPL); in a guest the intercept takes
priority over exceptions; not intercepted, #UD (15.18). -/
def vmmcall : M Unit := do
  if !svme (← cpu) then ud
  icpt4 1
  ud

/-- Drop the translation of `lin` from a set-aside TLB (and, for a large page, every slice: the
whole set is dropped, which INVLPGA allows: "may invalidate any number of additional TLB entries"). -/
def SvmTlb.drop (t : SvmTlb) (lin : UInt32) : SvmTlb :=
  if t.tag.size != tlbSize then t
  else if t.large then {}
  else { t with tag := t.tag.set! ((lin >>> 12) % tlbSize.toUInt32).toNat 0 }

/-- INVLPGA rAX, ECX (15.16.2): invalidate the page of linear address rAX (by the address size) in
ASID ECX. The running ASID's TLB is the machine's; the host's (ASID 0) is set aside while a guest
runs; no other ASID holds entries in the model. -/
def invlpga (i : Inst) : M Unit := do
  pre
  icpt3 26
  let c ← cpu
  let lin := if i.adsz == 2 then c.eax &&& 0xFFFF else c.eax
  if c.ecx == c.svmx.asid then flushTlbPage lin
  else if c.ecx == 0 then modS fun s => { s with hostTlb := SvmTlb.drop s.hostTlb lin }

/-- SKINIT EAX (15.27.6; vol. 3 SKINIT): #UD unless EFER.SVME or SVM-Lock/SKINIT support, and
outside protected mode; #GP(0) at CPL > 0; the intercept; then the CPU state of an INIT, flat 32-bit
protected mode (CS = 08h, SS = 10h, base 0, limit 4 GiB), EAX = SLB base (EAX[31:16]), EDX = the
processor signature, ESP = SLB base + 64 KiB, the other registers 0, EFER = 0, VM_CR.DPD, R_INIT,
DIS_A20M set, GIF = 0, and a jump to SLB base + the entry offset (SLB word 0). No TPM (see above). -/
def skinit : M Unit := do
  let c ← cpu
  if (!svme c && !svmLockOrSkinit) || !c.pe || c.vm86 then ud
  if c.cpl != 0 then gp 0
  icpt4 6
  let slb := c.eax &&& 0xFFFF0000
  let entry ← physRd slb.toUInt64 2
  let sig := (cpuid c 1 0).1
  let rm : SegReg := { sel := 0, base := 0, limit := 0xFFFF, attr := 0x92 }
  modCpu fun c => (({ c with
    eax := slb, ebx := 0, ecx := 0, edx := sig, esp := slb + 0x10000, ebp := 0, esi := 0, edi := 0,
    eip := slb + entry, eflags := 2,
    cs := { sel := 8, base := 0, limit := 0xFFFFFFFF, attr := 0xC09B },
    ss := { sel := 0x10, base := 0, limit := 0xFFFFFFFF, attr := 0xC093 },
    ds := rm, es := rm, fs := rm, gs := rm,
    ldtr := { attr := 0x82 }, tr := { attr := 0x83 },
    gdtBase := 0, gdtLimit := 0xFFFF, idtBase := 0, idtLimit := 0xFFFF,
    cr0 := 0x11 ||| (c.cr0 &&& (CR0.CD ||| CR0.NW)), cr2 := 0, cr3 := 0, cr4 := 0,
    dr0 := 0, dr1 := 0, dr2 := 0, dr3 := 0, dr6 := 0xFFFF0FF0, efer := 0, shadow := false,
    lmx := { c.lmx with ripHi := 0, rspHi := 0, fsBase := none, gsBase := none },
    svmx := { c.svmx with gif := false, vmCr := c.svmx.vmCr ||| 7 } } : Cpu).setDr7 0x400)
  flushTlbAll
  modM fun m => { m with dbHit := 0, dbPend := 0 }

/-- The 0F 01 hook: D8..DF with ModRM.mod = 11b. -/
def op0F? (i : Inst) : Option (M Unit) :=
  if i.op != 0x101 || i.isMem || !implemented .svm then none else
  match i.modrm with
  | 0xD8 => some (vmrun i)
  | 0xD9 => some vmmcall
  | 0xDA => some (vmloadSave i false)
  | 0xDB => some (vmloadSave i true)
  | 0xDC => some (stgiClgi true)
  | 0xDD => some (stgiClgi false)
  | 0xDE => if implemented .skinit then some skinit else none
  | 0xDF => some (invlpga i)
  | _ => none

/-! ## MSRs (15.30-15.31) -/

/-- VM_CR bits: DPD 0, R_INIT 1, DIS_A20M 2, LOCK 3, SVMDIS 4. -/
def vmCrLock : UInt64 := 8
def vmCrSvmDis : UInt64 := 0x10

/-- VM_CR (15.30.1): bits 63:5 MBZ (#GP(0)); with LOCK set, writes to LOCK and SVMDIS are ignored;
setting SVMDIS while EFER.SVME = 1 is #GP(0). -/
def vmCrMsr : MsrImpl where
  rd := do return (← svmx).vmCr
  wr v := do
    if v &&& ~~~0x1F != 0 then gp 0
    let s ← svmx
    let v := if s.vmCr &&& vmCrLock != 0 then (v &&& 7) ||| (s.vmCr &&& 0x18) else v
    if v &&& vmCrSvmDis != 0 && svme (← cpu) then gp 0
    modS fun s => { s with vmCr := v }

/-- VM_HSAVE_PA (15.30.4): #GP(0) for a value with bits 11:0 set or at/above MAXPHYADDR. -/
def hsaveMsr : MsrImpl where
  rd := do return (← svmx).hsavePa
  wr v := do
    if v &&& 0xFFF != 0 || v ≥ maxPa then gp 0
    modS fun s => { s with hsavePa := v }

/-- SVM_KEY (15.31.1): write-only (reads 0). With VM_CR.LOCK clear a write sets the key; with LOCK
set a write of the (non-zero) key clears LOCK, any other write is ignored. -/
def svmKeyMsr : MsrImpl where
  rd := return 0
  wr v := do
    let s ← svmx
    if s.vmCr &&& vmCrLock == 0 then modS fun s => { s with svmKey := v }
    else if v == s.svmKey && v != 0 then modS fun s => { s with vmCr := s.vmCr &&& ~~~vmCrLock }

/-- TSC_RATIO (15.30.5): bits 39:0 (8.32 fixed point), bits 63:40 MBZ (#GP(0)); reset 1.0. -/
def tscRatioMsr : MsrImpl where
  rd := do return (← svmx).tscRatio
  wr v := do
    if v >>> 40 != 0 then gp 0
    modS fun s => { s with tscRatio := v }

/-- IGNNE (15.30.2): bit 0 the internal IGNNE signal (storage: the model's FERR# path does not use
it), bits 63:1 MBZ. -/
def ignneMsr : MsrImpl where
  rd := do return (← svmx).ignne
  wr v := do
    if v &&& ~~~1 != 0 then gp 0
    modS fun s => { s with ignne := v }

/-- SMM_CTL (15.30.3), write-only (RDMSR #GP(0)): DISMISS clears the SMI latch, ENTER sets the SMM
state (recording and blocking NMIs), EXIT leaves it (restoring the NMI blocking); the SMI/RSM
special cycles have no effect; bits 63:5 MBZ. SMRAM mapping is the chipset's (not modelled);
HWCR.SmmLock does not exist in the model, so writes are never locked. Only the documented
combinations are defined (ENTER before SMI_CYCLE, DISMISS, RSM_CYCLE before EXIT). -/
def smmCtlMsr : MsrImpl where
  rd := gp 0
  wr v := do
    if v &&& ~~~0x1F != 0 then gp 0
    if v &&& 2 != 0 then
      modCpu fun c => { c with smm := true,
                               sysbx := { c.sysbx with smmNmiBlocked := c.sysbx.nmiBlocked, nmiBlocked := true } }
    if v &&& 1 != 0 then modM fun m => { m with smiPending := false }
    if v &&& 8 != 0 then
      modCpu fun c => { c with smm := false, sysbx := { c.sysbx with nmiBlocked := c.sysbx.smmNmiBlocked } }

def msr? (n : UInt32) : Option MsrImpl :=
  if !implemented .svm then none
  else if n == 0xC0010114 then some vmCrMsr
  else if n == 0xC0010115 then some ignneMsr
  else if n == 0xC0010116 then some smmCtlMsr
  else if n == 0xC0010117 then some hsaveMsr
  else if n == 0xC0010118 then (if implemented .svmFeatures then some svmKeyMsr else none)
  else if n == 0xC0000104 then (if implemented .svmFeatures then some tscRatioMsr else none)
  else none

end Svm
end X86
