import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_epyc`: with the final identity (AMD EPYC 7742) CPUID returns exactly `epycCpuid`, for every
  leaf and subleaf: an explicit table whose only CPU-dependent parts are CR4.OSXSAVE, leaf 0xD (XCR0,
  IA32_XSS) and the topology fields (`Cpuid.topo`).
* `cpuid_epyc_dump`: every bit CPUID reports in a feature register is set in the CPUID dump of a real
  EPYC 7742 (`dump7742`, transcribed independently of `Cpuid.raw`; `raw_dump` checks that the two
  agree): no feature bit is invented. `cpuid_epyc_descr`: the descriptive leaves (brand string,
  cache/TLB, MONITOR, address sizes, SVM revision and ASIDs) are the dump's values.
* `legacyLeaf_former`: the former identity (`Cpuid.legacyLeaf`, no longer selected) with the present
  feature set returns exactly `presentCpuid`: the model's former values (`formerCpuid`, the removed
  `cpuidVals`) plus the features implemented since.
* `cr4Writable_former`, `eferWritable_former`: the derived MOV CR4 / WRMSR EFER masks are the former
  constants.
* `vexExec_real`, `vexExec_vm86`, `vexExec_prefix`: a VEX-encoded instruction raises #UD in real and
  virtual-8086 mode and after a 66/F2/F3/LOCK prefix, before any extension hook runs.
-/
namespace X86

/-- The former CPUID (`Exec.cpuidVals` with `addSimd`), for reference. -/
def formerCpuid (leaf : UInt32) : Regs :=
  match leaf with
  | 0 => (1, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 0x80000000 => (0x80000001, 0, 0, 0)
  | 0x80000001 => (0, 0, 0, 1 <<< 20)
  | _ => (0x00000619, 0, 0, 0x07808365)

/-- The reported leaves with the features implemented since `formerCpuid`'s (the removed
`cpuidVals`): Gpr (MONITOR, MOVBE, POPCNT, RDRAND, CLFSH, BMI1/2, ADX, RDSEED, CLFLUSHOPT, CLWB,
RDPID, ABM, PREFETCHW, MONITORX, RDTSCP, CLZERO, IRPERF, RDPRU, WBNOINVD, MCOMMIT), Sse (SSE3, SSSE3,
SSE4.1, SSE4.2, SSE4A, MisAlignSse), Crypto (AES, PCLMULQDQ, SHA), Xsave (XSAVE, XSAVEOPT, XSAVEC,
XGETBV1, XSAVES, XSaveErPtr; leaf 0xD and OSXSAVE depend on the CPU state) and system A (SYSENTER,
SYSCALL, TSC, PSE, PSE-36, PGE, MCE, MCA, MTRR, PAT, SMEP, SMAP, UMIP, AltMovCr8, FFXSR, TCE, OSVW,
WDT, invariant TSC, ARAT, EffFreq, IBPB/IBRS/STIBP/SSBD), long mode (LM, Page1GB, LahfSahf, FSGSBASE),
Avx (AVX), Avx2 (AVX2, FMA, F16C), integration (MmxExt), system B (VME, IRPERF) and SMP (x2APIC, HTT, CmpLegacy, ExtApicSpace, TopoExt; the topology fields of leaves 1,
0xB, 8000_0001 and 8000_0008 depend on the CPU, `Cpuid.topo`), SVM (SVM, SKINIT and leaf 8000_000A:
revision 1, 8000h ASIDs, NP, SVML, NRIPS, TscRateMsr, VmcbClean, FlushByAsid, DecodeAssists,
PauseFilter, PauseFilterThreshold, VMSAVEvirt, VGIF, SpecCtrl): highest leaves 0xD and 0x8000000A. -/
def sysALeaf (c : Cpu) (l sub : UInt32) : Regs :=
  match l with
  | 0 => (0xD, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 1 => (0x619, Cpuid.topoEbx1 c 0x800, 0x76F8120B ||| Cpuid.osxsave c, Cpuid.topoEdx1 c 0x178BFBFF)
  | 0xB => Cpuid.topo c 0xB sub (0, 0, 0, 0)
  | 5 => (0x40, 0x40, 3, 0x11)
  | 6 => (4, 0, 1, 0)
  | 7 => if sub == 0 then (0, 0x219C01A9, 0x400004, 0) else (0, 0, 0, 0)
  | 0xD => Cpuid.leafD c sub
  | 0x80000000 => (0x8000000A, 0, 0, 0)
  | 0x80000001 => (0, 0, Cpuid.topoEcx81 c 0x204233FF, 0x2E500800)
  | 0x80000007 => (0, 0, 0, 0x100)
  | 0x80000008 => (0x3030, 0x0100D317, Cpuid.topoEcx88 c 0x707F, 0x10000)
  | 0x8000000A => (1, 0x8000, 0, 0x1194FD)
  | _ => (0, 0, 0, 0)

/-- CPUID with the present feature set: out-of-range leaves report leaf 0xD (Intel behaviour of the
legacy identity). -/
def presentCpuid (c : Cpu) (leaf sub : UInt32) : Regs :=
  let p := if leaf ≤ 0xD || (0x80000000 ≤ leaf && leaf ≤ 0x8000000A) then (leaf, sub) else (0xD, sub)
  sysALeaf c p.1 p.2

theorem legacyMax_former : Cpuid.legacyMax = (0xD, 0x8000000A) := by decide +kernel

/-- The former identity, for every leaf and subleaf, with the present feature set. -/
theorem legacyLeaf_former (c : Cpu) (leaf sub : UInt32) :
    Cpuid.legacyLeaf c leaf sub = presentCpuid c leaf sub := by
  simp only [Cpuid.legacyLeaf, legacyMax_former, presentCpuid]
  generalize (if leaf ≤ 0xD || (0x80000000 ≤ leaf && leaf ≤ 0x8000000A) then (leaf, sub)
    else ((0xD : UInt32), sub)) = p
  obtain ⟨l, s⟩ := p
  have h12 : Cpuid.featBits 1 0 2 true = 0x76F8120B := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x178BFBFF := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0x204233FF := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = 0x2E500800 := by decide
  have hc : implemented .clfsh = true := rfl
  by_cases h0 : l = 0
  · subst h0; rfl
  by_cases h1 : l = 1
  · subst h1; simp [h12, h13, hc, sysALeaf]
  by_cases h5 : l = 5
  · subst h5; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h6 : l = 6
  · subst h6; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h7 : l = 7
  · subst h7
    by_cases hs : s = 0
    · subst hs; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
    · simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf, hs]
  by_cases hb : l = 0xB
  · subst hb
    by_cases hs0 : s = 0 <;> by_cases hs1 : s = 1 <;>
      simp_all [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, Cpuid.topo, sysALeaf,
        show implemented .x2apic = true from rfl]
  by_cases hd : l = 0xD
  · subst hd; simp [Cpuid.amdLeaf, sysALeaf]
  by_cases h80 : l = 0x80000000
  · subst h80; rfl
  by_cases h81 : l = 0x80000001
  · subst h81; simp [he2, he3, sysALeaf]
  by_cases h87 : l = 0x80000007
  · subst h87; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h88 : l = 0x80000008
  · subst h88; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, Cpuid.topo, sysALeaf]
    exact ⟨by decide, by decide, congrArg _ (by decide), by decide⟩
  by_cases h8a : l = 0x8000000A
  · subst h8a; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, Cpuid.topo, sysALeaf,
      show implemented .svm = true from rfl]; decide
  simp only [sysALeaf]

/-! ## The final identity: AMD EPYC 7742 -/

/-- The leaves of the final identity other than 0 and 8000_0000h: the CPUID dump of a real 7742
(`Cpuid.raw`) with the masked features cleared — leaf 1 ECX: CX16; leaf 7 EBX: PQM, PQE; 8000_0001
ECX: IBS, PerfCtrExtCore, PerfCtrExtNb, DataBkptExt, PerfCtrExtLlc, AdMskExtn; 8000_0007: the
MCA-recovery and power-management bits; 8000_0008 EBX: INT_WBINVD, IbrsPreferred, IbrsSameMode, bits 6
and 10; 8000_000A EDX: LbrVirt, AVIC, GMET, bit 11; leaves 0Fh, 10h, 8000_001Bh, 8000_001Fh and
8000_0020h zero — with OSXSAVE from CR4, leaf 0xD computed (PKRU not reported) and the topology of
`Cpuid.topo`. -/
def amdTable (c : Cpu) (l sub : UInt32) : Regs :=
  match l with
  | 1 => (0x00830F10, Cpuid.topoEbx1 c 0x800, 0x76F8120B ||| Cpuid.osxsave c, Cpuid.topoEdx1 c 0x178BFBFF)
  | 5 => (0x40, 0x40, 3, 0x11)
  | 6 => (4, 0, 1, 0)
  | 7 => if sub == 0 then (0, 0x219C01A9, 0x400004, 0) else (0, 0, 0, 0)
  | 0xB => Cpuid.topo c 0xB sub (0, 0, 0, 0)
  | 0xD => Cpuid.leafD c sub
  | 0x80000001 => (0x00830F10, 0x40000000, Cpuid.topoEcx81 c 0x204233FF, 0x2FD3FBFF)
  | 0x80000002 => (0x20444D41, 0x43595045, 0x34373720, 0x34362032)
  | 0x80000003 => (0x726F432D, 0x72502065, 0x7365636F, 0x20726F73)
  | 0x80000004 => (0x20202020, 0x20202020, 0x20202020, 0x00202020)
  | 0x80000005 => (0xFF40FF40, 0xFF40FF40, 0x20080140, 0x20080140)
  | 0x80000006 => (0x48006400, 0x68006400, 0x02006140, 0x08009140)
  | 0x80000007 => (0, 0, 0, 0x100)
  | 0x80000008 => (0x3030, 0x0100D317, Cpuid.topoEcx88 c 0x707F, 0x10000)
  | 0x8000000A => (1, 0x8000, 0, 0x1194FD)
  | 0x80000019 => (0xF040F040, 0, 0, 0)
  | 0x8000001A => (6, 0, 0, 0)
  | 0x8000001D =>
    match sub with
    | 0 => Cpuid.topo c 0x8000001D 0 (0x4121, 0x01C0003F, 0x3F, 0)
    | 1 => Cpuid.topo c 0x8000001D 1 (0x4122, 0x01C0003F, 0x3F, 0)
    | 2 => Cpuid.topo c 0x8000001D 2 (0x4143, 0x01C0003F, 0x3FF, 2)
    | 3 => Cpuid.topo c 0x8000001D 3 (0x1C163, 0x03C0003F, 0x3FFF, 1)
    | _ => (0, 0, 0, 0)
  | 0x8000001E => Cpuid.topo c 0x8000001E sub (0, 0x100, 0, 0)
  | _ => (0, 0, 0, 0)

/-- CPUID of the final identity (`identity = .epyc7742`): "AuthenticAMD", highest leaves 10h and
8000_0020h, `amdTable` in range, zeros above (AMD returns zeros for unsupported leaves). -/
def epycCpuid (c : Cpu) (leaf sub : UInt32) : Regs :=
  if leaf == 0 then (0x10, 0x68747541, 0x444D4163, 0x69746E65)
  else if leaf == 0x80000000 then (0x80000020, 0x68747541, 0x444D4163, 0x69746E65)
  else if leaf ≤ 0x10 || (0x80000000 < leaf && leaf ≤ 0x80000020) then amdTable c leaf sub
  else (0, 0, 0, 0)

/-- A register without feature bits is reported as it is. -/
theorem maskReg_free {l s : UInt32} {k : Nat} (h : Cpuid.featBits l s k false = 0) (v : UInt32) :
    Cpuid.maskReg l s k v = v := by
  simp [Cpuid.maskReg, h]

set_option linter.unusedSimpArgs false in
theorem amdLeaf_epyc (c : Cpu) (l sub : UInt32) : Cpuid.amdLeaf c l sub = amdTable c l sub := by
  have gi : implemented .topoExt = true := rfl
  have gm : implemented .memEncrypt = false := rfl
  have gq : implemented .pqm = false := rfl
  have gp : implemented .pqe = false := rfl
  have gs : implemented .ibs = false := rfl
  have gt : implemented .svm = true := rfl
  have m10 : Cpuid.maskReg 1 0 0 0x00830F10 = 0x00830F10 := by decide
  have m11 : Cpuid.maskReg 1 0 1 0x00800800 = 0x00800800 := by decide
  have m12 : Cpuid.maskReg 1 0 2 0x7EF8320B &&& ~~~Cpuid.osxsaveBit = 0x76F8120B := by decide
  have m13 : Cpuid.maskReg 1 0 3 0x178BFBFF = 0x178BFBFF := by decide
  have m1b : (0x00800800 : UInt32) &&& 0xFFFF = 0x800 &&& 0xFFFF := by decide
  by_cases h1 : l = 1
  · subst h1
    simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, m10, m11, m12, m13, m1b, Cpuid.topoEbx1]
  by_cases h5 : l = 5
  · subst h5; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, show implemented .monitor = true from rfl]
    decide
  by_cases h6 : l = 6
  · subst h6; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable]; decide
  by_cases h7 : l = 7
  · subst h7
    by_cases hs : sub = 0
    · subst hs; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable]; decide
    · simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, hs]
  by_cases hb : l = 0xB
  · subst hb
    by_cases hs0 : sub = 0
    · subst hs0; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo]
    by_cases hs1 : sub = 1
    · subst hs1; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo]
    simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, hs0, hs1]
  by_cases hd : l = 0xD
  · subst hd; simp [Cpuid.amdLeaf, amdTable]
  by_cases e1 : l = 0x80000001
  · subst e1
    have a : Cpuid.maskReg 0x80000001 0 2 0x75C237FF = 0x204233FF := by decide
    have b : Cpuid.maskReg 0x80000001 0 3 0x2FD3FBFF &&& ~~~Feature.mirrorMask |||
        (Cpuid.featBits 1 0 3 true &&& Feature.mirrorMask) = 0x2FD3FBFF := by decide
    have z0 : Cpuid.maskReg 0x80000001 0 0 0x00830F10 = 0x00830F10 := by decide
    have z1 : Cpuid.maskReg 0x80000001 0 1 0x40000000 = 0x40000000 := by decide
    simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
    exact ⟨z0, z1, by rw [a], b⟩
  by_cases e2 : l = 0x80000002
  · subst e2; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e3 : l = 0x80000003
  · subst e3; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e4 : l = 0x80000004
  · subst e4; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e5 : l = 0x80000005
  · subst e5; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e6 : l = 0x80000006
  · subst e6; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e7 : l = 0x80000007
  · subst e7; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e8 : l = 0x80000008
  · subst e8
    have a : Cpuid.maskReg 0x80000008 0 2 0x707F = 0x707F := by decide
    simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
    exact ⟨by decide, by decide, by rw [a], by decide⟩
  by_cases ea : l = 0x8000000A
  · subst ea; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e19 : l = 0x80000019
  · subst e19; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e1a : l = 0x8000001A
  · subst e1a; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]; decide
  by_cases e1d : l = 0x8000001D
  · subst e1d
    have f0 := maskReg_free (l := 0x8000001D) (s := 0) (k := 0) (by decide)
    have f1 := maskReg_free (l := 0x8000001D) (s := 0) (k := 1) (by decide)
    have f2 := maskReg_free (l := 0x8000001D) (s := 0) (k := 2) (by decide)
    have f3 := maskReg_free (l := 0x8000001D) (s := 0) (k := 3) (by decide)
    by_cases s0 : sub = 0
    · subst s0; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, f0, f1, f2, f3]
    by_cases s1 : sub = 1
    · subst s1; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, f0, f1, f2, f3]
    by_cases s2 : sub = 2
    · subst s2; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, f0, f1, f2, f3]
    by_cases s3 : sub = 3
    · subst s3; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, f0, f1, f2, f3]
    simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt, s0, s1, s2, s3]
  by_cases e1e : l = 0x8000001E
  · subst e1e; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  -- the gated leaves of masked features
  by_cases hf : l = 0xF
  · subst hf; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  by_cases h10 : l = 0x10
  · subst h10; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  by_cases e1b : l = 0x8000001B
  · subst e1b; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  by_cases e1f : l = 0x8000001F
  · subst e1f; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  by_cases e20 : l = 0x80000020
  · subst e20; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, amdTable, Cpuid.topo, Cpuid.reg, gi, gm, gq, gp, gs, gt]
  -- every other leaf: no dump value, no gate
  have hg : Cpuid.leafGate l = none := by
    unfold Cpuid.leafGate; split <;> simp_all
  have hr : Cpuid.raw l sub = none := by
    unfold Cpuid.raw; split <;> simp_all
  have ht : amdTable c l sub = (0, 0, 0, 0) := by
    unfold amdTable; split <;> simp_all
  simp [Cpuid.amdLeaf, hg, hr, ht, hd]

/-- CPUID, for every leaf and subleaf, with the final identity (AMD EPYC 7742). -/
theorem cpuid_epyc (c : Cpu) (leaf sub : UInt32) : cpuid c leaf sub = epycCpuid c leaf sub := by
  simp only [cpuid, identity, epycCpuid, amdLeaf_epyc, Cpuid.amdMaxBasic, Cpuid.amdMaxExt]
  rfl

/-- The CPUID dump of a real EPYC 7742 (InstLatx64, `AuthenticAMD0830F10_K17_Rome_CPUID.txt`, logical
CPU #0: every leaf and subleaf it lists with a nonzero value; zeros elsewhere), transcribed here
independently of `Cpuid.raw`. It was taken under an OS: CR4.OSXSAVE = 1 and XCR0 = 7 (leaf 0xD.0 EBX
= 340h). -/
def dump7742 (leaf sub : UInt32) : Regs :=
  match leaf, sub with
  | 0x00000000, _ => (0x00000010, 0x68747541, 0x444D4163, 0x69746E65)
  | 0x00000001, _ => (0x00830F10, 0x00800800, 0x7EF8320B, 0x178BFBFF)
  | 0x00000005, _ => (0x00000040, 0x00000040, 0x00000003, 0x00000011)
  | 0x00000006, _ => (0x00000004, 0x00000000, 0x00000001, 0x00000000)
  | 0x00000007, 0 => (0x00000000, 0x219C91A9, 0x00400004, 0x00000000)
  | 0x0000000B, 0 => (0x00000001, 0x00000002, 0x00000100, 0x00000000)
  | 0x0000000B, 1 => (0x00000007, 0x00000080, 0x00000201, 0x00000000)
  | 0x0000000D, 0 => (0x00000207, 0x00000340, 0x00000380, 0x00000000)
  | 0x0000000D, 1 => (0x0000000F, 0x00000340, 0x00000000, 0x00000000)
  | 0x0000000D, 2 => (0x00000100, 0x00000240, 0x00000000, 0x00000000)
  | 0x0000000D, 9 => (0x00000040, 0x00000340, 0x00000000, 0x00000000)
  | 0x0000000F, 0 => (0x00000000, 0x000000FF, 0x00000000, 0x00000002)
  | 0x0000000F, 1 => (0x00000000, 0x00000040, 0x000000FF, 0x00000007)
  | 0x00000010, 0 => (0x00000000, 0x00000002, 0x00000000, 0x00000000)
  | 0x00000010, 1 => (0x0000000F, 0x00000000, 0x00000004, 0x0000000F)
  | 0x80000000, _ => (0x80000020, 0x68747541, 0x444D4163, 0x69746E65)
  | 0x80000001, _ => (0x00830F10, 0x40000000, 0x75C237FF, 0x2FD3FBFF)
  | 0x80000002, _ => (0x20444D41, 0x43595045, 0x34373720, 0x34362032)
  | 0x80000003, _ => (0x726F432D, 0x72502065, 0x7365636F, 0x20726F73)
  | 0x80000004, _ => (0x20202020, 0x20202020, 0x20202020, 0x00202020)
  | 0x80000005, _ => (0xFF40FF40, 0xFF40FF40, 0x20080140, 0x20080140)
  | 0x80000006, _ => (0x48006400, 0x68006400, 0x02006140, 0x08009140)
  | 0x80000007, _ => (0x00000000, 0x0000001B, 0x00000000, 0x00006799)
  | 0x80000008, _ => (0x00003030, 0x018EF757, 0x0000707F, 0x00010000)
  | 0x8000000A, _ => (0x00000001, 0x00008000, 0x00000000, 0x0013BCFF)
  | 0x80000019, _ => (0xF040F040, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001A, _ => (0x00000006, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001B, _ => (0x000003FF, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001D, 0 => (0x00004121, 0x01C0003F, 0x0000003F, 0x00000000)
  | 0x8000001D, 1 => (0x00004122, 0x01C0003F, 0x0000003F, 0x00000000)
  | 0x8000001D, 2 => (0x00004143, 0x01C0003F, 0x000003FF, 0x00000002)
  | 0x8000001D, 3 => (0x0001C163, 0x03C0003F, 0x00003FFF, 0x00000001)
  | 0x8000001E, _ => (0x00000000, 0x00000100, 0x00000000, 0x00000000)
  | 0x8000001F, _ => (0x0001000F, 0x0000016F, 0x000001FD, 0x00000001)
  | 0x80000020, _ => (0x00000000, 0x00000002, 0x00000000, 0x00000000)
  | _, _ => (0, 0, 0, 0)

/-- `Cpuid.raw` (the model's table) is the dump, for every leaf it lists and subleaves 0..9. -/
theorem raw_dump : ∀ l ∈ ([1, 5, 6, 7, 0xF, 0x10, 0x80000001, 0x80000002, 0x80000003, 0x80000004,
    0x80000005, 0x80000006, 0x80000007, 0x80000008, 0x8000000A, 0x80000019, 0x8000001A, 0x8000001B,
    0x8000001D, 0x8000001E, 0x8000001F, 0x80000020] : List UInt32),
    ∀ s ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List UInt32), (Cpuid.raw l s).getD (0, 0, 0, 0) = dump7742 l s := by
  decide

/-- The registers that hold feature flags (leaf, subleaf, register: 0 EAX .. 3 EDX), incl. the XCR0 and
IA32_XSS bits of leaf 0xD. -/
def featureRegs : List (UInt32 × UInt32 × Nat) :=
  [(1, 0, 2), (1, 0, 3), (6, 0, 0), (6, 0, 2), (7, 0, 1), (7, 0, 2), (7, 0, 3), (0xD, 0, 0), (0xD, 0, 3),
   (0xD, 1, 0), (0xD, 1, 2), (0xD, 1, 3), (0x80000001, 0, 2), (0x80000001, 0, 3), (0x80000007, 0, 1),
   (0x80000007, 0, 3), (0x80000008, 0, 1), (0x8000000A, 0, 3), (0x8000001F, 0, 0)]

/-- No invented feature bits: whatever the CPU state (CR4.OSXSAVE, XCR0, the number of CPUs, ...),
every feature bit CPUID reports is set in the dump of the real 7742. -/
theorem cpuid_epyc_dump (c : Cpu) :
    ∀ p ∈ featureRegs, Cpuid.reg (cpuid c p.1 p.2.1) p.2.2 &&& ~~~Cpuid.reg (dump7742 p.1 p.2.1) p.2.2 = 0 := by
  have hx : Cpuid.xcr0Supported = 7 := by decide
  have hf : Cpuid.featBits 0xD 1 0 true = 0xF := by decide
  simp only [featureRegs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, cpuid_epyc]
  simp [epycCpuid, amdTable, Cpuid.reg, dump7742, Cpuid.leafD, hx, hf, Cpuid.xssSupported,
    show implemented .xsave = true from rfl]
  refine ⟨?_, ?_, ?_⟩
  · unfold Cpuid.osxsave; split <;> decide
  · unfold Cpuid.topoEdx1; split <;> decide
  · unfold Cpuid.topoEcx81; split <;> decide

/-- The descriptive leaves are the dump's: vendor and maximum leaves, MONITOR line sizes, the brand
string, the L1/L2/L3 cache and TLB descriptors (8000_0005/6/19), the performance hints (8000_001A),
address sizes and RDPRU/INVLPGB limits (8000_0008 EAX, EDX), the SVM revision and ASID count. -/
theorem cpuid_epyc_descr (c : Cpu) (sub : UInt32) :
    (∀ l ∈ ([0, 5, 0x80000000, 0x80000002, 0x80000003, 0x80000004, 0x80000005, 0x80000006, 0x80000019,
      0x8000001A] : List UInt32), cpuid c l sub = dump7742 l sub) ∧
    (cpuid c 0x80000008 sub).1 = (dump7742 0x80000008 sub).1 ∧
    (cpuid c 0x80000008 sub).2.2.2 = (dump7742 0x80000008 sub).2.2.2 ∧
    (cpuid c 0x8000000A sub).1 = (dump7742 0x8000000A sub).1 ∧
    (cpuid c 0x8000000A sub).2.1 = (dump7742 0x8000000A sub).2.1 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, cpuid_epyc]
  simp [epycCpuid, amdTable, dump7742]

/-- MOV CR4 accepts the former bits, OSXSAVE (Xsave), UMIP, SMEP, SMAP (system A), FSGSBASE (long
mode) and VME, PVI (system B). -/
theorem cr4Writable_former :
    Cpuid.cr4Writable = 0x07FC ||| CR4.OSXSAVE ||| CR4.UMIP ||| CR4.SMEP ||| CR4.SMAP ||| CR4.FSGSBASE |||
      CR4.VME ||| CR4.PVI := by
  decide

/-- WRMSR EFER accepts NXE, system A's SCE, LMSLE, FFXSR, TCE, INTWB, Gpr's MCOMMIT, LME (long
mode; LMA is read-only, `LongMode.eferOk`) and SVME (SVM; MBZ while VM_CR.SVMDIS is set). -/
theorem eferWritable_former :
    Cpuid.eferWritable = EFER.NXE ||| EFER.SCE ||| EFER.LMSLE ||| EFER.FFXSR ||| EFER.TCE ||| EFER.INTWB |||
      EFER.MCOMMIT ||| EFER.LME ||| EFER.SVME := by
  decide

theorem vexExec_real {m : Machine} {i : Inst} (h : m.cpu.cr0 &&& CR0.PE = 0) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  simp [vexExec, cpu, Cpu.pe, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexExec_vm86 {m : Machine} {i : Inst} (h : m.cpu.eflags &&& Flag.VM ≠ 0) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  simp [vexExec, cpu, Cpu.vm86, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem vexExec_prefix {m : Machine} {i : Inst} (h : i.lock = true ∨ i.rep ≠ 0 ∨ i.p66 = true) :
    vexExec i m = .error (.exc Vec.UD none 0) m := by
  rcases h with h | h | h <;>
  · simp only [vexExec, cpu, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]
    split <;> simp_all [EStateM.bind, EStateM.throw]

end X86
