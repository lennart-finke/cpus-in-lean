import X86.Dispatch
import X86.Proofs.Basic
/-!
# Foundation of the Zen 2 extensions

* `cpuid_former`: with the present feature set and the legacy identity, CPUID returns exactly
  `presentCpuid`, for every leaf and subleaf: the model's former values (`formerCpuid`, the removed
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
RDPID, ABM, PREFETCHW, MONITORX, RDTSCP, CLZERO, IRPERF, RDPRU, WBNOINVD, MCOMMIT) and system A
(SYSENTER, SYSCALL, TSC, PSE, PSE-36, PGE, MCE, MCA, MTRR, PAT, SMEP, SMAP, UMIP, AltMovCr8, FFXSR,
TCE, OSVW, WDT, invariant TSC, ARAT, EffFreq, IBPB/IBRS/STIBP/SSBD): highest leaves 7 and
0x80000008. -/
def sysALeaf (l sub : UInt32) : Regs :=
  match l with
  | 0 => (7, 0x756E6547, 0x6C65746E, 0x49656E69)
  | 1 => (0x619, 0x800, 0x40C00008, 0x078BFBFD)
  | 5 => (0x40, 0x40, 3, 0x11)
  | 6 => (4, 0, 1, 0)
  | 7 => if sub == 0 then (0, 0x19C0188, 0x400004, 0) else (0, 0, 0, 0)
  | 0x80000000 => (0x80000008, 0, 0, 0)
  | 0x80000001 => (0, 0, 0x20022330, 0x0A100800)
  | 0x80000007 => (0, 0, 0, 0x100)
  | 0x80000008 => (0x3030, 0x0102D311, 0x707F, 0x10000)
  | _ => (0, 0, 0, 0)

/-- CPUID with the present feature set: out-of-range leaves report leaf 7 (Intel behaviour of the
legacy identity). -/
def presentCpuid (leaf sub : UInt32) : Regs :=
  let p := if leaf ≤ 7 || (0x80000000 ≤ leaf && leaf ≤ 0x80000008) then (leaf, sub) else (7, sub)
  sysALeaf p.1 p.2

set_option maxRecDepth 100000 in
theorem legacyMax_former : Cpuid.legacyMax = (7, 0x80000008) := by decide

set_option maxRecDepth 100000 in
theorem cpuid_former (c : Cpu) (leaf sub : UInt32) : cpuid c leaf sub = presentCpuid leaf sub := by
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, presentCpuid]
  generalize (if leaf ≤ 7 || (0x80000000 ≤ leaf && leaf ≤ 0x80000008) then (leaf, sub)
    else ((7 : UInt32), sub)) = p
  obtain ⟨l, s⟩ := p
  have hx : implemented .xsave = false := rfl
  have h12 : Cpuid.featBits 1 0 2 true = 0x40C00008 := by decide
  have h13 : Cpuid.featBits 1 0 3 true = 0x078BFBFD := by decide
  have he2 : Cpuid.featBits 0x80000001 0 2 true = 0x20022330 := by decide
  have he3 : Cpuid.featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask = 0x0A100800 := by decide
  have hc : implemented .clfsh = true := rfl
  by_cases h0 : l = 0
  · subst h0; rfl
  by_cases h1 : l = 1
  · subst h1; simp [h12, h13, hx, hc, sysALeaf]
  by_cases h5 : l = 5
  · subst h5; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h6 : l = 6
  · subst h6; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h7 : l = 7
  · subst h7
    by_cases hs : s = 0
    · subst hs; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
    · simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf, hs]
  by_cases hd : l = 0xD
  · subst hd; simp [Cpuid.amdLeaf, Cpuid.leafD, hx, sysALeaf]
  by_cases h80 : l = 0x80000000
  · subst h80; rfl
  by_cases h81 : l = 0x80000001
  · subst h81; simp [he2, he3, sysALeaf]
  by_cases h87 : l = 0x80000007
  · subst h87; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h88 : l = 0x80000008
  · subst h88; simp [Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, sysALeaf]; decide
  by_cases h8a : l = 0x8000000A
  · subst h8a; simp [Cpuid.amdLeaf, Cpuid.leafGate, sysALeaf, show implemented .svm = false from rfl]
  simp only [sysALeaf]

/-- MOV CR4 accepts the former bits and UMIP, SMEP, SMAP (system A). -/
theorem cr4Writable_former : Cpuid.cr4Writable = 0x07FC ||| CR4.UMIP ||| CR4.SMEP ||| CR4.SMAP := by decide

/-- WRMSR EFER accepts NXE, system A's SCE, LMSLE, FFXSR, TCE, INTWB and Gpr's MCOMMIT. -/
theorem eferWritable_former :
    Cpuid.eferWritable = EFER.NXE ||| EFER.SCE ||| EFER.LMSLE ||| EFER.FFXSR ||| EFER.TCE ||| EFER.INTWB |||
      EFER.MCOMMIT := by
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
