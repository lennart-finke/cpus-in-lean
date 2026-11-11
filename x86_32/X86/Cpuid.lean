import X86.State
/-!
# CPUID

Table-driven CPUID (leaf in EAX, subleaf in ECX) with the structure of an AMD EPYC 7742 (Zen 2,
family 17h model 31h stepping 0, "Rome" B0, signature 00830F10h).

**Source of the raw values** (`raw`): the CPUID dump of a real EPYC 7742, logical CPU #0, in
InstLatx64, `AuthenticAMD/AuthenticAMD0830F10_K17_Rome_CPUID.txt`
(https://github.com/InstLatx64/InstLatx64). Bit names follow the AMD64 APM vol. 3, appendix E
(CPUID Fn0000_0001, Fn0000_0007, Fn8000_0001, ...); the signature 00830F10h (Rome-B0) is also in
AMD's revision guide for family 17h models 30h–3Fh (pub. 56323). Where a bit of the dump could not
be given a name from a source, it is grouped into a feature marked UNCONFIRMED below.

**Feature bits are reported only for implemented features** (`implemented`). The raw value of a
feature register is masked by the features that are not implemented; registers without feature bits
(cache and TLB descriptors, address sizes, topology) are reported as in the dump. Leaves that only
describe a feature (5 MONITOR, 0xD XSAVE, 0x8000000A SVM, ...) are all zero while the feature is not
implemented.

**Identity** (`identity`): until the integration step, the vendor, signature and leaf structure stay
those of the model's former identity (`.legacy`: "GenuineIntel", family 6 model 1 stepping 9,
0x619, highest leaves 1 and 0x80000001 while no feature needs more, out-of-range leaves return the
highest basic leaf as on Intel CPUs). With exactly today's features this reproduces the former
`cpuidVals` bit for bit. `.epyc7742` reports the AMD identity.

To add a feature: flip its line in `implemented` to `true` (one line per feature, grouped by the
owning module; see `x86_32/EXTENDING.md`).
-/
namespace X86

/-- Model identity reported by CPUID leaves 0, 1 and 0x8000000x. -/
inductive Identity where
  /-- The former identity: "GenuineIntel", signature 0x619. -/
  | legacy
  /-- AMD EPYC 7742: "AuthenticAMD", signature 0x00830F10, the 7742 brand string. -/
  | epyc7742
  deriving DecidableEq, Repr

/-- THE identity switch (flipped to `.epyc7742` by the integration step). -/
def identity : Identity := .legacy

/-- One constructor per CPUID feature bit (or group of bits) of the EPYC 7742. -/
inductive Feature where
  -- CPUID 1:EDX
  | fpu | vme | de | pse | tsc | msr | pae | mce | cx8 | apic | sep | mtrr | pge | mca | cmov | pat
  | pse36 | clfsh | mmx | fxsr | sse | sse2 | htt
  -- CPUID 1:ECX (OSXSAVE, bit 27, is not a feature: it reflects CR4.OSXSAVE)
  | sse3 | pclmulqdq | monitor | ssse3 | fma | cx16 | sse41 | sse42 | x2apic | movbe | popcnt
  | aes | xsave | avx | f16c | rdrand
  -- CPUID 6
  | arat | effFreq
  -- CPUID 7.0:EBX, ECX
  | fsgsbase | bmi1 | avx2 | smep | bmi2 | pqm | pqe | rdseed | adx | smap | clflushopt | clwb | sha
  | umip | rdpid
  -- CPUID 0xD.1:EAX
  | xsaveopt | xsavec | xgetbv1 | xsaves
  -- CPUID 8000_0001:ECX
  | lahfsahf | cmpLegacy | svm | extApicSpace | altMovCr8 | abm | sse4a | misalignSse | prefetchw
  | osvw | ibs | skinit | wdt | tce | topoExt | perfCtrExtCore | perfCtrExtNb | dataBkptExt
  | perfCtrExtLlc | mwaitx | adMskExtn
  -- CPUID 8000_0001:EDX (bits 0–9, 12–17, 23, 24 mirror CPUID 1:EDX on AMD)
  | syscall | nx | mmxext | ffxsr | page1gb | rdtscp | lm
  -- CPUID 8000_0007
  | invariantTsc | powerMgmt | mcaRecovery
  -- CPUID 8000_0008:EBX
  | clzero | irPerf | xsaveErPtr | rdpru | wbnoinvd | ibpb | ibrs | stibp | stibpAlwaysOn | ppin
  | ssbd | ext8Misc
  -- CPUID 8000_000A (SVM revision and features) and 8000_001F (memory encryption)
  | svmFeatures | memEncrypt
  deriving DecidableEq, Repr, Inhabited

namespace Feature

/-- All features (in declaration order). -/
def all : List Feature := [
  fpu, vme, de, pse, tsc, msr, pae, mce, cx8, apic, sep, mtrr, pge, mca, cmov, pat, pse36, clfsh,
  mmx, fxsr, sse, sse2, htt,
  sse3, pclmulqdq, monitor, ssse3, fma, cx16, sse41, sse42, x2apic, movbe, popcnt, aes, xsave, avx,
  f16c, rdrand,
  arat, effFreq,
  fsgsbase, bmi1, avx2, smep, bmi2, pqm, pqe, rdseed, adx, smap, clflushopt, clwb, sha, umip, rdpid,
  xsaveopt, xsavec, xgetbv1, xsaves,
  lahfsahf, cmpLegacy, svm, extApicSpace, altMovCr8, abm, sse4a, misalignSse, prefetchw, osvw, ibs,
  skinit, wdt, tce, topoExt, perfCtrExtCore, perfCtrExtNb, dataBkptExt, perfCtrExtLlc, mwaitx,
  adMskExtn,
  syscall, nx, mmxext, ffxsr, page1gb, rdtscp, lm,
  invariantTsc, powerMgmt, mcaRecovery,
  clzero, irPerf, xsaveErPtr, rdpru, wbnoinvd, ibpb, ibrs, stibp, stibpAlwaysOn, ppin, ssbd, ext8Misc,
  svmFeatures, memEncrypt]

/-- Where CPUID reports the feature: leaf, subleaf, register (0 EAX, 1 EBX, 2 ECX, 3 EDX), bits. -/
def loc : Feature → UInt32 × UInt32 × Nat × UInt32
  | fpu => (1, 0, 3, 1 <<< 0) | vme => (1, 0, 3, 1 <<< 1) | de => (1, 0, 3, 1 <<< 2)
  | pse => (1, 0, 3, 1 <<< 3) | tsc => (1, 0, 3, 1 <<< 4) | msr => (1, 0, 3, 1 <<< 5)
  | pae => (1, 0, 3, 1 <<< 6) | mce => (1, 0, 3, 1 <<< 7) | cx8 => (1, 0, 3, 1 <<< 8)
  | apic => (1, 0, 3, 1 <<< 9) | sep => (1, 0, 3, 1 <<< 11) | mtrr => (1, 0, 3, 1 <<< 12)
  | pge => (1, 0, 3, 1 <<< 13) | mca => (1, 0, 3, 1 <<< 14) | cmov => (1, 0, 3, 1 <<< 15)
  | pat => (1, 0, 3, 1 <<< 16) | pse36 => (1, 0, 3, 1 <<< 17) | clfsh => (1, 0, 3, 1 <<< 19)
  | mmx => (1, 0, 3, 1 <<< 23) | fxsr => (1, 0, 3, 1 <<< 24) | sse => (1, 0, 3, 1 <<< 25)
  | sse2 => (1, 0, 3, 1 <<< 26) | htt => (1, 0, 3, 1 <<< 28)
  | sse3 => (1, 0, 2, 1 <<< 0) | pclmulqdq => (1, 0, 2, 1 <<< 1) | monitor => (1, 0, 2, 1 <<< 3)
  | ssse3 => (1, 0, 2, 1 <<< 9) | fma => (1, 0, 2, 1 <<< 12) | cx16 => (1, 0, 2, 1 <<< 13)
  | sse41 => (1, 0, 2, 1 <<< 19) | sse42 => (1, 0, 2, 1 <<< 20) | x2apic => (1, 0, 2, 1 <<< 21)
  | movbe => (1, 0, 2, 1 <<< 22) | popcnt => (1, 0, 2, 1 <<< 23) | aes => (1, 0, 2, 1 <<< 25)
  | xsave => (1, 0, 2, 1 <<< 26) | avx => (1, 0, 2, 1 <<< 28) | f16c => (1, 0, 2, 1 <<< 29)
  | rdrand => (1, 0, 2, 1 <<< 30)
  | arat => (6, 0, 0, 1 <<< 2) | effFreq => (6, 0, 2, 1 <<< 0)
  | fsgsbase => (7, 0, 1, 1 <<< 0) | bmi1 => (7, 0, 1, 1 <<< 3) | avx2 => (7, 0, 1, 1 <<< 5)
  | smep => (7, 0, 1, 1 <<< 7) | bmi2 => (7, 0, 1, 1 <<< 8) | pqm => (7, 0, 1, 1 <<< 12)
  | pqe => (7, 0, 1, 1 <<< 15) | rdseed => (7, 0, 1, 1 <<< 18) | adx => (7, 0, 1, 1 <<< 19)
  | smap => (7, 0, 1, 1 <<< 20) | clflushopt => (7, 0, 1, 1 <<< 23) | clwb => (7, 0, 1, 1 <<< 24)
  | sha => (7, 0, 1, 1 <<< 29) | umip => (7, 0, 2, 1 <<< 2) | rdpid => (7, 0, 2, 1 <<< 22)
  | xsaveopt => (0xD, 1, 0, 1 <<< 0) | xsavec => (0xD, 1, 0, 1 <<< 1)
  | xgetbv1 => (0xD, 1, 0, 1 <<< 2) | xsaves => (0xD, 1, 0, 1 <<< 3)
  | lahfsahf => (0x80000001, 0, 2, 1 <<< 0) | cmpLegacy => (0x80000001, 0, 2, 1 <<< 1)
  | svm => (0x80000001, 0, 2, 1 <<< 2) | extApicSpace => (0x80000001, 0, 2, 1 <<< 3)
  | altMovCr8 => (0x80000001, 0, 2, 1 <<< 4) | abm => (0x80000001, 0, 2, 1 <<< 5)
  | sse4a => (0x80000001, 0, 2, 1 <<< 6) | misalignSse => (0x80000001, 0, 2, 1 <<< 7)
  | prefetchw => (0x80000001, 0, 2, 1 <<< 8) | osvw => (0x80000001, 0, 2, 1 <<< 9)
  | ibs => (0x80000001, 0, 2, 1 <<< 10) | skinit => (0x80000001, 0, 2, 1 <<< 12)
  | wdt => (0x80000001, 0, 2, 1 <<< 13) | tce => (0x80000001, 0, 2, 1 <<< 17)
  | topoExt => (0x80000001, 0, 2, 1 <<< 22) | perfCtrExtCore => (0x80000001, 0, 2, 1 <<< 23)
  | perfCtrExtNb => (0x80000001, 0, 2, 1 <<< 24) | dataBkptExt => (0x80000001, 0, 2, 1 <<< 26)
  | perfCtrExtLlc => (0x80000001, 0, 2, 1 <<< 28) | mwaitx => (0x80000001, 0, 2, 1 <<< 29)
  | adMskExtn => (0x80000001, 0, 2, 1 <<< 30)
  | syscall => (0x80000001, 0, 3, 1 <<< 11) | nx => (0x80000001, 0, 3, 1 <<< 20)
  | mmxext => (0x80000001, 0, 3, 1 <<< 22) | ffxsr => (0x80000001, 0, 3, 1 <<< 25)
  | page1gb => (0x80000001, 0, 3, 1 <<< 26) | rdtscp => (0x80000001, 0, 3, 1 <<< 27)
  | lm => (0x80000001, 0, 3, 1 <<< 29)
  | invariantTsc => (0x80000007, 0, 3, 1 <<< 8)
  -- the other power-management bits of the dump (0x6799 without TscInvariant): TS, TTP, TM,
  -- HwPstate, CPB, EffFreqRO, ConnectedStandby, RAPL
  | powerMgmt => (0x80000007, 0, 3, 0x6699)
  -- McaOverflowRecov, SUCCOR, ScalableMca and bit 4 of the dump's EBX = 0x1B (bit 4 UNCONFIRMED)
  | mcaRecovery => (0x80000007, 0, 1, 0x1B)
  | clzero => (0x80000008, 0, 1, 1 <<< 0) | irPerf => (0x80000008, 0, 1, 1 <<< 1)
  | xsaveErPtr => (0x80000008, 0, 1, 1 <<< 2) | rdpru => (0x80000008, 0, 1, 1 <<< 4)
  | wbnoinvd => (0x80000008, 0, 1, 1 <<< 9) | ibpb => (0x80000008, 0, 1, 1 <<< 12)
  | ibrs => (0x80000008, 0, 1, 1 <<< 14) | stibp => (0x80000008, 0, 1, 1 <<< 15)
  | stibpAlwaysOn => (0x80000008, 0, 1, 1 <<< 17) | ppin => (0x80000008, 0, 1, 1 <<< 23)
  | ssbd => (0x80000008, 0, 1, 1 <<< 24)
  -- UNCONFIRMED: the remaining bits set in the dump's 8000_0008:EBX = 0x018EF757 (6, 8, 10, 13,
  -- 18, 19), whose names could not be confirmed from a source
  | ext8Misc => (0x80000008, 0, 1, 0x000C2540)
  -- SVM feature identifiers 8000_000A:EDX (NP, LbrVirt, SVML, NRIPS, TscRateMsr, VmcbClean,
  -- FlushByAsid, DecodeAssists, PauseFilter, ... as in the dump); the whole leaf is gated by `svm`
  | svmFeatures => (0x8000000A, 0, 3, 0x0013BCFF)
  -- SME/SEV capabilities 8000_001F:EAX; the whole leaf is gated by `memEncrypt`
  | memEncrypt => (0x8000001F, 0, 0, 0x0001000F)

/-- Bits of CPUID 8000_0001:EDX that AMD CPUs copy from CPUID 1:EDX (APM vol. 3, E.4.2); reported
only with the AMD identity. -/
def mirrorMask : UInt32 := 0x0183F3FF

end Feature

/-! ## Implemented features

ONE LINE PER FEATURE, grouped by the module that implements it (`EXTENDING.md`). A workstream flips
its own lines to `true` when its feature is complete (and tested); groups are separated by comment
lines so that parallel edits merge without conflicts. Present-day behaviour: exactly the first group. -/

/-- The features the model implements; CPUID reports exactly these. -/
def implemented : Feature → Bool
  -- implemented before the Zen 2 work (core model)
  | .fpu => true
  | .de => true
  | .msr => true
  | .pae => true
  | .cx8 => true
  | .apic => true
  | .cmov => true
  | .mmx => true
  | .fxsr => true
  | .sse => true
  | .sse2 => true
  | .nx => true
  -- X86/Ext/Gpr.lean
  | .popcnt => false
  | .abm => false
  | .bmi1 => false
  | .bmi2 => false
  | .adx => false
  | .movbe => false
  | .rdrand => false
  | .rdseed => false
  | .rdpid => false
  | .rdtscp => false
  | .clfsh => false
  | .clflushopt => false
  | .clwb => false
  | .clzero => false
  | .wbnoinvd => false
  | .monitor => false
  | .mwaitx => false
  | .prefetchw => false
  | .rdpru => false
  | .irPerf => false
  -- X86/Ext/Sse.lean
  | .sse3 => false
  | .ssse3 => false
  | .sse41 => false
  | .sse42 => false
  | .sse4a => false
  | .misalignSse => false
  -- X86/Ext/Crypto.lean
  | .aes => false
  | .pclmulqdq => false
  | .sha => false
  -- X86/Ext/Xsave.lean
  | .xsave => false
  | .xsaveopt => false
  | .xsavec => false
  | .xgetbv1 => false
  | .xsaves => false
  | .xsaveErPtr => false
  -- X86/Ext/Avx.lean
  | .avx => false
  -- X86/Ext/Avx2.lean
  | .avx2 => false
  | .fma => false
  | .f16c => false
  -- X86/Ext/Sys.lean (system A: SYSENTER/SYSCALL, MSRs, SMEP/SMAP/UMIP, paging features)
  | .tsc => true
  | .pse => true
  | .pge => true
  | .pse36 => true
  | .mce => true
  | .mca => true
  | .mtrr => true
  | .pat => true
  | .sep => true
  | .syscall => true
  | .ffxsr => true
  | .smep => true
  | .smap => true
  | .umip => true
  | .altMovCr8 => true
  | .tce => true
  | .osvw => true
  | .wdt => true
  | .invariantTsc => true
  | .arat => true
  | .effFreq => true
  | .mcaRecovery => false
  | .perfCtrExtCore => false
  | .dataBkptExt => false
  | .adMskExtn => false
  | .ibpb => true
  | .ibrs => true
  | .stibp => true
  | .stibpAlwaysOn => true
  | .ssbd => true
  | .ext8Misc => false
  -- system B (VME/PVI, NMI)
  | .vme => false
  -- X86/Ext/LongMode.lean
  | .lm => false
  | .page1gb => false
  | .lahfsahf => false
  | .cx16 => false
  | .fsgsbase => false
  -- X86/Ext/Smp.lean
  | .x2apic => false
  | .htt => false
  | .cmpLegacy => false
  | .topoExt => false
  | .extApicSpace => false
  -- X86/Ext/Svm.lean
  | .svm => false
  | .svmFeatures => false
  | .skinit => false
  -- integration (no new semantics needed; MMX extensions are part of X86/Simd.lean)
  | .mmxext => false
  -- not planned (Zen 2 has them; outside the model's scope)
  | .pqm => false
  | .pqe => false
  | .ibs => false
  | .perfCtrExtNb => false
  | .perfCtrExtLlc => false
  | .powerMgmt => false
  | .ppin => false
  | .memEncrypt => false

/-! ## Control-register masks derived from the features -/

namespace Cpuid

@[inline] private def ifImpl (f : Feature) (bits : UInt32) : UInt32 := if implemented f then bits else 0

/-- CR4 bits that MOV CR4 accepts (others #GP(0)). TSD, DE, PSE, PAE, MCE, PGE, PCE, OSFXSR and
OSXMMEXCPT (0x07FC) are accepted as before; the others follow the features. -/
def cr4Writable : UInt32 :=
  0x07FC ||| ifImpl .vme (CR4.VME ||| CR4.PVI) ||| ifImpl .umip CR4.UMIP |||
  ifImpl .fsgsbase CR4.FSGSBASE ||| ifImpl .xsave CR4.OSXSAVE ||| ifImpl .smep CR4.SMEP |||
  ifImpl .smap CR4.SMAP

/-- EFER bits that WRMSR accepts (others #GP(0)). LMA is set by the processor (long-mode work). -/
def eferWritable : UInt32 :=
  ifImpl .nx EFER.NXE ||| ifImpl .syscall EFER.SCE ||| ifImpl .lm EFER.LME |||
  ifImpl .svm EFER.SVME ||| ifImpl .ffxsr EFER.FFXSR ||| ifImpl .tce EFER.TCE |||
  -- system A: EFER bits of the 7742 without a feature of their own, writable with no effect outside
  -- long mode / on the model: LMSLE (8000_0008:EBX[EferLmsleUnsupported] = 0) and INTWB
  -- (8000_0008:EBX[INT_WBINVD] = 1; WBINVD has no duration in the model)
  ifImpl .syscall (EFER.LMSLE ||| EFER.INTWB)

/-- XCR0 bits the processor supports (CPUID 0xD.0:EDX:EAX): x87 and SSE with XSAVE, AVX state
with AVX. (The 7742 also reports PKRU, bit 9, in leaf 0xD although CPUID 7:ECX.PKU is 0; the
model has no PKRU.) -/
def xcr0Supported : UInt64 :=
  if implemented .xsave then XCR0.X87 ||| XCR0.SSE ||| (if implemented .avx then XCR0.YMM else 0)
  else 0

/-- Size of the standard-format XSAVE area for the components in `mask` (SDM vol. 1, 13.4:
legacy region 512 bytes, header 64, AVX state at offset 576, 256 bytes). -/
def xsaveSize (mask : UInt64) : UInt32 := if mask &&& XCR0.YMM != 0 then 0x340 else 0x240

end Cpuid

/-! ## Leaves -/

abbrev Regs := UInt32 × UInt32 × UInt32 × UInt32

namespace Cpuid

/-- Highest standard and extended leaves of the 7742 (dump). -/
def amdMaxBasic : UInt32 := 0x10
def amdMaxExt : UInt32 := 0x80000020

/-- The dump's values (logical CPU #0); `none` = all zero. Leaf 1 EBX = 0x00800800: CLFLUSH line
8 × 8 bytes, 128 logical processors, initial APIC ID 0; leaf 0xB and 8000_001E describe the
topology of CPU 0 (SMP work owns them). Leaf 0xD is computed (`leafD`). -/
def raw (leaf sub : UInt32) : Option Regs :=
  match leaf with
  | 0x00000001 => some (0x00830F10, 0x00800800, 0x7EF8320B, 0x178BFBFF)
  | 0x00000005 => some (0x00000040, 0x00000040, 0x00000003, 0x00000011)
  | 0x00000006 => some (0x00000004, 0x00000000, 0x00000001, 0x00000000)
  | 0x00000007 => if sub == 0 then some (0x00000000, 0x219C91A9, 0x00400004, 0x00000000) else none
  | 0x0000000B =>
    if sub == 0 then some (0x00000001, 0x00000002, 0x00000100, 0x00000000)
    else if sub == 1 then some (0x00000007, 0x00000080, 0x00000201, 0x00000000)
    else some (0, 0, sub &&& 0xFF, 0)  -- invalid level: ECX[7:0] echoes the input (SDM CPUID leaf 0BH)
  | 0x0000000F =>
    if sub == 0 then some (0x00000000, 0x000000FF, 0x00000000, 0x00000002)
    else if sub == 1 then some (0x00000000, 0x00000040, 0x000000FF, 0x00000007) else none
  | 0x00000010 =>
    if sub == 0 then some (0x00000000, 0x00000002, 0x00000000, 0x00000000)
    else if sub == 1 then some (0x0000000F, 0x00000000, 0x00000004, 0x0000000F) else none
  | 0x80000001 => some (0x00830F10, 0x40000000, 0x75C237FF, 0x2FD3FBFF)
  -- "AMD EPYC 7742 64-Core Processor" padded with spaces
  | 0x80000002 => some (0x20444D41, 0x43595045, 0x34373720, 0x34362032)
  | 0x80000003 => some (0x726F432D, 0x72502065, 0x7365636F, 0x20726F73)
  | 0x80000004 => some (0x20202020, 0x20202020, 0x20202020, 0x00202020)
  | 0x80000005 => some (0xFF40FF40, 0xFF40FF40, 0x20080140, 0x20080140)
  | 0x80000006 => some (0x48006400, 0x68006400, 0x02006140, 0x08009140)
  | 0x80000007 => some (0x00000000, 0x0000001B, 0x00000000, 0x00006799)
  | 0x80000008 => some (0x00003030, 0x018EF757, 0x0000707F, 0x00010000)
  | 0x8000000A => some (0x00000001, 0x00008000, 0x00000000, 0x0013BCFF)
  | 0x80000019 => some (0xF040F040, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001A => some (0x00000006, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001B => some (0x000003FF, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001D =>
    match sub with
    | 0 => some (0x00004121, 0x01C0003F, 0x0000003F, 0x00000000)
    | 1 => some (0x00004122, 0x01C0003F, 0x0000003F, 0x00000000)
    | 2 => some (0x00004143, 0x01C0003F, 0x000003FF, 0x00000002)
    | 3 => some (0x0001C163, 0x03C0003F, 0x00003FFF, 0x00000001)
    | _ => none
  | 0x8000001E => some (0x00000000, 0x00000100, 0x00000000, 0x00000000)
  | 0x8000001F => some (0x0001000F, 0x0000016F, 0x000001FD, 0x00000001)
  | 0x80000020 => some (0x00000000, 0x00000002, 0x00000000, 0x00000000)
  | _ => none

/-- Leaves that only describe one feature: all zero unless it is implemented. -/
def leafGate (leaf : UInt32) : Option Feature :=
  match leaf with
  | 0x5 => some .monitor
  | 0xF => some .pqm
  | 0x10 => some .pqe
  | 0x8000000A => some .svm
  | 0x8000001B => some .ibs
  | 0x8000001D | 0x8000001E => some .topoExt
  | 0x8000001F => some .memEncrypt
  | 0x80000020 => some .pqe
  | _ => none

@[inline] private def reg (r : Regs) (k : Nat) : UInt32 :=
  match k with | 0 => r.1 | 1 => r.2.1 | 2 => r.2.2.1 | _ => r.2.2.2

/-- Feature bits at (leaf, subleaf, register): all of them, and the implemented ones. -/
def featBits (leaf sub : UInt32) (k : Nat) (onlyImpl : Bool) : UInt32 :=
  Feature.all.foldl (fun acc f =>
    let (l, s, r, m) := f.loc
    if l == leaf && s == sub && r == k && (!onlyImpl || implemented f) then acc ||| m else acc) 0

/-- A raw register with the bits of unimplemented features cleared. -/
def maskReg (leaf sub : UInt32) (k : Nat) (v : UInt32) : UInt32 :=
  v &&& ~~~(featBits leaf sub k false &&& ~~~featBits leaf sub k true)

/-- Leaf 0xD (XSAVE), computed from the supported components, XCR0 and IA32_XSS. -/
def leafD (c : Cpu) (sub : UInt32) : Regs :=
  if !implemented .xsave then (0, 0, 0, 0)
  else match sub with
    | 0 => (xcr0Supported.toUInt32, xsaveSize c.xcr0, xsaveSize xcr0Supported, (xcr0Supported >>> 32).toUInt32)
    | 1 => (featBits 0xD 1 0 true, xsaveSize (c.xcr0 ||| c.xss), 0, 0)
    | 2 => if implemented .avx then (0x100, 0x240, 0, 0) else (0, 0, 0, 0)
    | _ => (0, 0, 0, 0)

/-- A leaf as reported with the AMD structure (feature-masked dump values), for a leaf in range. -/
def amdLeaf (c : Cpu) (leaf sub : UInt32) : Regs :=
  if leaf == 0xD then leafD c sub
  else if (leafGate leaf).any (!implemented ·) then (0, 0, 0, 0)
  else match raw leaf sub with
    | none => (0, 0, 0, 0)
    | some r =>
      -- feature bits are located by subleaf only in leaves 7 and 0xD; the others ignore ECX, so
      -- their bits are masked as for subleaf 0 whatever the subleaf (system A fix)
      let ms := if leaf == 7 || leaf == 0xD then sub else 0
      let a := maskReg leaf ms 0 (reg r 0)
      let b := maskReg leaf ms 1 (reg r 1)
      let cx := maskReg leaf ms 2 (reg r 2)
      let d := maskReg leaf ms 3 (reg r 3)
      -- 8000_0001:EDX bits that mirror 1:EDX
      let d := if leaf == 0x80000001 then d &&& ~~~Feature.mirrorMask ||| (featBits 1 0 3 true &&& Feature.mirrorMask) else d
      -- OSXSAVE reflects CR4.OSXSAVE
      let cx := if leaf == 1 && implemented .xsave && c.cr4 &&& CR4.OSXSAVE != 0 then cx ||| (1 <<< 27) else cx
      (a, b, cx, d)

/-- Highest basic and extended leaves of the legacy identity: 1 and 0x80000001 unless an implemented
feature is reported in a higher leaf. -/
def legacyMax : UInt32 × UInt32 :=
  Feature.all.foldl (fun (mb, me) f =>
    if !implemented f then (mb, me) else
    -- the leaf the feature needs: its bit, or the leaf describing it
    let l := match f with | .xsave => 0xD | .monitor => 5 | .svm => 0x8000000A | _ => f.loc.1
    if l < 0x80000000 then (max mb l, me) else (mb, max me l)) (1, 0x80000001)

/-- The legacy identity (see the module documentation). -/
def legacyLeaf (c : Cpu) (leaf sub : UInt32) : Regs :=
  let (mb, me) := legacyMax
  let inRange := leaf ≤ mb || (0x80000000 ≤ leaf && leaf ≤ me)
  -- out of range: the highest basic leaf (Intel)
  let (leaf, sub) := if inRange then (leaf, sub) else (mb, sub)
  match leaf with
  | 0 => (mb, 0x756E6547, 0x6C65746E, 0x49656E69)  -- "GenuineIntel"
  | 1 =>
    let osx : UInt32 := if implemented .xsave && c.cr4 &&& CR4.OSXSAVE != 0 then 1 <<< 27 else 0
    (0x00000619, 0, featBits 1 0 2 true ||| osx, featBits 1 0 3 true)
  | 0x80000000 => (me, 0, 0, 0)
  | 0x80000001 => (0, 0, featBits 0x80000001 0 2 true, featBits 0x80000001 0 3 true &&& ~~~Feature.mirrorMask)
  | 5 | 6 | 7 | 0xD | 0x80000007 | 0x80000008 | 0x8000000A => amdLeaf c leaf sub
  | _ => (0, 0, 0, 0)

end Cpuid

/-- CPUID: EAX, EBX, ECX, EDX for leaf `leaf` (EAX) and subleaf `sub` (ECX). -/
def cpuid (c : Cpu) (leaf sub : UInt32) : Regs :=
  match identity with
  | .legacy => Cpuid.legacyLeaf c leaf sub
  | .epyc7742 =>
    if leaf == 0 then (Cpuid.amdMaxBasic, 0x68747541, 0x444D4163, 0x69746E65)  -- "AuthenticAMD"
    else if leaf == 0x80000000 then (Cpuid.amdMaxExt, 0x68747541, 0x444D4163, 0x69746E65)
    else if leaf ≤ Cpuid.amdMaxBasic || (0x80000000 < leaf && leaf ≤ Cpuid.amdMaxExt) then
      Cpuid.amdLeaf c leaf sub
    else (0, 0, 0, 0)

end X86
