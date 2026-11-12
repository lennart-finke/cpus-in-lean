import X86.Proofs.Ext
/-!
# Facts established by the EPYC 7742 hardware run of the native campaign

The first run of the IA-32 native bundle on a real AMD EPYC 7742 (microcode 0x830107c, Linux 6.8,
campaigns 000-034, 137,144 cases; `validation/README.md`, "Hardware tests") settled the points below;
the hardware cases themselves are replayed by `validation/test/epyc_regression.py`.

* `cpuid_epyc_native_dump`: every feature bit CPUID reports is also set in the CPUID dump of that
  machine (`dumpEpycNative`, transcribed from the returned `cpuid.txt`), as `cpuid_epyc_dump` shows it
  for InstLatx64's dump: the model reports only bits both real 7742s have.
* `dumps_feature_diff`: the two dumps' feature registers differ only in StibpAlwaysOn
  (8000_0008h EBX bit 17, set by InstLatx64's machine, clear on this one), which the model masks.
* x87 facts as `#guard`s: the control word's reserved bits, FST of a denormal (no DE), F2XM1 and
  FYL2XP1 outside the documented domains, FYL2X of a power of two (PE), FSCALE's massive overflow and
  underflow, FPREM's underflow.
-/
namespace X86

/-- The CPUID dump of the EPYC 7742 the native campaign ran on (logical CPU 155: the APIC IDs in leaves
1, 0Bh, 8000_001Eh are that CPU's; `validation/test/fixtures/epyc7742-native-cpuid.txt`), every leaf
and subleaf with a nonzero value (leaf 0Bh: levels 0 and 1). Taken under Linux 6.8: CR4.OSXSAVE = 1,
XCR0 = 7. -/
def dumpEpycNative (leaf sub : UInt32) : Regs :=
  match leaf, sub with
  | 0x00000000, _ => (0x00000010, 0x68747541, 0x444D4163, 0x69746E65)
  | 0x00000001, _ => (0x00830F10, 0x9B800800, 0x7EF8320B, 0x178BFBFF)
  | 0x00000005, _ => (0x00000040, 0x00000040, 0x00000003, 0x00000011)
  | 0x00000006, _ => (0x00000004, 0x00000000, 0x00000001, 0x00000000)
  | 0x00000007, 0 => (0x00000000, 0x219C91A9, 0x00400004, 0x00000000)
  | 0x0000000B, 0 => (0x00000001, 0x00000002, 0x00000100, 0x0000009B)
  | 0x0000000B, 1 => (0x00000007, 0x00000080, 0x00000201, 0x0000009B)
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
  | 0x80000008, _ => (0x00003030, 0x018CF757, 0x0000707F, 0x00010000)
  | 0x8000000A, _ => (0x00000001, 0x00008000, 0x00000000, 0x0013BCFF)
  | 0x80000019, _ => (0xF040F040, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001A, _ => (0x00000006, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001B, _ => (0x000003FF, 0x00000000, 0x00000000, 0x00000000)
  | 0x8000001D, 0 => (0x00004121, 0x01C0003F, 0x0000003F, 0x00000000)
  | 0x8000001D, 1 => (0x00004122, 0x01C0003F, 0x0000003F, 0x00000000)
  | 0x8000001D, 2 => (0x00004143, 0x01C0003F, 0x000003FF, 0x00000002)
  | 0x8000001D, 3 => (0x0001C163, 0x03C0003F, 0x00003FFF, 0x00000001)
  | 0x8000001E, _ => (0x0000009B, 0x0000010D, 0x00000001, 0x00000000)
  | 0x8000001F, _ => (0x0001000F, 0x0000016F, 0x000001FD, 0x00000001)
  | 0x80000020, 0 => (0x00000000, 0x00000002, 0x00000000, 0x00000000)
  | 0x80000020, 1 => (0x0000000B, 0x00000000, 0x00000000, 0x0000000F)
  | _, _ => (0, 0, 0, 0)

/-- No feature bit the model reports is missing from the native campaign's dump either. -/
theorem cpuid_epyc_native_dump (c : Cpu) :
    ∀ p ∈ featureRegs, Cpuid.reg (cpuid c p.1 p.2.1) p.2.2 &&& ~~~Cpuid.reg (dumpEpycNative p.1 p.2.1) p.2.2 = 0 := by
  have hx : Cpuid.xcr0Supported = 7 := by decide
  have hf : Cpuid.featBits 0xD 1 0 true = 0xF := by decide
  simp only [featureRegs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, cpuid_epyc]
  simp [epycCpuid, amdTable, Cpuid.reg, dumpEpycNative, Cpuid.leafD, hx, hf, Cpuid.xssSupported,
    show implemented .xsave = true from rfl]
  refine ⟨?_, ?_, ?_⟩
  · unfold Cpuid.osxsave; split <;> decide
  · unfold Cpuid.topoEdx1; split <;> decide
  · unfold Cpuid.topoEcx81; split <;> decide

/-- The feature registers of the two real dumps differ only in 8000_0008h EBX bit 17 (StibpAlwaysOn). -/
theorem dumps_feature_diff :
    ∀ p ∈ featureRegs, Cpuid.reg (dump7742 p.1 p.2.1) p.2.2 ^^^ Cpuid.reg (dumpEpycNative p.1 p.2.1) p.2.2 =
      (if p = (0x80000008, 0, 1) then 0x20000 else 0) := by
  decide

/-! ## x87 (`X86/Fpu.lean`, `X86/Float80.lean`, `X86/Transcendental.lean`) -/

-- FRSTOR/FLDCW/FLDENV/FXRSTOR: bits 7, 13..15 read as 0, bit 6 as 1 (native `alignment_check`)
theorem fcwLoad_observed : fcwLoad 0x1F80 = 0x1F40 ∧ fcwLoad 0x001F = 0x005F ∧ fcwLoad 0x8000 = 0x0040 ∧
    fcwLoad 0x037F = 0x037F := by decide

-- FST m32 of a denormal extended value: underflow and precision, no denormal-operand exception
#guard (F80.toIeee { sig := 1, se := 0 } 23 8 0x37F).2 == FPF.UE ||| FPF.PE
-- F2XM1: |x| > 1 returns x with PE; ±∞; ±1 (native `x87_transcendental`)
#guard Trans.f2xm1 { sig := 0xC000000000000000, se := 0x4000 } 0x37F ==
  ({ sig := 0xC000000000000000, se := 0x4000 }, FPF.PE)
#guard Trans.f2xm1 (F80.inf true) 0x37F == (F80.one.withNeg true, 0)
#guard Trans.f2xm1 (F80.inf false) 0x37F == (F80.inf false, 0)
#guard Trans.f2xm1 F80.one 0x37F == (F80.one, FPF.PE ||| FPF.C1)
#guard Trans.f2xm1 F80.one 0xF7F == ({ sig := 0xFFFFFFFFFFFFFFFF, se := 0x3FFE }, FPF.PE)
#guard Trans.f2xm1 (F80.one.withNeg true) 0x37F == ({ sig := 0x8000000000000000, se := 0xBFFE }, FPF.PE)
-- FYL2X(2^63, 1) = 63 with PE
#guard Trans.fyl2x { sig := 0x8000000000000000, se := 0x403E } F80.one 0x37F ==
  ({ sig := 0xFC00000000000000, se := 0x4004 }, FPF.PE)
-- FYL2XP1: x ≤ -1 returns x with PE; x = 3 (outside the documented domain) gives y · 2, with PE
#guard Trans.fyl2xp1 { sig := 0xA000000000000000, se := 0xC000 } { sig := 0xC000000000000000, se := 0x4000 } 0x37F ==
  ({ sig := 0xA000000000000000, se := 0xC000 }, FPF.PE)
#guard Trans.fyl2xp1 { sig := 0xC000000000000000, se := 0x4000 } { sig := 0x8000000000000000, se := 1 } 0x37F ==
  ({ sig := 0x8000000000000000, se := 2 }, FPF.PE)
-- FSCALE with OE/UE unmasked: massive overflow gives ∞ with OE, PE, C1; massive underflow 0 with UE, PE
#guard F80.scale { sig := 0xFFFFFFFFFFFFFFFF, se := 0x3FFE } { sig := 0x8000000000000000, se := 0x403D } 0x377 ==
  (F80.inf false, FPF.OE ||| FPF.PE ||| FPF.C1)
#guard F80.scale (F80.one.withNeg true) { sig := 0xEE47E312DDDEAD5E, se := 0xD9BF } 0x040 ==
  (F80.zero true, FPF.UE ||| FPF.PE)
-- FPREM of a denormal by ∞ with UE unmasked: the remainder wrapped by 24576, UE
#guard F80.prem { sig := 0x7FFFFFFFFFFFFFFF, se := 0 } (F80.inf false) false 0x36F ==
  (({ sig := 0xFFFFFFFFFFFFFFFE, se := 0x6000 }, 0, true), FPF.DE ||| FPF.UE)

-- the status word loaded by XRSTOR (the oracle's signal frame), FXRSTOR, FLDENV, FRSTOR: B mirrors ES
theorem fswLoad_observed : fswLoad 0x3881 0x37E = 0xB881 ∧ fswLoad 0x3881 0x37F = 0x3801 := by decide
-- FADD m32 with an SNaN operand and a QNaN ST(0): ST(0)'s QNaN with IE (native `x87_snan_memory`)
#guard F80.arith .add { sig := 0xC000000000000001, se := 0x7FFF }
  (F80.ofIeee 0x7FBFFFFF 23 8 (quietSNaN := false)).1 64 0x37F == ({ sig := 0xC000000000000001, se := 0x7FFF }, FPF.IE)

/-! ## Integer and SIMD rules from the resumed run (campaigns 035–065) -/

-- 16-bit SHLD/SHRD with a count of 17..31: the 32-bit concatenation, AF set (native `open_questions`)
#guard shiftDouble true 2 0x5678 0 20 == some (0, Flag.ZF ||| Flag.PF ||| Flag.AF)
#guard shiftDouble false 2 0x5678 0 31 == some (0, Flag.ZF ||| Flag.PF ||| Flag.AF)
-- HADDPS with two QNaNs in a pair returns the lower element's (native `sse3_hadd_nan`)
#guard (Sse.hop false false { lo := 0x7FC000027FC00001, hi := 0x7FC000027FC00001 }
  { lo := 0x7FC000017FC00002, hi := 0x7FC000017FC00002 } 0x1F80).1 ==
  { lo := 0x7FC000017FC00001, hi := 0x7FC000027FC00002 }

/-! ## SHA (`X86/Ext/Crypto.lean`) -/

/-- The "NP" SHA instructions with a 66/F2/F3 prefix are #UD before anything else (EPYC 7742, native
`sha_prefix`); without one, a misaligned m128 operand is accepted (native `sha`: `shaOp` reads it with
`rdXE i 16 false`). -/
theorem shaOp_prefix {m : Machine} {i : Inst} {f : V128 → V128 → V128} (h : i.pp ≠ 0) :
    Crypto.shaOp i f m = .error (.exc Vec.UD none 0) m := by
  simp [Crypto.shaOp, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end X86
