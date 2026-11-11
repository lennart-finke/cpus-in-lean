import X86.Dispatch
import Std.Tactic.BVDecide
import X86.Proofs.Basic
import X86.Proofs.Ext
/-!
# General-purpose Zen 2 extensions (`X86/Ext/Gpr.lean`)

* Bit counts: `popcount32_spec` (the SWAR population count is the sum of the 32 bits),
  `tzcnt_spec` (TZCNT finds the lowest set bit and nothing below it), `lzcnt_spec` (LZCNT finds the
  highest set bit and nothing above it), `tzcnt_zero`/`lzcnt_zero` (a zero source gives the size).
* `bzhi_spec`, `bextr_full`: BZHI keeps exactly the bits below the index (all of them from 32 on),
  BEXTR with start 0 and length ≥ 32 is the identity.
* `crc32c_check`: CRC32 computes CRC-32C (check value E3069283h of "123456789", RFC 3720 B.4);
  `pdep_pext_example`: the SDM's PDEP/PEXT examples.
* Privilege and enable rules: `monitor_cpl3_ud`, `mwait_cpl3_ud` (#UD at CPL > 0 unless
  HWCR.MonMwaitUserEn), `mwait_unarmed` (without an armed monitor MWAIT neither halts nor skips
  time), `rdpru_tsd_ud` (#UD at CPL > 0 with CR4.TSD), `rdpmc_pce_gp` (#GP(0) at CPL > 0 without
  CR4.PCE), `mcommit_disabled_ud`/`op0F_mcommit` (F3 0F 01 FA is MCOMMIT, #UD while EFER.MCOMMIT
  = 0).
* `vex_L1_ud`: every BMI1/BMI2 form with VEX.L = 1 raises #UD before touching state.
* `rdrand_flags`: RDRAND/RDSEED set CF and clear OF, SF, ZF, AF, PF.
* `cpuid_leaf7_gpr`, `cpuid_ext8_gpr`: what CPUID reports for the Gpr features in leaf 7 and
  8000_0008h (legacy identity).
-/
namespace X86
namespace Gpr

/-! ## Bit counts -/

theorem popcount32_spec (x : UInt32) : popcount32 x =
    ((x >>> 0) &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1) + ((x >>> 3) &&& 1) + ((x >>> 4) &&& 1) +
    ((x >>> 5) &&& 1) + ((x >>> 6) &&& 1) + ((x >>> 7) &&& 1) + ((x >>> 8) &&& 1) + ((x >>> 9) &&& 1) +
    ((x >>> 10) &&& 1) + ((x >>> 11) &&& 1) + ((x >>> 12) &&& 1) + ((x >>> 13) &&& 1) +
    ((x >>> 14) &&& 1) + ((x >>> 15) &&& 1) + ((x >>> 16) &&& 1) + ((x >>> 17) &&& 1) +
    ((x >>> 18) &&& 1) + ((x >>> 19) &&& 1) + ((x >>> 20) &&& 1) + ((x >>> 21) &&& 1) +
    ((x >>> 22) &&& 1) + ((x >>> 23) &&& 1) + ((x >>> 24) &&& 1) + ((x >>> 25) &&& 1) +
    ((x >>> 26) &&& 1) + ((x >>> 27) &&& 1) + ((x >>> 28) &&& 1) + ((x >>> 29) &&& 1) +
    ((x >>> 30) &&& 1) + ((x >>> 31) &&& 1) := by
  simp only [popcount32, shr32]
  bv_decide

theorem tzcnt_zero : tzcnt 32 0 = 32 := by decide
theorem lzcnt_zero : lzcnt 32 0 = 32 := by decide

/-- TZCNT of a non-zero value: the bit at the count is set and every bit below it is clear. -/
theorem tzcnt_spec (x : UInt32) (h : x ≠ 0) :
    (x >>> tzcnt 32 x) &&& 1 = 1 ∧ x &&& ((1 <<< tzcnt 32 x) - 1) = 0 := by
  simp only [tzcnt, popcount32, shr32, shl32]
  simp only [show ((32 : UInt32) == 16) = false by decide, Bool.false_eq_true, ↓reduceIte]
  bv_decide

/-- LZCNT of a non-zero value: the bit 31 − count is the highest set bit. -/
theorem lzcnt_spec (x : UInt32) (h : x ≠ 0) :
    x >>> (31 - lzcnt 32 x) = 1 := by
  simp only [lzcnt, popcount32, shr32]
  simp only [show ((32 : UInt32) == 16) = false by decide, Bool.false_eq_true, ↓reduceIte]
  bv_decide

/-! ## BZHI, BEXTR -/

theorem bzhi_spec (x i : UInt32) :
    bzhi x i = if i &&& 0xFF ≥ 32 then x else x &&& ((1 <<< (i &&& 0xFF)) - 1) := rfl

theorem bzhi_lt (x i : UInt32) (h : i &&& 0xFF < 32) : bzhi x i < 1 <<< (i &&& 0xFF) := by
  have h' : ¬ (i &&& 0xFF ≥ 32) := by
    intro c; exact absurd h (Nat.not_lt.mpr (by simpa [UInt32.le_iff_toNat_le] using c))
  simp only [bzhi, h', ↓reduceIte, shl32]
  revert h
  bv_decide

theorem bextr_full (x : UInt32) (n : UInt32) (h : 32 ≤ n) (h2 : n < 256) :
    bextr x (n <<< 8) = x := by
  simp only [bextr, shl32, shr32]
  revert h h2
  bv_decide

/-! ## CRC32, PDEP, PEXT on known values -/

set_option maxRecDepth 100000 in
/-- CRC-32C of "123456789" (initial value and final inversion ~0): E3069283h. -/
theorem crc32c_check :
    ([0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] : List UInt32).foldl
      (fun c b => crc32c c b 1) 0xFFFFFFFF ^^^ 0xFFFFFFFF = 0xE3069283 := by decide

theorem pdep_pext_example : pdep 0b1011 0b11110000 = 0b10110000 ∧ pext 0b10110000 0b11110000 = 0b1011 := by
  decide

/-! ## Privilege and enable rules -/

private theorem err_ud {α} (m : Machine) : (ud : M α) m = .error (.exc Vec.UD none 0) m := rfl

/-- MONITOR at CPL > 0 without HWCR.MonMwaitUserEn raises #UD. -/
theorem monitor_cpl3_ud {i : Inst} {m : Machine} (h : m.cpu.cpl ≠ 0)
    (he : m.cpu.gprx.monMwaitUserEn = false) :
    monitor i false m = .error (.exc Vec.UD none 0) m := by
  simp [monitor, cpu, bind, EStateM.bind, h, he, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- MWAIT at CPL > 0 without HWCR.MonMwaitUserEn raises #UD. -/
theorem mwait_cpl3_ud {m : Machine} (h : m.cpu.cpl ≠ 0) (he : m.cpu.gprx.monMwaitUserEn = false) :
    mwait false m = .error (.exc Vec.UD none 0) m := by
  simp [mwait, cpu, bind, EStateM.bind, h, he, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- MWAIT without an armed monitor completes without waiting: only the CPU state is unchanged
(no halt, no skipped time). -/
theorem mwait_unarmed {m : Machine} (hc : m.cpu.cpl = 0) (hx : m.cpu.ecx &&& ~~~1 = 0)
    (hm : m.cpu.gprx.monLine = none) :
    ∃ m', mwait false m = .ok () m' ∧ m'.cpu.halted = m.cpu.halted ∧ m'.icount = m.icount := by
  simp [mwait, cpu, bind, EStateM.bind, hc, hx, hm, modG, modCpu, pure, EStateM.pure]

/-- RDPRU at CPL > 0 with CR4.TSD raises #UD. -/
theorem rdpru_tsd_ud {m : Machine} (h : m.cpu.cpl ≠ 0) (ht : m.cpu.cr4 &&& CR4.TSD ≠ 0) :
    rdpru m = .error (.exc Vec.UD none 0) m := by
  simp [rdpru, cpu, bind, EStateM.bind, h, ht, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- RDPMC at CPL > 0 with CR4.PCE clear raises #GP(0). -/
theorem rdpmc_pce_gp {m : Machine} (h : m.cpu.cpl ≠ 0) (hp : m.cpu.cr4 &&& CR4.PCE = 0) :
    rdpmc m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [rdpmc, cpu, bind, EStateM.bind, h, hp, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- MCOMMIT (F3 0F 01 FA) raises #UD while EFER.MCOMMIT is clear. -/
theorem mcommit_disabled_ud {m : Machine} (he : m.cpu.efer &&& EFER.MCOMMIT = 0) :
    mcommit m = .error (.exc Vec.UD none 0) m := by
  simp [mcommit, cpu, bind, EStateM.bind, he, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- F3 0F 01 FA is MCOMMIT (and not MONITORX). -/
theorem op0F_mcommit {i : Inst} (hop : i.op = 0x101) (hmem : i.isMem = false) (hmod : i.modrm = 0xFA)
    (hrep : i.rep = 0xF3) : op0F? i = some mcommit := by
  simp [op0F?, hop, hmem, hmod, hrep]; rfl

/-- Every BMI1/BMI2 instruction with VEX.L = 1 raises #UD (APM: "VEX.L is 1"), before any operand
access. -/
theorem vex_L1_ud {i : Inst} {a : M Unit} (hl : i.vexL = true) (ha : vex? i = some a) (m : Machine) :
    a m = .error (.exc Vec.UD none 0) m := by
  unfold vex? at ha
  cases hb : vexBody? i with
  | none => simp [hb] at ha
  | some body =>
    simp only [hb, Option.map_some, Option.some.injEq] at ha
    subst ha
    simp [hl, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem setReg_eflags (c : Cpu) (r : UInt8) (v : UInt32) : (c.setReg r v).eflags = c.eflags := by
  unfold Cpu.setReg; split <;> rfl

private theorem wrReg_eflags (c : Cpu) (sz : Sz) (r : UInt8) (v : UInt32) :
    (c.wrReg sz r v).eflags = c.eflags := by
  unfold Cpu.wrReg
  split <;> (try split) <;> (try split) <;> simp [setReg_eflags]

/-- RDRAND/RDSEED: CF = 1 and OF = SF = ZF = AF = PF = 0 afterwards. -/
theorem rdrand_flags (i : Inst) (m : Machine) :
    ∃ m', rdrand i m = .ok () m' ∧ m'.cpu.eflags &&& Flag.arith = Flag.CF := by
  refine ⟨_, rfl, ?_⟩
  simp only [rdrand, setArith, X86.setFlags, modCpu, modG, gst, X86.wrReg, bind, EStateM.bind,
    Cpu.setFlags, wrReg_eflags]
  generalize m.cpu.eflags = e
  simp only [Flag.arith, Flag.CF]
  bv_decide

end Gpr

/-! ## CPUID -/

/-- CPUID 7.0 (legacy identity): EBX = BMI1, BMI2, RDSEED, ADX, CLFLUSHOPT, CLWB and SHA (Crypto; reported
since SSSE3 exists); ECX = RDPID (and system A's SMEP, SMAP in EBX and UMIP in ECX: 0x00100080, 0x4). -/
theorem cpuid_leaf7_gpr (c : Cpu) :
    cpuid c 7 0 = (0, 0x218C0108 ||| 0x00100080, 0x00400000 ||| 0x4, 0) := by
  have h0 : Cpuid.maskReg 7 0 0 0 = 0 := by decide
  have h1 : Cpuid.maskReg 7 0 1 0x219C91A9 = 0x218C0108 ||| 0x00100080 := by decide
  have h2 : Cpuid.maskReg 7 0 2 0x00400004 = 0x00400000 ||| 0x4 := by decide
  have h3 : Cpuid.maskReg 7 0 3 0 = 0 := by decide
  simp [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw,
    h0, h1, h2, h3]
  decide

/-- CPUID 8000_0008h EBX (legacy identity): CLZERO, RDPRU, MCOMMIT, WBNOINVD (and XSaveErPtr, bit 2, of
the XSAVE work, and system A's IBPB, IBRS, STIBP, StibpAlwaysOn, SSBD: 0x0102D000). -/
theorem cpuid_ext8_gpr (c : Cpu) : (cpuid c 0x80000008 0).2.1 = 0x315 ||| 0x0102D000 := by
  have h1 : Cpuid.maskReg 0x80000008 0 1 0x018EF757 = 0x315 ||| 0x0102D000 := by decide
  simp [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, Cpuid.amdLeaf, Cpuid.leafGate, Cpuid.raw, h1]
  rfl

end X86
