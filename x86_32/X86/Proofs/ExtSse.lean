import Std.Tactic.BVDecide
import X86.Dispatch
import X86.Proofs.Basic
/-!
# SSE3, SSSE3, SSE4.1, SSE4.2, SSE4a, MisalignSse

* MisalignSse: `mxcsrMask_value` (MXCSR_MASK reports MM, bit 17, and nothing above bit 17 or bit 16);
  `misalignExc_mm0` (with MXCSR.MM = 0 every misaligned 16-byte operand is #GP, the former rule);
  `misalignExc_strict` (MOVAPx, MOVDQA, MOVNTPx, MOVNTDQ, MOVNTDQA, FXSAVE/FXRSTOR and VEX forms
  stay #GP whatever MM says); `misalignExc_mm1` (with MM = 1 and alignment checking off, no
  exception); `misalignExc_ac` (with MM = 1 and CR0.AM, EFLAGS.AC, CPL 3: #AC).
* Checks: `xmmOp_noosfxsr` (XMM forms raise #UD with CR4.OSFXSR = 0 before touching state),
  `mmxOp_em` (MMX forms of SSSE3 raise #UD with CR0.EM).
* Kernels: `ptest_zf`, `ptest_cf` (the PTEST flags are the AND / ANDN tests); `insertq_extrq` (EXTRQ
  of a field written by INSERTQ returns the inserted bits whenever the field fits in 64 bits);
  `extrq_len0` (length 0 means 64); `roundToIntegral_suppress` (ROUND* with imm8[3] never reports
  PE); `strFlags_cf`, `strFlags_of` (PCMPxSTRx: CF = IntRes2 ≠ 0, OF = IntRes2[0]).
* FISTTP: `roundQ_trunc` (the truncating conversion never rounds up: C1 = 0).
* Ownership: `map2?_crypto` (the AES and SHA opcodes of 0F 38 are left to `Crypto.lean`).
-/
namespace X86

theorem mxcsrMask_value : mxcsrMask = 0x2FFFF := by decide

theorem misalignExc_mm0 (c : Cpu) (i : Inst) (h : c.mxcsr &&& MXCSR_MM = 0) :
    misalignExc c i = some Vec.GP := by
  simp [misalignExc, h]

theorem misalignExc_strict (c : Cpu) (i : Inst) (h : alignStrict i = true) :
    misalignExc c i = some Vec.GP := by
  simp [misalignExc, h]

theorem alignStrict_movaps (i : Inst) (h : i.op = 0x128) : alignStrict i = true := by
  simp [alignStrict, h]

theorem alignStrict_movntdqa (i : Inst) (h : i.op = 0x22A) : alignStrict i = true := by
  simp [alignStrict, h]

theorem misalignExc_mm1 (c : Cpu) (i : Inst) (hm : c.mxcsr &&& MXCSR_MM ≠ 0)
    (hs : alignStrict i = false) (hac : c.cr0 &&& CR0.AM = 0) : misalignExc c i = none := by
  simp [misalignExc, hm, hs, hac]

theorem misalignExc_ac (c : Cpu) (i : Inst) (hm : c.mxcsr &&& MXCSR_MM ≠ 0)
    (hs : alignStrict i = false) (ham : c.cr0 &&& CR0.AM ≠ 0) (hac : c.eflags &&& Flag.AC ≠ 0)
    (hcpl : c.cpl = 3) : misalignExc c i = some Vec.AC := by
  simp [misalignExc, hm, hs, ham, hac, hcpl]

theorem xmmOp_noosfxsr {m : Machine} {i : Inst} {f : V128 → V128 → V128} {al : Bool}
    (h : m.cpu.cr4 &&& CR4.OSFXSR = 0) :
    Sse.xmmOp i f al m = .error (.exc Vec.UD none 0) m := by
  simp [Sse.xmmOp, sseCheck, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem mmxOp_em {m : Machine} {i : Inst} {f : V128 → V128 → V128}
    (h : m.cpu.cr0 &&& CR0.EM ≠ 0) :
    Sse.mmxOp i f m = .error (.exc Vec.UD none 0) m := by
  simp [Sse.mmxOp, mmxCheck, mmxPre, cpu, bind, EStateM.bind, h, ud, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw]

theorem ptest_zf (a b : V128) :
    (Sse.ptest a b).1 = true ↔ (a.lo &&& b.lo = 0 ∧ a.hi &&& b.hi = 0) := by
  have h : ∀ x y : UInt64, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := by
    intro x y; constructor
    · intro hxy; constructor <;> bv_decide
    · rintro ⟨hx, hy⟩; simp [hx, hy]
  simp [Sse.ptest, h]

theorem ptest_cf (a b : V128) :
    (Sse.ptest a b).2 = true ↔ (~~~a.lo &&& b.lo = 0 ∧ ~~~a.hi &&& b.hi = 0) := by
  have h : ∀ x y : UInt64, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := by
    intro x y; constructor
    · intro hxy; constructor <;> bv_decide
    · rintro ⟨hx, hy⟩; simp [hx, hy]
  simp [Sse.ptest, h]

/-- The bit-level identity behind `insertq_extrq`: a mask that survives the shift. -/
theorem insert_extract_field (d s m sh : UInt64) (hsh : sh < 64) (hfit : (m <<< sh) >>> sh = m) :
    (((d &&& ~~~(m <<< sh)) ||| ((s &&& m) <<< sh)) >>> sh) &&& m = s &&& m := by
  simp only [shl64, shr64] at *
  bv_decide

theorem insertq_extrq (d s : UInt64) (len idx : Nat)
    (hfit : (Sse.fieldMask len <<< (idx % 64).toUInt64) >>> (idx % 64).toUInt64 = Sse.fieldMask len) :
    Sse.extrq (Sse.insertq d s len idx) len idx = s &&& Sse.fieldMask len := by
  have hsh : (idx % 64).toUInt64 < 64 := by
    rw [UInt64.lt_iff_toNat_lt]
    have : idx % 64 < 64 := Nat.mod_lt _ (by decide)
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat]
    simp
    omega
  simp only [Sse.extrq, Sse.insertq]
  exact insert_extract_field d s _ _ hsh hfit

theorem extrq_len0 (v : UInt64) : Sse.extrq v 0 0 = v := by
  simp only [Sse.extrq, Sse.fieldMask]
  simp
  bv_decide

theorem roundToIntegral_suppress (f : FP.Format) (a mode mx : UInt64) :
    (FP.roundToIntegral f a mode mx true).2 &&& 0x20 = 0 := by
  unfold FP.roundToIntegral
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals ((try dsimp only); first | decide | rfl | simp)

theorem strFlags_cf (imm res la lb : Nat) :
    (Sse.strFlags imm res la lb &&& Flag.CF ≠ 0) ↔ res ≠ 0 := by
  unfold Sse.strFlags
  by_cases h1 : res = 0 <;> by_cases h2 : lb < Sse.strN imm <;> by_cases h3 : la < Sse.strN imm <;>
    by_cases h4 : res % 2 = 1 <;> simp [h1, h2, h3, h4, Flag.CF, Flag.ZF, Flag.SF, Flag.OF] <;> decide

theorem strFlags_of (imm res la lb : Nat) :
    (Sse.strFlags imm res la lb &&& Flag.OF ≠ 0) ↔ res % 2 = 1 := by
  unfold Sse.strFlags
  by_cases h1 : res = 0 <;> by_cases h2 : lb < Sse.strN imm <;> by_cases h3 : la < Sse.strN imm <;>
    by_cases h4 : res % 2 = 1 <;> simp [h1, h2, h3, h4, Flag.CF, Flag.ZF, Flag.SF, Flag.OF] <;> decide

/-- FISTTP's conversion (rounding control 3): the magnitude is truncated, never rounded up, so C1
("rounded up") stays clear. -/
theorem roundQ_trunc (n d : Nat) (neg : Bool) : roundQ n d neg 3 = (n / d, n % d != 0, false) := by
  simp [roundQ]

theorem map2?_crypto (i : Inst) (h : i.byte = 0xDB ∨ i.byte = 0xC8) : Sse.map2? i = none := by
  rcases h with h | h <;> simp [Sse.map2?, h] <;> split <;> rfl

end X86
