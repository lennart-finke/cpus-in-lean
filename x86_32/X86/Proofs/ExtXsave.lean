import Std.Tactic.BVDecide
import X86.Dispatch
import X86.Proofs.Basic
import X86.Proofs.Ext
/-!
# XSAVE (`X86/Ext/Xsave.lean`)

* `cpuid_osxsave_legacy`, `amdLeaf_osxsave`: CPUID 1:ECX[27] is CR4.OSXSAVE, with the former and
  with the AMD identity (whose raw dump value has the bit set).
* `cpuid_leafD`, `leafD_0/1/2`, `leafD_unsupported`: CPUID leaf 0xD (x87, SSE and AVX; standard sizes 576/832,
  XSAVEOPT/XSAVEC/XGETBV1/XSAVES, no supervisor component, zeros for other components).
* `xcr0Valid_iff`: XSETBV accepts exactly XCR0 = 1, 3 and 7; `xsetbv_invalid`, `xsetbv_cpl`,
  `xsetbv_noosxsave`, `xsetbv_valid`: its #GP/#UD rules and its effect.
* `xgetbv_noosxsave`, `pre_noosxsave`, `pre_ts`, `pre_priv`: #UD without CR4.OSXSAVE before any state is
  touched, #NM with CR0.TS, XSAVES/XRSTORS #GP(0) outside CPL 0.
* `area_misaligned`: an XSAVE area that is not 64-byte aligned raises #GP(0) (after the segment check).
* `xinuse_x87/sse/ymm`: a component outside its initial configuration is tracked as in use.
* `xsaveSize_7`, `compactSize_7`, `compactOffset_ymm`: the area layout.
-/
namespace X86
namespace Xsave

theorem cpuid_osxsave_legacy (c : Cpu) (sub : UInt32) :
    (cpuid c 1 sub).2.2.1 &&& Cpuid.osxsaveBit =
      (if c.cr4 &&& CR4.OSXSAVE != 0 then Cpuid.osxsaveBit else 0) := by
  have h12 : Cpuid.featBits 1 0 2 true = 0x44C00008 := by decide
  have hx : implemented .xsave = true := rfl
  simp only [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, Cpuid.osxsave, hx, h12]
  by_cases h : c.cr4 &&& CR4.OSXSAVE = 0 <;> simp [h, Cpuid.osxsaveBit] <;> decide

theorem amdLeaf_osxsave (c : Cpu) (sub : UInt32) :
    (Cpuid.amdLeaf c 1 sub).2.2.1 &&& Cpuid.osxsaveBit =
      (if c.cr4 &&& CR4.OSXSAVE != 0 then Cpuid.osxsaveBit else 0) := by
  have e : (Cpuid.amdLeaf c 1 sub).2.2.1 =
      (Cpuid.maskReg 1 sub 2 0x7EF8320B &&& ~~~Cpuid.osxsaveBit) ||| Cpuid.osxsave c := rfl
  rw [e]
  clear e
  generalize Cpuid.maskReg 1 sub 2 0x7EF8320B = x
  have hx : implemented .xsave = true := rfl
  have hb : Cpuid.osxsaveBit = 0x8000000 := by decide
  by_cases h : c.cr4 &&& CR4.OSXSAVE = 0
  · have ho : Cpuid.osxsave c = 0 := by simp [Cpuid.osxsave, h]
    rw [ho, hb]; simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; bv_decide
  · have ho : Cpuid.osxsave c = Cpuid.osxsaveBit := by simp [Cpuid.osxsave, h, hx]
    have h' : (c.cr4 &&& CR4.OSXSAVE != 0) = true := by simpa using h
    rw [ho, hb]; simp only [h', ↓reduceIte]; bv_decide

/-- With the former identity, leaf 0xD (in range: the highest basic leaf is 0xD) is `leafD`. -/
theorem cpuid_leafD (c : Cpu) (sub : UInt32) : cpuid c 0xD sub = Cpuid.leafD c sub := by
  simp [cpuid, identity, Cpuid.legacyLeaf, legacyMax_former, Cpuid.amdLeaf]

theorem leafD_0 (c : Cpu) : Cpuid.leafD c 0 = (7, Cpuid.xsaveSize c.xcr0, 0x340, 0) := by
  have hs : Cpuid.xcr0Supported = 7 := by decide
  have h7 : Cpuid.xsaveSize 7 = 0x340 := by decide
  simp [Cpuid.leafD, hs, h7, show implemented .xsave = true from rfl]
  decide

theorem leafD_1 (c : Cpu) : Cpuid.leafD c 1 = (0xF, Cpuid.compactSize (c.xcr0 ||| c.xss), 0, 0) := by
  have hf : Cpuid.featBits 0xD 1 0 true = 0xF := by decide
  simp [Cpuid.leafD, hf, Cpuid.xssSupported, show implemented .xsave = true from rfl]

theorem leafD_2 (c : Cpu) : Cpuid.leafD c 2 = (0x100, 0x240, 0, 0) := by
  have hs : Cpuid.xcr0Supported ||| Cpuid.xssSupported = 7 := by decide
  simp [Cpuid.leafD, hs, Cpuid.xcomp, show implemented .xsave = true from rfl]
  decide

/-- Subleaves ≥ 3 describe no component of the model (in particular not PKRU, 9). -/
theorem leafD_unsupported (c : Cpu) (sub : UInt32) (h1 : 3 ≤ sub) :
    Cpuid.leafD c sub = (0, 0, 0, 0) := by
  have hs : (Cpuid.xcr0Supported ||| Cpuid.xssSupported) = 7 := by decide
  have h0 : sub ≠ 0 := by intro h; subst h; exact absurd h1 (by decide)
  have h1' : sub ≠ 1 := by intro h; subst h; exact absurd h1 (by decide)
  unfold Cpuid.leafD
  simp only [show implemented .xsave = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hs]
  split
  · rename_i hc
    exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨hlt, hb⟩ := hc
    apply hb
    show (7 : UInt64) >>> sub.toUInt64 &&& 1 = 0
    have h3 : 3 ≤ sub.toNat := h1
    have h63 : sub.toNat < 63 := hlt
    have hz : (7 : UInt64) >>> sub.toUInt64 = 0 := by
      apply UInt64.toNat_inj.mp
      change ((7 : UInt64) >>> sub.toUInt64).toNat = (0 : UInt64).toNat
      rw [shr64, UInt64.toNat_shiftRight]
      simp only [UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : sub.toNat < 64), Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt
      calc (7 % 2 ^ 64) < 2 ^ 3 := by decide
        _ ≤ 2 ^ sub.toNat := Nat.pow_le_pow_right (by decide) h3
    rw [hz]; decide
  · rfl

theorem xsaveSize_7 : Cpuid.xsaveSize 7 = 0x340 := by decide
theorem xsaveSize_3 : Cpuid.xsaveSize 3 = 0x240 := by decide
theorem compactSize_7 : Cpuid.compactSize 7 = 0x340 := by decide
theorem compactOffset_ymm : Cpuid.compactOffset 4 2 = 0x240 ∧ Cpuid.compactOffset 7 2 = 0x240 := by decide

/-- XSETBV accepts exactly XCR0 = 1 (x87), 3 (x87, SSE) and 7 (x87, SSE, AVX). -/
theorem xcr0Valid_iff (v : UInt64) : xcr0Valid v = true ↔ v = 1 ∨ v = 3 ∨ v = 7 := by
  have hs : Cpuid.xcr0Supported = 7 := by decide
  simp only [xcr0Valid, hs, XCR0.X87, XCR0.SSE, XCR0.YMM, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  bv_decide

theorem xgetbv_noosxsave {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    xgetbv m = .error (.exc Vec.UD none 0) m := by
  simp [xgetbv, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem xsetbv_noosxsave {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    xsetbv m = .error (.exc Vec.UD none 0) m := by
  simp [xsetbv, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem xsetbv_cpl {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE ≠ 0) (hc : m.cpu.cpl ≠ 0) :
    xsetbv m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [xsetbv, cpu, h, hc, bind, EStateM.bind, gp, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem xsetbv_invalid {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE ≠ 0)
    (hv : xcr0Valid (edxEax m.cpu) = false) :
    xsetbv m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [xsetbv, cpu, h, hv, bind, EStateM.bind, gp, throw, throwThe, MonadExceptOf.throw]
  split <;> simp_all [EStateM.bind, EStateM.throw]

/-- XSETBV of a valid value at CPL 0 with ECX = 0 sets XCR0 := EDX:EAX and nothing else. -/
theorem xsetbv_valid {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE ≠ 0) (hc : m.cpu.cpl = 0)
    (he : m.cpu.ecx = 0) (hv : xcr0Valid (edxEax m.cpu) = true) :
    xsetbv m = .ok () { m with cpu := { m.cpu with xcr0 := edxEax m.cpu } } := by
  simp [xsetbv, cpu, h, hc, he, hv, bind, EStateM.bind, modCpu]

theorem pre_noosxsave {m : Machine} (priv : Bool) (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    pre priv m = .error (.exc Vec.UD none 0) m := by
  simp [pre, cpu, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem pre_ts {m : Machine} (priv : Bool) (h : m.cpu.cr4 &&& CR4.OSXSAVE ≠ 0)
    (ht : m.cpu.cr0 &&& CR0.TS ≠ 0) :
    pre priv m = .error (.exc Vec.NM none 0) m := by
  simp [pre, cpu, h, ht, bind, EStateM.bind, exc, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem pre_priv {m : Machine} (h : m.cpu.cr4 &&& CR4.OSXSAVE ≠ 0)
    (ht : m.cpu.cr0 &&& CR0.TS = 0) (hc : m.cpu.cpl ≠ 0) :
    pre true m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [pre, cpu, h, ht, hc, bind, EStateM.bind, gp, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- Every XSAVE-family instruction starts with `pre`: without CR4.OSXSAVE it is #UD and the machine
is unchanged. -/
theorem xsave_noosxsave {m : Machine} (i : Inst) (opt : Bool) (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    xsave i opt m = .error (.exc Vec.UD none 0) m := by
  simp only [xsave, bind, EStateM.bind, pre_noosxsave false h]

theorem xsavec_noosxsave {m : Machine} (i : Inst) (sup : Bool) (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    xsavec i sup m = .error (.exc Vec.UD none 0) m := by
  simp only [xsavec, bind, EStateM.bind, pre_noosxsave sup h]

theorem xrstor_noosxsave {m : Machine} (i : Inst) (sup : Bool) (h : m.cpu.cr4 &&& CR4.OSXSAVE = 0) :
    xrstor i sup m = .error (.exc Vec.UD none 0) m := by
  simp only [xrstor, bind, EStateM.bind, pre_noosxsave sup h]

/-- An XSAVE area that is not 64-byte aligned: #GP(0) once the segment check has passed. -/
theorem area_misaligned {m : Machine} {i : Inst} {n : UInt32} {write : Bool} {lin : UInt32}
    {m1 : Machine} (hs : (do segAddr i.seg (← fpEa i) n write : M UInt32) m = .ok lin m1)
    (ha : lin &&& 63 ≠ 0) :
    area i n write m = .error (.exc Vec.GP (some 0) 0) m1 := by
  simp only [area, bind, EStateM.bind] at hs ⊢
  split at hs <;> simp_all [gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]

theorem xinuse_x87 (c : Cpu) (h : x87Init c = false) : xinuse c &&& XCR0.X87 = XCR0.X87 := by
  simp only [xinuse, h, Bool.false_eq_true, ↓reduceIte, XCR0.X87, XCR0.SSE, XCR0.YMM]
  split <;> split <;> bv_decide

theorem xinuse_sse (c : Cpu) (h : sseInit c = false) : xinuse c &&& XCR0.SSE = XCR0.SSE := by
  simp only [xinuse, h, Bool.false_eq_true, ↓reduceIte, XCR0.X87, XCR0.SSE, XCR0.YMM]
  split <;> split <;> bv_decide

theorem xinuse_ymm (c : Cpu) (h : ymmInit c = false) : xinuse c &&& XCR0.YMM = XCR0.YMM := by
  simp only [xinuse, h, Bool.false_eq_true, ↓reduceIte, XCR0.X87, XCR0.SSE, XCR0.YMM]
  split <;> split <;> bv_decide

end Xsave
end X86
