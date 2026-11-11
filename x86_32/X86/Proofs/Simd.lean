import Std.Tactic.BVDecide
import X86.Simd
import X86.Proofs.Basic
/-!
# MMX and SSE state rules
-/
namespace X86

/-- SSE instructions raise #UD while the operating system has not enabled them (CR4.OSFXSR = 0),
before touching any state. -/
theorem sseCheck_noosfxsr {m : Machine} (h : m.cpu.cr4 &&& CR4.OSFXSR = 0) :
    sseCheck m = .error (.exc Vec.UD none 0) m := by
  simp [sseCheck, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- With CR0.EM set (x87 emulation), MMX instructions and EMMS raise #UD. -/
theorem mmxPre_em {m : Machine} (h : m.cpu.cr0 &&& CR0.EM ≠ 0) :
    mmxPre m = .error (.exc Vec.UD none 0) m := by
  simp [mmxPre, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- With CR0.EM clear and CR0.TS set, MMX instructions and EMMS raise #NM (lazy context switching). -/
theorem mmxPre_ts {m : Machine} (he : m.cpu.cr0 &&& CR0.EM = 0) (h : m.cpu.cr0 &&& CR0.TS ≠ 0) :
    mmxPre m = .error (.exc Vec.NM none 0) m := by
  simp [mmxPre, cpu, bind, EStateM.bind, he, h, exc, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- The x87-to-MMX transition: TOP = 0 and every register valid. -/
theorem mmxEnter_state (c : Cpu) : c.mmxEnter.ftop = 0 ∧ c.mmxEnter.fempty = 0 := by
  refine ⟨?_, rfl⟩
  have h0 : ((0 : Nat) % 8).toUInt16 = 0 := rfl
  have h : ∀ x : UInt16, ((x &&& ~~~0x3800 ||| (0 : UInt16) <<< 11) >>> 11) &&& 7 = 0 := by
    intro x; simp only [shl16, shr16]; bv_decide
  unfold Cpu.ftop Cpu.mmxEnter Cpu.setTop
  simp only [h0, h]
  rfl

/-- Once an MMX instruction is past its checks, TOP is 0 and all tags are valid. -/
theorem mmxCheck_ok {m m' : Machine} (h : mmxCheck m = .ok () m') :
    m'.cpu.ftop = 0 ∧ m'.cpu.fempty = 0 := by
  simp only [mmxCheck, bind, EStateM.bind] at h
  split at h
  · simp only [mmxEnter, modCpu] at h
    cases h
    exact mmxEnter_state _
  · cases h

/-- EMMS marks every x87 register empty. -/
theorem emms_empty {m m' : Machine} (h : emms m = .ok () m') : m'.cpu.fempty = 0xFF := by
  simp only [emms, bind, EStateM.bind] at h
  split at h
  · simp only [modCpu] at h
    cases h
    rfl
  · cases h

/-- Writing an MMX register sets the sign/exponent word of the aliased x87 register to all ones. -/
theorem setMm_reg {m m' : Machine} {r : UInt8} {v : UInt64} (h : setMm r v m = .ok () m') :
    m'.cpu.fpr[(r &&& 7).toNat]! = { sig := v, se := 0xFFFF } ∨ m'.cpu.fpr.size ≤ (r &&& 7).toNat := by
  simp only [setMm, modCpu] at h
  cases h
  by_cases hs : (r &&& 7).toNat < m.cpu.fpr.size
  · left
    have hs' : r.toNat &&& 7 < (m.cpu.fpr.setIfInBounds (r.toNat &&& 7) { sig := v, se := 0xFFFF }).size := by
      simpa using hs
    simp only [Array.set!, UInt8.toNat_and, UInt8.reduceToNat]
    rw [getElem!_pos (m.cpu.fpr.setIfInBounds (r.toNat &&& 7) { sig := v, se := 0xFFFF }) (r.toNat &&& 7) hs']
    simp
  · right
    simp only [Array.set!, Array.size_setIfInBounds]
    omega

end X86
