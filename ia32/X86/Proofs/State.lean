import Std.Tactic.BVDecide
import X86.Step
import X86.Proofs.Basic
/-!
# Register file, segmentation, paging and decoder properties
-/
namespace X86

/-! ## Register file -/

theorem reg_cases (r : UInt8) (h : r < 8) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
  bv_decide

/-- Reading back a register at the size it was written yields the written value (truncated). -/
theorem rdReg_wrReg (c : Cpu) (sz : Sz) (r : UInt8) (v : UInt32)
    (hsz : sz = 1 ∨ sz = 2 ∨ sz = 4) (hr : r < 8) :
    (c.wrReg sz r v).rdReg sz r = v &&& sz.mask := by
  rcases hsz with rfl | rfl | rfl <;>
  rcases reg_cases r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Cpu.wrReg, Cpu.rdReg, Cpu.setReg, Cpu.getReg, Sz.mask] <;> simp <;> bv_decide

/-- A 32-bit register write leaves the other registers unchanged. -/
theorem getReg_setReg_other (c : Cpu) (r r' : UInt8) (v : UInt32) (hr : r < 8) (hr' : r' < 8)
    (hne : r ≠ r') : (c.setReg r v).getReg r' = c.getReg r' := by
  rcases reg_cases r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases reg_cases r' hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp_all [Cpu.setReg, Cpu.getReg]

/-- Byte writes to AL..BL / AH..BH only change the addressed byte of the full register. -/
theorem wrReg8_bytes (c : Cpu) (r : UInt8) (v : UInt32) (hr : r < 8) :
    let r32 := if r < 4 then r else r - 4
    let sh : UInt32 := if r < 4 then 0 else 8
    (c.wrReg 1 r v).getReg r32 = (c.getReg r32 &&& ~~~(0xFF <<< sh)) ||| ((v &&& 0xFF) <<< sh) := by
  rcases reg_cases r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Cpu.wrReg, Cpu.setReg, Cpu.getReg] <;> simp <;> bv_decide

/-! ## Segmentation -/

/-- `segAddr` either faults or returns `base + off` without changing the machine, and it
succeeds exactly when `segAllowed` holds. -/
theorem segAddr_spec (s : UInt8) (off n : UInt32) (write : Bool) (m : Machine) :
    segAddr s off n write m =
      if segAllowed (m.cpu.getSeg s) off n write then .ok ((m.cpu.getSeg s).base + off) m
      else .error (.exc (if s == SegN.SS then Vec.SS else Vec.GP) (some 0) 0) m := rfl

/-- Permitted segment accesses: the segment is present; writes only to writable data
segments; reads from code only if readable; expand-up accesses lie within the limit;
expand-down accesses lie strictly above the limit. -/
theorem segAllowed_spec {sr : SegReg} {off n : UInt32} {write : Bool}
    (h : segAllowed sr off n write = true) :
    sr.attr &&& 0x80 ≠ 0 ∧
    (write = true → sr.attr &&& 0x8 = 0 ∧ sr.attr &&& 2 ≠ 0) ∧
    (write = false → sr.attr &&& 0x8 ≠ 0 → sr.attr &&& 2 ≠ 0) ∧
    (sr.attr &&& 0xC ≠ 4 → off.toUInt64 + n.toUInt64 - 1 ≤ sr.limit.toUInt64) ∧
    (sr.attr &&& 0xC = 4 → off > sr.limit) := by
  simp only [segAllowed, bne, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hp, hw⟩, hr⟩, hl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hp
  · intro hwr; subst hwr; simp at hw; constructor <;> bv_decide
  · intro hwr hc; subst hwr; simp at hr; bv_decide
  · intro hed
    split at hl
    · rename_i hc; exfalso; apply hed; simp at hc; bv_decide
    · simpa using hl
  · intro hed
    split at hl
    · simp at hl; exact hl.1
    · rename_i hc; exfalso; apply hc; simp; bv_decide

/-! ## Paging -/

/-- With paging disabled, translation is the identity and does not change the machine. -/
theorem translate_nopg {lin : UInt32} {w u : Bool} {m : Machine} (h : m.cpu.cr0 &&& CR0.PG = 0) :
    translate lin w u m = .ok lin m := by
  simp [translate, h]

/-- User-mode accesses are only allowed through entries with U/S set at every level. -/
theorem pageAllowed_user {pde pte : UInt32} {large w wp : Bool}
    (h : pageAllowed pde pte large w true wp = true) :
    pde &&& 4 ≠ 0 ∧ (large = false → pte &&& 4 ≠ 0) := by
  simp only [pageAllowed] at h
  cases large <;> simp at h <;> constructor <;> (try intro) <;> (try simp) <;> bv_decide

/-- Writes are only allowed through entries with R/W set at every level, except for
supervisor writes with CR0.WP clear. -/
theorem pageAllowed_write {pde pte : UInt32} {large u wp : Bool}
    (h : pageAllowed pde pte large true u wp = true) (hwp : u = true ∨ wp = true) :
    pde &&& 2 ≠ 0 ∧ (large = false → pte &&& 2 ≠ 0) := by
  simp only [pageAllowed] at h
  rcases hwp with rfl | rfl <;> cases large <;> simp at h <;> constructor <;> (try intro) <;>
    (try simp) <;> bv_decide

/-- Supervisor reads are always permitted by the protection bits. -/
theorem pageAllowed_super_read (pde pte : UInt32) (large wp : Bool) :
    pageAllowed pde pte large false false wp = true := by
  simp [pageAllowed]

/-! ## Decoder -/

/-- Every decoded instruction is at most 15 bytes long. -/
theorem decode_len {m m' : Machine} {i : Inst} (h : decode m = .ok i m') : i.len ≤ 15 := by
  unfold decode at h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i r m1 hr
    by_cases hn : r.snd > 15
    · simp [hn, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at h
    · simp [hn, pure, EStateM.pure, EStateM.bind] at h
      obtain ⟨rfl, -⟩ := h
      simpa using hn
  · simp at h

end X86
