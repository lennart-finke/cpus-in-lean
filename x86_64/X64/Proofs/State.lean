import Std.Tactic.BVDecide
import X64.Decode
import X64.Proofs.Basic
namespace X64

set_option maxHeartbeats 4000000

theorem reg_cases (r : UInt8) (h : r < 16) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
    r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by bv_decide

theorem getReg_setReg (c : Cpu) (r : UInt8) (v : UInt64) (h : r < 16) :
    (c.setReg r v).getReg r = v := by
  rcases reg_cases r h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem wr32_zero_extends (c : Cpu) (r : UInt8) (v : UInt64) (h : r < 16) (rex : Bool) :
    (c.wrReg 4 r v rex).getReg r = v &&& 0xFFFFFFFF := by
  simp only [Cpu.wrReg]; exact getReg_setReg c r _ h

theorem wr64_full (c : Cpu) (r : UInt8) (v : UInt64) (h : r < 16) (rex : Bool) :
    (c.wrReg 8 r v rex).getReg r = v := by
  simp only [Cpu.wrReg]; exact getReg_setReg c r _ h

theorem wr16_preserves_upper (c : Cpu) (r : UInt8) (v : UInt64) (h : r < 16) (rex : Bool) :
    (c.wrReg 2 r v rex).getReg r &&& 0xFFFFFFFFFFFF0000 = c.getReg r &&& 0xFFFFFFFFFFFF0000 := by
  simp only [Cpu.wrReg]; simp
  rw [getReg_setReg c r _ h]
  simp only [Sz.mask]; bv_decide

theorem ah_alias (c : Cpu) (v : UInt64) :
    (c.wrReg 1 4 v false).rax = (c.rax &&& 0xFFFFFFFFFFFF00FF) ||| ((v &&& 255) <<< 8) := by
  simp only [Cpu.wrReg, Cpu.setReg, Cpu.getReg]; simp; bv_decide

theorem rex_spl_alias (c : Cpu) (v : UInt64) :
    (c.wrReg 1 4 v true).rsp = (c.rsp &&& 0xFFFFFFFFFFFFFF00) ||| (v &&& 255) := by
  simp only [Cpu.wrReg, Cpu.setReg, Cpu.getReg, Sz.mask]; simp; bv_decide

theorem canonical_iff (v : UInt64) :
    canonical v = true ↔ v < 0x800000000000 ∨ v ≥ 0xFFFF800000000000 := by
  simp only [canonical, shr64]
  bv_decide

theorem pageAllowed_user (rw us nx : Bool) (a : Access) (wp : Bool)
    (h : pageAllowed rw us nx a true wp = true) : us = true := by
  cases us <;> simp_all (config := { decide := true }) [pageAllowed]

theorem pageAllowed_write (rw us nx user wp : Bool)
    (h : pageAllowed rw us nx .write user wp = true) (enforced : user = true ∨ wp = true) :
    rw = true := by
  cases rw <;> rcases enforced with rfl | rfl <;> simp_all (config := { decide := true }) [pageAllowed]

theorem pageAllowed_fetch (rw us nx user wp : Bool)
    (h : pageAllowed rw us nx .fetch user wp = true) : nx = false := by
  cases nx <;> simp_all (config := { decide := true }) [pageAllowed]

theorem decode_len {m m' : Machine} {i : Inst} (h : decode m = .ok i m') : i.len ≤ 15 := by
  unfold decode at h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i decoded m1 hd
    by_cases hn : decoded.len > 15
    · simp [hn, gp, exc, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at h
    · simp [hn, pure, EStateM.pure] at h
      obtain ⟨rfl, -⟩ := h
      simpa using hn
  · simp at h

end X64
