import X86.Step
import Std.Tactic.BVDecide
import X86.Proofs.Basic
import X86.Proofs.State
import X86.Proofs.ExtSys
/-!
# Long mode (`X86/Ext/LongModeBase.lean`, `X86/Ext/LongMode.lean`, `walkLong` in `X86/Machine.lean`)

* Activation: `withLma_lma` (EFER.LMA = LME ∧ CR0.PG after every write of CR0 or EFER),
  `movToCr0_lma` (after MOV CR0 the invariant holds, whatever held before), `movToCr0_nopae`,
  `movToCr0_csl` (#GP(0) for enabling paging with LME and PAE = 0 or CS.L = 1), `movToCr4_pae`
  (#GP(0) for clearing PAE in long mode), `eferOk_lme`, `eferOk_lma` (WRMSR cannot change LME with
  paging on, nor LMA), `lmaInv_efer` (the EFER write preserves the invariant).
* 4-level paging: `longCheck_user`, `longCheck_write`, `longCheck_nx` (user access, write and, with
  EFER.NXE, instruction fetch are allowed only if U/S, R/W, resp. NX = 0 hold at every level),
  `longCheck_smep` (a supervisor fetch with CR4.SMEP needs U/S = 0 at some level), `walkLong_check`
  (a successful walk passed `longCheck` on the entries it used), `walk_long` (with PAE and LMA the walk
  is the 4-level one), and the TLB theorems `translate_hit_nx`, `translate_hit_smep`,
  `translate_hit_smap` (`Proofs/State.lean`, `Proofs/ExtSys.lean`), which hold in every paging mode.
* The boundary: `decode_64bit`, `execInstr_64bit` (in 64-bit mode no instruction is fetched or
  executed: the step stops with `Fault.unsupported "64-bit mode"` and leaves memory and EIP unchanged).
* SYSENTER/SYSEXIT: `sysenter_long`, `sysexit_long` (#UD in long mode); `syscall_long` (SYSCALL from
  compatibility mode lands at CSTAR in a 64-bit DPL-0 code segment, with ECX = the return address and
  R11 = EFLAGS).
-/
/-- RIP split into the model's EIP and `ripHi`. -/
theorem X86.LongMode.split64 (x : UInt64) : ((x >>> 32).toUInt32.toUInt64 <<< 32) ||| x.toUInt32.toUInt64 = x := by
  simp only [X86.shl64, X86.shr64]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt64.toBitVec_toUInt32,
    UInt64.toBitVec_shiftRight]
  bv_decide

namespace X86
open LongMode

/-! ## Activation -/

/-- The LMA bit of `withLma` is LME ∧ PG. -/
theorem withLma_lma (efer cr0 : UInt32) :
    (withLma efer cr0 &&& EFER.LMA != 0) = (efer &&& EFER.LME != 0 && cr0 &&& CR0.PG != 0) := by
  cases hb : (efer &&& EFER.LME != 0 && cr0 &&& CR0.PG != 0) <;> simp [withLma, hb, EFER.LMA] <;> bv_decide

/-- `withLma` changes only the LMA bit. -/
theorem withLma_other (efer cr0 : UInt32) : withLma efer cr0 &&& ~~~EFER.LMA = efer &&& ~~~EFER.LMA := by
  have h1 : (efer ||| EFER.LMA) &&& ~~~EFER.LMA = efer &&& ~~~EFER.LMA := by simp only [EFER.LMA]; bv_decide
  have h2 : (efer &&& ~~~EFER.LMA) &&& ~~~EFER.LMA = efer &&& ~~~EFER.LMA := by simp only [EFER.LMA]; bv_decide
  unfold withLma; split <;> simp only [h1, h2]

/-- The activation invariant: EFER.LMA = EFER.LME ∧ CR0.PG (APM vol. 2, 14.6.1). -/
def lmaInv (c : Cpu) : Prop := (c.efer &&& EFER.LMA != 0) = (c.efer &&& EFER.LME != 0 && c.cr0 &&& CR0.PG != 0)

theorem lme_withLma (efer cr0 : UInt32) :
    (withLma efer cr0 &&& EFER.LME != 0) = (efer &&& EFER.LME != 0) := by
  have h1 : (efer ||| EFER.LMA) &&& EFER.LME = efer &&& EFER.LME := by simp only [EFER.LMA, EFER.LME]; bv_decide
  have h2 : (efer &&& ~~~EFER.LMA) &&& EFER.LME = efer &&& EFER.LME := by
    simp only [EFER.LMA, EFER.LME]; bv_decide
  unfold withLma; split <;> simp only [h1, h2]

/-- The state change of MOV CR0 establishes the invariant. -/
theorem setCr0_lma {v : UInt32} {m m' : Machine} (h : setCr0 v m = .ok () m') : lmaInv m'.cpu := by
  simp only [setCr0, flushTlbAll, modM] at h
  split at h <;> (cases h; simp only [lmaInv, lme_withLma, withLma_lma])

/-- The last action of a successful `x >>= f` succeeded from some state. -/
theorem bind_ok_last {α β : Type} {x : M α} {f : α → M β} {s s' : Machine} {b : β}
    (h : (x >>= f) s = .ok b s') : ∃ a s1, f a s1 = .ok b s' := by
  simp only [bind, EStateM.bind] at h
  split at h
  · exact ⟨_, _, h⟩
  · cases h

/-- After MOV CR0 (when it completes) the invariant holds, whatever the state before: the processor
sets EFER.LMA from LME and the new PG. -/
theorem movToCr0_lma {v : UInt32} {g : UInt8} {m m' : Machine} (h : movToCr 0 v g m = .ok () m') :
    lmaInv m'.cpu := by
  simp only [movToCr] at h
  obtain ⟨_, _, h⟩ := bind_ok_last h
  obtain ⟨_, _, h⟩ := bind_ok_last h
  repeat' (first | exact setCr0_lma h | (obtain ⟨_, _, h⟩ := bind_ok_last h) | (split at h))

/-- Enabling paging with EFER.LME = 1 and CR4.PAE = 0 is #GP(0) (APM vol. 2, table 14-5). -/
theorem movToCr0_nopae {v : UInt32} {c : Cpu} (hpg : c.cr0 &&& CR0.PG = 0) (hv : v &&& CR0.PG ≠ 0)
    (hlme : c.efer &&& EFER.LME ≠ 0) (hpae : c.cr4 &&& CR4.PAE = 0) : cr0Ok c v = false := by
  simp [cr0Ok, hpg, hv, hlme, hpae]

/-- Enabling paging with EFER.LME = 1 while CS.L = 1 is #GP(0) (table 14-5). -/
theorem movToCr0_csl {v : UInt32} {c : Cpu} (hpg : c.cr0 &&& CR0.PG = 0) (hv : v &&& CR0.PG ≠ 0)
    (hlme : c.efer &&& EFER.LME ≠ 0) (hl : lBit c.cs = true) : cr0Ok c v = false := by
  simp [cr0Ok, hpg, hv, hlme, hl]

/-- Clearing CR4.PAE while long mode is active is #GP(0) (table 14-5). -/
theorem movToCr4_pae {v : UInt32} {c : Cpu} (hl : lma c = true) (hv : v &&& CR4.PAE = 0) : cr4Ok c v = false := by
  simp [cr4Ok, hl, hv]

/-- WRMSR EFER cannot change LME while paging is enabled (table 14-5). -/
theorem eferOk_lme {v : UInt32} {c : Cpu} (h : eferOk c v = true) (hpg : c.cr0 &&& CR0.PG ≠ 0) :
    v &&& EFER.LME = c.efer &&& EFER.LME := by
  simp only [eferOk, Bool.and_eq_true, Bool.not_eq_true', hpg] at h
  simp at h
  have := h.1
  simp only [EFER.LME] at *
  bv_decide

/-- WRMSR EFER cannot change LMA (APM vol. 2, 3.1.7). -/
theorem eferOk_lma {v : UInt32} {c : Cpu} (h : eferOk c v = true) : v &&& EFER.LMA = c.efer &&& EFER.LMA := by
  simp only [eferOk, Bool.and_eq_true] at h
  have := h.2
  simp only [EFER.LMA] at *
  simp at this
  bv_decide

/-- An EFER value accepted by WRMSR keeps the activation invariant. -/
theorem lmaInv_efer {v : UInt32} {c : Cpu} (hi : lmaInv c) (h : eferOk c v = true) :
    lmaInv { c with efer := v } := by
  have h1 := eferOk_lma h
  simp only [lmaInv] at *
  by_cases hpg : c.cr0 &&& CR0.PG = 0
  · have : (c.efer &&& EFER.LMA != 0) = false := by rw [hi]; simp [hpg]
    simp at this
    simp [hpg]
    rw [h1]; simpa using this
  · have h2 := eferOk_lme h hpg
    have e1 : (v &&& EFER.LMA != 0) = (c.efer &&& EFER.LMA != 0) := by rw [h1]
    have e2 : (v &&& EFER.LME != 0) = (c.efer &&& EFER.LME != 0) := by rw [h2]
    rw [e1, e2, hi]

/-! ## 4-level paging -/

/-- A user access needs U/S = 1 at every level. -/
theorem longCheck_user {e4 e3 e2 e1 : UInt64} {nxe w wp f : Bool} {cr4 fl : UInt32} {i : Bool}
    (h : longCheck e4 e3 e2 e1 nxe w true wp f cr4 fl i = true) :
    e4 &&& 4 ≠ 0 ∧ e3 &&& 4 ≠ 0 ∧ e2 &&& 4 ≠ 0 ∧ e1 &&& 4 ≠ 0 := by
  simp only [longCheck, longAllowed, Bool.and_eq_true] at h
  have h := (pageAllowed_user h.1.1).1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- A write needs R/W = 1 at every level, unless it is a supervisor write with CR0.WP = 0. -/
theorem longCheck_write {e4 e3 e2 e1 : UInt64} {nxe u wp f : Bool} {cr4 fl : UInt32} {i : Bool}
    (h : longCheck e4 e3 e2 e1 nxe true u wp f cr4 fl i = true) (hw : u = true ∨ wp = true) :
    e4 &&& 2 ≠ 0 ∧ e3 &&& 2 ≠ 0 ∧ e2 &&& 2 ≠ 0 ∧ e1 &&& 2 ≠ 0 := by
  simp only [longCheck, longAllowed, Bool.and_eq_true] at h
  have h := (pageAllowed_write h.1.1 hw).1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- With EFER.NXE, an instruction fetch needs NX = 0 at every level. -/
theorem longCheck_nx {e4 e3 e2 e1 : UInt64} {w u wp : Bool} {cr4 fl : UInt32} {i : Bool}
    (h : longCheck e4 e3 e2 e1 true w u wp true cr4 fl i = true) :
    e4 &&& nxBit = 0 ∧ e3 &&& nxBit = 0 ∧ e2 &&& nxBit = 0 ∧ e1 &&& nxBit = 0 := by
  simp only [longCheck, longAllowed, Bool.and_eq_true, Bool.not_eq_true', Bool.true_and] at h
  have hx : ((e4 ||| e3 ||| e2 ||| e1) &&& nxBit != 0) = false := h.1.2
  simp only [bne_eq_false_iff_eq, nxBit] at hx
  simp only [nxBit]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- With CR4.SMEP, a supervisor instruction fetch needs U/S = 0 at some level. -/
theorem longCheck_smep {e4 e3 e2 e1 : UInt64} {nxe w wp : Bool} {cr4 fl : UInt32} {i : Bool}
    (h : longCheck e4 e3 e2 e1 nxe w false wp true cr4 fl i = true) (hs : cr4 &&& CR4.SMEP ≠ 0) :
    (e4 &&& e3 &&& e2 &&& e1) &&& 4 = 0 := by
  simp only [longCheck, Bool.and_eq_true] at h
  have h := smAllowed_smep h.2 hs
  bv_decide

/-- A successful long-mode walk passed `longCheck` on the entries it used (PML4E, PDPE, PDE, PTE; for
large pages the leaf repeated), with the access's NXE, WP, CR4 and EFLAGS. -/
theorem walkLong_check {lin : UInt64} {w u f i : Bool} {m : Machine} {r : UInt64 × UInt64 × UInt8}
    {m' : Machine} (h : walkLong lin w u f i m = .ok r m') :
    ∃ e4 e3 e2 e1, longCheck e4 e3 e2 e1 (m.cpu.efer &&& EFER.NXE != 0) w u (m.cpu.cr0 &&& CR0.WP != 0) f
      m.cpu.cr4 m.cpu.eflags i = true := by
  simp only [walkLong] at h
  split at h
  · simp at h
  · rename_i e4 e3 e2 e1 _ _ _ _
    split at h
    · simp at h
    · rename_i hc
      exact ⟨e4, e3, e2, e1, by simpa using hc⟩

/-- With CR4.PAE and EFER.LMA (and outside an SVM guest with nested paging, whose walk is the guest
walk through the nested tables, `gWalk`), the page walk is the 4-level walk. -/
theorem walk_long {lin : UInt32} {w u f i : Bool} {m : Machine} (hp : m.cpu.cr4 &&& CR4.PAE ≠ 0)
    (hl : m.cpu.efer &&& EFER.LMA ≠ 0) (hn : m.cpu.npOn = false) :
    walk lin w u f i m = walkLongTlb lin w u f i m := by
  have h1 : (m.cpu.cr4 &&& CR4.PAE != 0) = true := by simpa using hp
  have h2 : (m.cpu.efer &&& EFER.LMA != 0) = true := by simpa using hl
  unfold walk
  rw [if_neg (by simp [hn]), if_pos h1, if_pos h2]

/-! ## The 64-bit boundary -/

/-- In 64-bit mode the decoder fetches nothing and stops. -/
theorem decode_64bit {m : Machine} (h : in64 m.cpu = true) :
    decode m = .error (.unsupported "64-bit mode") m := by
  have hc : (m.cpu.cs.attr &&& 0x2000 != 0 && m.cpu.efer &&& EFER.LMA != 0) = true := by
    simpa [in64, lBit, lma] using h
  simp only [decode, bind, EStateM.bind, stop64, hc, ite_true]

/-- The model never executes an instruction in 64-bit mode (EFER.LMA = 1, CS.L = 1): the step's
instruction fetch stops with `Fault.unsupported "64-bit mode"` (which `step` records as the machine's
fatal stop), and memory and EIP are those before the step. -/
theorem execInstr_64bit {m : Machine} (h : in64 m.cpu = true) :
    ∃ m', execInstr m = .error (.unsupported "64-bit mode") m' ∧ m'.mem = m.mem ∧ m'.cpu.eip = m.cpu.eip ∧
      m'.cpu.cs = m.cpu.cs := by
  have hc : lBit m.cpu.cs = true := by simp only [in64, Bool.and_eq_true] at h; exact h.1
  have hl : lma m.cpu = true := by simp only [in64, Bool.and_eq_true] at h; exact h.2
  simp only [lBit, lma] at hc hl
  unfold execInstr
  split <;>
    (simp (disch := simp [in64, lBit, lma, hc, hl]) only [decode_64bit]; exact ⟨_, rfl, rfl, rfl, rfl⟩)

/-! ## SYSENTER, SYSEXIT, SYSCALL -/

theorem sysenter_long {m : Machine} (h : lma m.cpu = true) : Sys.sysenter m = .error (.exc Vec.UD none 0) m := by
  simp [Sys.sysenter, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem sysexit_long {m : Machine} (h : lma m.cpu = true) : Sys.sysexit m = .error (.exc Vec.UD none 0) m := by
  simp [Sys.sysexit, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- SYSCALL from compatibility mode: CPL 0 in a 64-bit code segment (so the model stops at the
next instruction), RIP = CSTAR, ECX = the return address, R11 = EFLAGS without RF. -/
theorem syscall_long {m m' : Machine} (hl : lma m.cpu = true) (h : Sys.syscall m = .ok () m') :
    m'.cpu.cs.dpl = 0 ∧ in64 m'.cpu = true ∧ rip m'.cpu = m.cpu.sysx.cstar ∧
      m'.cpu.ecx = m.cpu.eip ∧ m'.cpu.lmx.r11 = (m.cpu.eflags &&& ~~~Flag.RF).toUInt64 := by
  by_cases hs : m.cpu.efer &&& EFER.SCE = 0
  · simp [Sys.syscall, cpu, bind, EStateM.bind, hs, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · simp [Sys.syscall, cpu, bind, EStateM.bind, hs, hl, syscallLong, enter64, modCpu] at h
    subst h
    have hl' : m.cpu.efer &&& EFER.LMA ≠ 0 := by simpa [lma] using hl
    refine ⟨?_, ?_, ?_, rfl, rfl⟩
    · simp [SegReg.dpl]; decide
    · simp [in64, lBit, lma, hl']; decide
    · simp only [rip]; exact split64 _

end X86
