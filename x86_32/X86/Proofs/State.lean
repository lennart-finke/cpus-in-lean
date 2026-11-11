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

/-- With paging disabled (and outside an SVM guest with nested paging, where the linear address is a
guest-physical address translated by the nested tables), translation is the identity and does not
change the machine. -/
theorem translate_nopg {lin : UInt32} {w u f i : Bool} {m : Machine} (h : m.cpu.cr0 &&& CR0.PG = 0)
    (hn : m.cpu.npOn = false) :
    translate lin w u f i m = .ok lin.toUInt64 m := by
  simp [translate, h, hn]

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

/-- Execute-disable: with EFER.NXE set, PAE paging only permits an instruction fetch if the XD bit
(bit 63) is clear in the PDE and, for a 4 KiB page, in the PTE. -/
theorem paeAllowed_nx {pde pte : UInt64} {large w u wp : Bool}
    (h : paeAllowed pde pte large w u wp true true = true) :
    pde >>> 63 = 0 ∧ (large = false → pte >>> 63 = 0) := by
  simp only [paeAllowed, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨-, hx⟩ := h
  cases large <;> simp at hx <;> constructor <;> (try intro) <;> (try simp) <;> bv_decide

/-- Without EFER.NXE, PAE permissions are exactly those of 32-bit paging on the low entry dwords,
and instruction fetches are checked like reads. -/
theorem paeAllowed_no_nxe (pde pte : UInt64) (large w u wp f : Bool) :
    paeAllowed pde pte large w u wp f false = pageAllowed pde.toUInt32 pte.toUInt32 large w u wp := by
  simp [paeAllowed]

/-- PAE user and write permissions follow the 32-bit paging rules (`pageAllowed_user`,
`pageAllowed_write`) on the low dwords of the entries. -/
theorem paeAllowed_page {pde pte : UInt64} {large w u wp f nxe : Bool}
    (h : paeAllowed pde pte large w u wp f nxe = true) :
    pageAllowed pde.toUInt32 pte.toUInt32 large w u wp = true := by
  simp only [paeAllowed, Bool.and_eq_true] at h
  exact h.1

/-- A TLB hit never satisfies an instruction fetch from an execute-disabled translation: `translate`
with `fetch` only uses a cached entry whose NX bit is clear (otherwise it re-walks). -/
theorem translate_hit_nx {lin : UInt32} {w u i : Bool} {m : Machine}
    (hpg : m.cpu.cr0 &&& CR0.PG ≠ 0)
    (htag : m.tlbTag[((lin >>> 12) % tlbSize.toUInt32).toNat]! = ((lin &&& 0xFFFFF000) ||| 1))
    (hnx : m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.NX ≠ 0) :
    translate lin w u true i m = walk lin w u true i m := by
  have h1 : (m.cpu.cr0 &&& CR0.PG == 0) = false := by simpa using hpg
  have h2 : (m.tlbVal[((lin >>> 12) % tlbSize.toUInt32).toNat]! &&& Tlb.NX == 0) = false := by
    simpa using hnx
  simp only [translate, h1, htag, h2, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, Bool.or_false, Bool.and_false]

/-! ## Debug breakpoints -/

/-- With no breakpoint enabled in DR7, data accesses leave the machine unchanged (no breakpoint
bookkeeping), so the debug machinery is invisible to code that does not use it. -/
theorem dbData_disabled {lin n : UInt32} {w : Bool} {m : Machine} (h : m.cpu.bpOn = false) :
    dbData lin n w m = .ok () m := by
  simp [dbData, h]

/-- The same for I/O breakpoints. -/
theorem dbIo_disabled {port n : UInt32} {m : Machine} (h : m.cpu.bpOn = false) :
    dbIo port n m = .ok () m := by
  simp [dbIo, h]

/-! ## Virtual-8086 mode -/

/-- Virtual-8086 code always runs at CPL 3, so all its memory accesses are user-mode accesses for
paging (`pageAllowed_user`) and every privileged instruction is refused. -/
theorem cpl_vm86 (c : Cpu) (hpe : c.pe = true) (hvm : c.vm86 = true) : c.cpl = 3 := by
  simp [Cpu.cpl, hpe, hvm]

/-! ## Gates -/

/-- A far CALL or JMP through a call gate whose DPL is below the current privilege level raises
#GP(gate selector) before anything else happens: less privileged code can only use gates the
system made accessible to it. -/
theorem callGate_dpl {gsel : UInt16} {g : Desc} {call : Bool} {m : Machine}
    (h : g.dpl < m.cpu.cpl) :
    callGate gsel g call m = .error (.exc Vec.GP (some (gsel.toUInt32 &&& 0xFFFC)) 0) m := by
  simp [callGate, cpu, bind, EStateM.bind, h, gp, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-! ## System-management mode -/

/-- RSM outside SMM raises #UD and changes nothing: only SMM code can reload the processor state
from the SMRAM state-save map. -/
theorem rsm_outside_smm {m : Machine} (h : m.cpu.smm = false) :
    rsm m = .error (.exc Vec.UD none 0) m := by
  simp [rsm, cpu, bind, EStateM.bind, h, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-! ## x87 -/

/-- With CR0.EM or CR0.TS set, every ESC instruction raises #NM before touching any state: the
basis of lazy FPU context switching and of math emulation. -/
theorem fpCheck_nm {w : Bool} {m : Machine} (h : m.cpu.cr0 &&& (CR0.EM ||| CR0.TS) ≠ 0) :
    fpCheck w m = .error (.exc Vec.NM none 0) m := by
  simp [fpCheck, cpu, bind, EStateM.bind, h, exc, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-! ## Local APIC -/

/-- The local APIC only presents an interrupt whose priority class is above the processor priority
(TPR and the highest in-service class), and only while software-enabled: raising TPR to a class
masks every interrupt at or below it. -/
theorem apic_pending_above_ppr {a : Apic} {v : UInt32} (h : a.pending = some v) :
    a.swEnabled = true ∧ (v >>> 4) > (a.ppr >>> 4) := by
  unfold Apic.pending at h
  by_cases he : a.swEnabled = true
  · simp only [he, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · split at h
      · cases h; exact ⟨he, by assumption⟩
      · cases h
    · cases h
  · simp [he] at h

/-! ## Decoder -/

/-- Every decoded instruction is at most 15 bytes long. -/
theorem decode_len {m m' : Machine} {i : Inst} (h : decode m = .ok i m') : i.len ≤ 15 := by
  unfold decode at h
  simp only [bind, EStateM.bind] at h
  split at h
  · split at h
    · rename_i r m1 hr
      by_cases hn : r.snd > 15
      · simp [hn, gp, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at h
      · simp [hn, pure, EStateM.pure, EStateM.bind] at h
        obtain ⟨rfl, -⟩ := h
        simpa using hn
    · simp at h
  · simp at h

end X86
