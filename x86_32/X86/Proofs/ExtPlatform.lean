import X86.Boot
import Std.Tactic.BVDecide
import X86.Proofs.Basic
/-!
# Platform review fixes (long mode and SMP)

* `initCpu_sipi`: INIT keeps a STARTUP the APIC accepted while the INIT was pending, so INIT and
  STARTUP sent back to back start the CPU whatever the scheduling (`Machine.initCpu`).
* `recv_init_sipi`: a STARTUP that follows an INIT to a CPU that has not run since is accepted.
* `afterInit_*`: INIT clears R8–R15 (R11, the one the model keeps), RIP/RSP bits 63:32 and EFER, keeps
  CR0.CD/NW and the x87 control word (AMD APM vol. 2, table 14-1); `atReset_afterInit_cr0`,
  `atReset_afterInit_fcw`: an application processor at power-up has RESET's CR0 = 6000_0010h and x87
  control word 0040h.
* `rsmEfer_lma`: RSM sets EFER.LMA to LME ∧ CR0.PG ∧ CR4.PAE of the saved image (APM 10.4), and
  `rsmEfer_lma_pg`: with the shutdown check for LME ∧ PG ∧ ¬PAE passed, LMA = LME ∧ PG — the
  invariant of `LongMode.withLma`; `rsmEfer_svme`: RSM does not change EFER.SVME.
* `eoiVec_tmr`: an EOI leaves TMR unchanged (APM 16.6.3).
* `levelEntry_mode`, `ioapicService_edge`: I/O APIC entries in NMI, INIT, SMI or ExtINT mode are never
  level-triggered in effect, so they never set remote IRR or re-send on their own (82093AA).
-/
namespace X86

theorem Apic.afterInit_sipi (a : Apic) : a.afterInit.sipi = a.sipi := rfl

theorem rawAccept_sipi (a : Apic) (v : UInt32) (l : Bool) : (a.rawAccept v l).sipi = a.sipi := by
  unfold Apic.rawAccept; split <;> rfl
theorem lvtFire_sipi (a : Apic) (k : Nat) (l : Bool) : (a.lvtFire k l).sipi = a.sipi := by
  unfold Apic.lvtFire; dsimp only
  split
  · rfl
  · split <;> (try split) <;> simp [rawAccept_sipi]
theorem error_sipi (a : Apic) (b : UInt32) : (a.error b).sipi = a.sipi := by
  simp [Apic.error, lvtFire_sipi]
theorem localInt_sipi (a : Apic) (k : Nat) (l : Bool) : (a.localInt k l).sipi = a.sipi := by
  unfold Apic.localInt; dsimp only
  split <;> simp [error_sipi, lvtFire_sipi]

theorem syncSmi_sipi (m : Machine) : m.syncSmi.apic.sipi = m.apic.sipi := by
  unfold Machine.syncSmi; split <;> rfl
theorem lint0Sync_sipi (m : Machine) : m.lint0Sync.apic.sipi = m.apic.sipi := by
  unfold Machine.lint0Sync; dsimp only
  simp only [Machine.syncXev, syncSmi_sipi]
  split <;> (try split) <;> simp [localInt_sipi]
theorem syncIntr_sipi (m : Machine) : m.syncIntr.apic.sipi = m.apic.sipi := by
  unfold Machine.syncIntr; split <;> simp [lint0Sync_sipi]
theorem syncApic_sipi (m : Machine) : m.syncApic.apic.sipi = m.apic.sipi := by
  simp [Machine.syncApic, syncIntr_sipi, Machine.syncXev, syncSmi_sipi]

/-- INIT keeps a STARTUP the APIC accepted while the INIT was pending. -/
theorem initCpu_sipi (m : Machine) : m.initCpu.apic.sipi = m.apic.sipi := by
  simp [Machine.initCpu, syncApic_sipi, Machine.syncTimer, Apic.afterInit_sipi]

theorem afterInit_r11 (c : Cpu) (sig : UInt32) (bsp : Bool) : (c.afterInit sig bsp).lmx.r11 = 0 := rfl
theorem afterInit_ripHi (c : Cpu) (sig : UInt32) (bsp : Bool) :
    (c.afterInit sig bsp).lmx.ripHi = 0 ∧ (c.afterInit sig bsp).lmx.rspHi = 0 := ⟨rfl, rfl⟩
theorem afterInit_efer (c : Cpu) (sig : UInt32) (bsp : Bool) : (c.afterInit sig bsp).efer = 0 := rfl
theorem afterInit_fpu (c : Cpu) (sig : UInt32) (bsp : Bool) :
    (c.afterInit sig bsp).fcw = c.fcw ∧ (c.afterInit sig bsp).fpr = c.fpr ∧
    (c.afterInit sig bsp).fempty = c.fempty ∧ (c.afterInit sig bsp).sse.xmm = c.sse.xmm := ⟨rfl, rfl, rfl, rfl⟩

/-- INIT keeps CR0.CD and CR0.NW and sets CR0 to 10h otherwise. -/
theorem afterInit_cr0 (c : Cpu) (sig : UInt32) (bsp : Bool) :
    (c.afterInit sig bsp).cr0 = 0x10 ||| (c.cr0 &&& 0x60000000) := rfl

theorem atReset_afterInit_cr0 (sig : UInt32) : (Cpu.atReset.afterInit sig false).cr0 = 0x60000010 := by
  simp only [Cpu.afterInit, Cpu.atReset, CR0.CD, CR0.NW]; decide
theorem atReset_afterInit_fcw (sig : UInt32) :
    (Cpu.atReset.afterInit sig false).fcw = 0x40 ∧ (Cpu.atReset.afterInit sig false).fempty = 0 := ⟨rfl, rfl⟩

theorem rsmEfer_lma (e cur cr0 cr4 : UInt32) :
    rsmEfer e cur cr0 cr4 &&& EFER.LMA ≠ 0 ↔
      (e &&& EFER.LME ≠ 0 ∧ cr0 &&& CR0.PG ≠ 0 ∧ cr4 &&& CR4.PAE ≠ 0) := by
  unfold rsmEfer; simp only [EFER.LMA, EFER.LME, EFER.SVME, CR0.PG, CR4.PAE, X86.shl32, X86.shr32]
  bv_decide

/-- With the shutdown check of RSM passed (`rsmInvalid`: LME ∧ PG requires PAE), LMA = LME ∧ PG. -/
theorem rsmEfer_lma_pg (e cur cr0 cr4 : UInt32)
    (h : e &&& EFER.LME ≠ 0 → cr0 &&& CR0.PG ≠ 0 → cr4 &&& CR4.PAE ≠ 0) :
    rsmEfer e cur cr0 cr4 &&& EFER.LMA ≠ 0 ↔ (e &&& EFER.LME ≠ 0 ∧ cr0 &&& CR0.PG ≠ 0) := by
  rw [rsmEfer_lma]
  constructor
  · exact fun ⟨a, b, _⟩ => ⟨a, b⟩
  · exact fun ⟨a, b⟩ => ⟨a, b, h a b⟩

theorem rsmEfer_svme (e cur cr0 cr4 : UInt32) :
    rsmEfer e cur cr0 cr4 &&& EFER.SVME = cur &&& EFER.SVME := by
  unfold rsmEfer; simp only [EFER.LMA, EFER.LME, EFER.SVME, CR0.PG, CR4.PAE, X86.shl32, X86.shr32]
  bv_decide

theorem eoiVec_tmr (a : Apic) (v : UInt32) : (a.eoiVec v).1.tmr = a.tmr := by
  simp only [Apic.eoiVec]
  split
  · rfl
  · split <;> rfl

/-- Delivery modes SMI (2), NMI (4), INIT (5) and ExtINT (7) are never level-triggered in effect. -/
theorem levelEntry_mode (e : UInt64) (h : 2 ≤ (e >>> 8) &&& 7) : IoApic.levelEntry e = false := by
  simp only [IoApic.levelEntry, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; simp only [X86.shr64] at h ⊢; bv_decide

/-- An entry that is not level-triggered in effect is never serviced as a level (it sends only on an
edge of its pin): writing it or an EOI for its vector sends nothing. -/
theorem ioapicService_edge (m : Machine) (p : Nat) (h : IoApic.levelEntry (m.ioapic.entry p) = false) :
    m.ioapicService p = m := by
  simp [Machine.ioapicService, h]

end X86
