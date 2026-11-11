import X86.Boot
import X86.Proofs.Basic
/-!
# The multiprocessor platform (SMP workstream)

* `MpMachine.step_single`, `MpMachine.steps_single`: with one CPU the scheduler is exactly the
  single-CPU `step`, for any number of steps (`ofMachine_single`: `x86run`/`x86sys` without `--smp`
  build such a machine) — the N = 1 machine is the old machine.
* `step_waitSipi`: a CPU in the INIT state without INIT or STARTUP pending executes nothing and takes
  no other event, whatever INTR, NMI or SMI it has pending; `runnableState_waitSipi`: the scheduler
  never gives it a turn.
* `nextRunnable_runnable`: the CPU the scheduler switches to is runnable.
* `apicBaseWr_*`: the invalid IA32_APIC_BASE writes and x2APIC mode transitions are #GP(0) (APM vol. 2,
  table 16-5, figure 16-32); `x2Read_xapic`, `x2Write_xapic`: the x2APIC MSRs are #GP(0) outside
  x2APIC mode (16.11).
* `acceptFixed_swDisabled`: a software-disabled APIC accepts no fixed interrupt (16.3.1).
* `ioapicPin_masked`: a masked I/O APIC pin only records its level; nothing is delivered.
* `mpFloatingPointer_checksum`: the MP floating pointer structure's bytes sum to 0 (MP spec 4.1).
-/
namespace X86

namespace MpMachine

theorem step_single (s : MpMachine) (h : s.cores = #[]) : s.step = { s with m := X86.step s.m } := by
  cases s; simp_all [step]

theorem steps_single (s : MpMachine) (h : s.cores = #[]) (k : Nat) :
    Nat.repeat MpMachine.step k s = { s with m := Nat.repeat X86.step k s.m } := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.repeat, ih]
    rw [step_single _ (by simpa using h)]

theorem ofMachine_single (m : Machine) (q : Nat) : (ofMachine m 1 q).cores = #[] := by
  simp [ofMachine]

theorem runnableState_waitSipi (c : Cpu) (a : Apic) (smi : Bool) (d : UInt32) (i : Bool)
    (hw : c.smpx.waitSipi = true) (hi : a.init = false) (hs : a.sipi = none) :
    runnableState c a smi d i = false := by
  simp [runnableState, hw, hi, hs]

theorem nextRunnable_runnable (s : MpMachine) (k : Nat) (h : s.nextRunnable = some k) :
    s.runnableAt k = true := by
  unfold nextRunnable at h
  exact List.find?_some h

end MpMachine

/-- A CPU waiting for STARTUP (with no INIT or STARTUP message and no timer due) executes nothing:
the state is unchanged, whatever external interrupt, NMI or SMI is pending (APM vol. 2, 16.5). -/
theorem step_waitSipi (m : Machine) (ht : m.icount < m.timerAt) (hx : m.xev = true)
    (hw : m.cpu.smpx.waitSipi = true) (hi : m.apic.init = false) (hs : m.apic.sipi = none) :
    step m = m := by
  have hle : ¬ (m.icount ≥ m.timerAt) := by
    intro h'; exact absurd ht (UInt64.not_lt.mpr h')
  simp [step, hle, smpEvent?, hx, smpEventSlow, hi, hw, hs]

theorem apicBaseWr_reserved (m : Machine) (v : UInt64) (h : v &&& 0xFFFF0000000002FF ≠ 0) :
    m.apicBaseWr v = none := by
  simp [Machine.apicBaseWr, h]

/-- EXTD without AE is an invalid mode (APM table 16-5). -/
theorem apicBaseWr_extd_without_ae (m : Machine) (v : UInt64) (h1 : v &&& 0x800 = 0)
    (h2 : v &&& 0x400 ≠ 0) : m.apicBaseWr v = none := by
  simp only [Machine.apicBaseWr]
  split <;> simp_all

/-- x2APIC mode can only be left to the disabled state (APM 16.9.1). -/
theorem apicBaseWr_x2_to_xapic (m : Machine) (v : UInt64) (hx : m.apic.x2 = true)
    (h1 : v &&& 0x800 ≠ 0) (h2 : v &&& 0x400 = 0) : m.apicBaseWr v = none := by
  simp only [Machine.apicBaseWr]
  split <;> simp_all

/-- The disabled state can only be left to xAPIC mode (APM 16.9.1). -/
theorem apicBaseWr_disabled_to_x2 (m : Machine) (v : UInt64) (hd : m.apic.enabled = false)
    (h1 : v &&& 0x800 ≠ 0) (h2 : v &&& 0x400 ≠ 0) : m.apicBaseWr v = none := by
  simp only [Machine.apicBaseWr]
  split <;> simp_all

theorem x2Read_xapic (n : UInt32) (m : Machine) (h : m.apic.x2 = false) :
    Smp.x2Read n m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [Smp.x2Read, getM, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, h, gp, throw,
    throwThe, MonadExceptOf.throw, EStateM.throw]

theorem x2Write_xapic (n : UInt32) (v : UInt64) (m : Machine) (h : m.apic.x2 = false) :
    Smp.x2Write n v m = .error (.exc Vec.GP (some 0) 0) m := by
  simp [Smp.x2Write, getM, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, h, gp, throw,
    throwThe, MonadExceptOf.throw, EStateM.throw]

theorem acceptFixed_swDisabled (a : Apic) (v : UInt32) (l : Bool) (h : a.swEnabled = false) :
    a.acceptFixed v l = a := by
  simp [Apic.acceptFixed, h]

/-- A masked pin (redirection entry bit 16) only records its new level. -/
theorem ioapicPin_masked (m : Machine) (p : Nat) (l : Bool) (h : m.ioapic.entry p &&& 0x10000 ≠ 0) :
    ∃ s, m.ioapicPin p l = { m with ioapic := s } ∧ s.redir = m.ioapic.redir := by
  simp only [Machine.ioapicPin]
  split
  · exact ⟨m.ioapic, rfl, rfl⟩
  · refine ⟨{ m.ioapic with lines := if l then m.ioapic.lines ||| ((1 : UInt32) <<< p.toUInt32)
               else m.ioapic.lines &&& ~~~((1 : UInt32) <<< p.toUInt32) }, ?_, rfl⟩
    simp only [IoApic.entry] at h ⊢
    simp [h]

theorem mpFloatingPointer_checksum : mpFloatingPointer.foldl (· + ·) 0 = 0 := by decide +kernel

end X86
