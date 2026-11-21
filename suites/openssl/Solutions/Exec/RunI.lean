import Solutions.Exec.Call
/-!
# Running straight-line code at any instruction count

`runOk` (`Exec.Call`) evaluates `X86.step`, whose first test compares the instruction count with the
timer (`timerAt`); with a literal count `cbv` decides it, with a variable count it cannot. `runI`
evaluates the instruction part `stepInstr` instead, and checks with `Bool`s that `X86.step` is that
instruction part (no timer armed, no pending event, no SVM) and that the instruction advanced the count
by one. Its result is a `Run` as long as the count stays below the (disarmed) timer, which a bound on
the starting count gives (`run_of_runI`). The count itself is never inspected: `cbv` carries a variable
count `ic` through as `ic + 1 + 1 + …` (`icAdd ic n`), so one evaluation holds at every count.
-/
namespace Solutions.Exec
open X86 Ssl Solutions.Logic

/-- `x + 1 + 1 + … + 1` (`n` ones), the count after `n` instructions. -/
def icAdd (x : UInt64) : Nat → UInt64
  | 0 => x
  | n + 1 => icAdd x n + 1

theorem icAdd_eq (x : UInt64) : ∀ n, icAdd x n = x + n.toUInt64
  | 0 => by simp [icAdd]
  | n + 1 => by
    rw [icAdd, icAdd_eq x n, UInt64.add_assoc]; congr 1
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_add, Nat.toUInt64]

theorem icAdd_add (x : UInt64) (a b : Nat) : icAdd (icAdd x a) b = icAdd x (a + b) := by
  rw [icAdd_eq, icAdd_eq, icAdd_eq, UInt64.add_assoc]; congr 1
  apply UInt64.toNat_inj.1; simp [UInt64.toNat_add, Nat.toUInt64]

theorem icAdd_toNat (x : UInt64) (n : Nat) (h : x.toNat + n < 2 ^ 64) : (icAdd x n).toNat = x.toNat + n := by
  rw [icAdd_eq, UInt64.toNat_add]; simp [Nat.toUInt64]; omega

/-- No timer armed, no INIT/STARTUP/NMI event, outside SVM, and the next event is the instruction. -/
def stepOkB (m : Machine) : Bool :=
  m.timerAt == 0xFFFFFFFFFFFFFFFF && !m.xev && !m.cpu.svmx.guest && m.cpu.svmx.gif &&
    (match nextEvent m with | .instr => true | _ => false)

theorem step_eq_stepInstr (m : Machine) (h : stepOkB m = true) (hic : m.icount.toNat < 2 ^ 64 - 1) :
    X86.step m = stepInstr m := by
  simp only [stepOkB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨ht, hx⟩, hg⟩, hgif⟩, he⟩ := h
  have h1 : ¬ (m.icount ≥ m.timerAt) := by
    rw [ht]; intro h2; have := UInt64.le_iff_toNat_le.mp h2; simp at this; omega
  unfold X86.step
  simp only [h1, ite_false, smpEvent?, hx, Bool.false_eq_true, ite_false, hg, hgif, Bool.not_true,
    Bool.false_or]
  show stepAt m = stepInstr m
  unfold stepAt
  split <;> simp_all

/-- The rest of a step of `runI`: continue from `m'` if the instruction advanced the count by one. -/
def runIK (runI : Machine → Option Machine) (m m' : Machine) : Option Machine :=
  if m'.icount == m.icount + 1 then runI m' else none

/-- `k` instruction steps from `m` through running states, or `none`. -/
def runI (img : Img) : Nat → Machine → Option Machine
  | 0, m => some m
  | k + 1, m => if runningB img m && stepOkB m then runIK (runI img k) m (stepInstr m) else none

theorem run_of_runI' {img : Img} : ∀ {k : Nat} {m m' : Machine}, runI img k m = some m' →
    m.icount.toNat + k < 2 ^ 64 - 1 → Run img m m'
  | 0, m, m', h, _ => by
    simp only [runI, Option.some.injEq] at h; subst h; exact Run.refl img m
  | k + 1, m, m', h, hb => by
    simp only [runI] at h
    split at h
    · rename_i hr
      simp only [Bool.and_eq_true] at hr
      simp only [runIK] at h
      split at h
      · rename_i he
        have he' := beq_iff_eq.mp he
        have hstep := step_eq_stepInstr m hr.2 (by omega)
        refine Run.step ?_ hstep (run_of_runI' h ?_)
        · unfold Running; unfold runningB at hr; simpa using hr.1
        · rw [he', UInt64.toNat_add]; simp; omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- `runI` as a run, for a starting count `icAdd ic n` below the timer after `k` more steps. -/
theorem run_of_runI {img : Img} {k : Nat} {m m' : Machine} (h : runI img k m = some m')
    (hb : m.icount.toNat + k < 2 ^ 64 - 1) : Run img m m' := run_of_runI' h hb

end Solutions.Exec
