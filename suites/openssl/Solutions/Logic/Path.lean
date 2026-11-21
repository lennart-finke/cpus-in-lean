import Solutions.Logic.Run
import Solutions.Logic.Step
import Solutions.Exec.Call
/-!
# Runs along a path, by evaluation

`runOkP img k m` takes `k` steps from `m` like `Solutions.Exec.runOk`, and also returns the
instruction addresses it ran; `cbv` evaluates both in one call, and `prun_of_runOkP` turns the result
into a `PRun`. `prun_step` is a single step proved through `execInstr` (at any instruction count).
-/
namespace Solutions.Logic
open X86 Ssl Solutions.Exec

/-- `k` steps from `m` through running states, with the instruction addresses, or `none`. -/
def runOkP (img : Img) : Nat → Machine → Option (Machine × List UInt32)
  | 0, m => some (m, [])
  | k + 1, m =>
    if runningB img m then
      match runOkP img k (X86.step m) with
      | some (m', l) => some (m', m.cpu.eip :: l)
      | none => none
    else none

theorem prun_of_runOkP {img : Img} : ∀ {k : Nat} {m m' : Machine} {l : List UInt32},
    runOkP img k m = some (m', l) → PRun img l m m'
  | 0, m, m', l, h => by
    simp only [runOkP, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact PRun.nil img m
  | k + 1, m, m', l, h => by
    simp only [runOkP] at h
    split at h
    · rename_i hr
      split at h
      · rename_i m₁ l₁ h₁
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrun : Running img m := by unfold Running; unfold runningB at hr; simpa using hr
        exact (PRun.single hrun rfl).append (prun_of_runOkP h₁)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- One step proved through `execInstr`, as a run along its address. -/
theorem prun_step (img : Img) (s s' : St) (hic : s.ic < 0xFFFFFFFFFFFFFFFF) (hTF : s.fl &&& Flag.TF = 0)
    (hx : okState (execInstr s.m) = some s'.m) (hic' : s'.ic = s.ic)
    (hr : Running img s.m) : PRun img [s.eip] s.m { s' with ic := s.ic + 1 }.m :=
  PRun.single hr (step_of_okState s hic hTF s' hx hic')

/-- A run of `a + b` steps is a run of `a` steps and then of `b` (to split long runs into small
`cbv` proofs). -/
theorem runOk_add (img : Img) (a b : Nat) (m : Machine) :
    runOk img (a + b) m = (runOk img a m).bind (runOk img b) := by
  induction a generalizing m with
  | zero => simp [runOk]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runOk]
    split
    · exact ih _
    · rfl

theorem runOk_split {img : Img} {a b : Nat} {m m₁ m₂ : Machine} (h₁ : runOk img a m = some m₁)
    (h₂ : runOk img b m₁ = some m₂) : runOk img (a + b) m = some m₂ := by
  rw [runOk_add, h₁]; exact h₂

/-- `runOkP` over `a + b` steps: the two runs, with their addresses concatenated. -/
theorem runOkP_split {img : Img} : ∀ {a b : Nat} {m m₁ m₂ : Machine} {l₁ l₂ : List UInt32},
    runOkP img a m = some (m₁, l₁) → runOkP img b m₁ = some (m₂, l₂) →
    runOkP img (a + b) m = some (m₂, l₁ ++ l₂)
  | 0, b, m, m₁, m₂, l₁, l₂, h₁, h₂ => by
    simp only [runOkP, Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simpa using h₂
  | a + 1, b, m, m₁, m₂, l₁, l₂, h₁, h₂ => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runOkP] at h₁ ⊢
    split at h₁
    · rename_i hr
      rw [if_pos hr]
      split at h₁
      · rename_i m' l' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h₁
        obtain ⟨rfl, rfl⟩ := h₁
        rw [runOkP_split h' h₂]
        rfl
      · exact absurd h₁ (by simp)
    · exact absurd h₁ (by simp)

end Solutions.Logic
