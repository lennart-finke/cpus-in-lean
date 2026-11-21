import Solutions.Logic.Machine
/-!
# A step is its instruction

For a machine `St.m s` (the state of a flat call) whose instruction count is below the timer's
(which `Ssl.entry` disables) and whose trap flag is clear, `X86.step` is `stepInstr`
(`step_eq`), and `stepInstr` is the instruction (`execInstr`) with the count advanced
(`stepInstr_eq`). An instruction's effect can so be proved once for any instruction count: the
count only enters through these two lemmas.
-/
namespace Solutions.Logic
open X86

theorem step_eq (s : St) (hic : s.ic < 0xFFFFFFFFFFFFFFFF) : X86.step s.m = stepInstr s.m := by
  have h1 : (s.m.icount ≥ s.m.timerAt) = False := by
    simp [St.m]; exact UInt64.lt_iff_toNat_lt.mp hic |> fun h => by omega
  unfold X86.step
  simp only [h1, ite_false]
  rfl

theorem stepInstr_eq (s : St) (hTF : s.fl &&& Flag.TF = 0) (i : Inst) (s' : St)
    (hx : execInstr s.m = .ok i s'.m) (hic : s'.ic = s.ic) :
    stepInstr s.m = { s' with ic := s.ic + 1 }.m := by
  have hbp : instrBp s.m.cpu = 0 := rfl
  have hm : ({ s.m with cpu := { s.m.cpu with shadow := false }, dbHit := 0 } : Machine) = s.m := rfl
  unfold stepInstr
  simp only [hbp, hm]
  simp only [show s.m.cpu.halted = false from rfl, show s.m.icount = s.ic from rfl, hx]
  simp only [show s'.m.icount = s'.ic from rfl, hic, show s.m.cpu.eflags = s.fl from rfl, hTF]
  simp only [beq_iff_eq, ↓reduceIte, bne_self_eq_false, Bool.false_and, Bool.false_eq_true]
  simp only [show s'.m.dbPend = 0 from rfl, show s'.m.cpu.shadow = false from rfl]
  simp
  rfl

/-- One step of an instruction whose effect `execInstr` is known, at any instruction count. -/
theorem step_of_exec (s : St) (hic : s.ic < 0xFFFFFFFFFFFFFFFF) (hTF : s.fl &&& Flag.TF = 0)
    (i : Inst) (s' : St) (hx : execInstr s.m = .ok i s'.m) (hic' : s'.ic = s.ic) :
    X86.step s.m = { s' with ic := s.ic + 1 }.m := by
  rw [step_eq s hic, stepInstr_eq s hTF i s' hx hic']

/-- The machine after an instruction that completed, or `none`. -/
def okState {α : Type} : EStateM.Result Fault Machine α → Option Machine
  | .ok _ m => some m
  | .error _ _ => none

/-- `step_of_exec` with the instruction left implicit (`okState`, which `cbv` evaluates). -/
theorem step_of_okState (s : St) (hic : s.ic < 0xFFFFFFFFFFFFFFFF) (hTF : s.fl &&& Flag.TF = 0)
    (s' : St) (hx : okState (execInstr s.m) = some s'.m) (hic' : s'.ic = s.ic) :
    X86.step s.m = { s' with ic := s.ic + 1 }.m := by
  cases h : execInstr s.m with
  | ok i m =>
    rw [h] at hx
    simp only [okState, Option.some.injEq] at hx
    subst hx
    exact step_of_exec s hic hTF i s' h hic'
  | error e m => rw [h] at hx; simp [okState] at hx

end Solutions.Logic
