import X64.Step
namespace X64.Application

/-- A compositional contract speaks about the same architectural step as the runner. -/
def steps : Nat → Machine → Machine
  | 0, m => m
  | n+1, m => steps n (step m)

def Reaches (m : Machine) (post : Machine → Prop) : Prop := ∃ n, post (steps n m)

theorem steps_add (a b : Nat) (m : Machine) : steps (a+b) m = steps b (steps a m) := by
  induction a generalizing m with
  | zero => simp [steps]
  | succ a ih => simpa [steps, Nat.succ_add] using ih (step m)

theorem Reaches.done (h : post m) : Reaches m post := ⟨0,h⟩

theorem Reaches.trans (h : Reaches m middle)
    (next : ∀ m', middle m' → Reaches m' post) : Reaches m post := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := next _ ha
  exact ⟨a+b, by simpa [steps_add] using hb⟩

/-- Application proofs can rule out asynchronous device events through an invariant;
there is no second instruction implementation in this layer. -/
structure Quiet (m : Machine) : Prop where
  timer : m.timerAt = maxU64
  count : m.icount < maxU64
  intr : m.intr = false
  awake : m.cpu.halted = false
  trap : m.cpu.flag Flag.TF = false

end X64.Application
