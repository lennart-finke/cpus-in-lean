import Ssl.Harness
/-!
# Runs: composing steps, reaching states, loops

`Run img m m'`: `m'` is reached from `m` by some number of steps, each taken from a running state
(no return to the sentinel, no fault, no halt before `m'`). Runs compose (`Run.trans`); a single
step from a running state is a run (`Run.single`); a loop of `N` iterations with an invariant is a
run (`Run.loop`). `Reaches` and `Returns` follow from a run to a state with the property
(`Reaches.of_run`, `Returns.intro`).

`Run2 img m₁ m₂ m₁' m₂'` is the lock-step version for two machines executing the same instruction
addresses, from which `SameTraceG` (the shape of the suites' constant-time statements) follows.
-/
namespace Solutions.Logic
open X86 Ssl

theorem steps_zero (m : Machine) : steps 0 m = m := rfl

theorem steps_succ (n : Nat) (m : Machine) : steps (n + 1) m = steps n (X86.step m) := rfl

theorem steps_add (a b : Nat) (m : Machine) : steps (a + b) m = steps b (steps a m) := by
  induction a generalizing m with
  | zero => simp [steps]
  | succ a ih => rw [Nat.add_right_comm, steps_succ, steps_succ, ih]

theorem steps_succ' (n : Nat) (m : Machine) : steps (n + 1) m = X86.step (steps n m) := by
  rw [steps_add]; rfl

theorem trace_zero (img : Img) (m : Machine) : Trace img 0 m := fun _ h => absurd h (Nat.not_lt_zero _)

theorem trace_add {img : Img} {a b : Nat} {m : Machine} :
    Trace img (a + b) m ↔ Trace img a m ∧ Trace img b (steps a m) := by
  constructor
  · intro h
    refine ⟨fun i hi => h i (by omega), fun i hi => ?_⟩
    rw [← steps_add]; exact h (a + i) (by omega)
  · rintro ⟨h1, h2⟩ i hi
    by_cases hia : i < a
    · exact h1 i hia
    · have := h2 (i - a) (by omega)
      rwa [← steps_add, Nat.add_sub_cancel' (by omega)] at this

/-! ## Runs -/

/-- `m'` is reached from `m` through running states. -/
def Run (img : Img) (m m' : Machine) : Prop := ∃ k, Trace img k m ∧ steps k m = m'

theorem Run.refl (img : Img) (m : Machine) : Run img m m := ⟨0, trace_zero img m, rfl⟩

theorem Run.trans {img : Img} {m₁ m₂ m₃ : Machine} (h₁ : Run img m₁ m₂) (h₂ : Run img m₂ m₃) :
    Run img m₁ m₃ := by
  obtain ⟨a, ha, rfl⟩ := h₁
  obtain ⟨b, hb, rfl⟩ := h₂
  exact ⟨a + b, trace_add.2 ⟨ha, hb⟩, steps_add a b m₁⟩

theorem Run.single {img : Img} {m m' : Machine} (hr : Running img m) (h : X86.step m = m') :
    Run img m m' :=
  ⟨1, fun i hi => by rw [Nat.lt_one_iff.1 hi]; exact hr, h⟩

/-- A step from a running state followed by a run. -/
theorem Run.step {img : Img} {m m' m'' : Machine} (hr : Running img m) (h : X86.step m = m')
    (h' : Run img m' m'') : Run img m m'' :=
  (Run.single hr h).trans h'

/-- A loop: if each of `N` iterations runs from a state with invariant `I i` to one with
`I (i + 1)`, the whole loop runs from `I 0` to `I N`. -/
theorem Run.loop {img : Img} (I : Nat → Machine → Prop) (N : Nat)
    (hstep : ∀ i m, i < N → I i m → ∃ m', Run img m m' ∧ I (i + 1) m')
    {m : Machine} (h0 : I 0 m) : ∃ m', Run img m m' ∧ I N m' := by
  suffices ∀ j, j ≤ N → ∃ m', Run img m m' ∧ I j m' from this N (Nat.le_refl N)
  intro j
  induction j with
  | zero => intro _; exact ⟨m, Run.refl img m, h0⟩
  | succ j ih =>
    intro hj
    obtain ⟨m₁, hr₁, hI₁⟩ := ih (by omega)
    obtain ⟨m₂, hr₂, hI₂⟩ := hstep j m₁ (by omega) hI₁
    exact ⟨m₂, hr₁.trans hr₂, hI₂⟩

/-- A loop whose iteration count is not fixed in advance: a measure `μ` decreases with each
iteration until the exit condition holds. -/
theorem Run.loop_measure {img : Img} (I : Machine → Prop) (Q : Machine → Prop) (μ : Machine → Nat)
    (hstep : ∀ m, I m → Q m ∨ ∃ m', Run img m m' ∧ I m' ∧ μ m' < μ m)
    {m : Machine} (h0 : I m) : ∃ m', Run img m m' ∧ I m' ∧ Q m' := by
  suffices ∀ n m, μ m ≤ n → I m → ∃ m', Run img m m' ∧ I m' ∧ Q m' from this _ m (Nat.le_refl _) h0
  intro n
  induction n with
  | zero =>
    intro m hμ hI
    rcases hstep m hI with hQ | ⟨m', _, _, hlt⟩
    · exact ⟨m, Run.refl img m, hI, hQ⟩
    · omega
  | succ n ih =>
    intro m hμ hI
    rcases hstep m hI with hQ | ⟨m', hr, hI', hlt⟩
    · exact ⟨m, Run.refl img m, hI, hQ⟩
    · obtain ⟨m'', hr', hI'', hQ⟩ := ih m' (by omega) hI'
      exact ⟨m'', hr.trans hr', hI'', hQ⟩

/-! ## Reaching and returning -/

theorem Reaches.of_run {img : Img} {m m' : Machine} {P : Machine → Prop} (h : Run img m m')
    (hP : P m') : Reaches img m P := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, hk, hP⟩

theorem Reaches.run {img : Img} {m m' : Machine} {P : Machine → Prop} (h : Run img m m')
    (h' : Reaches img m' P) : Reaches img m P := by
  obtain ⟨k, hk, hP⟩ := h'
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨j + k, trace_add.2 ⟨hj, hk⟩, by rw [steps_add]; exact hP⟩

theorem Reaches.mono {img : Img} {m : Machine} {P Q : Machine → Prop} (h : Reaches img m P)
    (hPQ : ∀ m', P m' → Q m') : Reaches img m Q := by
  obtain ⟨k, hk, hP⟩ := h
  exact ⟨k, hk, hPQ _ hP⟩

/-- The usual way to prove a contract: a run from the entry to the return. -/
theorem Returns.intro {img : Img} {m₀ m₁ : Machine} {stack : Nat} {W : UInt32 → Prop}
    {Q : Machine → Prop} (hrun : Run img m₀ m₁) (hret : Returned img m₀ m₁) (hcs : CalleeSaved m₀ m₁)
    (hpres : Preserved m₀ m₁ stack W) (hQ : Q m₁) : Returns img m₀ stack W Q :=
  Reaches.of_run hrun ⟨hret, hcs, hpres, hQ⟩

/-! ## Callee-saved registers and memory -/

theorem CalleeSaved.refl (m : Machine) : CalleeSaved m m := ⟨rfl, rfl, rfl, rfl⟩

theorem CalleeSaved.of_eq {m₀ m₁ : Machine} (h₁ : m₁.cpu.ebx = m₀.cpu.ebx) (h₂ : m₁.cpu.esi = m₀.cpu.esi)
    (h₃ : m₁.cpu.edi = m₀.cpu.edi) (h₄ : m₁.cpu.ebp = m₀.cpu.ebp) : CalleeSaved m₀ m₁ :=
  ⟨h₁, h₂, h₃, h₄⟩

theorem Preserved.refl (m : Machine) (stack : Nat) (W : UInt32 → Prop) : Preserved m m stack W :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

theorem Preserved.mono {m₀ m₁ : Machine} {stack : Nat} {W W' : UInt32 → Prop}
    (h : Preserved m₀ m₁ stack W) (hW : ∀ a, W a → W' a) : Preserved m₀ m₁ stack W' :=
  ⟨h.1, fun a ha hw hs => h.2 a ha (fun hw' => hw (hW a hw')) hs⟩

/-- `Preserved` only looks at the memory and the entry stack pointer. -/
theorem Preserved.congr {m₀ m₁ m₀' m₁' : Machine} {stack : Nat} {W : UInt32 → Prop}
    (h : Preserved m₀ m₁ stack W) (h₀ : m₀'.mem = m₀.mem) (h₁ : m₁'.mem = m₁.mem)
    (hsp : m₀'.cpu.esp = m₀.cpu.esp) : Preserved m₀' m₁' stack W := by
  obtain ⟨hs, hb⟩ := h
  refine ⟨by rw [h₀, h₁, hs], fun a ha hw hst => ?_⟩
  rw [h₀, h₁]
  rw [h₀] at ha
  rw [hsp] at hst
  exact hb a ha hw hst

/-! ## Regions -/

theorem inRange_iff {lo : UInt32} {n : Nat} {a : UInt32} :
    InRange lo n a ↔ lo.toNat ≤ a.toNat ∧ a.toNat < lo.toNat + n := by
  unfold InRange
  rw [UInt32.le_iff_toNat_le]

theorem not_noWrites (a : UInt32) : ¬ NoWrites a := id

/-! ## Two runs in lock step -/

/-- Two runs of the same length through running states, at the same instruction addresses. -/
def Run2 (img : Img) (m₁ m₂ m₁' m₂' : Machine) : Prop :=
  ∃ k, Trace img k m₁ ∧ Trace img k m₂ ∧ steps k m₁ = m₁' ∧ steps k m₂ = m₂' ∧
    ∀ i, i < k → (steps i m₁).cpu.eip = (steps i m₂).cpu.eip

theorem Run2.refl (img : Img) (m₁ m₂ : Machine) : Run2 img m₁ m₂ m₁ m₂ :=
  ⟨0, trace_zero img m₁, trace_zero img m₂, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem Run2.trans {img : Img} {a₁ a₂ b₁ b₂ c₁ c₂ : Machine} (h₁ : Run2 img a₁ a₂ b₁ b₂)
    (h₂ : Run2 img b₁ b₂ c₁ c₂) : Run2 img a₁ a₂ c₁ c₂ := by
  obtain ⟨j, hj₁, hj₂, rfl, rfl, hje⟩ := h₁
  obtain ⟨k, hk₁, hk₂, rfl, rfl, hke⟩ := h₂
  refine ⟨j + k, trace_add.2 ⟨hj₁, hk₁⟩, trace_add.2 ⟨hj₂, hk₂⟩, steps_add _ _ _, steps_add _ _ _,
    fun i hi => ?_⟩
  by_cases hij : i < j
  · exact hje i hij
  · have := hke (i - j) (by omega)
    rwa [← steps_add, ← steps_add, Nat.add_sub_cancel' (by omega)] at this

theorem Run2.single {img : Img} {m₁ m₂ m₁' m₂' : Machine} (hr₁ : Running img m₁) (hr₂ : Running img m₂)
    (he : m₁.cpu.eip = m₂.cpu.eip) (h₁ : X86.step m₁ = m₁') (h₂ : X86.step m₂ = m₂') :
    Run2 img m₁ m₂ m₁' m₂' :=
  ⟨1, fun i hi => by rw [Nat.lt_one_iff.1 hi]; exact hr₁, fun i hi => by rw [Nat.lt_one_iff.1 hi]; exact hr₂,
    h₁, h₂, fun i hi => by rw [Nat.lt_one_iff.1 hi]; exact he⟩

theorem Run2.loop {img : Img} (I : Nat → Machine → Machine → Prop) (N : Nat)
    (hstep : ∀ i m₁ m₂, i < N → I i m₁ m₂ → ∃ m₁' m₂', Run2 img m₁ m₂ m₁' m₂' ∧ I (i + 1) m₁' m₂')
    {m₁ m₂ : Machine} (h0 : I 0 m₁ m₂) : ∃ m₁' m₂', Run2 img m₁ m₂ m₁' m₂' ∧ I N m₁' m₂' := by
  suffices ∀ j, j ≤ N → ∃ m₁' m₂', Run2 img m₁ m₂ m₁' m₂' ∧ I j m₁' m₂' from this N (Nat.le_refl N)
  intro j
  induction j with
  | zero => intro _; exact ⟨m₁, m₂, Run2.refl img m₁ m₂, h0⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, b, hr, hI⟩ := ih (by omega)
    obtain ⟨a', b', hr', hI'⟩ := hstep j a b (by omega) hI
    exact ⟨a', b', hr.trans hr', hI'⟩

/-- The suites' constant-time property for an image `img` (`Sodium.Utils.SameTrace` is this with the
libsodium image). -/
def SameTraceG (img : Img) (m m' : Machine) : Prop :=
  ∃ k, Trace img k m ∧ returned img (steps k m) = true ∧
       Trace img k m' ∧ returned img (steps k m') = true ∧
       ∀ i, i < k → (steps i m).cpu.eip = (steps i m').cpu.eip

theorem SameTraceG.intro {img : Img} {m m' r r' : Machine} (h : Run2 img m m' r r')
    (hr : returned img r = true) (hr' : returned img r' = true) : SameTraceG img m m' := by
  obtain ⟨k, h₁, h₂, rfl, rfl, he⟩ := h
  exact ⟨k, h₁, hr, h₂, hr', he⟩

/-- Two runs from equal starting states are in lock step. -/
theorem Run2.of_run {img : Img} {m m' : Machine} (h : Run img m m') : Run2 img m m m' m' := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, hk, hk, rfl, rfl, fun _ _ => rfl⟩

/-! ## Runs along a path of instruction addresses

`PRun img l m m'`: `m'` is reached from `m` through running states, the `i`-th step taken at the
address `l[i]`. Two runs along the same path are in lock step (`SameTraceG.of_prun`): this is how the
constant-time statements follow from runs whose path depends only on public values. -/

def PRun (img : Img) (l : List UInt32) (m m' : Machine) : Prop :=
  Trace img l.length m ∧ steps l.length m = m' ∧ ∀ i (h : i < l.length), (steps i m).cpu.eip = l[i]

theorem PRun.nil (img : Img) (m : Machine) : PRun img [] m m :=
  ⟨trace_zero img m, rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩

theorem PRun.single {img : Img} {m m' : Machine} (hr : Running img m) (h : X86.step m = m') :
    PRun img [m.cpu.eip] m m' :=
  ⟨fun i hi => by rw [Nat.lt_one_iff.1 hi]; exact hr, h, fun i hi => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi; rfl⟩

theorem PRun.append {img : Img} {l₁ l₂ : List UInt32} {m₁ m₂ m₃ : Machine} (h₁ : PRun img l₁ m₁ m₂)
    (h₂ : PRun img l₂ m₂ m₃) : PRun img (l₁ ++ l₂) m₁ m₃ := by
  obtain ⟨t₁, rfl, e₁⟩ := h₁
  obtain ⟨t₂, rfl, e₂⟩ := h₂
  refine ⟨by rw [List.length_append]; exact trace_add.2 ⟨t₁, t₂⟩, by rw [List.length_append, steps_add], ?_⟩
  intro i hi
  by_cases h : i < l₁.length
  · rw [List.getElem_append_left h]; exact e₁ i h
  · rw [List.length_append] at hi
    have := e₂ (i - l₁.length) (by omega)
    rw [← steps_add, Nat.add_sub_cancel' (by omega)] at this
    rw [List.getElem_append_right (by omega)]; exact this

theorem PRun.run {img : Img} {l : List UInt32} {m m' : Machine} (h : PRun img l m m') : Run img m m' :=
  ⟨l.length, h.1, h.2.1⟩

theorem PRun.cast {img : Img} {l l' : List UInt32} {m m' : Machine} (h : PRun img l m m') (e : l = l') :
    PRun img l' m m' := e ▸ h

/-- `N` iterations, each along the path `L`. -/
theorem PRun.loop {img : Img} (L : List UInt32) (I : Nat → Machine → Prop) (N : Nat)
    (hstep : ∀ i m, i < N → I i m → ∃ m', PRun img L m m' ∧ I (i + 1) m')
    {m : Machine} (h0 : I 0 m) : ∃ m', PRun img (List.replicate N L).flatten m m' ∧ I N m' := by
  suffices ∀ j, j ≤ N → ∃ m', PRun img (List.replicate j L).flatten m m' ∧ I j m' from this N (Nat.le_refl N)
  intro j
  induction j with
  | zero => intro _; exact ⟨m, PRun.nil img m, h0⟩
  | succ j ih =>
    intro hj
    obtain ⟨m₁, hr₁, hI₁⟩ := ih (by omega)
    obtain ⟨m₂, hr₂, hI₂⟩ := hstep j m₁ (by omega) hI₁
    refine ⟨m₂, (hr₁.append hr₂).cast ?_, hI₂⟩
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]

theorem SameTraceG.of_prun {img : Img} {l : List UInt32} {m m' r r' : Machine} (h : PRun img l m r)
    (h' : PRun img l m' r') (hr : returned img r = true) (hr' : returned img r' = true) : SameTraceG img m m' := by
  obtain ⟨t, rfl, e⟩ := h
  obtain ⟨t', rfl, e'⟩ := h'
  exact ⟨l.length, t, hr, t', hr', fun i hi => by rw [e i hi, e' i hi]⟩

end Solutions.Logic
