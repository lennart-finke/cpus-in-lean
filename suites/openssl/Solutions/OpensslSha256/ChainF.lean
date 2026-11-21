import Solutions.OpensslSha256.Chain
/-! Chains of steps with the flags given, for `apply` (the count is a literal). -/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256

theorem StepsF.consK {E : Env} (k : Nat) {n : Nat} {p₁ p₂ p₃ : UInt32} {r₁ r₂ r₃ : R} {f₁ f₂ f₃ : UInt32}
    {F₁ F₂ F₃ : Nat → UInt32} (h₁ : StepsF E k p₁ r₁ f₁ F₁ p₂ r₂ f₂ F₂) (h₂ : StepsF E n p₂ r₂ f₂ F₂ p₃ r₃ f₃ F₃) :
    StepsF E (n + k) p₁ r₁ f₁ F₁ p₃ r₃ f₃ F₃ := by
  have := h₁.trans h₂; rwa [Nat.add_comm] at this

theorem StepsF.refl (E : Env) (p : UInt32) (r : R) (fl : UInt32) (F : Nat → UInt32) :
    StepsF E 0 p r fl F p r fl F :=
  fun M ic hI _ => ⟨M, by simpa using Run.refl img _, hI⟩

end Solutions.OpensslSha256
