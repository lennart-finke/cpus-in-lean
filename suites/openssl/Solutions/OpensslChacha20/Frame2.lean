import Solutions.OpensslChacha20.Frame
/-!
# Stores inside a region given by a predicate
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec

theorem agreeOn_wrBytes4 {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a v : UInt32}
    (ha : a.toNat + 4 ≤ B.size) (hP : ∀ k, k < 4 → P (a.toNat + k)) :
    AgreeOn P A (wrBytes B a 4 v) := by
  refine ⟨by rw [size_wrBytes4 ha]; exact h.1, fun b hb hd => ?_⟩
  have h0 := hP 0 (by omega); have h1 := hP 1 (by omega)
  have h2 := hP 2 (by omega); have h3 := hP 3 (by omega)
  rw [get!_wrBytes4 ha]
  rw [if_neg (fun e => hd (by rw [e]; simpa using h0)), if_neg (fun e => hd (by rw [e]; exact h1)),
    if_neg (fun e => hd (by rw [e]; exact h2)), if_neg (fun e => hd (by rw [e]; exact h3))]
  exact h.2 b hb hd

theorem agreeOn_wr4 {base : UInt32} {size : Nat} {code : Nat → UInt8} {P : Nat → Prop} {A : ByteArray}
    {g : CodeMem base size code} (h : AgreeOn P A g.get) {a v : UInt32} (ok : StoreOk base size g.mem a)
    (hP : ∀ k, k < 4 → P (a.toNat + k)) : AgreeOn P A (CodeMem.wr4 g a v ok).get :=
  agreeOn_wrBytes4 h ok.1 hP

theorem agreeOn_wrBytes1 {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a v : UInt32}
    (ha : a.toNat < B.size) (hP : P a.toNat) : AgreeOn P A (wrBytes B a 1 v) := by
  refine ⟨by rw [size_wrBytes1 ha]; exact h.1, fun b hb hd => ?_⟩
  rw [get!_wrBytes1 ha, if_neg (fun e => hd (by rw [e]; exact hP))]
  exact h.2 b hb hd

theorem agreeOn_wr1 {base : UInt32} {size : Nat} {code : Nat → UInt8} {P : Nat → Prop} {A : ByteArray}
    {g : CodeMem base size code} (h : AgreeOn P A g.get) {a v : UInt32} (ok : StoreOk1 base size g.mem a)
    (hP : P a.toNat) : AgreeOn P A (CodeMem.wr1 g a v ok).get :=
  agreeOn_wrBytes1 h ok.1 hP

end Solutions.OpensslChacha20
