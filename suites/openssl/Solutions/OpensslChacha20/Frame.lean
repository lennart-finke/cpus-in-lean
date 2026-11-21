import Solutions.Logic.MemRules
/-!
# Memories that agree outside a region

`Agree lo n A B`: `B` has the size of `A` and the same bytes outside `[lo, lo + n)`. Stores inside
the region keep it (`agree_wr4`, `agree_wr1`); loads outside it read the same (`rdRaw_agree4`,
`rdRaw_agree1`).
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec

/-- `B` is `A` outside `[lo, lo + n)`. -/
def Agree (lo : Nat) (n : Nat) (A B : ByteArray) : Prop :=
  B.size = A.size ∧ ∀ a, a < A.size → (a < lo ∨ lo + n ≤ a) → B.get! a = A.get! a

theorem Agree.refl (lo n : Nat) (A : ByteArray) : Agree lo n A A := ⟨rfl, fun _ _ _ => rfl⟩

theorem Agree.trans {lo n : Nat} {A B C : ByteArray} (h1 : Agree lo n A B) (h2 : Agree lo n B C) :
    Agree lo n A C :=
  ⟨h2.1.trans h1.1, fun a ha hd => (h2.2 a (by rw [h1.1]; exact ha) hd).trans (h1.2 a ha hd)⟩

theorem Agree.mono {lo n lo' n' : Nat} {A B : ByteArray} (h : Agree lo n A B) (h1 : lo' ≤ lo)
    (h2 : lo + n ≤ lo' + n') : Agree lo' n' A B :=
  ⟨h.1, fun a ha hd => h.2 a ha (by omega)⟩

theorem agree_wrBytes4 {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) {a v : UInt32}
    (ha : a.toNat + 4 ≤ B.size) (h1 : lo ≤ a.toNat) (h2 : a.toNat + 4 ≤ lo + n) :
    Agree lo n A (wrBytes B a 4 v) := by
  refine ⟨by rw [size_wrBytes4 ha]; exact h.1, fun b hb hd => ?_⟩
  rw [get!_wrBytes4 ha, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact h.2 b hb hd

theorem agree_wrBytes1 {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) {a v : UInt32}
    (ha : a.toNat < B.size) (h1 : lo ≤ a.toNat) (h2 : a.toNat < lo + n) :
    Agree lo n A (wrBytes B a 1 v) := by
  refine ⟨by rw [size_wrBytes1 ha]; exact h.1, fun b hb hd => ?_⟩
  rw [get!_wrBytes1 ha, if_neg (by omega)]
  exact h.2 b hb hd

theorem agree_wr4 {base : UInt32} {size : Nat} {code : Nat → UInt8} {lo n : Nat} {A : ByteArray}
    {g : CodeMem base size code} (h : Agree lo n A g.get) {a v : UInt32} (ok : StoreOk base size g.mem a)
    (h1 : lo ≤ a.toNat) (h2 : a.toNat + 4 ≤ lo + n) : Agree lo n A (CodeMem.wr4 g a v ok).get :=
  agree_wrBytes4 h ok.1 h1 h2

theorem agree_wr1 {base : UInt32} {size : Nat} {code : Nat → UInt8} {lo n : Nat} {A : ByteArray}
    {g : CodeMem base size code} (h : Agree lo n A g.get) {a v : UInt32} (ok : StoreOk1 base size g.mem a)
    (h1 : lo ≤ a.toNat) (h2 : a.toNat < lo + n) : Agree lo n A (CodeMem.wr1 g a v ok).get :=
  agree_wrBytes1 h ok.1 h1 h2

theorem rdRaw_agree4 {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) {a : UInt32}
    (ha : a.toNat + 4 ≤ A.size) (hd : a.toNat + 4 ≤ lo ∨ lo + n ≤ a.toNat) : rdRaw B a 4 = rdRaw A a 4 := by
  unfold rdRaw
  exact rdBytes4_congr (by rw [h.1]; exact ha) ha fun k hk => h.2 _ (by omega) (by omega)

theorem memByte_agree {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) {a : UInt32}
    (ha : a.toNat < A.size) (hd : a.toNat < lo ∨ lo + n ≤ a.toNat) : memByte B a = memByte A a := by
  rw [memByte_def (by rw [h.1]; exact ha), memByte_def ha, h.2 _ ha hd]

theorem rdRaw_agree1 {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) {a : UInt32}
    (ha : a.toNat < A.size) (hd : a.toNat < lo ∨ lo + n ≤ a.toNat) : rdRaw B a 1 = rdRaw A a 1 := by
  unfold rdRaw
  rw [rdBytes1_eq (by rw [h.1]; exact ha), rdBytes1_eq ha, memByte_agree h ha hd]

/-- `B` is `A` outside the addresses satisfying `P`. -/
def AgreeOn (P : Nat → Prop) (A B : ByteArray) : Prop :=
  B.size = A.size ∧ ∀ a, a < A.size → ¬ P a → B.get! a = A.get! a

theorem AgreeOn.refl (P : Nat → Prop) (A : ByteArray) : AgreeOn P A A := ⟨rfl, fun _ _ _ => rfl⟩

theorem AgreeOn.trans {P : Nat → Prop} {A B C : ByteArray} (h1 : AgreeOn P A B) (h2 : AgreeOn P B C) :
    AgreeOn P A C :=
  ⟨h2.1.trans h1.1, fun a ha hd => (h2.2 a (by rw [h1.1]; exact ha) hd).trans (h1.2 a ha hd)⟩

theorem AgreeOn.mono {P Q : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) (hPQ : ∀ a, P a → Q a) :
    AgreeOn Q A B :=
  ⟨h.1, fun a ha hd => h.2 a ha (fun hp => hd (hPQ a hp))⟩

theorem AgreeOn.of_agree {P : Nat → Prop} {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B)
    (hP : ∀ a, lo ≤ a → a < lo + n → P a) : AgreeOn P A B :=
  ⟨h.1, fun a ha hd => h.2 a ha (by
    by_cases h1 : lo ≤ a
    · by_cases h2 : a < lo + n
      · exact absurd (hP a h1 h2) hd
      · omega
    · omega)⟩

theorem AgreeOn.memByte {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a : UInt32}
    (ha : a.toNat < A.size) (hd : ¬ P a.toNat) : memByte B a = memByte A a := by
  rw [memByte_def (by rw [h.1]; exact ha), memByte_def ha, h.2 _ ha hd]

theorem AgreeOn.rdRaw4 {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a : UInt32}
    (ha : a.toNat + 4 ≤ A.size) (hd : ∀ k, k < 4 → ¬ P (a.toNat + k)) : rdRaw B a 4 = rdRaw A a 4 := by
  unfold rdRaw
  exact rdBytes4_congr (by rw [h.1]; exact ha) ha fun k hk => h.2 _ (by omega) (hd k hk)

end Solutions.OpensslChacha20
