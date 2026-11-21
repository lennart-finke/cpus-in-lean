import Solutions.Logic.Mem
import Solutions.Logic.Decode
/-!
# Byte stores that keep the code

`CodeMem.wr1` is a byte store outside the code range as a new `CodeMem` (the byte counterpart of
`Solutions.Exec.CodeMem.wr4`); `wr1_get_size` is used by `sym_omega` (`Solutions.Logic.Cbx`).
-/
namespace Solutions.Logic
open X86

/-- A byte store at `a` is inside memory and outside the code range. -/
def StoreOk1 (base : UInt32) (size : Nat) (mem : ByteArray) (a : UInt32) : Prop :=
  a.toNat < mem.size ∧ (a.toNat < base.toNat ∨ base.toNat + size ≤ a.toNat)

/-- The memory after a byte store outside the code. -/
def CodeMem.wr1 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk1 base size g.mem a) : CodeMem base size code where
  mem := wrBytes g.mem a 1 v
  fits := by rw [size_wrBytes1 h.1]; exact g.fits
  ok := fun i hi => by
    rw [get!_wrBytes1 h.1]
    have := g.ok i hi
    rcases h.2 with h2 | h2 <;> rw [if_neg (by omega)] <;> exact this

theorem wr1_get {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk1 base size g.mem a) : (CodeMem.wr1 g a v h).get = wrBytes g.get a 1 v := rfl

theorem wr1_get_size {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk1 base size g.mem a) : (CodeMem.wr1 g a v h).get.size = g.get.size :=
  size_wrBytes1 h.1

/-- A byte stored twice at the same place: the second store wins. -/
theorem wr1_wr1 {base : UInt32} {size : Nat} {code : Nat → UInt8} (L : CodeMem base size code)
    (a v w : UInt32) (ok : StoreOk1 base size L.mem a)
    (ok' : StoreOk1 base size (CodeMem.wr1 L a v ok).mem a) :
    (CodeMem.wr1 (CodeMem.wr1 L a v ok) a w ok').get = (CodeMem.wr1 L a w ok).get := by
  show wrBytes (wrBytes L.mem a 1 v) a 1 w = wrBytes L.mem a 1 w
  have h1 := ok.1
  have s1 : (wrBytes L.mem a 1 v).size = L.mem.size := size_wrBytes1 h1
  apply bytes_ext
  · rw [size_wrBytes1 (by rw [s1]; exact h1), s1, size_wrBytes1 h1]
  · intro j _
    rw [get!_wrBytes1 (mem := wrBytes L.mem a 1 v) (by rw [s1]; exact h1), get!_wrBytes1 (mem := L.mem) h1,
      get!_wrBytes1 (mem := L.mem) h1]
    by_cases hj : j = a.toNat
    · simp [hj]
    · simp [hj]

end Solutions.Logic
