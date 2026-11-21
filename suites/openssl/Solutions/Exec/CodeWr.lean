import Solutions.Exec.Mem
import Solutions.Logic.Decode
/-!
# Stores that keep the code

A word store outside the code range keeps a `CodeMem` a `CodeMem`: `CodeMem.wr4` is the store as a
new `CodeMem`, so that instruction fetches after stores still read the code bytes directly
(`Solutions.Logic.rdBytes_codeMem`) instead of looking through every earlier store.
-/
namespace Solutions.Exec
open X86 Solutions.Logic

/-- A word store at `a` is inside memory and outside the code range. -/
def StoreOk (base : UInt32) (size : Nat) (mem : ByteArray) (a : UInt32) : Prop :=
  a.toNat + 4 ≤ mem.size ∧ (a.toNat + 4 ≤ base.toNat ∨ base.toNat + size ≤ a.toNat)

/-- The memory after a word store outside the code. -/
def CodeMem.wr4 {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk base size g.mem a) : CodeMem base size code where
  mem := wrBytes g.mem a 4 v
  fits := by rw [size_wrBytes]; exact g.fits
  ok := fun i hi => by
    rw [get!_wrBytes4 h.1]
    have := g.ok i hi
    rcases h.2 with h2 | h2 <;>
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] <;> exact this

theorem wr4_get {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk base size g.mem a) : (CodeMem.wr4 g a v h).get = wrBytes g.get a 4 v := rfl

theorem wr4_get_size {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk base size g.mem a) : (CodeMem.wr4 g a v h).get.size = g.get.size :=
  size_wrBytes _ _ _ _

end Solutions.Exec
