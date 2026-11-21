import Solutions.Exec.CodeWr
import Solutions.Logic.Mem
/-!
# Frames of runs: what stores leave alone

The byte view (`Ssl.memByte`) of a memory after word stores, outside the stored words.
-/
namespace Solutions.Exec
open X86 Solutions.Logic

theorem memByte_wr4_other {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a v : UInt32) (h : StoreOk base size g.mem a) {b : UInt32} (hb : b.toNat < g.get.size)
    (hd : b.toNat < a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    Ssl.memByte (CodeMem.wr4 g a v h).get b = Ssl.memByte g.get b :=
  memByte_wrBytes4_other h.1 hb hd

end Solutions.Exec
