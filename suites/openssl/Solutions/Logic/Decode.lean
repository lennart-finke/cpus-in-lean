import Solutions.Logic.Machine
import Solutions.Logic.Mem
/-!
# Decoding by evaluation

The decoder (`X86.decode`) reads the instruction bytes through `fetch8`, i.e. `rdBytes mem a 1`. With
an abstract memory these reads do not reduce, so neither does the decoder. `CodeMem base size code`
is a memory together with the fact that it holds the bytes `code i` at `base + i` for `i < size`
(an image placed at its link address). Reading such a memory through `CodeMem.get` is rewritten by
`rdBytes_codeMem`: inside the code range a 1-byte read is `code i`, every other read stays as the
opaque `rdRaw` (which is `rdBytes`). With these rules registered for the `cbv` tactic
(scoped to the namespace: `open Solutions.Logic`), `cbv` decodes
an instruction at a concrete address in one call, with the rest of the machine symbolic:

    example (g : CodeMem …) … : decode (St.m ⟨g.get, …, 0x100C00, …⟩) = .ok { op := 0x50, len := 1 } … := by
      cbv

`cbv` builds its proof from the defining equations and the rules below, so it needs no
extra trust. `opInfoTable_get` and `execTable_get` keep `cbv` from evaluating the two
1024-entry dispatch tables of the model in full.
-/
namespace Solutions.Logic
open X86

/-- `rdBytes`, under another name that `cbv` leaves alone. -/
def rdRaw (mem : ByteArray) (a n : UInt32) : UInt32 := rdBytes mem a n

/-- A memory that holds `code i` at `base + i` for every `i < size`. -/
structure CodeMem (base : UInt32) (size : Nat) (code : Nat → UInt8) where
  mem : ByteArray
  fits : base.toNat + size ≤ mem.size
  ok : ∀ i, i < size → mem.get! (base.toNat + i) = code i

/-- The memory of a `CodeMem`, as a function `cbv` does not unfold. -/
def CodeMem.get {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code) :
    ByteArray := g.mem

/-- A read of a `CodeMem`: a byte of the code range is the code byte. -/
theorem rdBytes_codeMem {base : UInt32} {size : Nat} {code : Nat → UInt8} (g : CodeMem base size code)
    (a n : UInt32) :
    rdBytes g.get a n =
      if n = 1 ∧ base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size then (code (a.toNat - base.toNat)).toUInt32
      else rdRaw g.get a n := by
  split
  · rename_i h
    obtain ⟨rfl, h1, h2⟩ := h
    have hs : a.toNat < g.mem.size := by have := g.fits; omega
    have := g.ok (a.toNat - base.toNat) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    unfold rdBytes CodeMem.get
    have h3 : a.toNat + (1 : UInt32).toNat ≤ g.mem.size := by simp; omega
    simp only [h3, ite_true]
    simp [this]
  · rfl

theorem opInfoTable_get (k : Nat) :
    opInfoTable.get! k = if k < 1024 then opInfo k.toUInt32 else 0 := by
  unfold opInfoTable
  split
  · rename_i h
    simp only [ByteArray.get!]
    rw [getElem!_pos _ _ (by simpa using h)]
    simp
  · rename_i h
    simp only [ByteArray.get!]
    rw [getElem!_neg _ _ (by simpa using h)]
    rfl

theorem execTable_get (k : Nat) :
    execTable[k]! = if k < 1024 then execOne k else default := by
  unfold execTable
  split
  · rename_i h
    rw [getElem!_pos _ _ (by simpa using h)]
    simp
  · rename_i h
    rw [getElem!_neg _ _ (by simpa using h)]

/-- Another description of the same code bytes. -/
def CodeMem.recode {base : UInt32} {size : Nat} {code code' : Nat → UInt8} (g : CodeMem base size code)
    (h : ∀ i, i < size → code i = code' i) : CodeMem base size code' :=
  ⟨g.mem, g.fits, fun i hi => (g.ok i hi).trans (h i hi)⟩

/-- The memory of a well-formed call holds the image (`Ssl.Calls`, its third clause). -/
def CodeMem.ofMemBytes (mem : ByteArray) (base : UInt32) (bytes : ByteArray)
    (hfit : base.toNat + bytes.size ≤ mem.size) (hlt : mem.size ≤ 2 ^ 32)
    (h : Ssl.memBytes mem base bytes.size = bytes.data.toList) :
    CodeMem base bytes.size (fun i => bytes.get! i) :=
  ⟨mem, hfit, fun i hi => by
    have h2 := (memBytes_eq_iff.mp h).2 i (by simpa using hi)
    have hn : (base + i.toUInt32).toNat = base.toNat + i := toNat_add_of_lt (by omega)
    rw [memByte_def (by omega), hn] at h2
    rw [h2]
    simp [ByteArray.get!, getElem!_pos, hi]⟩

/-! With `open Solutions.Logic`, `cbv` leaves memory reads and writes, the dispatch tables and the
`CodeMem` accessor alone and rewrites with the rules above. -/
attribute [scoped cbv_opaque] X86.rdBytes X86.wrBytes X86.opInfoTable X86.execTable rdRaw CodeMem.get
attribute [scoped cbv_eval] rdBytes_codeMem opInfoTable_get execTable_get

end Solutions.Logic
