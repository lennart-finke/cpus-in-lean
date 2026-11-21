import Solutions.Logic.Decode
import Curl.Hostcheck.Statement
/-!
# The curl image in the caller's memory

A well-formed call (`Ssl.Calls`) has the image at its link address; `codeMem` packages the caller's
memory with that fact, in the form `cbv` decodes from (`Solutions.Logic.Decode`): the code bytes are
`Image.byte i`, which `cbv` evaluates directly.
-/
namespace Curl.Proofs
open X86 Ssl Solutions.Logic Curl.Hostcheck

/-- A memory holding the curl image. -/
abbrev CMem := CodeMem Image.base Image.size Image.byte

theorem image_size : Image.bytes.size = Image.size := by
  simp [Image.bytes, ByteArray.size]

theorem image_get (i : Nat) (h : i < Image.size) : Image.bytes.get! i = Image.byte i := by
  simp [Image.bytes, ByteArray.get!, getElem!_pos, h]

theorem img_bytes : img.bytes = Image.bytes := rfl
theorem img_base : img.base = Image.base := rfl

/-- The memory of a well-formed call, with the image in it. -/
def codeMem (c : Caller) {stack : Nat} {args : List UInt32} (h : Calls img c stack args) : CMem where
  mem := c.mem
  fits := by
    have h2 := h.2.1
    rw [img_bytes, img_base, image_size] at h2
    exact h2
  ok := fun i hi => by
    have h3 := h.2.2.1
    rw [img_bytes, img_base] at h3
    have h1 : c.mem.size ≤ 2 ^ 32 := Nat.le_trans h.1 (by decide)
    have h2 := h.2.1
    rw [img_bytes, img_base] at h2
    rw [← image_get i hi]
    exact (CodeMem.ofMemBytes c.mem Image.base Image.bytes h2 h1 h3).ok i (by rw [image_size]; exact hi)

theorem codeMem_get (c : Caller) {stack : Nat} {args : List UInt32} (h : Calls img c stack args) :
    (codeMem c h).get = c.mem := rfl

end Curl.Proofs
