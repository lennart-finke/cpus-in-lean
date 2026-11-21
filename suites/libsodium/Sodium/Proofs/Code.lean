import Solutions.Logic.Decode
import Sodium.Utils.Statement
/-!
# The libsodium image in the caller's memory

A well-formed call (`Ssl.Calls`) has the image at its link address; `codeMem` packages the caller's
memory with that fact, in the form `cbv` decodes from (`Solutions.Logic.Decode`): the code bytes are
`Image.byte i`, which `cbv` evaluates directly. `decode_*` are two instructions of
`sodium_memzero` decoded this way.
-/
namespace Sodium.Proofs
open X86 Ssl Solutions.Logic Sodium.Utils

/-- A memory holding the libsodium image. -/
abbrev SMem := CodeMem Image.base Image.size Image.byte

theorem image_size : Image.bytes.size = Image.size := by
  simp [Image.bytes, ByteArray.size]

theorem image_get (i : Nat) (h : i < Image.size) : Image.bytes.get! i = Image.byte i := by
  simp [Image.bytes, ByteArray.get!, getElem!_pos, h]

theorem img_bytes : img.bytes = Image.bytes := rfl
theorem img_base : img.base = Image.base := rfl

/-- The memory of a well-formed call, with the image in it. -/
def codeMem (c : Caller) {stack : Nat} {args : List UInt32} (h : Calls img c stack args) : SMem where
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

set_option maxRecDepth 100000 in
theorem decode_memzero_push (g : SMem) (eax ecx edx ebx esp ebp esi edi fl : UInt32) (ic : UInt64) :
    decode (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100C00, fl, ic⟩) =
      .ok { op := 0x50, len := 1 } (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100C00, fl, ic⟩) := by
  cbv

set_option maxRecDepth 100000 in
theorem decode_memzero_store (g : SMem) (eax ecx edx ebx esp ebp esi edi fl : UInt32) (ic : UInt64) :
    decode (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100C23, fl, ic⟩) =
      .ok { op := 0xC6, len := 4, modrm := 4, isMem := true, base := 2, index := 1, seg := 3 }
        (St.m ⟨g.get, eax, ecx, edx, ebx, esp, ebp, esi, edi, 0x100C23, fl, ic⟩) := by
  cbv

end Sodium.Proofs
