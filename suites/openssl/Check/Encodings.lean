import Check.Support
/-! Which of the instruction fuzzer's vectors fall into a given set of instruction classes. -/
namespace Check
open X86 Ssl

/-- Size of one record of `validation/test/gen.py`'s `vectors.bin`: a length byte, 15 instruction
bytes, then the initial state. -/
def vectorSize : Nat := 88

/-- The class of the instruction of the vector at offset `o`, decoded as the differential test
decodes it (32-bit code segment); `none` if it does not decode. -/
def vectorKey (base : ByteArray) (v : ByteArray) (o : Nat) : Option String :=
  let code := v.extract (o + 1) (o + 16)
  let mem := code.copySlice 0 base 0x20000 15
  let r : Regs := { eax := 0, ecx := 0, edx := 0, ebx := 0, esi := 0, edi := 0, ebp := 0, flags := 0 }
  match decode (entry mem r 0x20000 0x10000) with
  | .ok i _ => some (encKey i)
  | .error _ _ => none

/-- Count the vectors of each class. -/
def vectorClasses (path : String) : IO (Std.HashMap String Nat) := do
  let v ← IO.FS.readBinFile path
  let base := ByteArray.mk (Array.replicate 0x40000 0)
  let mut h : Std.HashMap String Nat := {}
  for k in [0:v.size / vectorSize] do
    if let some key := vectorKey base v (k * vectorSize) then h := h.insert key (h.getD key 0 + 1)
  return h

end Check
