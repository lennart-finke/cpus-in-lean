import Sodium.Utils.Statement
import Check.Support
/-! Executable checks of the pinned machine code against the statements, on the CPU model: each
case is run in the OpenSSL suite's four memory placements (`Check.Support`), the precondition is
evaluated, every clause of `Returns` is checked, the result is compared with the specification,
and the instruction addresses of the run are compared with those of a run on other buffer
contents. These finite examples do not discharge the tasks. -/
open X86 Ssl Check Sodium.Utils Sodium.Spec

/-- The instruction addresses of the call, up to its return. -/
def eips (c : Caller) (fn : UInt32) : Array UInt32 := Id.run do
  let mut m := c.enter fn
  let mut out := #[]
  let mut fuel := 1000000
  while fuel > 0 && !(returned img m || m.fatal.isSome || m.cpu.halted) do
    out := out.push m.cpu.eip
    m := X86.step m
    fuel := fuel - 1
  return out

/-- Run the call of `c`, check its contract clauses, and check that the call of `c'` (the same
arguments, other buffer contents) executes the same instruction addresses. -/
def run (t : T) (name : String) (c c' : Caller) (fn : UInt32) (W : List (UInt32 × Nat)) : IO Machine := do
  let m ← t.call "sodium_utils" img c fn stackBound W
  ensure s!"{name}: the instruction addresses depend on the buffer contents" (eips c fn == eips c' fn)
  return m

def lengths : List Nat := [0, 1, 2, 3, 4, 5, 15, 16, 17, 31, 32, 33, 64]

def main : IO Unit := do
  let t ← T.new
  -- `sodium_base642bin` takes eight arguments, one word more than the placements leave above the stack pointer
  let layouts := (t.layouts img (stackBound + 16)).map fun L => { L with sp := L.sp - 16 }
  for n in lengths do for L in layouts do
    let (x, x') := (bytes n n, bytes n (n + 1000))
    let (s0, s1, s2) := (L.slot 0, L.slot 1, L.slot 2)
    -- hexadecimal
    for cap in [2 * n + 1, 2 * n + 9] do
      let args := bin2hexArgs s0 s1 cap
      let c ← t.caller img L (args x) [(s1, x)]
      let c' ← t.caller img L (args x') [(s1, x')]
      ensure "bin2hex precondition" (decide (EncodePre c (args x) s0 s1 cap (2 * n) x))
      let m ← run t "bin2hex" c c' Image.sym_sodium_bin2hex [(s0, 2 * n + 1)]
      ensure "bin2hex" (m.cpu.eax == s0 && bytesAt m s0 (2 * n + 1) == hex x ++ [0])
    for cap in [n, n + 5] do
      let args := fun y => hex2binArgs s0 s1 s2 cap (hex y)
      let c ← t.caller img L (args x) [(s1, hex x)]
      let c' ← t.caller img L (args x') [(s1, hex x')]
      ensure "hex2bin precondition" (decide (DecodePre c (args x) s0 s1 s2 cap n (hex x)))
      let m ← run t "hex2bin" c c' Image.sym_sodium_hex2bin [(s0, n), (s2, 4)]
      ensure "hex2bin" (m.cpu.eax == 0 && wordAt m s2 == n.toUInt32 && bytesAt m s0 n == x)
    -- base64
    for v in variants do
      let (e, e') := (encode v x, encode v x')
      for cap in [e.length + 1, e.length + 7] do
        let args := fun y => bin2base64Args s0 s1 cap y v
        let c ← t.caller img L (args x) [(s1, x)]
        let c' ← t.caller img L (args x') [(s1, x')]
        ensure "bin2base64 precondition" (decide (EncodePre c (args x) s0 s1 cap e.length x))
        let m ← run t "bin2base64" c c' Image.sym_sodium_bin2base64 [(s0, cap)]
        ensure "bin2base64" (m.cpu.eax == s0 && bytesAt m s0 cap == e ++ List.replicate (cap - e.length) 0)
      let args := fun y => base642binArgs s0 s1 s2 n y v
      let c ← t.caller img L (args e) [(s1, e)]
      let c' ← t.caller img L (args e') [(s1, e')]
      ensure "base642bin precondition" (decide (DecodePre c (args e) s0 s1 s2 n n e))
      let m ← run t "base642bin" c c' Image.sym_sodium_base642bin [(s0, n), (s2, 4)]
      ensure "base642bin" (m.cpu.eax == 0 && wordAt m s2 == n.toUInt32 && bytesAt m s0 n == x)
    -- comparing: equal buffers, buffers differing everywhere, buffers differing in the last byte
    let last := x.dropLast ++ (x.getLast?.map (· ^^^ 1)).toList
    for (a, b) in [(x, x), (x, x'), (x, last)] do
      let c ← t.caller img L [s0, s1, n.toUInt32] [(s0, a), (s1, b)]
      let c' ← t.caller img L [s0, s1, n.toUInt32] [(s0, x'), (s1, x')]
      ensure "memcmp precondition" (decide (MemcmpPre c s0 s1 a b))
      let m ← run t "memcmp" c c' Image.sym_sodium_memcmp []
      ensure "memcmp" (m.cpu.eax == if a == b then 0 else minusOne)
    -- wiping
    let c ← t.caller img L [s0, n.toUInt32] [(s0, x)]
    ensure "memzero precondition" (decide (MemzeroPre c s0 n))
    let m ← run t "memzero" c c Image.sym_sodium_memzero [(s0, n)]
    ensure "memzero" (bytesAt m s0 n == List.replicate n 0)
    -- padding
    for block in [1, 2, 3, 7, 8, 16, 100] do
      let len := paddedLength n block
      for cap in [len, len + 3] do
        let args := [s2, s0, n.toUInt32, block.toUInt32, cap.toUInt32]
        let c ← t.caller img L args [(s0, x)]
        ensure "pad precondition" (decide (PadPre c s2 s0 x block cap))
        let m ← run t "pad" c c Image.sym_sodium_pad [(s0, len), (s2, 4)]
        ensure "pad" (m.cpu.eax == 0 && wordAt m s2 == len.toUInt32 && bytesAt m s0 len == pad x block)
      -- unpadding: a valid padding, and buffers of the same length that are not
      let good := pad x block
      let others := [good, List.replicate len 0, good.map (fun b => if b == 0x80 then 0x81 else b),
                     bytes len (n + block), good.dropLast ++ [0x80], good.dropLast ++ [1]]
      for buf in others do
        let args := [s2, s0, len.toUInt32, block.toUInt32]
        let c ← t.caller img L args [(s0, buf)]
        let c' ← t.caller img L args [(s0, good)]
        ensure "unpad precondition" (decide (UnpadPre c s2 s0 buf block))
        let m ← run t "unpad" c c' Image.sym_sodium_unpad [(s2, 4)]
        ensure s!"unpad of {buf} with block {block}" <| match unpad buf block with
          | some k => m.cpu.eax == 0 && wordAt m s2 == k.toUInt32
          | none => m.cpu.eax == minusOne
      ensure "unpad inverts pad" (unpad good block == some n)
  -- the comparison of instruction addresses can fail: it tells an invalid hexadecimal digit from a valid one
  let L := layouts.head!
  let args := hex2binArgs (L.slot 0) (L.slot 1) (L.slot 2) 8 (hex [1, 2])
  let c ← t.caller img L args [(L.slot 1, hex [1, 2])]
  let c' ← t.caller img L args [(L.slot 1, [0x30, 0x67, 0x30, 0x32])]
  ensure "the instruction addresses of a rejected input differ"
    (eips c Image.sym_sodium_hex2bin != eips c' Image.sym_sodium_hex2bin)
  t.report [("sodium_utils", stackBound)]
