import Check.Support
/-! Compare the specifications with vectors produced by a reference implementation
(`tools/spec_vectors.py`). One vector per line; fields are hex strings, `-` for the empty string:

    sha256 MSG DIGEST            sha224 MSG DIGEST
    chacha20 KEY COUNTER NONCE PLAINTEXT CIPHERTEXT     (COUNTER: 8 hex digits, the 32-bit value)
    poly1305 KEY MSG TAG         x25519 SCALAR U RESULT

The transcripts of `tools/hw.py` (the task images run on QEMU or on real hardware) use the same
format, with further line kinds for results that have no reference implementation:

    sha256_transform H BLOCK H'  (hash words as 32 little-endian bytes)
    poly1305_ctx_size VALUE      x25519_public SCALAR RESULT
    fe_mul F G H   fe_sq F H   fe_add F G H   fe_sub F G H     (limb vectors as 40 bytes)

A line starting with `!` is a failure reported by the driver.
-/
namespace Check
open Ssl

def unhex (s : String) : Option (List UInt8) :=
  if s == "-" then some [] else
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87) else none
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
      let hi ← digit a
      let lo ← digit b
      let tail ← go rest
      return (hi * 16 + lo).toUInt8 :: tail
    | _ => none
  go s.toList

def leWords (b : List UInt8) : Array UInt32 :=
  Array.ofFn (n := b.length / 4) fun i =>
    b[4 * i.val]!.toUInt32 ||| (b[4 * i.val + 1]!.toUInt32 <<< 8) |||
    (b[4 * i.val + 2]!.toUInt32 <<< 16) ||| (b[4 * i.val + 3]!.toUInt32 <<< 24)

def sigma : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- `some true` if the specification reproduces the vector, `none` if the line is malformed. -/
def checkLine (line : String) : Option Bool := do
  match line.splitOn " " with
  | ["sha256", msg, want] => return Spec.Sha256.sha256 (← unhex msg) == (← unhex want)
  | ["sha224", msg, want] => return Spec.Sha256.sha224 (← unhex msg) == (← unhex want)
  | ["chacha20", key, counter, nonce, pt, ct] =>
    let key ← unhex key
    let nonce ← unhex nonce
    let counter ← unhex counter
    guard (key.length == 32 && nonce.length == 12 && counter.length == 4)
    let ctr : UInt32 := counter.foldl (fun acc b => (acc <<< 8) ||| b.toUInt32) 0
    let state := sigma ++ leWords key ++ #[ctr] ++ leWords nonce
    return Spec.Chacha.crypt 20 state (← unhex pt) == (← unhex ct)
  | ["poly1305", key, msg, want] =>
    let key ← unhex key
    guard (key.length == 32)
    return Spec.Poly1305.poly1305 key (← unhex msg) == (← unhex want)
  | ["x25519", k, u, want] =>
    let k ← unhex k
    let u ← unhex u
    guard (k.length == 32 && u.length == 32)
    return Spec.X25519.x25519 k u == (← unhex want)
  | ["sha256_transform", h, block, want] =>
    let h ← unhex h
    let block ← unhex block
    guard (h.length == 32 && block.length == 64)
    return wordBytes (Spec.Sha256.compress (leWords h) block) == (← unhex want)
  | ["poly1305_ctx_size", v] => return v == "000000ec"
  | ["x25519_public", k, want] =>
    let k ← unhex k
    guard (k.length == 32)
    return Spec.X25519.x25519 k OpensslX25519.basePoint == (← unhex want)
  | [op, f, g, h] => field op (← unhex f) (← unhex g) (← unhex h)
  | ["fe_sq", f, h] => field "fe_sq" (← unhex f) (← unhex f) (← unhex h)
  | _ => none
where
  /-- A field-operation line: inputs within the documented bounds, output within its bounds and
  congruent to the result modulo p. -/
  field (op : String) (f g h : List UInt8) : Option Bool := do
    guard (f.length == 40 && g.length == 40 && h.length == 40)
    let (f, g, h) := (leWords f, leWords g, leWords h)
    let (a, b, r) := (OpensslX25519.feValI f, OpensslX25519.feValI g, OpensslX25519.feValI h)
    let p := OpensslX25519.pI
    let (inN, inE, outN, outE, want) ← match op with
      | "fe_mul" => some (165, 26, 101, 25, a * b)
      | "fe_sq" => some (165, 26, 101, 25, a * a)
      | "fe_add" => some (110, 25, 110, 26, a + b)
      | "fe_sub" => some (110, 25, 110, 26, a - b)
      | _ => none
    guard (decide (OpensslX25519.Bounded inN inE f) && decide (OpensslX25519.Bounded inN inE g))
    return decide (OpensslX25519.Bounded outN outE h) && r % p == want % p

/-- Evaluate every line of `file`; `required` are line kinds that must occur. -/
def specVectors (file : String) (required : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines file).filter fun l => !l.isEmpty && !l.startsWith "#" && l != "END"
  let mut counts : List (String × Nat) := []
  for line in lines do
    if line.startsWith "!" then
      IO.eprintln s!"the driver reported a failure: {line}"; return 1
    match checkLine line with
    | some true =>
      let name := (line.splitOn " ").head!
      counts := match counts.lookup name with
        | some n => (name, n + 1) :: counts.filter (·.1 != name)
        | none => (name, 1) :: counts
    | some false => IO.eprintln s!"disagrees with the specification: {line.take 100}"; return 1
    | none => IO.eprintln s!"malformed line: {line.take 100}"; return 1
  for name in required do
    if (counts.lookup name).isNone then
      IO.eprintln s!"no {name} lines in {file}"; return 1
  if counts.isEmpty then
    IO.eprintln s!"no lines in {file}"; return 1
  for (name, n) in counts.reverse do
    IO.println s!"spec: {name} agrees with the specification on {n} lines"
  return 0

end Check
