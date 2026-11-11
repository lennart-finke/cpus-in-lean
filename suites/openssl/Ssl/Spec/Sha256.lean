import Ssl.Bytes
/-!
# Specification: FIPS 180-4 SHA-256 / SHA-224

Padding (§5.1.1), message schedule and compression (§6.2.2), constants (§4.2.2), initial values
(§5.3.2/§5.3.3). Checked against FIPS/NIST vectors by kernel evaluation below, and against a
reference implementation by `tools/spec_vectors.py`. `pad` encodes the bit length in 64 bits, so
the definition is SHA-256 for messages shorter than `lenBound` = 2^61 bytes, the standard's limit.
-/
namespace Ssl.Spec.Sha256
open Ssl

/-- FIPS 180-4 §1: SHA-256 and SHA-224 are defined for messages of fewer than 2^64 bits, that is
fewer than `lenBound` bytes. -/
def lenBound : Nat := 2 ^ 61

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
/-- FIPS 180-4 §4.1.2 (`Sigma`/`sigma` are the standard's upper/lower-case sigma functions). -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def Sigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def Sigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def sigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def sigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- FIPS 180-4 §4.2.2: the first 32 bits of the fractional parts of the cube roots of the first 64 primes. -/
def K : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- FIPS 180-4 §5.3.3: SHA-256 initial hash value. -/
def H0_256 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
/-- FIPS 180-4 §5.3.2: SHA-224 initial hash value. -/
def H0_224 : Array UInt32 :=
  #[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-- FIPS 180-4 §5.1.1: append `1`, then zeros, then the 64-bit big-endian bit length, to a multiple of
512 bits. -/
def pad (msg : List UInt8) : List UInt8 :=
  let l := msg.length
  msg ++ [0x80] ++ List.replicate ((119 - l % 64) % 64) 0 ++ be64 (8 * l).toUInt64

/-- The big-endian word `i` of a block. -/
def be32At (block : List UInt8) (i : Nat) : UInt32 :=
  (block[4 * i]!.toUInt32 <<< 24) ||| (block[4 * i + 1]!.toUInt32 <<< 16) |||
  (block[4 * i + 2]!.toUInt32 <<< 8) ||| block[4 * i + 3]!.toUInt32

/-- FIPS 180-4 §6.2.2 step 1: the 64-word message schedule of a 64-byte block. -/
def schedule (block : List UInt8) : Array UInt32 :=
  let W := (List.range 16).foldl (fun W i => W.push (be32At block i)) #[]
  (List.range 48).foldl (fun W t => W.push (sigma1 W[t + 14]! + W[t + 9]! + sigma0 W[t + 1]! + W[t]!)) W

/-- FIPS 180-4 §6.2.2 steps 2–4: one block through the compression function. -/
def compress (H : Array UInt32) (block : List UInt8) : Array UInt32 :=
  let W := schedule block
  let (a, b, c, d, e, f, g, h) :=
    (List.range 64).foldl
      (fun (a, b, c, d, e, f, g, h) t =>
        let T1 := h + Sigma1 e + Ch e f g + K[t]! + W[t]!
        let T2 := Sigma0 a + Maj a b c
        (T1 + T2, a, b, c, d + T1, e, f, g))
      (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!)
  #[H[0]! + a, H[1]! + b, H[2]! + c, H[3]! + d, H[4]! + e, H[5]! + f, H[6]! + g, H[7]! + h]

/-- The 64-byte blocks of a padded message. -/
def blocksAux : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | _, [] => []
  | n + 1, bs => bs.take 64 :: blocksAux n (bs.drop 64)
def blocks (bs : List UInt8) : List (List UInt8) := blocksAux bs.length bs

/-- The final hash words from an initial value. -/
def hashWords (H0 : Array UInt32) (msg : List UInt8) : Array UInt32 := (blocks (pad msg)).foldl compress H0

/-- SHA-256 of a byte string: the 8 hash words big-endian. -/
def sha256 (msg : List UInt8) : List UInt8 :=
  let H := hashWords H0_256 msg
  (List.range 8).flatMap fun i => be32 H[i]!
/-- SHA-224: the SHA-224 initial value, truncated to the first 7 words. -/
def sha224 (msg : List UInt8) : List UInt8 :=
  let H := hashWords H0_224 msg
  (List.range 7).flatMap fun i => be32 H[i]!

set_option maxRecDepth 100000 in
/-- FIPS 180-4 / NIST CAVP: SHA-256("abc"). -/
theorem sha256_abc :
    sha256 [0x61, 0x62, 0x63] =
      [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
       0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by
  decide

set_option maxRecDepth 100000 in
/-- SHA-224("abc"). -/
theorem sha224_abc :
    sha224 [0x61, 0x62, 0x63] =
      [0x23, 0x09, 0x7d, 0x22, 0x34, 0x05, 0xd8, 0x22, 0x86, 0x42, 0xa4, 0x77, 0xbd, 0xa2, 0x55, 0xb3,
       0x2a, 0xad, 0xbc, 0xe4, 0xbd, 0xa0, 0xb3, 0xf7, 0xe3, 0x6c, 0x9d, 0xa7] := by
  decide

set_option maxRecDepth 100000 in
/-- SHA-256 of the empty message. -/
theorem sha256_empty :
    sha256 [] =
      [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
       0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] := by
  decide

set_option maxRecDepth 100000 in
/-- FIPS 180-4 / NIST CAVP two-block message `abcdbcde…nopq` (56 bytes: the padding spills into a
second block). -/
theorem sha256_two_blocks :
    sha256 [0x61, 0x62, 0x63, 0x64, 0x62, 0x63, 0x64, 0x65, 0x63, 0x64, 0x65, 0x66, 0x64, 0x65, 0x66, 0x67,
       0x65, 0x66, 0x67, 0x68, 0x66, 0x67, 0x68, 0x69, 0x67, 0x68, 0x69, 0x6a, 0x68, 0x69, 0x6a, 0x6b,
       0x69, 0x6a, 0x6b, 0x6c, 0x6a, 0x6b, 0x6c, 0x6d, 0x6b, 0x6c, 0x6d, 0x6e, 0x6c, 0x6d, 0x6e, 0x6f,
       0x6d, 0x6e, 0x6f, 0x70, 0x6e, 0x6f, 0x70, 0x71] =
      [0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
       0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1] := by
  decide

set_option maxRecDepth 100000 in
/-- SHA-224 of the same two-block message. -/
theorem sha224_two_blocks :
    sha224 [0x61, 0x62, 0x63, 0x64, 0x62, 0x63, 0x64, 0x65, 0x63, 0x64, 0x65, 0x66, 0x64, 0x65, 0x66, 0x67,
       0x65, 0x66, 0x67, 0x68, 0x66, 0x67, 0x68, 0x69, 0x67, 0x68, 0x69, 0x6a, 0x68, 0x69, 0x6a, 0x6b,
       0x69, 0x6a, 0x6b, 0x6c, 0x6a, 0x6b, 0x6c, 0x6d, 0x6b, 0x6c, 0x6d, 0x6e, 0x6c, 0x6d, 0x6e, 0x6f,
       0x6d, 0x6e, 0x6f, 0x70, 0x6e, 0x6f, 0x70, 0x71] =
      [0x75, 0x38, 0x8b, 0x16, 0x51, 0x27, 0x76, 0xcc, 0x5d, 0xba, 0x5d, 0xa1, 0xfd, 0x89, 0x01, 0x50,
       0xb0, 0xc6, 0x45, 0x5c, 0xb4, 0xf5, 0x8b, 0x19, 0x52, 0x52, 0x25, 0x25] := by
  decide
end Ssl.Spec.Sha256
