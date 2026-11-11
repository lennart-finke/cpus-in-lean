/-!
# Hexadecimal, base64 and ISO/IEC 7816-4 padding

Written from the standards, not from libsodium's code.

* `hex`: two lower-case hexadecimal digits per byte, most significant first (RFC 4648 §8 with the
  lower-case alphabet, which is what libsodium documents).
* `base64`: RFC 4648 §4 (alphabet `A–Z a–z 0–9 + /`) and §5 (URL-safe: `-` and `_`), with the `=`
  padding of §3.2 or without it.
* `pad`: ISO/IEC 7816-4 padding as libsodium documents it: a `0x80` byte, then zero bytes up to the
  next multiple of the block size. At least one byte is always added.
* `unpad`: the length of the data in a padded buffer, when its last block ends in `0x80` followed
  only by zero bytes.
-/
namespace Sodium.Spec

/-- The lower-case hexadecimal digit of a value below 16. -/
def hexDigit (v : UInt8) : UInt8 := if v < 10 then 0x30 + v else 0x57 + v

def hex (x : List UInt8) : List UInt8 := x.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit (b &&& 15)]

/-- RFC 4648 Table 1 (`url = false`) and Table 2 (`url = true`): the character of a 6-bit value. -/
def b64Char (url : Bool) (v : UInt8) : UInt8 :=
  if v < 26 then 0x41 + v
  else if v < 52 then 0x61 + (v - 26)
  else if v < 62 then 0x30 + (v - 52)
  else if v == 62 then (if url then 0x2D else 0x2B)
  else (if url then 0x5F else 0x2F)

/-- RFC 4648 §4: 24-bit groups as four characters; a final group of 8 or 16 bits as two or three
characters, followed by `=` up to four when `padding` holds. -/
def base64 (url padding : Bool) : List UInt8 → List UInt8
  | a :: b :: c :: rest =>
    [b64Char url (a >>> 2), b64Char url (((a &&& 3) <<< 4) ||| (b >>> 4)),
     b64Char url (((b &&& 15) <<< 2) ||| (c >>> 6)), b64Char url (c &&& 63)] ++ base64 url padding rest
  | [a, b] =>
    [b64Char url (a >>> 2), b64Char url (((a &&& 3) <<< 4) ||| (b >>> 4)), b64Char url ((b &&& 15) <<< 2)]
      ++ (if padding then [0x3D] else [])
  | [a] => [b64Char url (a >>> 2), b64Char url ((a &&& 3) <<< 4)] ++ (if padding then [0x3D, 0x3D] else [])
  | [] => []

/-- The length of `x` padded to a multiple of `block` (at least one byte is added). -/
def paddedLength (n block : Nat) : Nat := (n / block + 1) * block

/-- ISO/IEC 7816-4: `x`, a `0x80` byte, zero bytes up to a multiple of `block`. -/
def pad (x : List UInt8) (block : Nat) : List UInt8 :=
  x ++ 0x80 :: List.replicate (paddedLength x.length block - x.length - 1) 0

/-- The data length of a padded buffer: the last non-zero byte is `0x80` and lies in the last
`block` bytes. `none` if the buffer is not padded that way. -/
def unpad (buf : List UInt8) (block : Nat) : Option Nat :=
  let zeros := (buf.reverse.takeWhile (· == 0)).length
  if zeros < block && zeros < buf.length && buf[buf.length - 1 - zeros]? == some 0x80
  then some (buf.length - 1 - zeros) else none

private def ascii (s : String) : List UInt8 := s.toUTF8.toList

-- RFC 4648 §10 test vectors.
#guard base64 false true (ascii "") == ascii "" && base64 false true (ascii "f") == ascii "Zg=="
#guard base64 false true (ascii "fo") == ascii "Zm8=" && base64 false true (ascii "foo") == ascii "Zm9v"
#guard base64 false true (ascii "foob") == ascii "Zm9vYg==" && base64 false true (ascii "fooba") == ascii "Zm9vYmE="
#guard base64 false true (ascii "foobar") == ascii "Zm9vYmFy" && base64 false false (ascii "foob") == ascii "Zm9vYg"
#guard base64 false true [0xFB, 0xFF, 0xBE] == ascii "+/++" && base64 true true [0xFB, 0xFF, 0xBE] == ascii "-_--"
#guard hex (ascii "foobar") == ascii "666f6f626172" && hex [0x00, 0x9A, 0xFF] == ascii "009aff"
-- Padding always adds a byte, and `unpad` inverts `pad`.
#guard pad [1, 2, 3] 4 == [1, 2, 3, 0x80] && pad [1, 2, 3, 4] 4 == [1, 2, 3, 4, 0x80, 0, 0, 0] && pad [] 3 == [0x80, 0, 0]
#guard unpad (pad [1, 2, 3] 4) 4 == some 3 && unpad (pad [1, 2, 3, 4] 4) 4 == some 4 && unpad (pad [] 3) 3 == some 0
#guard unpad [1, 2, 3, 0] 4 == none && unpad [0x80, 0, 0, 0, 0] 4 == none && unpad [0, 0, 0x81, 0] 4 == none
#guard unpad [5, 0x80, 0x80, 0] 4 == some 2 && unpad [0, 0, 0, 0] 4 == none

end Sodium.Spec
