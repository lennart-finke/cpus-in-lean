import X86.Exec
/-!
# AES, PCLMULQDQ, SHA

Owner: the crypto workstream (legacy encodings; the VEX.128 forms belong to `Avx.lean`).

## Semantic kernels (pure functions, reused by the VEX forms)

Every instruction is a pure function of 128-bit values; the VEX three-operand forms (VAESENC
xmm1, xmm2, xmm3/m128, VPCLMULQDQ, ...) apply the same function to (VEX.vvvv, r/m) instead of
(ModRM.reg, r/m). Byte `k` of a `V128` is bits 8k+7..8k (memory byte k of a 16-byte load), dword `k`
bits 32k+31..32k (`dw`, `ofDw`).

| kernel | instruction | operands |
|---|---|---|
| `aesenc s k`, `aesenclast s k` | AESENC, AESENCLAST | state (xmm1), round key (xmm2/m128) |
| `aesdec s k`, `aesdeclast s k` | AESDEC, AESDECLAST | state, round key |
| `aesimc s` | AESIMC | source |
| `aeskeygenassist s imm` | AESKEYGENASSIST | source, imm8 |
| `pclmulqdq a b imm` | PCLMULQDQ | xmm1, xmm2/m128, imm8 (bits 0 and 4 select the quadwords) |
| `sha1rnds4 a b imm` | SHA1RNDS4 | xmm1 (A..D), xmm2/m128 (W+E), imm8[1:0] |
| `sha1nexte a b`, `sha1msg1 a b`, `sha1msg2 a b` | SHA1NEXTE, SHA1MSG1, SHA1MSG2 | xmm1, xmm2/m128 |
| `sha256rnds2 a b wk` | SHA256RNDS2 | xmm1 (C,D,G,H), xmm2/m128 (A,B,E,F), XMM0 |
| `sha256msg1 a b`, `sha256msg2 a b` | SHA256MSG1, SHA256MSG2 | xmm1, xmm2/m128 |

Sources: the instruction pages of the Intel SDM vol. 2 (AESENC ... SHA256MSG2, operation sections;
the AMD APM vol. 4 describes the same operations) and FIPS-197 (S-box, ShiftRows, MixColumns, the
key-expansion words SubWord/RotWord). The AES state is the FIPS-197 state in column-major order:
byte r + 4c is row r of column c, so dword c is column c. The S-box tables are those of FIPS-197
figures 7 and 14; `X86/Proofs/ExtCrypto.lean` proves them equal to the algebraic definition
(multiplicative inverse in GF(2^8) and the affine map, FIPS-197 5.1.1).

## Instructions (legacy encodings)

* 66 0F 38 DB..DF AESIMC, AESENC, AESENCLAST, AESDEC, AESDECLAST; 66 0F 3A DF AESKEYGENASSIST
  (CPUID.1:ECX.AES); 66 0F 3A 44 PCLMULQDQ (CPUID.1:ECX.PCLMULQDQ).
* 0F 38 C8..CD SHA1NEXTE, SHA1MSG1, SHA1MSG2, SHA256RNDS2, SHA256MSG1, SHA256MSG2; 0F 3A CC SHA1RNDS4
  (CPUID.7.0:EBX.SHA).

Exceptions (SDM vol. 2, table 2-21 "Type 4"; AMD APM vol. 4, the instruction pages): #UD with any
other mandatory prefix (AES/PCLMULQDQ need 66; the SHA instructions are "NP": a 66, F2 or F3 prefix
is #UD, as in Bochs' decoder; QEMU's TCG executes them, see `validation/README.md`), with LOCK
(`Step.lockOk`), CR0.EM = 1 or CR4.OSFXSR = 0; then #NM with CR0.TS = 1 (`sseCheck`); then the
memory operand: segment checks, #GP(0) unless 16-byte aligned (`vecAddr`; AMD's MisalignSse mode is
the Sse workstream's), #PF. No flags, no MXCSR effect, YMM bits 255:128 unchanged (legacy SSE). The
undefined-prefix #UD is checked first, as for the SSE instructions of the core model.

Hooks (called by `X86/Dispatch.lean` after `Sse.map2?`/`Sse.map3?`; `none` = not handled here):

* `map2?` (0F 38): 0F 38 DB..DF and 0F 38 C8..CD (every prefix; wrong ones raise #UD here).
* `map3?` (0F 3A, imm8 in `imm`): 0F 3A 44, 0F 3A DF, 0F 3A CC.
-/
namespace X86
namespace Crypto

/-! ## 128-bit values as dwords and bytes -/

/-- Dword `k` (0..3) of `v`: bits 32k+31..32k. -/
@[inline] def dw (v : V128) (k : Nat) : UInt32 :=
  match k with
  | 0 => v.lo.toUInt32
  | 1 => (v.lo >>> 32).toUInt32
  | 2 => v.hi.toUInt32
  | _ => (v.hi >>> 32).toUInt32

/-- The value with dwords `d0` (bits 31..0) .. `d3` (bits 127..96). -/
@[inline] def ofDw (d0 d1 d2 d3 : UInt32) : V128 :=
  { lo := d0.toUInt64 ||| (d1.toUInt64 <<< 32), hi := d2.toUInt64 ||| (d3.toUInt64 <<< 32) }

/-- Byte `k` (0..3) of a dword. -/
@[inline] def b8 (w : UInt32) (k : UInt32) : UInt8 := (w >>> (8 * k)).toUInt8

/-- The dword with bytes `a0` (bits 7..0) .. `a3` (bits 31..24). -/
@[inline] def ofB8 (a0 a1 a2 a3 : UInt8) : UInt32 :=
  a0.toUInt32 ||| (a1.toUInt32 <<< 8) ||| (a2.toUInt32 <<< 16) ||| (a3.toUInt32 <<< 24)

@[inline] def xor128 (a b : V128) : V128 := { lo := a.lo ^^^ b.lo, hi := a.hi ^^^ b.hi }

/-- Apply `f` to each dword (AES: to each column). -/
@[inline] def mapDw (f : UInt32 → UInt32) (v : V128) : V128 :=
  ofDw (f (dw v 0)) (f (dw v 1)) (f (dw v 2)) (f (dw v 3))

/-! ## AES (FIPS-197) -/

/-- Multiplication by x in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1 (FIPS-197 4.2.1). -/
@[inline] def xtime (b : UInt8) : UInt8 := (b <<< 1) ^^^ (if b &&& 0x80 != 0 then 0x1B else 0)

/-- The S-box (FIPS-197 figure 7), indexed by the input byte. -/
def sboxTable : Array UInt8 := #[
  0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
  0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
  0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
  0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
  0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
  0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
  0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
  0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
  0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
  0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
  0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
  0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
  0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
  0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
  0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
  0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16]

/-- The inverse S-box (FIPS-197 figure 14). -/
def invSboxTable : Array UInt8 := #[
  0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
  0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
  0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
  0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
  0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
  0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
  0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
  0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
  0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
  0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
  0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
  0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
  0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
  0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
  0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D]

@[inline] def sbox (b : UInt8) : UInt8 := sboxTable[b.toNat]!
@[inline] def invSbox (b : UInt8) : UInt8 := invSboxTable[b.toNat]!

/-- SubWord (FIPS-197 5.2): the S-box on each byte of a word (and, as SubBytes, of a column). -/
@[inline] def subWord (w : UInt32) : UInt32 :=
  ofB8 (sbox (b8 w 0)) (sbox (b8 w 1)) (sbox (b8 w 2)) (sbox (b8 w 3))

@[inline] def invSubWord (w : UInt32) : UInt32 :=
  ofB8 (invSbox (b8 w 0)) (invSbox (b8 w 1)) (invSbox (b8 w 2)) (invSbox (b8 w 3))

/-- RotWord (FIPS-197 5.2): [a0, a1, a2, a3] ↦ [a1, a2, a3, a0]; with a0 in bits 7..0 (the SDM's
little-endian dwords) a rotation right by 8. -/
@[inline] def rotWord (w : UInt32) : UInt32 := (w >>> 8) ||| (w <<< 24)

/-- MixColumns on one column (FIPS-197 5.1.3, equation 5.6). -/
def mixColumn (w : UInt32) : UInt32 :=
  let a0 := b8 w 0
  let a1 := b8 w 1
  let a2 := b8 w 2
  let a3 := b8 w 3
  ofB8 (xtime a0 ^^^ (xtime a1 ^^^ a1) ^^^ a2 ^^^ a3)
       (a0 ^^^ xtime a1 ^^^ (xtime a2 ^^^ a2) ^^^ a3)
       (a0 ^^^ a1 ^^^ xtime a2 ^^^ (xtime a3 ^^^ a3))
       ((xtime a0 ^^^ a0) ^^^ a1 ^^^ a2 ^^^ xtime a3)

/-- InvMixColumns on one column (FIPS-197 5.3.3, equation 5.10): the coefficients 0e, 0b, 0d, 09. -/
def invMixColumn (w : UInt32) : UInt32 :=
  -- 9x, 11x, 13x, 14x from x, 2x, 4x, 8x
  let m := fun (x : UInt8) =>
    let x2 := xtime x
    let x4 := xtime x2
    let x8 := xtime x4
    (x8 ^^^ x, x8 ^^^ x2 ^^^ x, x8 ^^^ x4 ^^^ x, x8 ^^^ x4 ^^^ x2)
  let (a9, ab, ad, ae) := m (b8 w 0)
  let (b9, bb, bd, be) := m (b8 w 1)
  let (c9, cb, cd, ce) := m (b8 w 2)
  let (d9, db, dd, de) := m (b8 w 3)
  ofB8 (ae ^^^ bb ^^^ cd ^^^ d9) (a9 ^^^ be ^^^ cb ^^^ dd) (ad ^^^ b9 ^^^ ce ^^^ db)
       (ab ^^^ bd ^^^ c9 ^^^ de)

/-- ShiftRows (FIPS-197 5.1.2): row r of column c comes from column c + r (mod 4). -/
def shiftRows (s : V128) : V128 :=
  let w := fun (c : Nat) => dw s (c % 4)
  let col := fun (c : Nat) =>
    (w c &&& 0xFF) ||| (w (c + 1) &&& 0xFF00) ||| (w (c + 2) &&& 0xFF0000) ||| (w (c + 3) &&& 0xFF000000)
  ofDw (col 0) (col 1) (col 2) (col 3)

/-- InvShiftRows (FIPS-197 5.3.1): row r of column c comes from column c - r (mod 4). -/
def invShiftRows (s : V128) : V128 :=
  let w := fun (c : Nat) => dw s (c % 4)
  let col := fun (c : Nat) =>
    (w c &&& 0xFF) ||| (w (c + 3) &&& 0xFF00) ||| (w (c + 2) &&& 0xFF0000) ||| (w (c + 1) &&& 0xFF000000)
  ofDw (col 0) (col 1) (col 2) (col 3)

def subBytes : V128 → V128 := mapDw subWord
def invSubBytes : V128 → V128 := mapDw invSubWord
def mixColumns : V128 → V128 := mapDw mixColumn
def invMixColumns : V128 → V128 := mapDw invMixColumn

/-- AESENC: one encryption round (SDM AESENC: ShiftRows, SubBytes, MixColumns, XOR round key). -/
def aesenc (s k : V128) : V128 := xor128 (mixColumns (subBytes (shiftRows s))) k
/-- AESENCLAST: the last encryption round (no MixColumns). -/
def aesenclast (s k : V128) : V128 := xor128 (subBytes (shiftRows s)) k
/-- AESDEC: one round of the equivalent inverse cipher (FIPS-197 5.3.5; SDM AESDEC: InvShiftRows,
InvSubBytes, InvMixColumns, XOR round key). -/
def aesdec (s k : V128) : V128 := xor128 (invMixColumns (invSubBytes (invShiftRows s))) k
/-- AESDECLAST: the last decryption round (no InvMixColumns). -/
def aesdeclast (s k : V128) : V128 := xor128 (invSubBytes (invShiftRows s)) k
/-- AESIMC: InvMixColumns of a round key (for the equivalent inverse cipher). -/
def aesimc (s : V128) : V128 := invMixColumns s
/-- AESKEYGENASSIST (SDM): SubWord of dwords 1 and 3, and their RotWord XOR RCON (imm8). -/
def aeskeygenassist (s : V128) (imm : UInt8) : V128 :=
  let rcon := imm.toUInt32
  let x1 := subWord (dw s 1)
  let x3 := subWord (dw s 3)
  ofDw x1 (rotWord x1 ^^^ rcon) x3 (rotWord x3 ^^^ rcon)

/-! ## Carry-less multiplication -/

/-- The 128-bit carry-less (GF(2)[x]) product of two 64-bit values (SDM PCLMULQDQ). -/
def clmul (a b : UInt64) : V128 :=
  (List.range 64).foldl (fun (r : V128) k =>
    if (b >>> k.toUInt64) &&& 1 != 0 then
      { lo := r.lo ^^^ (a <<< k.toUInt64),
        hi := r.hi ^^^ (if k == 0 then 0 else a >>> (64 - k).toUInt64) }
    else r) {}

/-- PCLMULQDQ: imm8 bit 0 selects the quadword of the first operand, bit 4 that of the second;
the other immediate bits are ignored. -/
def pclmulqdq (a b : V128) (imm : UInt8) : V128 :=
  clmul (if imm &&& 0x01 != 0 then a.hi else a.lo) (if imm &&& 0x10 != 0 then b.hi else b.lo)

/-! ## SHA-1 and SHA-256 (FIPS 180-4; SDM SHA1RNDS4 .. SHA256MSG2) -/

@[inline] def rol (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
@[inline] def ror (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The SHA-1 round function selected by imm8[1:0]: Ch, Parity, Maj, Parity (FIPS 180-4 4.1.1). -/
def sha1f (sel : UInt8) (b c d : UInt32) : UInt32 :=
  match sel &&& 3 with
  | 0 => (b &&& c) ^^^ (~~~b &&& d)
  | 2 => (b &&& c) ^^^ (b &&& d) ^^^ (c &&& d)
  | _ => b ^^^ c ^^^ d

/-- The SHA-1 constant selected by imm8[1:0] (FIPS 180-4 4.2.1). -/
def sha1k (sel : UInt8) : UInt32 :=
  match sel &&& 3 with
  | 0 => 0x5A827999
  | 1 => 0x6ED9EBA1
  | 2 => 0x8F1BBCDC
  | _ => 0xCA62C1D6

/-- SHA1RNDS4: four SHA-1 rounds. `a` holds A, B, C, D in dwords 3..0; `b` holds W0 + E, W1, W2,
W3 in dwords 3..0 (the first round takes E from W0E). -/
def sha1rnds4 (a b : V128) (imm : UInt8) : V128 :=
  let f := sha1f imm
  let k := sha1k imm
  let round := fun (st : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (w : UInt32) =>
    let (a, b, c, d, e) := st
    (f b c d + rol a 5 + w + e + k, a, rol b 30, c, d)
  let st := (dw a 3, dw a 2, dw a 1, dw a 0, (0 : UInt32))
  let st := round st (dw b 3)
  let st := round st (dw b 2)
  let st := round st (dw b 1)
  let (a, b, c, d, _) := round st (dw b 0)
  ofDw d c b a

/-- SHA1NEXTE: dword 3 of `b` plus (dword 3 of `a`) rotated left by 30; dwords 2..0 of `b`. -/
def sha1nexte (a b : V128) : V128 := ofDw (dw b 0) (dw b 1) (dw b 2) (dw b 3 + rol (dw a 3) 30)

/-- SHA1MSG1: the XORs W[i-16] ^ W[i-14] of the next four message words. -/
def sha1msg1 (a b : V128) : V128 :=
  let w0 := dw a 3
  let w1 := dw a 2
  let w2 := dw a 1
  let w3 := dw a 0
  let w4 := dw b 3
  let w5 := dw b 2
  ofDw (w5 ^^^ w3) (w4 ^^^ w2) (w3 ^^^ w1) (w2 ^^^ w0)

/-- SHA1MSG2: completes W[i] = (... ^ W[i-3]) rol 1 for four message words. -/
def sha1msg2 (a b : V128) : V128 :=
  let w13 := dw b 2
  let w14 := dw b 1
  let w15 := dw b 0
  let w16 := rol (dw a 3 ^^^ w13) 1
  let w17 := rol (dw a 2 ^^^ w14) 1
  let w18 := rol (dw a 1 ^^^ w15) 1
  let w19 := rol (dw a 0 ^^^ w16) 1
  ofDw w19 w18 w17 w16

/-- FIPS 180-4 4.1.2: Σ0, Σ1, σ0, σ1, Ch, Maj. -/
@[inline] def bsig0 (x : UInt32) : UInt32 := ror x 2 ^^^ ror x 13 ^^^ ror x 22
@[inline] def bsig1 (x : UInt32) : UInt32 := ror x 6 ^^^ ror x 11 ^^^ ror x 25
@[inline] def ssig0 (x : UInt32) : UInt32 := ror x 7 ^^^ ror x 18 ^^^ (x >>> 3)
@[inline] def ssig1 (x : UInt32) : UInt32 := ror x 17 ^^^ ror x 19 ^^^ (x >>> 10)
@[inline] def ch (e f g : UInt32) : UInt32 := (e &&& f) ^^^ (~~~e &&& g)
@[inline] def maj (a b c : UInt32) : UInt32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- SHA256RNDS2: two SHA-256 rounds. `a` (xmm1) holds C, D, G, H and `b` (xmm2/m128) A, B, E, F in
dwords 3..0; `wk` (XMM0) the two message-plus-constant words in dwords 0 and 1. The result is the
new A, B, E, F. -/
def sha256rnds2 (a b wk : V128) : V128 :=
  let round := fun (st : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32)
      (w : UInt32) =>
    let (sa, sb, sc, sd, se, sf, sg, sh) := st
    let t := ch se sf sg + bsig1 se + w + sh
    (t + maj sa sb sc + bsig0 sa, sa, sb, sc, t + sd, se, sf, sg)
  let st := (dw b 3, dw b 2, dw a 3, dw a 2, dw b 1, dw b 0, dw a 1, dw a 0)
  let st := round st (dw wk 0)
  let (sa, sb, _, _, se, sf, _, _) := round st (dw wk 1)
  ofDw sf se sb sa

/-- SHA256MSG1: W[i-16] + σ0(W[i-15]) for four message words. -/
def sha256msg1 (a b : V128) : V128 :=
  ofDw (dw a 0 + ssig0 (dw a 1)) (dw a 1 + ssig0 (dw a 2)) (dw a 2 + ssig0 (dw a 3))
       (dw a 3 + ssig0 (dw b 0))

/-- SHA256MSG2: completes W[i] = ... + σ1(W[i-2]) for four message words. -/
def sha256msg2 (a b : V128) : V128 :=
  let w16 := dw a 0 + ssig1 (dw b 2)
  let w17 := dw a 1 + ssig1 (dw b 3)
  let w18 := dw a 2 + ssig1 w16
  let w19 := dw a 3 + ssig1 w17
  ofDw w16 w17 w18 w19

/-! ## Instructions -/

/-- `xmm1 := f xmm1 (xmm2/m128)` with mandatory prefix `pp` (`Inst.pp`) and CPUID feature `feat`:
#UD for another prefix or an unreported feature, then the SSE checks (#UD/#NM), then the aligned
128-bit source. -/
@[inline] def xmmOp (i : Inst) (pp : UInt8) (feat : Feature) (f : V128 → V128 → V128) : M Unit := do
  if i.pp != pp || !implemented feat then ud
  sseCheck
  let a ← getXmm i.reg
  let b ← rdXE i 16 true
  setXmm i.reg (f a b)

/-- SHA256RNDS2 xmm1, xmm2/m128, <XMM0>. -/
def sha256rnds2Op (i : Inst) : M Unit := do
  if i.pp != 0 || !implemented .sha then ud
  sseCheck
  let a ← getXmm i.reg
  let b ← rdXE i 16 true
  let wk ← getXmm 0
  setXmm i.reg (sha256rnds2 a b wk)

/-- 0F 38 map: AES (66 DB..DF) and SHA (NP C8..CD). -/
def map2? (i : Inst) : Option (M Unit) :=
  if i.vex then none else
  match i.byte with
  | 0xC8 => some (xmmOp i 0 .sha sha1nexte)
  | 0xC9 => some (xmmOp i 0 .sha sha1msg1)
  | 0xCA => some (xmmOp i 0 .sha sha1msg2)
  | 0xCB => some (sha256rnds2Op i)
  | 0xCC => some (xmmOp i 0 .sha sha256msg1)
  | 0xCD => some (xmmOp i 0 .sha sha256msg2)
  | 0xDB => some (xmmOp i 1 .aes fun _ b => aesimc b)
  | 0xDC => some (xmmOp i 1 .aes aesenc)
  | 0xDD => some (xmmOp i 1 .aes aesenclast)
  | 0xDE => some (xmmOp i 1 .aes aesdec)
  | 0xDF => some (xmmOp i 1 .aes aesdeclast)
  | _ => none

/-- 0F 3A map (imm8 in `imm`): PCLMULQDQ (66 44), AESKEYGENASSIST (66 DF), SHA1RNDS4 (NP CC). -/
def map3? (i : Inst) : Option (M Unit) :=
  if i.vex then none else
  let imm := i.imm.toUInt8
  match i.byte with
  | 0x44 => some (xmmOp i 1 .pclmulqdq fun a b => pclmulqdq a b imm)
  | 0xDF => some (xmmOp i 1 .aes fun _ b => aeskeygenassist b imm)
  | 0xCC => some (xmmOp i 0 .sha fun a b => sha1rnds4 a b imm)
  | _ => none

end Crypto
end X86
