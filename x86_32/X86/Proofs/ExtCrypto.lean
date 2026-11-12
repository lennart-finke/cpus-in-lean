import Std.Tactic.BVDecide
import X86.Dispatch
import X86.Proofs.Basic
/-!
# AES, PCLMULQDQ, SHA (`X86/Ext/Crypto.lean`)

**Theorems** (proved for all inputs):
* `sbox_spec`, `invSbox_spec`: the S-box tables are the FIPS-197 definition (inverse in GF(2^8),
  then the affine map; the inverse affine map, then the inverse); `invSbox_sbox`, `sbox_invSbox`.
* `invMixColumn_mixColumn`, `mixColumn_invMixColumn`, `invMixColumn_xor` (InvMixColumns is linear),
  `invShiftRows_shiftRows`, `invSubBytes_subBytes`.
* `decrypt_encrypt`: for every round-key schedule (any number of rounds ≥ 1) and every block, the
  equivalent inverse cipher built from AESDEC/AESDECLAST with AESIMC'd round keys inverts the cipher
  built from AESENC/AESENCLAST (FIPS-197 5.3.5).
* `pclmulqdq_imm`: PCLMULQDQ depends on imm8 bits 0 and 4 only.
* Instruction rules: a wrong mandatory prefix is #UD (`xmmOp_prefix`), CR4.OSFXSR = 0 is #UD
  (`xmmOp_noosfxsr`), CR0.TS is #NM (`xmmOp_ts`), in that order, before any state changes; the hooks
  take exactly their opcodes (`map2?_isSome`, `map3?_isSome`).

**Test vectors**, also theorems (evaluated by the kernel with `decide +kernel`, no `native_decide`):
* FIPS-197 appendix C.1–C.3 (AES-128/192/256) and appendix B: encryption and decryption composed
  from AESENC/AESENCLAST/AESDEC/AESDECLAST/AESIMC, with the key expansion's SubWord/RotWord/Rcon
  computed by AESKEYGENASSIST (`fips197_*`).
* FIPS 180-4 example digests (the NIST "abc" and 448-bit two-block messages) of SHA-1 and SHA-256,
  composed from SHA1RNDS4/SHA1NEXTE/SHA1MSG1/SHA1MSG2 and SHA256RNDS2/SHA256MSG1/SHA256MSG2
  (`sha1_*`, `sha256_*`).
* GCM test case 2 of McGrew and Viega (AES-128, zero key and IV): H, the ciphertext, GHASH and
  the tag, with GF(2^128) multiplication composed from four PCLMULQDQ products and a PCLMULQDQ
  reduction (`gcm_*`); carry-less multiplication identities on samples (`clmul_*`).
-/
namespace X86
namespace Crypto

deriving instance DecidableEq for V128

/-! ## The S-box from its definition (FIPS-197 5.1.1, 5.3.2) -/

/-- Multiplication in GF(2^8) (FIPS-197 4.2). -/
def gmul (a b : UInt8) : UInt8 :=
  ((List.range 8).foldl (fun (acc : UInt8 × UInt8) k =>
    ((if (b >>> k.toUInt8) &&& 1 != 0 then acc.1 ^^^ acc.2 else acc.1), xtime acc.2)) (0, a)).1

/-- Multiplicative inverse in GF(2^8), 0 ↦ 0: b^254. -/
def ginv (b : UInt8) : UInt8 :=
  -- square-and-multiply over 254 = 0b11111110
  let sq := fun (x : UInt8) => gmul x x
  let x := b                       -- b^1
  let x := gmul (sq x) b           -- b^3
  let x := gmul (sq x) b           -- b^7
  let x := gmul (sq x) b           -- b^15
  let x := gmul (sq x) b           -- b^31
  let x := gmul (sq x) b           -- b^63
  let x := gmul (sq x) b           -- b^127
  sq x                             -- b^254

@[inline] def rotl8 (b k : UInt8) : UInt8 := (b <<< k) ||| (b >>> (8 - k))

/-- The affine transformation of the S-box (FIPS-197 equation 5.1). -/
def affine (b : UInt8) : UInt8 := b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

/-- Its inverse (FIPS-197 5.3.2). -/
def invAffine (b : UInt8) : UInt8 := rotl8 b 1 ^^^ rotl8 b 3 ^^^ rotl8 b 6 ^^^ 0x05

theorem sbox_spec_nat : ∀ n, n < 256 → sbox n.toUInt8 = affine (ginv n.toUInt8) := by decide +kernel
theorem invSbox_spec_nat : ∀ n, n < 256 → invSbox n.toUInt8 = ginv (invAffine n.toUInt8) := by
  decide +kernel
theorem invSbox_sbox_nat : ∀ n, n < 256 → invSbox (sbox n.toUInt8) = n.toUInt8 := by decide +kernel
theorem sbox_invSbox_nat : ∀ n, n < 256 → sbox (invSbox n.toUInt8) = n.toUInt8 := by decide +kernel

private theorem forall_uint8 {P : UInt8 → Prop} (h : ∀ n, n < 256 → P n.toUInt8) (b : UInt8) : P b := by
  have := h b.toNat b.toNat_lt
  simpa using this

theorem sbox_spec (b : UInt8) : sbox b = affine (ginv b) :=
  forall_uint8 (P := fun b => sbox b = affine (ginv b)) sbox_spec_nat b
theorem invSbox_spec (b : UInt8) : invSbox b = ginv (invAffine b) :=
  forall_uint8 (P := fun b => invSbox b = ginv (invAffine b)) invSbox_spec_nat b
theorem invSbox_sbox (b : UInt8) : invSbox (sbox b) = b :=
  forall_uint8 (P := fun b => invSbox (sbox b) = b) invSbox_sbox_nat b
theorem sbox_invSbox (b : UInt8) : sbox (invSbox b) = b :=
  forall_uint8 (P := fun b => sbox (invSbox b) = b) sbox_invSbox_nat b

/-! ## AES round algebra -/

-- The column maps are GF(2)-linear (xtime is), so they are inverse to each other iff they are on
-- each byte position; a direct SAT check of the 32-bit composition times out.
private theorem col_split (w : UInt32) :
    w = (w &&& 0xFF) ^^^ (w &&& 0xFF00) ^^^ (w &&& 0xFF0000) ^^^ (w &&& 0xFF000000) := by bv_decide


theorem xtime_xor (a b : UInt8) : xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  simp only [xtime, shl8, bne_iff_ne, ne_eq]; bv_decide

theorem b8_xor (x y k : UInt32) : b8 (x ^^^ y) k = b8 x k ^^^ b8 y k := by
  simp only [b8, shr32]; bv_decide

theorem ofB8_xor (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8) :
    ofB8 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) = ofB8 a0 a1 a2 a3 ^^^ ofB8 b0 b1 b2 b3 := by
  simp only [ofB8, shl32]; bv_decide

theorem mixColumn_xor (x y : UInt32) : mixColumn (x ^^^ y) = mixColumn x ^^^ mixColumn y := by
  simp only [mixColumn, b8_xor, xtime_xor]
  rw [← ofB8_xor]
  generalize b8 x 0 = a0
  generalize b8 x 1 = a1
  generalize b8 x 2 = a2
  generalize b8 x 3 = a3
  generalize b8 y 0 = c0
  generalize b8 y 1 = c1
  generalize b8 y 2 = c2
  generalize b8 y 3 = c3
  congr 1 <;> ac_rfl

theorem invMixColumn_xor (x y : UInt32) :
    invMixColumn (x ^^^ y) = invMixColumn x ^^^ invMixColumn y := by
  simp only [invMixColumn, b8_xor, xtime_xor]
  rw [← ofB8_xor]
  generalize b8 x 0 = a0
  generalize b8 x 1 = a1
  generalize b8 x 2 = a2
  generalize b8 x 3 = a3
  generalize b8 y 0 = c0
  generalize b8 y 1 = c1
  generalize b8 y 2 = c2
  generalize b8 y 3 = c3
  congr 1 <;> ac_rfl

private theorem imc_mc_byte (w : UInt32) (m : UInt32) (hm : m = 0xFF ∨ m = 0xFF00 ∨ m = 0xFF0000 ∨ m = 0xFF000000) :
    invMixColumn (mixColumn (w &&& m)) = w &&& m := by
  rcases hm with rfl | rfl | rfl | rfl <;>
  · simp only [invMixColumn, mixColumn, b8, ofB8, xtime, shl8, shl32, shr32, bne_iff_ne, ne_eq]
    bv_decide

private theorem mc_imc_byte (w : UInt32) (m : UInt32) (hm : m = 0xFF ∨ m = 0xFF00 ∨ m = 0xFF0000 ∨ m = 0xFF000000) :
    mixColumn (invMixColumn (w &&& m)) = w &&& m := by
  rcases hm with rfl | rfl | rfl | rfl <;>
  · simp only [invMixColumn, mixColumn, b8, ofB8, xtime, shl8, shl32, shr32, bne_iff_ne, ne_eq]
    bv_decide

theorem invMixColumn_mixColumn (w : UInt32) : invMixColumn (mixColumn w) = w := by
  rw [col_split w]
  simp only [mixColumn_xor, invMixColumn_xor]
  rw [imc_mc_byte w 0xFF (by simp), imc_mc_byte w 0xFF00 (by simp), imc_mc_byte w 0xFF0000 (by simp),
    imc_mc_byte w 0xFF000000 (by simp)]

theorem mixColumn_invMixColumn (w : UInt32) : mixColumn (invMixColumn w) = w := by
  rw [col_split w]
  simp only [mixColumn_xor, invMixColumn_xor]
  rw [mc_imc_byte w 0xFF (by simp), mc_imc_byte w 0xFF00 (by simp), mc_imc_byte w 0xFF0000 (by simp),
    mc_imc_byte w 0xFF000000 (by simp)]

/-! ### Dwords, ShiftRows, SubBytes -/

@[simp] theorem dw_ofDw0 (a b c d : UInt32) : dw (ofDw a b c d) 0 = a := by
  simp only [dw, ofDw, shl64]; bv_decide
@[simp] theorem dw_ofDw1 (a b c d : UInt32) : dw (ofDw a b c d) 1 = b := by
  simp only [dw, ofDw, shl64, shr64]; bv_decide
@[simp] theorem dw_ofDw2 (a b c d : UInt32) : dw (ofDw a b c d) 2 = c := by
  simp only [dw, ofDw, shl64]; bv_decide
@[simp] theorem dw_ofDw3 (a b c d : UInt32) : dw (ofDw a b c d) 3 = d := by
  simp only [dw, ofDw, shl64, shr64]; bv_decide

theorem ofDw_dw (v : V128) : ofDw (dw v 0) (dw v 1) (dw v 2) (dw v 3) = v := by
  rcases v with ⟨lo, hi⟩
  simp only [ofDw, dw, shl64, shr64, V128.mk.injEq]
  constructor <;> bv_decide

/-- The byte permutation of ShiftRows/InvShiftRows: one byte from each of four columns. -/
def mix (x0 x1 x2 x3 : UInt32) : UInt32 :=
  (x0 &&& 0xFF) ||| (x1 &&& 0xFF00) ||| (x2 &&& 0xFF0000) ||| (x3 &&& 0xFF000000)

theorem shiftRows_eq (s : V128) : shiftRows s =
    ofDw (mix (dw s 0) (dw s 1) (dw s 2) (dw s 3)) (mix (dw s 1) (dw s 2) (dw s 3) (dw s 0))
      (mix (dw s 2) (dw s 3) (dw s 0) (dw s 1)) (mix (dw s 3) (dw s 0) (dw s 1) (dw s 2)) := rfl

theorem invShiftRows_eq (s : V128) : invShiftRows s =
    ofDw (mix (dw s 0) (dw s 3) (dw s 2) (dw s 1)) (mix (dw s 1) (dw s 0) (dw s 3) (dw s 2))
      (mix (dw s 2) (dw s 1) (dw s 0) (dw s 3)) (mix (dw s 3) (dw s 2) (dw s 1) (dw s 0)) := rfl

theorem invShiftRows_shiftRows (s : V128) : invShiftRows (shiftRows s) = s := by
  rw [invShiftRows_eq, shiftRows_eq]
  simp only [dw_ofDw0, dw_ofDw1, dw_ofDw2, dw_ofDw3]
  conv => rhs; rw [← ofDw_dw s]
  generalize dw s 0 = a
  generalize dw s 1 = b
  generalize dw s 2 = c
  generalize dw s 3 = d
  simp only [mix]
  congr 1 <;> bv_decide

/-- A bytewise map on a dword (SubWord for `sbox`). -/
def byteMap (h : UInt8 → UInt8) (w : UInt32) : UInt32 :=
  ofB8 (h (b8 w 0)) (h (b8 w 1)) (h (b8 w 2)) (h (b8 w 3))

private theorem b8_mix (x0 x1 x2 x3 : UInt32) :
    b8 (mix x0 x1 x2 x3) 0 = b8 x0 0 ∧ b8 (mix x0 x1 x2 x3) 1 = b8 x1 1 ∧
    b8 (mix x0 x1 x2 x3) 2 = b8 x2 2 ∧ b8 (mix x0 x1 x2 x3) 3 = b8 x3 3 := by
  simp only [b8, mix, shr32]; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

private theorem b8_ofB8 (a0 a1 a2 a3 : UInt8) :
    b8 (ofB8 a0 a1 a2 a3) 0 = a0 ∧ b8 (ofB8 a0 a1 a2 a3) 1 = a1 ∧
    b8 (ofB8 a0 a1 a2 a3) 2 = a2 ∧ b8 (ofB8 a0 a1 a2 a3) 3 = a3 := by
  simp only [b8, ofB8, shr32, shl32]; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

private theorem ofB8_b8 (w : UInt32) : ofB8 (b8 w 0) (b8 w 1) (b8 w 2) (b8 w 3) = w := by
  simp only [b8, ofB8, shr32, shl32]; bv_decide

/-- A bytewise map commutes with the byte permutations. -/
theorem byteMap_mix (h : UInt8 → UInt8) (x0 x1 x2 x3 : UInt32) :
    byteMap h (mix x0 x1 x2 x3) = mix (byteMap h x0) (byteMap h x1) (byteMap h x2) (byteMap h x3) := by
  obtain ⟨e0, e1, e2, e3⟩ := b8_mix x0 x1 x2 x3
  simp only [byteMap, e0, e1, e2, e3]
  generalize h (b8 x0 0) = a0
  generalize h (b8 x1 1) = a1
  generalize h (b8 x2 2) = a2
  generalize h (b8 x3 3) = a3
  generalize h (b8 x0 1) = b1
  generalize h (b8 x0 2) = b2
  generalize h (b8 x0 3) = b3
  generalize h (b8 x1 0) = c0
  generalize h (b8 x1 2) = c2
  generalize h (b8 x1 3) = c3
  generalize h (b8 x2 0) = d0
  generalize h (b8 x2 1) = d1
  generalize h (b8 x2 3) = d3
  generalize h (b8 x3 0) = f0
  generalize h (b8 x3 1) = f1
  generalize h (b8 x3 2) = f2
  simp only [mix, ofB8, shl32]
  bv_decide

theorem byteMap_comp (g h : UInt8 → UInt8) (w : UInt32) :
    byteMap g (byteMap h w) = byteMap (fun b => g (h b)) w := by
  obtain ⟨e0, e1, e2, e3⟩ := b8_ofB8 (h (b8 w 0)) (h (b8 w 1)) (h (b8 w 2)) (h (b8 w 3))
  simp only [byteMap, e0, e1, e2, e3]

theorem subWord_eq : subWord = byteMap sbox := rfl
theorem invSubWord_eq : invSubWord = byteMap invSbox := rfl

theorem invSubWord_subWord (w : UInt32) : invSubWord (subWord w) = w := by
  rw [invSubWord_eq, subWord_eq, byteMap_comp]
  simp only [invSbox_sbox, byteMap]
  exact ofB8_b8 w

theorem mapDw_mapDw (f g : UInt32 → UInt32) (v : V128) : mapDw f (mapDw g v) = mapDw (fun w => f (g w)) v := by
  simp only [mapDw, dw_ofDw0, dw_ofDw1, dw_ofDw2, dw_ofDw3]

theorem invSubBytes_subBytes (s : V128) : invSubBytes (subBytes s) = s := by
  simp only [invSubBytes, subBytes, mapDw_mapDw, invSubWord_subWord]
  exact ofDw_dw s

theorem invMixColumns_mixColumns (s : V128) : invMixColumns (mixColumns s) = s := by
  simp only [invMixColumns, mixColumns, mapDw_mapDw, invMixColumn_mixColumn]
  exact ofDw_dw s

theorem invShiftRows_subBytes (s : V128) : invShiftRows (subBytes s) = subBytes (invShiftRows s) := by
  simp only [invShiftRows_eq, subBytes, mapDw, dw_ofDw0, dw_ofDw1, dw_ofDw2, dw_ofDw3, subWord_eq,
    byteMap_mix]

private theorem dw_xor (a b : V128) (k : Nat) (hk : k < 4) : dw (xor128 a b) k = dw a k ^^^ dw b k := by
  rcases a with ⟨alo, ahi⟩
  rcases b with ⟨blo, bhi⟩
  rcases k with _ | _ | _ | _ | k
  all_goals simp only [dw, xor128, shr64]
  all_goals first | omega | bv_decide

theorem invMixColumns_xor (a b : V128) :
    invMixColumns (xor128 a b) = xor128 (invMixColumns a) (invMixColumns b) := by
  simp only [invMixColumns, mapDw, dw_xor a b 0 (by omega), dw_xor a b 1 (by omega),
    dw_xor a b 2 (by omega), dw_xor a b 3 (by omega), invMixColumn_xor]
  generalize invMixColumn (dw a 0) = a0
  generalize invMixColumn (dw a 1) = a1
  generalize invMixColumn (dw a 2) = a2
  generalize invMixColumn (dw a 3) = a3
  generalize invMixColumn (dw b 0) = b0
  generalize invMixColumn (dw b 1) = b1
  generalize invMixColumn (dw b 2) = b2
  generalize invMixColumn (dw b 3) = b3
  simp only [ofDw, xor128, shl64, V128.mk.injEq]
  constructor <;> bv_decide

theorem xor128_cancel (a b : V128) : xor128 (xor128 a b) b = a := by
  rcases a with ⟨alo, ahi⟩
  rcases b with ⟨blo, bhi⟩
  simp only [xor128, V128.mk.injEq]
  constructor <;> bv_decide

/-! ### The equivalent inverse cipher inverts the cipher (FIPS-197 5.3.5) -/

/-- SubBytes ∘ ShiftRows, the part of a round that AESDEC/AESDECLAST undo with
InvSubBytes ∘ InvShiftRows. -/
def sbsr (s : V128) : V128 := subBytes (shiftRows s)

theorem inv_sbsr (s : V128) : invSubBytes (invShiftRows (sbsr s)) = s := by
  rw [sbsr, invShiftRows_subBytes, invSubBytes_subBytes, invShiftRows_shiftRows]

/-- The cipher: initial AddRoundKey with `k0`, AESENC with each middle key, AESENCLAST with `kl`. -/
def encryptL (k0 : V128) (mid : List V128) (kl : V128) (pt : V128) : V128 :=
  aesenclast (mid.foldl aesenc (xor128 pt k0)) kl

/-- The equivalent inverse cipher: AddRoundKey with `kl`, AESDEC with the AESIMC'd middle keys in
reverse order, AESDECLAST with `k0`. -/
def decryptL (k0 : V128) (mid : List V128) (kl : V128) (ct : V128) : V128 :=
  aesdeclast ((mid.reverse.map aesimc).foldl aesdec (xor128 ct kl)) k0

private theorem aesdec_step (u k : V128) : aesdec (sbsr (aesenc u k)) (aesimc k) = sbsr u := by
  simp only [aesdec, aesimc, inv_sbsr, aesenc]
  rw [← invMixColumns_xor, xor128_cancel, ← sbsr, invMixColumns_mixColumns]

private theorem dec_fold_rev (l : List V128) : ∀ s : V128,
    (l.map aesimc).foldl aesdec (sbsr (l.reverse.foldl aesenc s)) = sbsr s := by
  induction l with
  | nil => intro s; rfl
  | cons k t ih =>
    intro s
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_cons]
    rw [aesdec_step, ih]

private theorem dec_fold (mid : List V128) (s : V128) :
    (mid.reverse.map aesimc).foldl aesdec (sbsr (mid.foldl aesenc s)) = sbsr s := by
  have := dec_fold_rev mid.reverse s
  rwa [List.reverse_reverse] at this

/-- For every round-key schedule and block, decryption with AESDEC/AESDECLAST and AESIMC'd keys
inverts encryption with AESENC/AESENCLAST. -/
theorem decrypt_encrypt (k0 : V128) (mid : List V128) (kl pt : V128) :
    decryptL k0 mid kl (encryptL k0 mid kl pt) = pt := by
  simp only [decryptL, encryptL, aesenclast]
  rw [xor128_cancel, ← sbsr, dec_fold, aesdeclast, inv_sbsr, xor128_cancel]

/-! ## FIPS-197 test vectors, with the key expansion done by AESKEYGENASSIST -/

def bswap64 (x : UInt64) : UInt64 :=
  ((x &&& 0xFF) <<< 56) ||| (((x >>> 8) &&& 0xFF) <<< 48) ||| (((x >>> 16) &&& 0xFF) <<< 40) |||
  (((x >>> 24) &&& 0xFF) <<< 32) ||| (((x >>> 32) &&& 0xFF) <<< 24) ||| (((x >>> 40) &&& 0xFF) <<< 16) |||
  (((x >>> 48) &&& 0xFF) <<< 8) ||| (x >>> 56)

/-- A 16-byte block written as in the standards (first byte most significant), as loaded by MOVDQU:
byte 0 in bits 7..0. -/
def blk (x : Nat) : V128 := { lo := bswap64 (x >>> 64).toUInt64, hi := bswap64 x.toUInt64 }

/-- The key as words w[0..nk) (FIPS-197 5.2; byte 4i of the key in bits 7..0 of w[i]). -/
def keyWords (key nk : Nat) : List UInt32 :=
  (List.range nk).map fun i =>
    let byte := fun (j : Nat) => ((key >>> (8 * (4 * nk - 1 - j))) % 256).toUInt8
    ofB8 (byte (4 * i)) (byte (4 * i + 1)) (byte (4 * i + 2)) (byte (4 * i + 3))

def rconOf (i : Nat) : UInt8 := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36].getD (i - 1) 0

/-- KeyExpansion (FIPS-197 figure 11) with RotWord(SubWord(w)) ^ Rcon and SubWord(w) taken from
AESKEYGENASSIST (dwords 3 and 2 of `aeskeygenassist [0, 0, 0, w] rcon`); `n` more words. -/
def expand (nk : Nat) : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n + 1, w =>
    let i := w.size
    let t := w[i - 1]!
    let t := if i % nk == 0 then dw (aeskeygenassist (ofDw 0 0 0 t) (rconOf (i / nk))) 3
             else if nk > 6 && i % nk == 4 then dw (aeskeygenassist (ofDw 0 0 0 t) 0) 2
             else t
    expand nk n (w.push (w[i - nk]! ^^^ t))

/-- The round keys of a key of `nk` words. -/
def roundKeys (key nk : Nat) : List V128 :=
  let nr := nk + 6
  let w := expand nk (4 * (nr + 1) - nk) (keyWords key nk).toArray
  (List.range (nr + 1)).map fun r => ofDw w[4 * r]! w[4 * r + 1]! w[4 * r + 2]! w[4 * r + 3]!

def encrypt (key nk : Nat) (pt : V128) : V128 :=
  let rk := roundKeys key nk
  encryptL rk.head! (rk.drop 1).dropLast rk.getLast! pt

def decrypt (key nk : Nat) (ct : V128) : V128 :=
  let rk := roundKeys key nk
  decryptL rk.head! (rk.drop 1).dropLast rk.getLast! ct

/-- FIPS-197 appendix A.1: the last round key of the example key expansion. -/
theorem fips197_a1_w43 : (roundKeys 0x2b7e151628aed2a6abf7158809cf4f3c 4).getLast! =
    blk 0xd014f9a8c9ee2589e13f0cc8b6630ca6 := by decide +kernel
/-- FIPS-197 appendix A.2 (192-bit key): w[51]. -/
theorem fips197_a2_w51 : dw (roundKeys 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b 6).getLast! 3 =
    ofB8 0x01 0x00 0x22 0x02 := by decide +kernel
/-- FIPS-197 appendix A.3 (256-bit key): w[59]. -/
theorem fips197_a3_w59 :
    dw (roundKeys 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4 8).getLast! 3 =
    ofB8 0x70 0x6c 0x63 0x1e := by decide +kernel

theorem fips197_b_enc : encrypt 0x2b7e151628aed2a6abf7158809cf4f3c 4 (blk 0x3243f6a8885a308d313198a2e0370734) =
    blk 0x3925841d02dc09fbdc118597196a0b32 := by decide +kernel
theorem fips197_c1_enc : encrypt 0x000102030405060708090a0b0c0d0e0f 4 (blk 0x00112233445566778899aabbccddeeff) =
    blk 0x69c4e0d86a7b0430d8cdb78070b4c55a := by decide +kernel
theorem fips197_c1_dec : decrypt 0x000102030405060708090a0b0c0d0e0f 4 (blk 0x69c4e0d86a7b0430d8cdb78070b4c55a) =
    blk 0x00112233445566778899aabbccddeeff := by decide +kernel
theorem fips197_c2_enc : encrypt 0x000102030405060708090a0b0c0d0e0f1011121314151617 6
    (blk 0x00112233445566778899aabbccddeeff) = blk 0xdda97ca4864cdfe06eaf70a0ec0d7191 := by decide +kernel
theorem fips197_c2_dec : decrypt 0x000102030405060708090a0b0c0d0e0f1011121314151617 6
    (blk 0xdda97ca4864cdfe06eaf70a0ec0d7191) = blk 0x00112233445566778899aabbccddeeff := by decide +kernel
theorem fips197_c3_enc : encrypt 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f 8
    (blk 0x00112233445566778899aabbccddeeff) = blk 0x8ea2b7ca516745bfeafc49904b496089 := by decide +kernel
theorem fips197_c3_dec : decrypt 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f 8
    (blk 0x8ea2b7ca516745bfeafc49904b496089) = blk 0x00112233445566778899aabbccddeeff := by decide +kernel

/-! ## FIPS 180-4 digests composed from the SHA instructions -/

/-- PADDD. -/
def add32 (a b : V128) : V128 := ofDw (dw a 0 + dw b 0) (dw a 1 + dw b 1) (dw a 2 + dw b 2) (dw a 3 + dw b 3)

/-- The padded message (FIPS 180-4 5.1.1) as big-endian 32-bit words, in 16-word blocks. -/
def padWords (msg : List UInt8) : List (List UInt32) :=
  let len := msg.length
  let zeros := (64 + 56 - (len + 1) % 64) % 64
  let bits := 8 * len
  let bytes := msg ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range 8).map fun k => ((bits >>> (8 * (7 - k))) % 256).toUInt8
  let words := (List.range (bytes.length / 4)).map fun i =>
    (bytes.getD (4 * i) 0).toUInt32 <<< 24 ||| (bytes.getD (4 * i + 1) 0).toUInt32 <<< 16 |||
    (bytes.getD (4 * i + 2) 0).toUInt32 <<< 8 ||| (bytes.getD (4 * i + 3) 0).toUInt32
  (List.range (words.length / 16)).map fun b => (words.drop (16 * b)).take 16

/-- SHA-1 message groups: W[4j..4j+3] with W[4j] in dword 3; groups 4..19 by
SHA1MSG1, PXOR and SHA1MSG2. -/
def sha1Groups (m : List UInt32) : Array V128 :=
  let g := fun (j : Nat) => ofDw (m.getD (4 * j + 3) 0) (m.getD (4 * j + 2) 0) (m.getD (4 * j + 1) 0) (m.getD (4 * j) 0)
  (List.range 16).foldl (fun (gs : Array V128) j =>
    let j := j + 4
    gs.push (sha1msg2 (xor128 (sha1msg1 gs[j - 4]! gs[j - 3]!) gs[j - 2]!) gs[j - 1]!))
    #[g 0, g 1, g 2, g 3]

/-- One SHA-1 block: `abcd` holds A..D in dwords 3..0. Each group of four rounds is SHA1RNDS4 with
the message group plus E, which SHA1NEXTE derives from the state four rounds earlier. -/
def sha1Block (st : V128 × UInt32) (m : List UInt32) : V128 × UInt32 :=
  let (abcd0, e0) := st
  let gs := sha1Groups m
  let x0 := add32 gs[0]! (ofDw 0 0 0 e0)
  let (prev, cur) := (List.range 19).foldl (fun (pc : V128 × V128) j =>
    let (prev, cur) := pc
    (cur, sha1rnds4 cur (sha1nexte prev gs[j + 1]!) ((j + 1) / 5).toUInt8))
    (abcd0, sha1rnds4 abcd0 x0 0)
  (add32 cur abcd0, dw (sha1nexte prev (ofDw 0 0 0 e0)) 3)

def sha1 (msg : List UInt8) : List UInt32 :=
  let (abcd, e) := (padWords msg).foldl sha1Block (ofDw 0x10325476 0x98BADCFE 0xEFCDAB89 0x67452301, 0xC3D2E1F0)
  [dw abcd 3, dw abcd 2, dw abcd 1, dw abcd 0, e]

def sha256K : List UInt32 := [
  0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
  0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
  0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
  0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
  0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
  0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
  0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
  0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208, 0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2]

/-- SHA-256 message groups: W[4j..4j+3] with W[4j] in dword 0; groups 4..15 by SHA256MSG1, PALIGNR,
PADDD and SHA256MSG2. -/
def sha256Groups (m : List UInt32) : Array V128 :=
  let g := fun (j : Nat) => ofDw (m.getD (4 * j) 0) (m.getD (4 * j + 1) 0) (m.getD (4 * j + 2) 0) (m.getD (4 * j + 3) 0)
  let alignr := fun (hi lo : V128) => ofDw (dw lo 1) (dw lo 2) (dw lo 3) (dw hi 0)
  (List.range 12).foldl (fun (gs : Array V128) j =>
    let j := j + 4
    gs.push (sha256msg2 (add32 (sha256msg1 gs[j - 4]! gs[j - 3]!) (alignr gs[j - 1]! gs[j - 2]!)) gs[j - 1]!))
    #[g 0, g 1, g 2, g 3]

/-- One SHA-256 block: `s0` holds A, B, E, F and `s1` C, D, G, H (dwords 3, 2, 1, 0). Four rounds
are two SHA256RNDS2 with XMM0 = message group + K and its high half (PSHUFD 0x0E). -/
def sha256Block (st : V128 × V128) (m : List UInt32) : V128 × V128 :=
  let gs := sha256Groups m
  let k := fun (j : Nat) => ofDw (sha256K.getD (4 * j) 0) (sha256K.getD (4 * j + 1) 0)
    (sha256K.getD (4 * j + 2) 0) (sha256K.getD (4 * j + 3) 0)
  let (s0, s1) := (List.range 16).foldl (fun (st : V128 × V128) j =>
    let (s0, s1) := st
    let wk := add32 gs[j]! (k j)
    let s1 := sha256rnds2 s1 s0 wk
    let s0 := sha256rnds2 s0 s1 (ofDw (dw wk 2) (dw wk 3) 0 0)
    (s0, s1)) st
  (add32 s0 st.1, add32 s1 st.2)

def sha256 (msg : List UInt8) : List UInt32 :=
  let h := [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB,
    0x5BE0CD19]
  let init := (ofDw (h.getD 5 0) (h.getD 4 0) (h.getD 1 0) (h.getD 0 0),
               ofDw (h.getD 7 0) (h.getD 6 0) (h.getD 3 0) (h.getD 2 0))
  let (s0, s1) := (padWords msg).foldl sha256Block init
  [dw s0 3, dw s0 2, dw s1 3, dw s1 2, dw s0 1, dw s0 0, dw s1 1, dw s1 0]

def abc : List UInt8 := [0x61, 0x62, 0x63]
/-- "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (448 bits, two blocks padded). -/
def msg448 : List UInt8 := (List.range 14).flatMap fun i => (List.range 4).map fun k => (0x61 + i + k).toUInt8

theorem sha1_abc : sha1 abc = [0xa9993e36, 0x4706816a, 0xba3e2571, 0x7850c26c, 0x9cd0d89d] := by
  decide +kernel
theorem sha1_448 : sha1 msg448 = [0x84983e44, 0x1c3bd26e, 0xbaae4aa1, 0xf95129e5, 0xe54670f1] := by
  decide +kernel
theorem sha256_abc : sha256 abc =
    [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by
  decide +kernel
theorem sha256_448 : sha256 msg448 =
    [0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1] := by
  decide +kernel

/-! ## Carry-less multiplication: identities on samples, GCM test case 2 -/

theorem pclmulqdq_imm (a b : V128) (imm : UInt8) : pclmulqdq a b imm = pclmulqdq a b (imm &&& 0x11) := by
  have h1 : imm &&& 0x11 &&& 0x01 = imm &&& 0x01 := by bv_decide
  have h2 : imm &&& 0x11 &&& 0x10 = imm &&& 0x10 := by bv_decide
  simp only [pclmulqdq, h1, h2]

/-- Samples: commutativity, distributivity over XOR, multiplication by x^k, and the classic
(x+1)^2 = x^2+1 and all-ones squares. -/
def clmulSamples : List (UInt64 × UInt64 × UInt64) :=
  [(0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x8000000000000001),
   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x0000000100000000),
   (0x7B5B54657374566F, 0x6966796D65644B65, 0xA5A5A5A55A5A5A5A),
   (0x8000000000000000, 0x0000000000000003, 0xDEADBEEFCAFEBABE)]

theorem clmul_comm_samples : clmulSamples.all (fun (a, b, _) => clmul a b == clmul b a) = true := by
  decide +kernel
theorem clmul_distrib_samples : clmulSamples.all (fun (a, b, c) =>
    clmul a (b ^^^ c) == xor128 (clmul a b) (clmul a c)) = true := by decide +kernel
theorem clmul_shift_samples : clmulSamples.all (fun (a, _, _) =>
    (List.range 64).all fun k =>
      clmul a ((1 : UInt64) <<< k.toUInt64) ==
        { lo := a <<< k.toUInt64, hi := if k == 0 then 0 else a >>> (64 - k).toUInt64 }) = true := by
  decide +kernel
theorem clmul_square : clmul 3 3 = { lo := 5 } ∧
    clmul 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = { lo := 0x5555555555555555, hi := 0x5555555555555555 } := by
  decide +kernel
/-- PCLMULQDQ selects the quadwords by imm8 bits 0 and 4 (SDM PCLMULQDQ table 4-13). -/
theorem pclmulqdq_select :
    let a : V128 := { lo := 0x0123456789ABCDEF, hi := 0x7B5B54657374566F }
    let b : V128 := { lo := 0xFEDCBA9876543210, hi := 0x6966796D65644B65 }
    pclmulqdq a b 0x00 = clmul a.lo b.lo ∧ pclmulqdq a b 0x01 = clmul a.hi b.lo ∧
    pclmulqdq a b 0x10 = clmul a.lo b.hi ∧ pclmulqdq a b 0x11 = clmul a.hi b.hi ∧
    pclmulqdq a b 0xEE = clmul a.lo b.lo := by decide +kernel

/-- Reverse the bits of each byte: GCM numbers bits from the most significant bit of byte 0
(McGrew–Viega, 2.5), so the polynomial with coefficient x^i = GCM bit i is the block with each
byte bit-reversed. -/
def brev8 (b : UInt8) : UInt8 :=
  (List.range 8).foldl (fun r k => r ||| (((b >>> k.toUInt8) &&& 1) <<< (7 - k).toUInt8)) 0
def reflect (v : V128) : V128 := mapDw (byteMap brev8) v

/-- Multiplication in GF(2^128) modulo x^128 + x^7 + x^2 + x + 1 (GCM): four PCLMULQDQ products,
then the high half folded back twice with PCLMULQDQ by 0x87. -/
def gfmul (x h : V128) : V128 :=
  let a := reflect x
  let b := reflect h
  let mid := xor128 (pclmulqdq a b 0x10) (pclmulqdq a b 0x01)
  let lo := xor128 (pclmulqdq a b 0x00) { lo := 0, hi := mid.lo }
  let hi := xor128 (pclmulqdq a b 0x11) { lo := mid.hi, hi := 0 }
  let r : V128 := { lo := 0x87 }
  let t0 := pclmulqdq hi r 0x00
  let t1 := pclmulqdq hi r 0x01
  let t2 := pclmulqdq { lo := t1.hi } r 0x00
  reflect (xor128 (xor128 (xor128 lo t0) { lo := 0, hi := t1.lo }) t2)

/-- GHASH_H of the given blocks. -/
def ghash (h : V128) (blocks : List V128) : V128 := blocks.foldl (fun y x => gfmul (xor128 y x) h) {}

/-- GCM test case 2: K = 0^128, IV = 0^96, P = 0^128. -/
def gcmH : V128 := encrypt 0 4 (blk 0)
def gcmC : V128 := xor128 (encrypt 0 4 (blk 2)) (blk 0)
def gcmTag : V128 := xor128 (encrypt 0 4 (blk 1)) (ghash gcmH [gcmC, blk 128])

theorem gcm_h : gcmH = blk 0x66e94bd4ef8a2c3b884cfa59ca342b2e := by decide +kernel
theorem gcm_c : gcmC = blk 0x0388dace60b6a392f328c2b971b2fe78 := by decide +kernel
theorem gcm_ghash : ghash gcmH [gcmC, blk 128] = blk 0xf38cbb1ad69223dcc3457ae5b6b0f885 := by decide +kernel
theorem gcm_tag : gcmTag = blk 0xab6e47d42cec13bdf53a67b21257bddf := by decide +kernel

/-! ## Instruction rules -/

/-- Another mandatory prefix (or none, for AES/PCLMULQDQ; any, for SHA) is #UD, before anything
else is checked or changed. -/
theorem xmmOp_prefix {m : Machine} {i : Inst} {pp : UInt8} {avail : Bool} {f : V128 → V128 → V128}
    (h : i.pp ≠ pp) : xmmOp i pp avail f m = .error (.exc Vec.UD none 0) m := by
  simp [xmmOp, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem sha256rnds2Op_prefix {m : Machine} {i : Inst} (h : i.pp ≠ 0) :
    sha256rnds2Op i m = .error (.exc Vec.UD none 0) m := by
  simp [sha256rnds2Op, h, bind, EStateM.bind, ud, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- With the right prefix: #UD while CR4.OSFXSR = 0 (SSE not enabled by the OS), state unchanged. -/
theorem xmmOp_noosfxsr {m : Machine} {i : Inst} {pp : UInt8} {avail : Bool} {f : V128 → V128 → V128}
    (hf : avail = true) (h : m.cpu.cr4 &&& CR4.OSFXSR = 0) :
    xmmOp i pp avail f m = .error (.exc Vec.UD none 0) m := by
  by_cases hp : i.pp = pp
  · simp [xmmOp, hp, hf, sseCheck, cpu, h, bind, EStateM.bind, ud, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]
  · exact xmmOp_prefix hp

/-- With the right prefix, CR0.EM = 0 and CR4.OSFXSR = 1: #NM while CR0.TS = 1, state unchanged. -/
theorem xmmOp_ts {m : Machine} {i : Inst} {pp : UInt8} {avail : Bool} {f : V128 → V128 → V128}
    (hp : i.pp = pp) (hf : avail = true) (he : m.cpu.cr0 &&& CR0.EM = 0)
    (ho : m.cpu.cr4 &&& CR4.OSFXSR ≠ 0) (h : m.cpu.cr0 &&& CR0.TS ≠ 0) :
    xmmOp i pp avail f m = .error (.exc Vec.NM none 0) m := by
  simp [xmmOp, hp, hf, sseCheck, cpu, he, ho, h, bind, EStateM.bind, exc, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw]

theorem crypto_available : implemented .aes = true ∧ implemented .pclmulqdq = true ∧
    shaAvail = true := ⟨rfl, rfl, rfl⟩

/-- The 0F 38 hook takes AES and SHA opcodes only (legacy encodings), each with its own prefix. -/
theorem map2?_forms (i : Inst) (h : i.vex = false) :
    (i.byte = 0xDC → map2? i = some (xmmOp i 1 (implemented .aes) aesenc)) ∧
    (i.byte = 0xDD → map2? i = some (xmmOp i 1 (implemented .aes) aesenclast)) ∧
    (i.byte = 0xDE → map2? i = some (xmmOp i 1 (implemented .aes) aesdec)) ∧
    (i.byte = 0xDF → map2? i = some (xmmOp i 1 (implemented .aes) aesdeclast)) ∧
    (i.byte = 0xC8 → map2? i = some (shaOp i sha1nexte)) ∧
    (i.byte = 0xCB → map2? i = some (sha256rnds2Op i)) ∧
    (i.byte < 0xC8 → map2? i = none) ∧ (0xCD < i.byte → i.byte < 0xDB → map2? i = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hb <;> (try intro hb2) <;>
    simp only [map2?, h, hb, Bool.false_eq_true, ↓reduceIte]
  · split <;> simp_all <;> (rename_i heq; rw [heq] at hb; revert hb; decide)
  · split <;> simp_all <;> (rename_i heq; rw [heq] at hb hb2; revert hb hb2; decide)

/-- VEX-encoded instructions never reach these hooks' instructions (the VEX forms are `Avx`'s). -/
theorem hooks_vex (i : Inst) (h : i.vex = true) : map2? i = none ∧ map3? i = none := by
  simp [map2?, map3?, h]

end Crypto
end X86
