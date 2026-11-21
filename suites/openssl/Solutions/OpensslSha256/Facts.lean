import Solutions.OpensslSha256.Chain
import Solutions.OpensslSha256.Alg
import Solutions.Exec.Call
/-!
# The facts of a `SHA256_Transform` call

From the precondition of the task (`TransformPre`): the environment of the run (`Env`), the
argument and return-address words above the frame, and the big-endian words of the block as the
byte-swapped words of memory.
-/
namespace Solutions.OpensslSha256
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256 Ssl.Spec.Sha256

/-! ## Byte swaps -/

theorem bswap_join (b0 b1 b2 b3 : UInt8) :
    let x : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    ((((x <<< 24) ||| ((x &&& 65280) <<< 8)) ||| ((x >>> 8) &&& 65280)) ||| (x >>> 24)) =
      (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32 := by
  intro x
  apply bit_ext
  intro i hi
  have h65 : ∀ j, j < 32 → (UInt32.toBitVec 65280).getLsbD j = decide (8 ≤ j ∧ j < 16) := by decide
  simp only [x, shl32, shr32, UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, UInt8.toBitVec_toUInt32, BitVec.getLsbD_setWidth, h65 i hi]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨
      i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;> simp

/-! ## The environment of a call -/

theorem image_size : Image.bytes.size = 4944 := by simp [Image.bytes, ByteArray.size, Image.size]

theorem apart_nat {a : UInt32} {n : Nat} {b : UInt32} {k : Nat} (h : Apart a n b k) (hn : n ≠ 0)
    (hk : k ≠ 0) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  rcases h with h | h | h <;> omega

theorem stackLo_toNat {c : Caller} {stack : Nat} (h : stack ≤ c.sp.toNat) :
    (c.stackLo stack).toNat = c.sp.toNat - stack := by
  unfold Caller.stackLo
  have hs : stack < 2 ^ 32 := by have := c.sp.toNat_lt; omega
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp; omega

/-- The address facts of a call, in `toNat` form. -/
structure CallFacts (S s x b : Nat) : Prop where
  ram : S ≤ ramTop
  img : 0x100000 + 4944 ≤ S
  sp_lo : 512 ≤ s
  sp_hi : s + 12 ≤ S
  sp_img : s - 512 + 524 ≤ 0x100000 ∨ 0x100000 + 4944 ≤ s - 512
  x_mem : x + 32 ≤ S
  x_img : x + 32 ≤ 0x100000 ∨ 0x100000 + 4944 ≤ x
  x_stk : x + 32 ≤ s - 512 ∨ s - 512 + 524 ≤ x
  b_mem : b + 64 ≤ S
  b_img : b + 64 ≤ 0x100000 ∨ 0x100000 + 4944 ≤ b
  b_stk : b + 64 ≤ s - 512 ∨ s - 512 + 524 ≤ b
  xb : x + 32 ≤ b ∨ b + 64 ≤ x

theorem callFacts {c : Caller} {ctx blockp : UInt32} {H : Array UInt32} {block : List UInt8}
    (h : TransformPre c ctx blockp H block) :
    CallFacts c.mem.size c.sp.toNat ctx.toNat blockp.toNat := by
  obtain ⟨hc, -, -, hbx, hbb, hxb, -, -⟩ := h
  have hs : 512 ≤ c.sp.toNat := hc.2.2.2.2.1
  have hlo := stackLo_toNat (c := c) (stack := stackBound) hs
  have hsi := apart_nat hc.2.2.2.2.2.2 (by simp [stackSize]) (by show img.bytes.size ≠ 0; rw [show img.bytes = Image.bytes from rfl, image_size]; decide)
  rw [hlo, show img.bytes = Image.bytes from rfl, image_size, show img.base.toNat = 0x100000 from rfl] at hsi
  simp only [stackSize, stackBound, List.length] at hsi
  have hsp : c.sp.toNat + 4 * ([ctx, blockp].length + 1) ≤ c.mem.size := hc.2.2.2.2.2.1
  simp only [List.length] at hsp
  have hfit := hc.2.1
  rw [show img.bytes = Image.bytes from rfl, image_size, show img.base.toNat = 0x100000 from rfl] at hfit
  obtain ⟨fx, -, ax, sx⟩ := hbx
  obtain ⟨fb, -, ab, sb⟩ := hbb
  have ax' := apart_nat ax (by decide) (by show img.bytes.size ≠ 0; rw [show img.bytes = Image.bytes from rfl, image_size]; decide)
  have ab' := apart_nat ab (by decide) (by show img.bytes.size ≠ 0; rw [show img.bytes = Image.bytes from rfl, image_size]; decide)
  rw [show img.bytes = Image.bytes from rfl, image_size, show img.base.toNat = 0x100000 from rfl] at ax' ab'
  have sx' := apart_nat sx (by decide) (by simp [stackSize])
  have sb' := apart_nat sb (by decide) (by simp [stackSize])
  rw [hlo] at sx' sb'
  simp only [stackSize, stackBound] at sx' sb'
  have xb' := apart_nat hxb (by decide) (by decide)
  have hram : c.mem.size ≤ ramTop := hc.1
  refine ⟨hram, by omega, hs, by omega, by omega, ?_, ax', by omega, ?_, ab', by omega, xb'⟩
  · rcases fx with h | h
    · simp at h
    · exact h
  · rcases fb with h | h
    · simp at h
    · exact h

theorem sp192_toNat {c : Caller} (hs : 512 ≤ c.sp.toNat) : (c.sp - 192).toNat = c.sp.toNat - 192 := by
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp

/-- The environment of a call. -/
def envOf (c : Caller) (ctx blockp : UInt32) (hF : CallFacts c.mem.size c.sp.toNat ctx.toNat blockp.toNat)
    (hcode : ∀ i, i < imgSize → c.mem.get! (imgBase + i) = Image.byte i) : Env where
  M0 := c.mem
  sp := c.sp - 192
  ctx := ctx
  blk := blockp
  hsz := hF.ram
  himg := by have := hF.img; unfold imgBase imgSize; omega
  hcode := hcode
  hsp := by rw [sp192_toNat hF.sp_lo]; have := hF.sp_hi; have := hF.sp_lo; omega
  hctx := hF.x_mem
  hblk := hF.b_mem
  sp_img := by rw [sp192_toNat hF.sp_lo]; have := hF.sp_img; have := hF.sp_lo; unfold imgBase imgSize; omega
  ctx_img := by have := hF.x_img; unfold imgBase imgSize; omega
  blk_img := by have := hF.b_img; unfold imgBase imgSize; omega
  ctx_sp := by rw [sp192_toNat hF.sp_lo]; have := hF.x_stk; have := hF.sp_lo; omega
  blk_sp := by rw [sp192_toNat hF.sp_lo]; have := hF.b_stk; have := hF.sp_lo; omega
  blk_ctx := by have := hF.xb; omega

theorem calls_code {c : Caller} {args : List UInt32} (h : Calls img c stackBound args) :
    ∀ i, i < imgSize → c.mem.get! (imgBase + i) = Image.byte i :=
  fun i hi => (callMem (byte := Image.byte) (halt := Image.sym_halt) rfl h).ok i hi

end Solutions.OpensslSha256
