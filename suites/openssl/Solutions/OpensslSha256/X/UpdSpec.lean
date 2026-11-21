import Solutions.OpensslSha256.X.UpdGlue
/-!
# The context fields in memory, and what an `Update` does to them

`CtxOk M ctx Hw nl nh num md buf`: the hash words, the two bit count words, `num`, `md_len` and the
buffered bytes in memory. `Good` is `CtxOk` for the values of a message (`ctxOk_of_good`,
`good_of_ctxOk`). `updH`/`updB`: the hash words and the buffered bytes after an `Update` with a chunk
(whole blocks compressed, the rest buffered); `good_upd`: they are those of the longer message.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslSha256 Ssl.Spec.Sha256
open Solutions.OpensslSha256 (lw Good hOf tailOf tailOf_length hOf_small hOf_big)

/-- The fields of the context at `ctx` in `M`. -/
structure CtxOk (M : ByteArray) (ctx : UInt32) (Hw : Array UInt32) (nl nh num md : UInt32) (buf : List UInt8) :
    Prop where
  h : ∀ k, k < 8 → rdRaw M (ctx + (4 * k).toUInt32) 4 = Hw[k]!
  nl : rdRaw M (ctx.add 32) 4 = nl
  nh : rdRaw M (ctx.add 36) 4 = nh
  num : rdRaw M (ctx.add 104) 4 = num
  md : rdRaw M (ctx.add 108) 4 = md
  buf : ∀ i, i < buf.length → M.get! (ctx.toNat + 40 + i) = buf[i]!

theorem ctxOk_of_good {M : ByteArray} {ctx : UInt32} {H0 : Array UInt32} {md : Nat} {msg : List UInt8}
    (hfit : ctx.toNat + 112 ≤ M.size) (hM : M.size < 2 ^ 32) (hG : Good H0 md msg (memBytes M ctx 112)) :
    CtxOk M ctx (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
      (msg.length % 64).toUInt32 md.toUInt32 (tailOf msg) where
  h k hk := by
    have := hG.h k hk
    rwa [lw_memBytes (by omega) hfit hM] at this
  nl := by have := hG.nl; rwa [lw_memBytes (by omega) hfit hM] at this
  nh := by have := hG.nh; rwa [lw_memBytes (by omega) hfit hM] at this
  num := by have := hG.num; rwa [lw_memBytes (by omega) hfit hM] at this
  md := by have := hG.md; rwa [lw_memBytes (by omega) hfit hM] at this
  buf i hi := by
    rw [tailOf_length] at hi
    have := hG.data i hi
    rw [memBytes_get (by omega) hfit hM] at this
    rw [← this, Nat.add_assoc]

theorem good_of_ctxOk {M : ByteArray} {ctx : UInt32} {H0 : Array UInt32} {md : Nat} {msg : List UInt8}
    (hfit : ctx.toNat + 112 ≤ M.size) (hM : M.size < 2 ^ 32) (hlt : msg.length < lenBound)
    (hC : CtxOk M ctx (hOf H0 msg) (8 * msg.length).toUInt32 (8 * msg.length / 2 ^ 32).toUInt32
      (msg.length % 64).toUInt32 md.toUInt32 (tailOf msg)) : Good H0 md msg (memBytes M ctx 112) where
  len := memBytes_length _ _ _
  lt := hlt
  h k hk := by rw [lw_memBytes (by omega) hfit hM]; exact hC.h k hk
  nl := by rw [lw_memBytes (by omega) hfit hM]; exact hC.nl
  nh := by rw [lw_memBytes (by omega) hfit hM]; exact hC.nh
  num := by rw [lw_memBytes (by omega) hfit hM]; exact hC.num
  md := by rw [lw_memBytes (by omega) hfit hM]; exact hC.md
  data i hi := by
    rw [memBytes_get (by omega) hfit hM, ← Nat.add_assoc]
    exact hC.buf i (by rw [tailOf_length]; exact hi)

theorem toUInt32_toNat_mod (n : Nat) : (n.toUInt32).toNat = n % 2 ^ 32 := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']

/-- The bytes of the chunk consumed to complete the buffered block. -/
def jOf (buf : List UInt8) : Nat := if buf.length = 0 then 0 else 64 - buf.length

/-- The hash words after an `Update`. -/
def updH (Hw : Array UInt32) (buf chunk : List UInt8) : Array UInt32 :=
  if buf.length + chunk.length < 64 then Hw
  else (blocks ((chunk.drop (jOf buf)).take (64 * ((chunk.length - jOf buf) / 64)))).foldl compress
    ((blocks (buf ++ chunk.take (jOf buf))).foldl compress Hw)

/-- The buffered bytes after an `Update`. -/
def updB (buf chunk : List UInt8) : List UInt8 :=
  if buf.length + chunk.length < 64 then buf ++ chunk
  else (chunk.drop (jOf buf)).drop (64 * ((chunk.length - jOf buf) / 64))

theorem upd_spec (H0 : Array UInt32) (msg chunk : List UInt8) :
    hOf H0 (msg ++ chunk) = updH (hOf H0 msg) (tailOf msg) chunk ∧
    tailOf (msg ++ chunk) = updB (tailOf msg) chunk := by
  have hT := tailOf_length msg
  unfold updH updB
  by_cases hs : (tailOf msg).length + chunk.length < 64
  · rw [if_pos hs, if_pos hs]
    exact hOf_small H0 msg chunk (by omega)
  · rw [if_neg hs, if_neg hs]
    apply hOf_big
    unfold jOf
    by_cases h0 : msg.length % 64 = 0
    · left; rw [hT]; simp [h0]
    · right; rw [hT] at hs ⊢; simp only [h0, ite_false]; exact ⟨h0, trivial, by omega⟩

/-- The context after an `Update` is that of the longer message. -/
theorem good_upd {M : ByteArray} {ctx : UInt32} {H0 : Array UInt32} {md : Nat} {msg chunk : List UInt8}
    (hfit : ctx.toNat + 112 ≤ M.size) (hM : M.size < 2 ^ 32) (hlt : (msg ++ chunk).length < lenBound)
    (nl nh num : UInt32)
    (hnl : nl.toNat = (8 * msg.length % 2 ^ 32 + 8 * chunk.length) % 2 ^ 32)
    (hnh : nh.toNat = ((8 * msg.length / 2 ^ 32) % 2 ^ 32 + chunk.length / 2 ^ 29 % 2 ^ 32 +
        (if 8 * msg.length % 2 ^ 32 % 2 ^ 32 + 8 * chunk.length % 2 ^ 32 ≥ 2 ^ 32 then 1 else 0)) % 2 ^ 32)
    (hnum : num.toNat = (msg.length % 64 + chunk.length) % 64)
    (hC : CtxOk M ctx (updH (hOf H0 msg) (tailOf msg) chunk) nl nh num md.toUInt32 (updB (tailOf msg) chunk)) :
    Good H0 md (msg ++ chunk) (memBytes M ctx 112) := by
  obtain ⟨e1, e2⟩ := upd_spec H0 msg chunk
  rw [← e1, ← e2] at hC
  have hl : (msg ++ chunk).length = msg.length + chunk.length := List.length_append
  rw [hl] at hlt
  obtain ⟨b1, b2⟩ := Solutions.OpensslSha256.bitcount_add msg.length chunk.length hlt
  refine good_of_ctxOk hfit hM (by rw [hl]; exact hlt) ?_
  rw [hl]
  have enl : nl = (8 * (msg.length + chunk.length)).toUInt32 := by
    apply UInt32.toNat_inj.1; rw [hnl, toUInt32_toNat_mod]; omega
  have enh : nh = (8 * (msg.length + chunk.length) / 2 ^ 32).toUInt32 := by
    apply UInt32.toNat_inj.1; rw [hnh, toUInt32_toNat_mod, b2]
    simp only [Nat.mod_mod]
  have enum : num = ((msg.length + chunk.length) % 64).toUInt32 := by
    apply UInt32.toNat_inj.1; rw [hnum, toUInt32_toNat_mod]; omega
  rw [enl, enh, enum] at hC
  exact hC

/-! ## Frames of `Update`/`Final` and the bit operations of the block loop -/

/-- The stack frame and the context of a call whose caller's stack pointer is `U.add 24` (the block
function uses 168 bytes below `U`). -/
structure UF (M : ByteArray) (U ctx : UInt32) : Prop where
  sz : M.size ≤ 4273995776
  lo : 168 ≤ U.toNat
  hi : U.toNat + 56 ≤ M.size
  img : U.toNat + 56 ≤ 1048576 ∨ 1048576 + 4944 + 168 ≤ U.toNat
  cfit : ctx.toNat + 112 ≤ M.size
  cimg : 1048576 + 4944 ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ 1048576
  cU : ctx.toNat + 112 + 168 ≤ U.toNat ∨ U.toNat + 56 ≤ ctx.toNat

theorem UF.size {M M' : ByteArray} {U ctx : UInt32} (h : UF M U ctx) (hs : M'.size = M.size) : UF M' U ctx :=
  ⟨by rw [hs]; exact h.sz, h.lo, by rw [hs]; exact h.hi, h.img, by rw [hs]; exact h.cfit, h.cimg, h.cU⟩

/-- A non-empty region `[p, p + n)` apart from the image, the frame and the context. -/
structure MF (M : ByteArray) (U ctx p : UInt32) (n : Nat) : Prop where
  fit : p.toNat + n ≤ M.size
  img : 1048576 + 4944 ≤ p.toNat ∨ p.toNat + n ≤ 1048576
  stk : p.toNat + n + 168 ≤ U.toNat ∨ U.toNat + 56 ≤ p.toNat
  c : p.toNat + n ≤ ctx.toNat ∨ ctx.toNat + 112 ≤ p.toNat

theorem MF.size {M M' : ByteArray} {U ctx p : UInt32} {n : Nat} (h : MF M U ctx p n) (hs : M'.size = M.size) :
    MF M' U ctx p n := ⟨by rw [hs]; exact h.fit, h.img, h.stk, h.c⟩

theorem MF.sub {M : ByteArray} {U ctx p q : UInt32} {n m : Nat} (h : MF M U ctx p n) (hq : p.toNat ≤ q.toNat)
    (hm : q.toNat + m ≤ p.toNat + n) : MF M U ctx q m := by
  have := h.fit; have := h.img; have := h.stk; have := h.c
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The saved registers and the return address in the frame. -/
structure SV (M : ByteArray) (U sesi sedi sebx sebp ra : UInt32) : Prop where
  s0 : rdRaw M (U.add 24) 4 = sesi
  s1 : rdRaw M (U.add 28) 4 = sedi
  s2 : rdRaw M (U.add 32) 4 = sebx
  s3 : rdRaw M (U.add 36) 4 = sebp
  s4 : rdRaw M (U.add 40) 4 = ra

theorem land_hi (x : Nat) (hx : x < 2 ^ 32) : x &&& 4294967232 = 2 ^ 6 * (x / 2 ^ 6) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hm : (4294967232 : Nat) = 2 ^ 6 * (2 ^ 26 - 1) := by decide
  have hb := Nat.testBit_two_pow_mul_add (x / 2 ^ 6) (Nat.mod_lt x (by decide : 2 ^ 6 > 0)) i
  rw [Nat.div_add_mod] at hb
  rw [Nat.testBit_and, hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, hb]
  by_cases h6 : i < 6
  · simp [h6, show ¬ i ≥ 6 by omega]
  · simp only [h6, ite_false, show i ≥ 6 by omega, decide_true, Bool.true_and]
    by_cases h32 : i - 6 < 26
    · simp [h32]
    · have : (x / 2 ^ 6).testBit (i - 6) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : x / 2 ^ 6 < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h32, this]

theorem u32_hi (L : UInt32) : (L &&& 4294967232).toNat = 64 * (L.toNat / 64) := by
  rw [UInt32.toNat_and, show (4294967232 : UInt32).toNat = 4294967232 from rfl, land_hi _ L.toNat_lt]

theorem u32_lo (L : UInt32) : (L &&& 63).toNat = L.toNat % 64 := by
  rw [UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem u32_shr6 (L : UInt32) : (L >>> 6).toNat = L.toNat / 64 := by
  have e2 : ∀ x y : UInt32, ShiftRight.shiftRight x y = HShiftRight.hShiftRight x y := fun _ _ => rfl
  simp only [e2]
  rw [UInt32.toNat_shiftRight]
  simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]

end Solutions.ShaX
