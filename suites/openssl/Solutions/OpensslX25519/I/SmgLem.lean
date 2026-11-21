import Solutions.OpensslX25519.I.CSt4
import Solutions.OpensslX25519.I.LadCSt
import Solutions.OpensslX25519.I.Memcpy
import Solutions.OpensslX25519.I.Cleanse
/-!
# `x25519_scalar_mult_generic`: helper facts

The clamp of the scalar copy as bytes (OpenSSL's `(b & 63) | 64` equals RFC 7748's `(b & 127) | 64`),
`memBytes`/`clamp` lookups, the initial buffer list of the frame state, address shifts. Prover R.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

set_option maxRecDepth 100000 in
theorem clamp0_nat : ∀ n, n < 256 →
    (UInt32.land (UInt8.ofNat n).toUInt32 248).toUInt8 = UInt8.ofNat n &&& 248 := by decide

set_option maxRecDepth 100000 in
theorem clamp31_nat : ∀ n, n < 256 →
    (UInt32.land (UInt32.lor (UInt32.land (UInt32.lor (UInt32.land (UInt8.ofNat n).toUInt32 4294967040)
      (UInt32.land (UInt32.land (UInt32.land (UInt8.ofNat n).toUInt32 255) 63) 255)) 4294967040)
      (UInt32.land (UInt32.lor (UInt32.land (UInt32.lor (UInt32.land (UInt8.ofNat n).toUInt32 4294967040)
        (UInt32.land (UInt32.land (UInt32.land (UInt8.ofNat n).toUInt32 255) 63) 255)) 255) 64) 255)) 255).toUInt8 =
      (UInt8.ofNat n &&& 127) ||| 64 := by decide

theorem clamp0 (b : UInt8) : (UInt32.land b.toUInt32 248).toUInt8 = b &&& 248 := by
  have := clamp0_nat b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem clamp31 (b : UInt8) :
    (UInt32.land (UInt32.lor (UInt32.land (UInt32.lor (UInt32.land b.toUInt32 4294967040)
      (UInt32.land (UInt32.land (UInt32.land b.toUInt32 255) 63) 255)) 4294967040)
      (UInt32.land (UInt32.lor (UInt32.land (UInt32.lor (UInt32.land b.toUInt32 4294967040)
        (UInt32.land (UInt32.land (UInt32.land b.toUInt32 255) 63) 255)) 255) 64) 255)) 255).toUInt8 =
      (b &&& 127) ||| 64 := by
  have := clamp31_nat b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem rd1_memByte {m : ByteArray} {a : UInt32} (h : a.toNat + 1 ≤ m.size) :
    rdRaw m a 1 = (memByte m a).toUInt32 := by
  apply UInt32.toNat_inj.1
  rw [rd1_toNat h, memByte_def (by omega)]
  simp

theorem memBytes_get (m : ByteArray) (a : UInt32) (n i : Nat) (hi : i < n) :
    (memBytes m a n)[i]! = memByte m (a + i.toUInt32) := by
  unfold memBytes
  rw [getElem!_pos _ i (by simp; omega)]
  simp

theorem clamp_get (k : List UInt8) (i : Nat) (hi : i < 32) :
    (Ssl.Spec.X25519.clamp k)[i]! =
      if i = 0 then k[i]! &&& 248 else if i = 31 then (k[i]! &&& 127) ||| 64 else k[i]! := by
  unfold Ssl.Spec.X25519.clamp
  rw [getElem!_pos _ i (by simp; omega)]
  simp

theorem uadd_uadd (a b c d : UInt32) (h : b + c = d) : UInt32.add (UInt32.add a b) c = UInt32.add a d := by
  show a + b + c = a + d
  rw [UInt32.add_assoc, h]

/-- The buffers of the frame of `x25519_scalar_mult_generic` with their current contents. -/
def smgBufs (M : ByteArray) (L : UInt32) : List (Nat × Array UInt32) :=
  [(48, memWords M (UInt32.add L (48 : Nat).toUInt32) 10), (88, memWords M (UInt32.add L (88 : Nat).toUInt32) 10),
    (128, memWords M (UInt32.add L (128 : Nat).toUInt32) 10), (168, memWords M (UInt32.add L (168 : Nat).toUInt32) 10),
    (208, memWords M (UInt32.add L (208 : Nat).toUInt32) 10), (248, memWords M (UInt32.add L (248 : Nat).toUInt32) 10),
    (288, memWords M (UInt32.add L (288 : Nat).toUInt32) 10)]

theorem smgBufs_buf (M : ByteArray) (L : UInt32) :
    ∀ k v, (smgBufs M L).lookup k = some v → memWords M (UInt32.add L k.toUInt32) 10 = v := by
  intro k v h
  unfold smgBufs at h
  simp only [List.lookup] at h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  split at h
  · rename_i e; simp at e; subst e; simp at h; exact h
  simp at h

theorem smg_lay (M : ByteArray) (L out b : UInt32) (w : Nat → UInt32) (s0 s1 s2 s3 : UInt32) :
    LayoutOK 344 ((ladSl out b w s0 s1 s2 s3).map Prod.fst) ((smgBufs M L).map Prod.fst) = true := by
  rfl

/-- `memcpy_call` for 32 bytes, from the count `ic0` (not `icAdd ic0 0`) to `icAdd ic0 183`. -/
theorem memcpy32 (G : XMem) (L ret dst src eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 24) (lr : rdRaw G.get (UInt32.add L 8) 4 = ret)
    (ld : rdRaw G.get (UInt32.add L 12) 4 = dst) (ls : rdRaw G.get (UInt32.add L 16) 4 = src)
    (ln : rdRaw G.get (UInt32.add L 20) 4 = 32) (hd : dst.toNat + 32 ≤ G.get.size)
    (hs : src.toNat + 32 ≤ G.get.size)
    (hdi : dst.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat)
    (hsi : src.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ src.toNat)
    (hds : dst.toNat + 32 ≤ src.toNat ∨ src.toNat + 32 ≤ dst.toNat)
    (hdL : dst.toNat + 32 ≤ L.toNat ∨ L.toNat + 24 ≤ dst.toNat)
    (hsL : src.toNat + 32 ≤ L.toNat ∨ L.toNat + 8 ≤ src.toNat)
    (hic : ic0.toNat + 190 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103ee0, efl fl, ic0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 12, ebp, esi, edi, ret, efl fl', icAdd ic0 183⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 8 ≤ x) ∧ (x < dst.toNat ∨ dst.toNat + 32 ≤ x)) ∧
      ∀ k : Nat, k < 32 → memByte N.get (UInt32.add dst k.toUInt32) = memByte G.get (UInt32.add src k.toUInt32) :=
  memcpy_call G L ret dst src 32 eax ecx edx ebx ebp esi edi fl ic0 hS lr ld ls ln (by decide) hd hs hdi hsi hds hdL hsL
    hic

/-- `cleanse_call` for 32 bytes, from the count `ic0` to `icAdd ic0 157`. -/
theorem cleanse32 (G : XMem) (L ret ptr eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 32) (lr : rdRaw G.get (UInt32.add L 20) 4 = ret)
    (lp : rdRaw G.get (UInt32.add L 24) 4 = ptr) (ll : rdRaw G.get (UInt32.add L 28) 4 = 32)
    (hd : ptr.toNat + 32 ≤ G.get.size)
    (hdi : ptr.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ ptr.toNat)
    (hdL : ptr.toNat + 32 ≤ L.toNat ∨ L.toNat + 32 ≤ ptr.toNat)
    (hic : ic0.toNat + 170 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 20, ebp, esi, edi, 0x103e80, efl fl, ic0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 24, ebp, esi, edi, ret, efl fl', icAdd ic0 157⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 20 ≤ x) ∧ (x < ptr.toNat ∨ ptr.toNat + 32 ≤ x)) ∧
      ∀ a : UInt32, ptr.toNat ≤ a.toNat → a.toNat < ptr.toNat + 32 → memByte N.get a = 0 :=
  cleanse_call G L ret ptr 32 eax ecx edx ebx ebp esi edi fl ic0 hS lr lp ll (by decide) hd hdi hdL
    (by rw [show (32 : UInt32).toNat = 32 from rfl]; omega)

theorem u8_u32_inj {x y : UInt8} (h : x.toUInt32 = y.toUInt32) : x = y := by
  have := congrArg UInt32.toNat h
  simp only [UInt8.toNat_toUInt32] at this
  exact UInt8.toNat_inj.1 this

/-- The scalar words of the frame hold the bytes `eb` when every byte of `[L + 16, L + 48)` does. -/
theorem smg_eb {M : ByteArray} {L : UInt32} {eb : List UInt8} (hs : L.toNat + 48 ≤ M.size) (ht : M.size < 2 ^ 32)
    (hb : ∀ i, i < 32 → ∀ a : UInt32, a.toNat = L.toNat + 16 + i → memByte M a = eb[i]!) :
    EB (fun t => rdRaw M (UInt32.add L (16 + 4 * t).toUInt32) 4) eb := by
  intro t ht8 j hj
  have ea : (UInt32.add L (16 + 4 * t).toUInt32).toNat = L.toNat + 16 + 4 * t := by
    rw [toNat_uadd, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have h1 := rdRaw1_word (m := M) (a := UInt32.add L (16 + 4 * t).toUInt32) (by rw [ea]; omega) (by rw [ea]; omega)
    j hj
  have e2 : (UInt32.add L (16 + 4 * t).toUInt32 + j.toUInt32).toNat = L.toNat + 16 + (4 * t + j) := by
    rw [UInt32.toNat_add, ea, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have h2 := hb (4 * t + j) (by omega) _ e2
  rw [rd1_memByte (by rw [e2]; omega), h2] at h1
  exact (u8_u32_inj h1).symm

/-- The slots of `ladSl` from the word facts. -/
theorem ladSl_slot {M : ByteArray} {L out b s0 s1 s2 s3 : UInt32} {w : Nat → UInt32}
    (h8 : rdRaw M (UInt32.add L 8) 4 = out) (h12 : rdRaw M (UInt32.add L 12) 4 = b)
    (hw : ∀ t, t < 8 → rdRaw M (UInt32.add L (16 + 4 * t).toUInt32) 4 = w t)
    (h0 : rdRaw M (UInt32.add L 328) 4 = s0) (h1 : rdRaw M (UInt32.add L 332) 4 = s1)
    (h2 : rdRaw M (UInt32.add L 336) 4 = s2) (h3 : rdRaw M (UInt32.add L 340) 4 = s3) :
    ∀ k v, (ladSl out b w s0 s1 s2 s3).lookup k = some v → rdRaw M (UInt32.add L k.toUInt32) 4 = v := by
  intro k v hl
  simp only [ladSl, List.lookup] at hl
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h8
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h12
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 0 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 1 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 2 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 3 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 4 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 5 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 6 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact hw 7 (by decide)
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h0
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h1
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h2
  split at hl
  · rename_i e; simp at e; subst e; simp at hl; subst hl; exact h3
  simp at hl

end Solutions.OpensslX25519.I
