import Solutions.OpensslChacha20.Head
import Solutions.OpensslChacha20.Tail
import Solutions.OpensslChacha20.Setup
import Solutions.OpensslChacha20.Output
import Solutions.OpensslChacha20.Rounds10
import Solutions.OpensslChacha20.XorLoop
import Solutions.OpensslChacha20.BlockSpec
import Solutions.OpensslChacha20.StateSpec
/-!
# One block of `ChaCha20_ctr32`

From the loop head `0x1000b0` with the state matrix `w` at `C + 144`: `n = min(64, rem)` output
bytes are the input bytes xor the keystream block of `w`, the block counter (word 12) is
incremented, the pointers advance by `n`, and the run goes back to the loop head or, for the last
block, to the epilogue. Memory changes only in the stack frames `[C - 24, C + 272)` and the `n`
output bytes.
-/
namespace Solutions.OpensslChacha20
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslChacha20 Ssl.Spec.Chacha

theorem Agree.toOn {lo n : Nat} {A B : ByteArray} (h : Agree lo n A B) :
    AgreeOn (fun a => lo ≤ a ∧ a < lo + n) A B :=
  AgreeOn.of_agree h (fun _ h1 h2 => ⟨h1, h2⟩)

/-- The block length. -/
def blockN (rem : UInt32) : UInt32 := if rem.toNat < 64 then rem else 64

theorem blockN_toNat (rem : UInt32) : (blockN rem).toNat = min rem.toNat 64 := by
  unfold blockN
  by_cases h : rem.toNat < 64
  · rw [if_pos h]; omega
  · rw [if_neg h]; show (64 : UInt32).toNat = _; rw [show (64 : UInt32).toNat = 64 from rfl]; omega

/-- What a block changes: the stack frames and the output bytes. -/
def BlockRegion (C out : UInt32) (n : Nat) (a : Nat) : Prop :=
  (C.toNat - 24 ≤ a ∧ a < C.toNat + 272) ∨ (out.toNat ≤ a ∧ a < out.toNat + n)

/-- The address facts of a block. -/
structure BlockOk (size : Nat) (C inp out : UInt32) (n : Nat) : Prop where
  stack : StackOk size C
  n1 : 1 ≤ n
  n64 : n ≤ 64
  binp : ByteRegion size inp n
  bout : ByteRegion size out n
  io : inp = out ∨ inp.toNat + n ≤ out.toNat ∨ out.toNat + n ≤ inp.toNat
  inpS : inp.toNat + n ≤ C.toNat - 24 ∨ C.toNat + 312 ≤ inp.toNat
  outS : out.toNat + n ≤ C.toNat - 24 ∨ C.toNat + 312 ≤ out.toNat

theorem caddv {C : UInt32} {k : Nat} (h : C.toNat + k < 2 ^ 32) (hk : k < 2 ^ 32) :
    (C.add (OfNat.ofNat k)).toNat = C.toNat + k := by
  show (C + OfNat.ofNat k).toNat = _
  rw [UInt32.toNat_add]
  have : (OfNat.ofNat k : UInt32).toNat = k := by
    show (k.toUInt32).toNat = k
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  rw [this]; exact Nat.mod_eq_of_lt h

theorem cadd {C : UInt32} {k : Nat} (h : C.toNat + (OfNat.ofNat k : Nat) < 2 ^ 32)
    (hk : (OfNat.ofNat k : Nat) < 2 ^ 32) :
    (C.add (OfNat.ofNat k)).toNat = C.toNat + (OfNat.ofNat k : Nat) := by
  show (C + OfNat.ofNat k).toNat = _
  rw [UInt32.toNat_add]
  have : (OfNat.ofNat k : UInt32).toNat = k := by
    show (k.toUInt32).toNat = k
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  rw [this]; exact Nat.mod_eq_of_lt h

theorem csub24 {C : UInt32} (h : 24 ≤ C.toNat) : (C.add 4294967272).toNat = C.toNat - 24 := by
  show (C + 4294967272).toNat = _
  rw [UInt32.toNat_add]
  have := C.toNat_lt
  simp only [UInt32.reduceToNat]
  omega

/-- `InAt` moves along memories that agree on the state matrix. -/
theorem inAt_transfer {P : Nat → Prop} {M M' : ByteArray} {C : UInt32} {w : V16} (h : InAt M C w)
    (ha : AgreeOn P M M') (hsz : C.toNat + 208 ≤ M.size) (hC : C.toNat + 312 < 2 ^ 32)
    (hP : ∀ a, C.toNat + 144 ≤ a → a < C.toNat + 208 → ¬ P a) : InAt M' C w := by
  have e : ∀ k : Nat, 144 ≤ k → k + 4 ≤ 208 → ∀ v, rdRaw M (C.add (OfNat.ofNat k)) 4 = v →
      rdRaw M' (C.add (OfNat.ofNat k)) 4 = v := by
    intro k h1 h2 v hv
    rw [ha.rdRaw4 (by rw [caddv (by omega) (by omega)]; omega)
      (fun j hj => hP _ (by rw [caddv (by omega) (by omega)]; omega) (by rw [caddv (by omega) (by omega)]; omega))]
    exact hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨e 144 (by omega) (by omega) _ h0, e 148 (by omega) (by omega) _ h1, e 152 (by omega) (by omega) _ h2,
    e 156 (by omega) (by omega) _ h3, e 160 (by omega) (by omega) _ h4, e 164 (by omega) (by omega) _ h5,
    e 168 (by omega) (by omega) _ h6, e 172 (by omega) (by omega) _ h7, e 176 (by omega) (by omega) _ h8,
    e 180 (by omega) (by omega) _ h9, e 184 (by omega) (by omega) _ h10, e 188 (by omega) (by omega) _ h11,
    e 192 (by omega) (by omega) _ h12, e 196 (by omega) (by omega) _ h13, e 200 (by omega) (by omega) _ h14,
    e 204 (by omega) (by omega) _ h15⟩

/-- The block counter store. -/
theorem inAt_next {M : ByteArray} {C : UInt32} {w : V16} (h : InAt M C w) (hsz : C.toNat + 208 ≤ M.size)
    (hC : C.toNat + 312 < 2 ^ 32) : InAt (wrBytes M (C.add 192) 4 (w.x12 + 1)) C w.next := by
  have h192 : (C.add 192).toNat = C.toNat + 192 := cadd (by omega) (by omega)
  have ha : Agree (C.toNat + 192) 4 M (wrBytes M (C.add 192) 4 (w.x12 + 1)) :=
    agree_wrBytes4 (Agree.refl _ _ _) (by rw [h192]; omega) (by omega) (by omega)
  have h' := inAt_transfer (P := fun a => C.toNat + 192 ≤ a ∧ a < C.toNat + 196) h
    (AgreeOn.of_agree ha (fun a h1 h2 => ⟨h1, h2⟩)) hsz hC
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have e : ∀ k : Nat, 144 ≤ k → k + 4 ≤ 208 → (k + 4 ≤ 192 ∨ 196 ≤ k) → ∀ v,
      rdRaw M (C.add (OfNat.ofNat k)) 4 = v → rdRaw (wrBytes M (C.add 192) 4 (w.x12 + 1)) (C.add (OfNat.ofNat k)) 4 = v := by
    intro k h1 h2 h3 v hv
    unfold rdRaw at hv ⊢
    rw [rdBytes4_wrBytes4_other (by rw [h192]; omega) (by rw [caddv (by omega) (by omega)]; omega)
      (by rw [h192, caddv (by omega) (by omega)]; omega)]
    exact hv
  refine ⟨e 144 (by omega) (by omega) (by omega) _ h0, e 148 (by omega) (by omega) (by omega) _ h1,
    e 152 (by omega) (by omega) (by omega) _ h2, e 156 (by omega) (by omega) (by omega) _ h3,
    e 160 (by omega) (by omega) (by omega) _ h4, e 164 (by omega) (by omega) (by omega) _ h5,
    e 168 (by omega) (by omega) (by omega) _ h6, e 172 (by omega) (by omega) (by omega) _ h7,
    e 176 (by omega) (by omega) (by omega) _ h8, e 180 (by omega) (by omega) (by omega) _ h9,
    e 184 (by omega) (by omega) (by omega) _ h10, e 188 (by omega) (by omega) (by omega) _ h11, ?_,
    e 196 (by omega) (by omega) (by omega) _ h13, e 200 (by omega) (by omega) (by omega) _ h14,
    e 204 (by omega) (by omega) (by omega) _ h15⟩
  show rdRaw (wrBytes M (C.add 192) 4 (w.x12 + 1)) (C.add 192) 4 = w.x12 + 1
  exact rdBytes4_wrBytes4_self (by rw [h192]; omega)

theorem setupRS_toV (r : RS) (w : V16) : (setupRS r w).toV = w := by
  rcases w with ⟨⟩; rfl

/-- The output words at `C + 0xd0`, uniformly. -/
theorem outWord {M : ByteArray} {C : UInt32} {v w : V16}
    (h : rdRaw M (C.add 208) 4 = UInt32.add v.x0 w.x0 ∧ rdRaw M (C.add 212) 4 = UInt32.add v.x1 w.x1 ∧
      rdRaw M (C.add 216) 4 = UInt32.add v.x2 w.x2 ∧ rdRaw M (C.add 220) 4 = UInt32.add v.x3 w.x3 ∧
      rdRaw M (C.add 224) 4 = UInt32.add v.x4 w.x4 ∧ rdRaw M (C.add 228) 4 = UInt32.add v.x5 w.x5 ∧
      rdRaw M (C.add 232) 4 = UInt32.add v.x6 w.x6 ∧ rdRaw M (C.add 236) 4 = UInt32.add v.x7 w.x7 ∧
      rdRaw M (C.add 240) 4 = UInt32.add v.x8 w.x8 ∧ rdRaw M (C.add 244) 4 = UInt32.add v.x9 w.x9 ∧
      rdRaw M (C.add 248) 4 = UInt32.add v.x10 w.x10 ∧ rdRaw M (C.add 252) 4 = UInt32.add v.x11 w.x11 ∧
      rdRaw M (C.add 256) 4 = UInt32.add v.x12 w.x12 ∧ rdRaw M (C.add 260) 4 = UInt32.add v.x13 w.x13 ∧
      rdRaw M (C.add 264) 4 = UInt32.add v.x14 w.x14 ∧ rdRaw M (C.add 268) 4 = UInt32.add v.x15 w.x15)
    (q : Nat) (hq : q < 16) :
    rdRaw M (C.add (OfNat.ofNat (208 + 4 * q))) 4 = v.get q + w.get q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨
    q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- The run to the copy loop. -/
theorem block_head (H0 : CMem) (C eax ecx edx edi rem inp out f : UInt32) (ic : UInt64)
    (hS : StackOk H0.get.size C) :
    ∃ (H1 : CMem) (f1 : UInt32),
      exN Image.sym_halt 38 ⟨H0.get, eax, ecx, edx, rem, C.add 144, inp, out, edi, 0x1000b0, efl f, ic⟩ =
        some ⟨H1.get, C.add 60, 64, C.add 144, rem, C.add 4294967272, inp, 0, blockN rem, 0x100420, efl f1,
          ic + 3 + 35⟩ ∧
      CallFrame H1.get C rem inp out (blockN rem) ∧
      AgreeOn (fun a => C.toNat - 24 ≤ a ∧ a < C.toNat + 144) H0.get H1.get := by
  have e1 : ∃ f1 : UInt32, exN Image.sym_halt 3 ⟨H0.get, eax, ecx, edx, rem, C.add 144, inp, out, edi, 0x1000b0,
      efl f, ic⟩ = some ⟨H0.get, eax, ecx, edx, rem, C.add 144, inp, out, blockN rem, 0x1000bb, efl f1, ic + 3⟩ := by
    unfold blockN
    split
    · exact blockLen_lt H0 C eax ecx edx rem inp out edi f ic hS (by assumption)
    · exact blockLen_ge H0 C eax ecx edx rem inp out edi f ic hS (by omega)
  obtain ⟨f1, e1⟩ := e1
  obtain ⟨H1, f2, e2, hcf, ha⟩ := call_run H0 C eax ecx edx rem inp out (blockN rem) f1 (ic + 3) hS
  exact ⟨H1, f2, exN_trans e1 e2, hcf, ha⟩

theorem ic_bound {ic : UInt64} {k : Nat} (h : ic.toNat + (OfNat.ofNat k : Nat) < 2 ^ 64)
    (hk : (OfNat.ofNat k : Nat) < 2 ^ 64) :
    (ic + (OfNat.ofNat k : UInt64)).toNat = ic.toNat + (OfNat.ofNat k : Nat) := u64_add_lit hk h

theorem ic_step {x : UInt64} {c k : Nat} (hx : x.toNat = c) (h : c + (OfNat.ofNat k : Nat) < 2 ^ 64)
    (hk : (OfNat.ofNat k : Nat) < 2 ^ 64) :
    (x + (OfNat.ofNat k : UInt64)).toNat = c + (OfNat.ofNat k : Nat) := by
  rw [ic_bound (by rw [hx]; exact h) hk, hx]

theorem ic_stepN {x : UInt64} {c k : Nat} (hx : x.toNat = c) (h : c + k < 2 ^ 64) (hk : k < 2 ^ 64) :
    (x + k.toUInt64).toNat = c + k := by rw [u64_add_toNat hk (by omega), hx]

theorem caddk {C : UInt32} (k : Nat) : (C.add (OfNat.ofNat k)).toNat = (C.toNat + k % 2 ^ 32) % 2 ^ 32 := by
  show (C + OfNat.ofNat k).toNat = _
  rw [UInt32.toNat_add]
  rfl

/-- The copy of the state matrix at `C + 60`. -/
theorem copyAt_of {M1 M2 : ByteArray} {C : UInt32} {w : V16} (hw : InAt M1 C w)
    (hcp : Copied M1 M2 (C.add 60) (C.add 144) 64) (hsz : C.toNat + 312 ≤ M1.size) (hC : C.toNat + 312 < 2 ^ 32) :
    CopyAt M2 C w := by
  have h60 : (C.add 60).toNat = C.toNat + 60 := cadd (by omega) (by omega)
  have h144 : (C.add 144).toNat = C.toNat + 144 := cadd (by omega) (by omega)
  have hs : M2.size = M1.size := hcp.1.1
  have e : ∀ k : Nat, k < 16 → ∀ v, rdRaw M1 (C.add (OfNat.ofNat (144 + 4 * k))) 4 = v →
      rdRaw M2 (C.add (OfNat.ofNat (60 + 4 * k))) 4 = v := by
    intro k hk v hv
    rw [← hv]
    apply rdRaw4_of_bytes (by rw [hs, caddv (by omega) (by omega)]; omega) (by rw [caddv (by omega) (by omega)]; omega)
    intro j hj
    rw [caddv (by omega) (by omega), caddv (by omega) (by omega)]
    have := hcp.2 (4 * k + j) (by omega)
    rw [h60, h144] at this
    rw [show C.toNat + (60 + 4 * k) + j = C.toNat + 60 + (4 * k + j) by omega,
      show C.toNat + (144 + 4 * k) + j = C.toNat + 144 + (4 * k + j) by omega]
    exact this
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hw
  exact ⟨e 0 (by omega) _ h0, e 1 (by omega) _ h1, e 2 (by omega) _ h2, e 3 (by omega) _ h3, e 4 (by omega) _ h4,
    e 5 (by omega) _ h5, e 6 (by omega) _ h6, e 7 (by omega) _ h7, e 8 (by omega) _ h8, e 9 (by omega) _ h9,
    e 10 (by omega) _ h10, e 11 (by omega) _ h11, e 12 (by omega) _ h12, e 13 (by omega) _ h13,
    e 14 (by omega) _ h14, e 15 (by omega) _ h15⟩

set_option maxHeartbeats 4000000 in
theorem block_run (H0 : CMem) (C eax ecx edx edi rem inp out f : UInt32) (w : V16) (ic : UInt64)
    (hB : BlockOk H0.get.size C inp out (blockN rem).toNat) (hw : InAt H0.get C w)
    (hic : ic.toNat + 4096 < 2 ^ 64) :
    ∃ (H : CMem) (f' eax' ecx' edx' : UInt32) (ic' : UInt64),
      Run img (St.m ⟨H0.get, eax, ecx, edx, rem, C.add 144, inp, out, edi, 0x1000b0, efl f, ic⟩)
        (St.m ⟨H.get, eax', ecx', edx', UInt32.sub rem (blockN rem), C.add 144, UInt32.add inp (blockN rem),
          UInt32.add out (blockN rem), blockN rem, if rem.toNat ≤ 64 then 0x1000ed else 0x1000b0, efl f', ic'⟩) ∧
      ic'.toNat ≤ ic.toNat + 4096 ∧
      AgreeOn (BlockRegion C out (blockN rem).toNat) H0.get H.get ∧
      InAt H.get C w.next ∧
      ∀ i (hi : i < (blockN rem).toNat), H.get.get! (out.toNat + i) =
        H0.get.get! (inp.toNat + i) ^^^ (block 20 w.toArr)[i]'(by rw [block_length]; have := hB.n64; omega) := by
  obtain ⟨hS, hn1, hn64, hinp, hout, hio, hinpS, houtS⟩ := hB
  obtain ⟨hsz, hClo, hfit, hcode⟩ := hS
  have hS : StackOk H0.get.size C := ⟨hsz, hClo, hfit, hcode⟩
  have hC32 : C.toNat + 312 < 2 ^ 32 := by omega
  -- 1. to the copy loop
  obtain ⟨H1, f1, e1, hcf, ha1⟩ := block_head H0 C eax ecx edx edi rem inp out f ic hS
  have r1 := run_of_exN e1 (by show ic.toNat + 38 < 2 ^ 64; omega)
  have hs1 : H1.get.size = H0.get.size := ha1.1
  have ic1 : (ic + 3 + 35).toNat = ic.toNat + 38 := by
    rw [ic_bound (by rw [ic_bound (by omega) (by omega)]; omega) (by omega), ic_bound (by omega) (by omega)]
  -- 2. the copy loop
  have h60 : (C.add 60).toNat = C.toNat + 60 := cadd (by omega) (by omega)
  have h144 : (C.add 144).toNat = C.toNat + 144 := cadd (by omega) (by omega)
  obtain ⟨H2, f2, ebx2, r2, hcp⟩ := memcpy_loop H1 (C.add 4294967272) (C.add 60) (C.add 144) rem inp (blockN rem)
    f1 (ic + 3 + 35) (by rw [hs1]; exact hsz)
    ⟨by rw [hs1, h60]; omega, by rw [h60]; omega⟩ ⟨by rw [hs1, h144]; omega, by rw [h144]; omega⟩
    (by rw [h60, h144]; omega) (by rw [ic1]; omega)
  have hs2 : H2.get.size = H0.get.size := hcp.1.1.trans hs1
  have hcpR : ∀ a, (C.add 60).toNat ≤ a ∧ a < (C.add 60).toNat + 64 → C.toNat + 60 ≤ a ∧ a < C.toNat + 124 := by
    intro a h; rw [h60] at h; omega
  -- words of `H1` outside the copy are words of `H2`
  have keep2 : ∀ a : UInt32, a.toNat + 4 ≤ C.toNat + 60 ∨ C.toNat + 124 ≤ a.toNat → a.toNat + 4 ≤ H1.get.size →
      rdRaw H2.get a 4 = rdRaw H1.get a 4 := by
    intro a ha hb
    exact hcp.1.rdRaw4 hb (fun k hk h => by rw [h60] at h; omega)
  obtain ⟨cf20, cf36, cf124, cf128, cf132, cf136, cf140, cfm20, cfm24, cfm16⟩ := hcf
  have k2 : ∀ k : Nat, (k < 56 ∨ (124 ≤ k ∧ k ≤ 308) ∨ (4294967272 ≤ k ∧ k < 2 ^ 32)) →
      rdRaw H2.get (C.add (OfNat.ofNat k)) 4 = rdRaw H1.get (C.add (OfNat.ofNat k)) 4 := by
    intro k hk
    apply keep2 <;> rw [caddk] <;> (try rw [hs1]) <;> omega
  -- 3. back from `memcpy`
  have ic2 : (ic + 3 + 35 + (320 : Nat).toUInt64).toNat = ic.toNat + 358 := by
    rw [u64_add_toNat (by omega) (by rw [ic1]; omega), ic1]
  obtain ⟨f3, e3⟩ := memcpyRet_run H2 C (C.add 60) 64 (C.add 144) ebx2 inp 64 (blockN rem) f2 rem out
    (ic + 3 + 35 + (320 : Nat).toUInt64) (by rw [hs2]; exact hS)
    (by rw [k2 4294967272 (by omega)]; exact cfm24) (by rw [k2 4294967276 (by omega)]; exact cfm20)
    (by rw [k2 4294967280 (by omega)]; exact cfm16)
  have r3 := run_of_exN e3 (by show (ic + 3 + 35 + (320 : Nat).toUInt64).toNat + 4 < 2 ^ 64; rw [ic2]; omega)
  -- 4. the set-up of the rounds
  let r0 : RS := ⟨C.add 60, 64, C.add 144, rem, inp, out, blockN rem, rdRaw H2.get C 4, rdRaw H2.get (C.add 4) 4,
    rdRaw H2.get (C.add 8) 4, rdRaw H2.get (C.add 12) 4, rdRaw H2.get (C.add 16) 4, rdRaw H2.get (C.add 20) 4,
    rdRaw H2.get (C.add 24) 4, rdRaw H2.get (C.add 28) 4, rdRaw H2.get (C.add 32) 4, rdRaw H2.get (C.add 36) 4,
    rdRaw H2.get (C.add 40) 4, rdRaw H2.get (C.add 44) 4, rdRaw H2.get (C.add 48) 4, rdRaw H2.get (C.add 52) 4,
    rdRaw H2.get (C.add 56) 4⟩
  have hF2 : FrameOk H2 C := ⟨by rw [hs2]; exact hsz, by rw [hs2]; omega, by omega⟩
  have hcopy : CopyAt H2.get C w :=
    copyAt_of (inAt_transfer hw ha1 (by omega) hC32 (fun a h1 h2 h => by omega)) hcp (by rw [hs1]; omega) hC32
  have ic3 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4).toNat = ic.toNat + 362 := ic_step ic2 (by omega) (by omega)
  obtain ⟨H3, f5, e5, c3, a3⟩ := setup_run H2 C f3 r0 w (ic + 3 + 35 + (320 : Nat).toUInt64 + 4)
    (by rw [hs2]; exact hS)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcopy
  have r5 := run_of_exN e5 (by show (ic + 3 + 35 + (320 : Nat).toUInt64 + 4).toNat + 29 < 2 ^ 64; rw [ic3]; omega)
  have hs3 : H3.get.size = H0.get.size := a3.1.trans hs2
  -- 5. the rounds
  have ic5 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29).toNat = ic.toNat + 391 := ic_step ic3 (by omega) (by omega)
  obtain ⟨H4, f6, r6, c4, a4⟩ := rounds_run H3 C f5 (setupRS r0 w) (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29)
    (hF2.of_agree a3) c3 rfl (by rw [ic5]; omega)
  have hs4 : H4.get.size = H0.get.size := a4.1.trans hs3
  -- 6. the output words and the return
  have ic6 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64).toNat = ic.toNat + 1771 :=
    ic_stepN ic5 (by omega) (by omega)
  have hw4 : InAt H4.get C w :=
    inAt_transfer (inAt_transfer (inAt_transfer (inAt_transfer hw ha1 (by omega) hC32 (fun a h1 h2 h => by omega))
      hcp.1 (by rw [hs1]; omega) hC32 (fun a h1 h2 h => by rw [h60] at h; omega))
      (Agree.toOn a3) (by rw [hs2]; omega) hC32 (fun a h1 h2 h => by
        (try simp only at h) <;> omega))
      (Agree.toOn a4) (by rw [hs3]; omega) hC32 (fun a h1 h2 h => by
        (try simp only at h) <;> omega)
  -- words of `H1` above the slots are words of `H4`
  have k4 : ∀ k : Nat, 124 ≤ k → k ≤ 308 →
      rdRaw H4.get (C.add (OfNat.ofNat k)) 4 = rdRaw H1.get (C.add (OfNat.ofNat k)) 4 := by
    intro k hk1 hk2
    have hk : (C.add (OfNat.ofNat k)).toNat = C.toNat + k := caddv (by omega) (by omega)
    rw [(AgreeOn.of_agree a4 (P := fun a => C.toNat ≤ a ∧ a < C.toNat + 60) (fun a h1 h2 => ⟨h1, h2⟩)).rdRaw4
      (by rw [hk, hs3]; omega) (fun j hj h => by rw [hk] at h; omega),
      (AgreeOn.of_agree a3 (P := fun a => C.toNat ≤ a ∧ a < C.toNat + 60) (fun a h1 h2 => ⟨h1, h2⟩)).rdRaw4
      (by rw [hk, hs2]; omega) (fun j hj h => by rw [hk] at h; omega)]
    exact k2 k (by omega)
  have h14 : (rfin (setupRS r0 w)).s14 = C.add 144 := by
    rw [rfin_s14]; show rdRaw H2.get (C.add 20) 4 = C.add 144; rw [k2 20 (by omega)]; exact cf20
  have h24 : (rfin (setupRS r0 w)).s24 = C.add 208 := by
    rw [rfin_s24]; show rdRaw H2.get (C.add 36) 4 = C.add 208; rw [k2 36 (by omega)]; exact cf36
  obtain ⟨H5, f7, a7, c7, d7, e7, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, a5⟩ := output_run H4 C f6 (rfin (setupRS r0 w)) w out (blockN rem) rem inp
    (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64) (by rw [hs4]; exact hS)
    c4 h14 h24 hw4
    ⟨by rw [k4 124 (by omega) (by omega)]; exact cf124, by rw [k4 128 (by omega) (by omega)]; exact cf128,
     by rw [k4 132 (by omega) (by omega)]; exact cf132, by rw [k4 136 (by omega) (by omega)]; exact cf136,
     by rw [k4 140 (by omega) (by omega)]; exact cf140⟩
  have r7 := run_of_exN e7 (by
    show (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64).toNat + 61 < 2 ^ 64
    rw [ic6]; omega)
  have hs5 : H5.get.size = H0.get.size := a5.1.trans hs4
  have ow := And.intro o0 (And.intro o1 (And.intro o2 (And.intro o3 (And.intro o4 (And.intro o5 (And.intro o6
    (And.intro o7 (And.intro o8 (And.intro o9 (And.intro o10 (And.intro o11 (And.intro o12 (And.intro o13
    (And.intro o14 o15))))))))))))))
  -- 7. to the xor loop
  have ic7 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61).toNat = ic.toNat + 1832 :=
    ic_step ic6 (by omega) (by omega)
  obtain ⟨f8, e8⟩ := xorStart_run H5 C a7 c7 d7 rem inp out (blockN rem) f7
    (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61) (by rw [hs5]; exact hS)
  have r8 := run_of_exN e8 (by
    show (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61).toNat + 9 < 2 ^ 64
    rw [ic7]; omega)
  -- 8. the xor loop
  have ic8 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9).toNat =
      ic.toNat + 1841 := ic_step ic7 (by omega) (by omega)
  have h208 : ((C.add 144).add 64).toNat = C.toNat + 208 := by
    rw [cadd (by rw [h144]; omega) (by omega), h144]
  obtain ⟨H6, f9, c9, r9, hx⟩ := xor_loop H5 (C.add 144) rem inp out (blockN rem) c7 d7 f8
    (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9) (by rw [hs5]; exact hsz)
    ⟨by rw [h208, hs5]; omega, by rw [h208]; omega⟩ (by rw [h144]; omega)
    ⟨by rw [hs5]; exact hinp.1, hinp.2⟩ ⟨by rw [hs5]; exact hout.1, hout.2⟩ hn1 hn64 hio
    (by rw [h144]; omega) (by rw [ic8]; omega)
  have hs6 : H6.get.size = H0.get.size := hx.1.1.trans hs5
  -- 9. the end of the block
  have ic9 : (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9 +
      (6 * (blockN rem).toNat).toUInt64).toNat = ic.toNat + 1841 + 6 * (blockN rem).toNat :=
    ic_stepN ic8 (by omega) (by omega)
  have hw5 : InAt H5.get C w := inAt_transfer hw4 a5 (by rw [hs4]; omega) hC32 (fun a h1 h2 h => by
    unfold OutRegion at h; omega)
  have hw6 : InAt H6.get C w := inAt_transfer hw5 hx.1 (by rw [hs5]; omega) hC32 (fun a h1 h2 h => by omega)
  have hctr : rdRaw H6.get (C.add 192) 4 = w.x12 := hw6.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS6 : StackOk H6.get.size C := by rw [hs6]; exact hS
  have last : ∃ (H7 : CMem) (f10 : UInt32),
      exN Image.sym_halt 5 ⟨H6.get, blockN rem, c9, d7, rem, C.add 144, inp, out, blockN rem, 0x1000e1, efl f9,
        ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9 +
          (6 * (blockN rem).toNat).toUInt64⟩ =
        some ⟨H7.get, blockN rem, c9, d7, UInt32.sub rem (blockN rem), C.add 144, UInt32.add inp (blockN rem),
          UInt32.add out (blockN rem), blockN rem, if rem.toNat ≤ 64 then 0x1000ed else 0x1000b0, efl f10,
          ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9 +
            (6 * (blockN rem).toNat).toUInt64 + 5⟩ ∧
      H7.get = wrBytes H6.get (C.add 192) 4 (UInt32.add w.x12 1) := by
    by_cases hl : rem.toNat ≤ 64
    · rw [if_pos hl]
      exact blockEnd_last H6 C _ c9 d7 rem inp out (blockN rem) f9 w.x12 _ hS6 hctr (by rw [blockN_toNat]; omega)
    · rw [if_neg hl]
      exact blockEnd_more H6 C _ c9 d7 rem inp out (blockN rem) f9 w.x12 _ hS6 hctr (by rw [blockN_toNat]; omega)
  obtain ⟨H7, f10, e10, hm7⟩ := last
  have r10 := run_of_exN e10 (by
    show (ic + 3 + 35 + (320 : Nat).toUInt64 + 4 + 29 + (1380 : Nat).toUInt64 + 61 + 9 +
      (6 * (blockN rem).toNat).toUInt64).toNat + 5 < 2 ^ 64
    rw [ic9]; omega)
  have h192 : (C.add 192).toNat = C.toNat + 192 := cadd (by omega) (by omega)
  refine ⟨H7, f10, _, _, _, _, r1.trans (r2.trans (r3.trans (r5.trans (r6.trans (r7.trans (r8.trans
    (r9.trans r10))))))), ?_, ?_, ?_, ?_⟩
  · rw [ic_step ic9 (by omega) (by omega)]; omega
  · -- what changed
    have a7 : Agree (C.toNat + 192) 4 H6.get H7.get := by
      rw [hm7]; exact agree_wrBytes4 (Agree.refl _ _ _) (by rw [h192, hs6]; omega) (by omega) (by omega)
    refine ((((((ha1.mono ?_).trans (hcp.1.mono ?_)).trans ((Agree.toOn a3).mono ?_)).trans
      ((Agree.toOn a4).mono ?_)).trans (a5.mono ?_)).trans (hx.1.mono ?_)).trans
      ((Agree.toOn a7).mono ?_)
    all_goals intro a h
    all_goals (try unfold OutRegion at h)
    all_goals (try rw [h60] at h)
    all_goals (unfold BlockRegion; (try simp only at h) <;> omega)
  · rw [hm7]; exact inAt_next hw6 (by rw [hs6]; omega) hC32
  · -- the output bytes
    intro i hi
    have hiS : ¬ (C.toNat + 192 ≤ out.toNat + i ∧ out.toNat + i < C.toNat + 196) := by omega
    rw [hm7, get!_wrBytes4 (by rw [h192, hs6]; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), hx.2 i hi, h208]
    -- the input byte is the caller's
    have hin5 : H5.get.get! (inp.toNat + i) = H0.get.get! (inp.toNat + i) := by
      have hP : AgreeOn (fun a => C.toNat - 24 ≤ a ∧ a < C.toNat + 272) H0.get H5.get := by
        refine (((((ha1.mono ?_).trans (hcp.1.mono ?_)).trans
          ((Agree.toOn a3).mono ?_)).trans
          ((Agree.toOn a4).mono ?_)).trans (a5.mono ?_))
        all_goals intro a h
        all_goals (try unfold OutRegion at h)
        all_goals (try rw [h60] at h)
        all_goals ((try simp only at h ⊢) <;> omega)
      exact hP.2 _ (by have := hinp.1; omega) (by omega)
    rw [hin5, UInt8.xor_comm]
    refine congrArg (fun x => H0.get.get! (inp.toNat + i) ^^^ x) ?_
    -- the keystream byte
    have hq : i / 4 < 16 := by omega
    have hw' := outWord (v := Nat.repeat dround 10 w) (w := w) (M := H5.get) (C := C)
      (by rw [← setupRS_toV r0 w, ← rfin_toV]; exact ow) (i / 4) hq
    have hb := get!_of_rdRaw4 (by rw [caddv (by omega) (by omega), hs5]; omega) hw' (i % 4) (Nat.mod_lt _ (by decide))
    rw [caddv (by omega) (by omega), show C.toNat + (208 + 4 * (i / 4)) + i % 4 = C.toNat + 208 + i by omega] at hb
    rw [hb, ← block_getElem w i (by omega)]

end Solutions.OpensslChacha20
