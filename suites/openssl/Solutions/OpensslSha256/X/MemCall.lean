import Solutions.OpensslSha256.X.MemcpyRun
/-!
# Calls of `memset` and `memcpy`, as runs of machine states

`memset_call`: `memset(dst, c, n)` called with the stack pointer at `U.add 4`: returns to the
return address, with the `n` bytes at `dst` set to the low byte of `c` and nothing else written but
the saved register word at `U`. `memcpy_call`: `memcpy(dst, src, n)` called with the stack pointer at
`U.add 8`, for disjoint `dst` and `src`: the `n` bytes at `dst` are those at `src`, the two saved
register words at `U`, `U.add 4` are the only other bytes written.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

/-- `B` is `A` outside the addresses satisfying `P` (and has its size). -/
def AgreeOn (P : Nat → Prop) (A B : ByteArray) : Prop :=
  B.size = A.size ∧ ∀ a, a < A.size → ¬ P a → B.get! a = A.get! a

theorem AgreeOn.refl (P : Nat → Prop) (A : ByteArray) : AgreeOn P A A := ⟨rfl, fun _ _ _ => rfl⟩

theorem AgreeOn.trans {P : Nat → Prop} {A B C : ByteArray} (h1 : AgreeOn P A B) (h2 : AgreeOn P B C) :
    AgreeOn P A C :=
  ⟨h2.1.trans h1.1, fun a ha hn => (h2.2 a (by rw [h1.1]; exact ha) hn).trans (h1.2 a ha hn)⟩

theorem AgreeOn.mono {P Q : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) (hPQ : ∀ a, P a → Q a) :
    AgreeOn Q A B := ⟨h.1, fun a ha hn => h.2 a ha (fun hp => hn (hPQ a hp))⟩

theorem agreeOn_wr1 {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a v : UInt32}
    (ha : a.toNat < B.size) (hP : P a.toNat) : AgreeOn P A (wrBytes B a 1 v) := by
  refine ⟨by rw [size_wrBytes1 ha]; exact h.1, fun b hb hd => ?_⟩
  rw [get!_wrBytes1 ha, if_neg (fun e => hd (by rw [e]; exact hP))]
  exact h.2 b hb hd

theorem agreeOn_wr4 {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a v : UInt32}
    (ha : a.toNat + 4 ≤ B.size) (hP : ∀ k, k < 4 → P (a.toNat + k)) : AgreeOn P A (wrBytes B a 4 v) := by
  refine ⟨by rw [size_wrBytes4 ha]; exact h.1, fun b hb hd => ?_⟩
  rw [get!_wrBytes4 ha]
  have h0 : b ≠ a.toNat := fun e => hd (by have := hP 0 (by decide); rw [e]; simpa using this)
  have h1 : b ≠ a.toNat + 1 := fun e => hd (by rw [e]; exact hP 1 (by decide))
  have h2 : b ≠ a.toNat + 2 := fun e => hd (by rw [e]; exact hP 2 (by decide))
  have h3 : b ≠ a.toNat + 3 := fun e => hd (by rw [e]; exact hP 3 (by decide))
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
  exact h.2 b hb hd

/-- A word whose bytes agree. -/
theorem rdRaw4_agree {P : Nat → Prop} {A B : ByteArray} (h : AgreeOn P A B) {a : UInt32}
    (ha : a.toNat + 4 ≤ A.size) (hP : ∀ k, k < 4 → ¬ P (a.toNat + k)) : rdRaw B a 4 = rdRaw A a 4 := by
  unfold rdRaw
  exact rdBytes4_congr (by rw [h.1]; exact ha) ha (fun k hk => h.2 _ (by omega) (hP k hk))

theorem toUInt32_toNat' {i : Nat} (h : i < 2 ^ 32) : (i.toUInt32).toNat = i := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem toNat_addN {a : UInt32} {k : Nat} (h : a.toNat + k < 2 ^ 32) : (a.add k.toUInt32).toNat = a.toNat + k := by
  show (a + k.toUInt32).toNat = _
  rw [UInt32.toNat_add, toUInt32_toNat' (by omega)]; exact Nat.mod_eq_of_lt h

theorem addN_succ (a : UInt32) (i : Nat) : (a.add i.toUInt32).add 1 = a.add (i + 1).toUInt32 := by
  show a + i.toUInt32 + 1 = a + (i + 1).toUInt32
  rw [UInt32.add_assoc]; congr 1
  apply UInt32.toNat_inj.1
  simp only [Nat.toUInt32_eq, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

theorem subN_succ (N i : Nat) (h : i + 1 ≤ N) (hN : N < 2 ^ 32) :
    ((N - i).toUInt32).add 4294967295 = (N - (i + 1)).toUInt32 := by
  apply UInt32.toNat_inj.1
  show ((N - i).toUInt32 + 4294967295).toNat = _
  simp only [Nat.toUInt32_eq, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

theorem u64_add4 (ic : UInt64) (a b : Nat) : ic + a.toUInt64 + (OfNat.ofNat b : UInt64) = ic + (a + b).toUInt64 := by
  rw [UInt64.add_assoc]
  congr 1
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  show _ = (a + b) % 2 ^ 64
  have : (OfNat.ofNat b : UInt64).toNat = b % 2 ^ 64 := rfl
  rw [this]
  omega

theorem low_byte (c : UInt32) : (c.land 255).toUInt8 = c.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((c &&& 255).toUInt8).toBitVec.getLsbD i = _
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt32.toBitVec_and, BitVec.getLsbD_and, hi,
    decide_true, Bool.true_and]
  have h2 : ∀ j, j < 8 → (UInt32.toBitVec 255).getLsbD j = true := by decide
  rw [h2 i hi, Bool.and_true]

/-- Not in the image `[0x100000, 0x101350)`. -/
def OffCode (a : UInt32) (n : Nat) : Prop := 1048576 + 4944 ≤ a.toNat ∨ a.toNat + n ≤ 1048576

/-! ## `memset` -/

/-- The loop after `i` bytes. -/
theorem memset_loop (H1 : CMem) (U dst c N ebx ebp edi f : UInt32) (ic : UInt64) (hN : 1 ≤ N.toNat)
    (hsz : H1.get.size ≤ 4273995776) (hd : dst.toNat + N.toNat ≤ H1.get.size) (hdc : OffCode dst N.toNat)
    (hic : ic.toNat + 4 * N.toNat < 2 ^ 64) :
    ∀ i, i < N.toNat → ∃ (H : CMem) (f' : UInt32),
      Run img (St.m ⟨H1.get, dst, N, c, ebx, U, ebp, dst, edi, 0x101240, efl f, ic⟩)
        (St.m ⟨H.get, dst, (N.toNat - i).toUInt32, c, ebx, U, ebp, dst.add i.toUInt32, edi, 0x101240, efl f',
          ic + (4 * i).toUInt64⟩) ∧
      AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + N.toNat) H1.get H.get ∧
      ∀ k, k < i → H.get.get! (dst.toNat + k) = c.toUInt8 := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨H1, f, ?_, AgreeOn.refl _ _, fun k hk => absurd hk (by omega)⟩
    have e1 : (N.toNat - 0).toUInt32 = N := by simp
    have e2 : dst.add (0 : Nat).toUInt32 = dst := uadd_zero dst
    rw [e1, e2, show ic + (4 * 0 : Nat).toUInt64 = ic by simp]
    exact Run.refl _ _
  | succ i ih =>
    intro hi
    obtain ⟨H, f1, hr, ha, hb⟩ := ih (by omega)
    have hS : H.get.size = H1.get.size := ha.1
    have hdi : (dst.add i.toUInt32).toNat = dst.toNat + i := toNat_addN (by unfold OffCode at hdc; omega)
    obtain ⟨H', f2, e, hm⟩ := memset_cont H U dst (N.toNat - i).toUInt32 c ebx ebp (dst.add i.toUInt32) edi f1
      (ic + (4 * i).toUInt64) (by rw [hS]; exact hsz) (by rw [hdi, hS]; omega)
      (by rw [hdi]; unfold OffCode at hdc; omega) (by rw [toUInt32_toNat' (by omega)]; omega)
    have hic' : (ic + (4 * i).toUInt64).toNat = ic.toNat + 4 * i := by
      rw [UInt64.toNat_add]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    have hr2 := exN_run (img := img) 4 _ _ e (by show (ic + (4 * i).toUInt64).toNat + 4 < 2 ^ 64; rw [hic']; omega)
    rw [subN_succ N.toNat i (by omega) (by omega), addN_succ, u64_add4] at hr2
    refine ⟨H', f2, hr.trans (by rw [show 4 * (i + 1) = 4 * i + 4 by omega]; exact hr2), ?_, fun k hk => ?_⟩
    · rw [hm]; exact agreeOn_wr1 ha (by rw [hdi, hS]; omega) (by rw [hdi]; omega)
    · have hlt : (dst.add i.toUInt32).toNat < H.get.size := by rw [hdi, hS]; omega
      rw [hm, get!_wrBytes1 hlt]
      by_cases hk' : k = i
      · subst hk'; rw [if_pos hdi.symm, low_byte]
      · rw [if_neg (by rw [hdi]; omega)]; exact hb k (by omega)

theorem u64_toNat_add {ic : UInt64} {k : Nat} (h : ic.toNat + k < 2 ^ 64) : (ic + k.toUInt64).toNat = ic.toNat + k := by
  rw [UInt64.toNat_add]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega

theorem u64_lit (k : Nat) (h : k < 2 ^ 64) : (OfNat.ofNat k : UInt64) = k.toUInt64 := rfl

theorem rdRaw_wr4_self {M : ByteArray} {a v : UInt32} (h : a.toNat + 4 ≤ M.size) : rdRaw (wrBytes M a 4 v) a 4 = v :=
  rdBytes4_wrBytes4_self h

theorem rdRaw_wr4_other {M : ByteArray} {a b v : UInt32} (ha : a.toNat + 4 ≤ M.size) (hb : b.toNat + 4 ≤ M.size)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) : rdRaw (wrBytes M a 4 v) b 4 = rdRaw M b 4 :=
  rdBytes4_wrBytes4_other ha hb hd

theorem toNat_add_lit {U : UInt32} {k : Nat} (h : U.toNat + k < 2 ^ 32) (hk : k < 2 ^ 32) :
    (U.add (OfNat.ofNat k)).toNat = U.toNat + k := by
  show (U + (OfNat.ofNat k : UInt32)).toNat = _
  rw [UInt32.toNat_add]
  have : (OfNat.ofNat k : UInt32).toNat = k := by
    show (UInt32.ofNat k).toNat = k
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  rw [this]; exact Nat.mod_eq_of_lt h

/-- A call of `memset(dst, c, n)`. -/
theorem memset_call (H : CMem) (U ra dst c n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 20 ≤ H.get.size) (hUc : OffCode U 20)
    (hra : rdRaw H.get (U.add 4) 4 = ra) (hdst : rdRaw H.get (U.add 8) 4 = dst)
    (hc : rdRaw H.get (U.add 12) 4 = c) (hn : rdRaw H.get (U.add 16) 4 = n)
    (hd : dst.toNat + n.toNat ≤ H.get.size) (hdc : OffCode dst n.toNat)
    (hdU : dst.toNat + n.toNat ≤ U.toNat ∨ U.toNat + 20 ≤ dst.toNat)
    (hic : ic.toNat + 4 * n.toNat + 30 < 2 ^ 64) :
    ∃ (H' : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 4 * n.toNat + 22 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 4, ebp, esi, edi, 0x101220, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, U.add 8, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 4 ∨ dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H.get H'.get ∧
      ∀ i, i < n.toNat → H'.get.get! (dst.toNat + i) = c.toUInt8 := by
  unfold OffCode at hUc hdc
  have hU4 : (U.add 4).toNat = U.toNat + 4 := toNat_add_lit (k := 4) (by omega) (by decide)
  have hUw : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 4 ∨ dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H.get
      (wrBytes H.get U 4 esi) :=
    agreeOn_wr4 (AgreeOn.refl _ _) (by omega) (fun k hk => Or.inl ⟨by omega, by omega⟩)
  by_cases hn0 : n.toNat = 0
  · obtain ⟨H', f', e, hm⟩ := memset_zero H U dst c n ra eax ecx edx ebx ebp esi edi f ic hsz hU hUc hra hdst hn hn0
    refine ⟨H', dst, n, edx, f', ic + 7, ?_, exN_run (img := img) 7 _ _ e (by show ic.toNat + 7 < _; omega),
      by rw [hm]; exact hUw, fun i hi => absurd hi (by omega)⟩
    rw [u64_lit 7 (by decide), u64_toNat_add (by omega)]; omega
  · obtain ⟨H1, f1, e1, hm1⟩ := memset_head H U dst c n eax ecx edx ebx ebp esi edi f ic hsz hU hUc hdst hc hn hn0
    have r1 := exN_run (img := img) 20 _ _ e1 (by show ic.toNat + 20 < _; omega)
    have hS1 : H1.get.size = H.get.size := by rw [hm1, size_wrBytes4 (by omega)]
    have hic1 : (ic + 20).toNat = ic.toNat + 20 := by rw [u64_lit 20 (by decide), u64_toNat_add (by omega)]
    obtain ⟨H2, f2, r2, ha2, hb2⟩ := memset_loop H1 U dst c n ebx ebp edi f1 (ic + 20) (by omega)
      (by rw [hS1]; exact hsz) (by rw [hS1]; exact hd) hdc (by rw [hic1]; omega) (n.toNat - 1) (by omega)
    have hS2 : H2.get.size = H.get.size := by rw [ha2.1, hS1]
    have hp : (dst.add (n.toNat - 1).toUInt32).toNat = dst.toNat + (n.toNat - 1) := toNat_addN (by omega)
    have hic2 : (ic + 20 + (4 * (n.toNat - 1)).toUInt64).toNat = ic.toNat + 20 + 4 * (n.toNat - 1) := by
      rw [u64_toNat_add (by rw [hic1]; omega), hic1]
    obtain ⟨H3, f3, e3, hm3⟩ := memset_exit H2 U dst (n.toNat - (n.toNat - 1)).toUInt32 c ebx ebp
      (dst.add (n.toNat - 1).toUInt32) edi f2 (ic + 20 + (4 * (n.toNat - 1)).toUInt64) (by rw [hS2]; exact hsz)
      (by rw [hp, hS2]; omega) (by rw [hp]; omega) (by rw [toUInt32_toNat' (by omega)]; omega)
    have r3 := exN_run (img := img) 4 _ _ e3 (by show (ic + 20 + (4 * (n.toNat - 1)).toUInt64).toNat + 4 < _; rw [hic2]; omega)
    have hD3 : AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H1.get H3.get := by
      rw [hm3]; exact agreeOn_wr1 ha2 (by rw [hp, hS2]; omega) (by rw [hp]; omega)
    have hS3 : H3.get.size = H.get.size := by rw [hD3.1, hS1]
    have hsv : rdRaw H3.get U 4 = esi := by
      rw [rdRaw4_agree hD3 (by rw [hS1]; omega) (fun k hk => by omega), hm1, rdRaw_wr4_self (by omega)]
    have hra3 : rdRaw H3.get (U.add 4) 4 = ra := by
      rw [rdRaw4_agree hD3 (by rw [hS1, hU4]; omega) (fun k hk => by rw [hU4]; omega), hm1,
        rdRaw_wr4_other (by omega) (by rw [hU4]; omega) (by rw [hU4]; omega), hra]
    have hic3 : (ic + 20 + (4 * (n.toNat - 1)).toUInt64 + 4).toNat = ic.toNat + 20 + 4 * (n.toNat - 1) + 4 := by
      rw [u64_lit 4 (by decide), u64_toNat_add (by rw [hic2]; omega), hic2]
    obtain ⟨f4, e4⟩ := memset_tail H3 U ra esi dst ((n.toNat - (n.toNat - 1)).toUInt32.add 4294967295) c ebx ebp
      ((dst.add (n.toNat - 1).toUInt32).add 1) edi f3 _ (by rw [hS3]; exact hsz) (by rw [hS3]; exact hU) hUc hsv hra3
    have r4 := exN_run (img := img) 2 _ _ e4 (by show (ic + 20 + (4 * (n.toNat - 1)).toUInt64 + 4).toNat + 2 < _; rw [hic3]; omega)
    refine ⟨H3, _, _, _, f4, _, ?_, r1.trans (r2.trans (r3.trans r4)), ?_, fun i hi => ?_⟩
    · rw [u64_lit 2 (by decide), u64_toNat_add (by rw [hic3]; omega), hic3]; omega
    · rw [hm1] at hD3
      exact hUw.trans (hD3.mono fun a h => Or.inr h)
    · have hlt : (dst.add (n.toNat - 1).toUInt32).toNat < H2.get.size := by rw [hp, hS2]; omega
      rw [hm3, get!_wrBytes1 hlt]
      by_cases hi' : i = n.toNat - 1
      · subst hi'; rw [if_pos hp.symm, low_byte]
      · rw [if_neg (by rw [hp]; omega)]; exact hb2 i (by omega)

/-! ## `memcpy` -/

theorem rd1_byte {M : ByteArray} {a : UInt32} (h : a.toNat < M.size) :
    ((rdRaw M a 1).land 255).toUInt8 = M.get! a.toNat := by
  rw [low_byte]
  unfold rdRaw
  rw [rdBytes1_eq h, memByte_def h]
  apply UInt8.toNat_inj.1
  simp

/-- The copy loop after `i` bytes. -/
theorem memcpy_loop (H1 : CMem) (U dst src N ebx ebp edi f : UInt32) (ic : UInt64) (hN : 1 ≤ N.toNat)
    (hsz : H1.get.size ≤ 4273995776) (hd : dst.toNat + N.toNat ≤ H1.get.size) (hdc : OffCode dst N.toNat)
    (hs : src.toNat + N.toNat ≤ H1.get.size) (hsc : OffCode src N.toNat)
    (hds : dst.toNat + N.toNat ≤ src.toNat ∨ src.toNat + N.toNat ≤ dst.toNat)
    (hic : ic.toNat + 5 * N.toNat < 2 ^ 64) :
    ∀ i, i < N.toNat → ∃ (H : CMem) (f' ebx' : UInt32),
      Run img (St.m ⟨H1.get, dst, N, src, ebx, U, ebp, 0, edi, 0x101210, efl f, ic⟩)
        (St.m ⟨H.get, dst, N, src, ebx', U, ebp, i.toUInt32, edi, 0x101210, efl f', ic + (5 * i).toUInt64⟩) ∧
      AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + N.toNat) H1.get H.get ∧
      ∀ k, k < i → H.get.get! (dst.toNat + k) = H1.get.get! (src.toNat + k) := by
  unfold OffCode at hdc hsc
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨H1, f, ebx, ?_, AgreeOn.refl _ _, fun k hk => absurd hk (by omega)⟩
    rw [show ic + (5 * 0 : Nat).toUInt64 = ic by simp]
    exact Run.refl _ _
  | succ i ih =>
    intro hi
    obtain ⟨H, f1, ebx1, hr, ha, hb⟩ := ih (by omega)
    have hS : H.get.size = H1.get.size := ha.1
    have hi32 : (i.toUInt32).toNat = i := toUInt32_toNat' (by omega)
    obtain ⟨H', f2, e, hm⟩ := memcpy_cont H U dst src N i.toUInt32 ebx1 ebp edi f1 (ic + (5 * i).toUInt64)
      (by rw [hS]; exact hsz) (by rw [hS]; exact hd) (by omega) (by rw [hS]; exact hs) (by omega)
      (by rw [hi32]; omega)
    have hic' : (ic + (5 * i).toUInt64).toNat = ic.toNat + 5 * i := u64_toNat_add (by omega)
    have hr2 := exN_run (img := img) 5 _ _ e (by show (ic + (5 * i).toUInt64).toNat + 5 < 2 ^ 64; rw [hic']; omega)
    have hdi : (dst.add i.toUInt32).toNat = dst.toNat + i := toNat_addN (by omega)
    have hsi : (src.add i.toUInt32).toNat = src.toNat + i := toNat_addN (by omega)
    have e1 : i.toUInt32.add 1 = (i + 1).toUInt32 := by
      have := addN_succ 0 i
      simp only [show ∀ x : UInt32, (0 : UInt32).add x = x from fun x => UInt32.zero_add x] at this
      exact this
    rw [e1, u64_add4] at hr2
    refine ⟨H', f2, _, hr.trans (by rw [show 5 * (i + 1) = 5 * i + 5 by omega]; exact hr2), ?_, fun k hk => ?_⟩
    · rw [hm]; exact agreeOn_wr1 ha (by rw [hdi, hS]; omega) (by rw [hdi]; omega)
    · have hlt : (dst.add i.toUInt32).toNat < H.get.size := by rw [hdi, hS]; omega
      rw [hm, get!_wrBytes1 hlt]
      by_cases hk' : k = i
      · subst hk'
        rw [if_pos hdi.symm, rd1_byte (by rw [hsi, hS]; omega), hsi]
        exact ha.2 _ (by omega) (by omega)
      · rw [if_neg (by rw [hdi]; omega)]; exact hb k (by omega)

/-- A call of `memcpy(dst, src, n)` for disjoint `dst` and `src`. -/
theorem memcpy_call (H : CMem) (U ra dst src n eax ecx edx ebx ebp esi edi f : UInt32) (ic : UInt64)
    (hsz : H.get.size ≤ 4273995776) (hU : U.toNat + 24 ≤ H.get.size) (hUc : OffCode U 24)
    (hra : rdRaw H.get (U.add 8) 4 = ra) (hdst : rdRaw H.get (U.add 12) 4 = dst)
    (hsrc : rdRaw H.get (U.add 16) 4 = src) (hn : rdRaw H.get (U.add 20) 4 = n)
    (hd : dst.toNat + n.toNat ≤ H.get.size) (hdc : OffCode dst n.toNat)
    (hs : src.toNat + n.toNat ≤ H.get.size) (hsc : OffCode src n.toNat)
    (hdU : dst.toNat + n.toNat ≤ U.toNat ∨ U.toNat + 24 ≤ dst.toNat)
    (hsU : src.toNat + n.toNat ≤ U.toNat ∨ U.toNat + 24 ≤ src.toNat)
    (hds : dst.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ dst.toNat)
    (hic : ic.toNat + 5 * n.toNat + 40 < 2 ^ 64) :
    ∃ (H' : CMem) (eax' ecx' edx' f' : UInt32) (ic' : UInt64), ic'.toNat ≤ ic.toNat + 5 * n.toNat + 23 ∧
      Run img (St.m ⟨H.get, eax, ecx, edx, ebx, U.add 8, ebp, esi, edi, 0x1011f0, efl f, ic⟩)
        (St.m ⟨H'.get, eax', ecx', edx', ebx, U.add 12, ebp, esi, edi, ra, efl f', ic'⟩) ∧
      AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 8 ∨ dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H.get H'.get ∧
      ∀ i, i < n.toNat → H'.get.get! (dst.toNat + i) = H.get.get! (src.toNat + i) := by
  unfold OffCode at hUc hdc hsc
  have hU4 : (U.add 4).toNat = U.toNat + 4 := toNat_add_lit (k := 4) (by omega) (by decide)
  have hU8 : (U.add 8).toNat = U.toNat + 8 := toNat_add_lit (k := 8) (by omega) (by decide)
  have hUw : AgreeOn (fun a => U.toNat ≤ a ∧ a < U.toNat + 8 ∨ dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H.get
      (wrBytes (wrBytes H.get (U.add 4) 4 ebx) U 4 esi) :=
    agreeOn_wr4 (agreeOn_wr4 (AgreeOn.refl _ _) (by rw [hU4]; omega) (fun k hk => Or.inl ⟨by omega, by omega⟩))
      (by rw [size_wrBytes4 (by rw [hU4]; omega)]; omega) (fun k hk => Or.inl ⟨by omega, by omega⟩)
  have hS1' : (wrBytes (wrBytes H.get (U.add 4) 4 ebx) U 4 esi).size = H.get.size := hUw.1
  have rsv : ∀ M : ByteArray, M.size = H.get.size →
      AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) (wrBytes (wrBytes H.get (U.add 4) 4 ebx) U 4 esi) M →
      rdRaw M U 4 = esi ∧ rdRaw M (U.add 4) 4 = ebx ∧ rdRaw M (U.add 8) 4 = ra := by
    intro M hM hA
    have hs1 : (wrBytes H.get (U.add 4) 4 ebx).size = H.get.size := size_wrBytes4 (by rw [hU4]; omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [rdRaw4_agree hA (by rw [hS1']; omega) (fun k hk => by omega), rdRaw_wr4_self (by rw [hs1]; omega)]
    · rw [rdRaw4_agree hA (by rw [hS1', hU4]; omega) (fun k hk => by rw [hU4]; omega),
        rdRaw_wr4_other (by rw [hs1]; omega) (by rw [hs1, hU4]; omega) (by rw [hU4]; omega),
        rdRaw_wr4_self (by rw [hU4]; omega)]
    · rw [rdRaw4_agree hA (by rw [hS1', hU8]; omega) (fun k hk => by rw [hU8]; omega),
        rdRaw_wr4_other (by rw [hs1]; omega) (by rw [hs1, hU8]; omega) (by rw [hU8]; omega),
        rdRaw_wr4_other (by rw [hU4]; omega) (by rw [hU8]; omega) (by rw [hU4, hU8]; omega), hra]
  by_cases hn0 : n.toNat = 0
  · obtain ⟨H', f', e, hm⟩ := memcpy_zero H U dst n ra eax ecx edx ebx ebp esi edi f ic hsz hU hUc hra hdst hn hn0
    refine ⟨H', dst, n, edx, f', ic + 9, ?_, exN_run (img := img) 9 _ _ e (by show ic.toNat + 9 < _; omega),
      by rw [hm]; exact hUw, fun i hi => absurd hi (by omega)⟩
    rw [u64_lit 9 (by decide), u64_toNat_add (by omega)]; omega
  · obtain ⟨H1, f1, e1, hm1⟩ := memcpy_head H U dst src n eax ecx edx ebx ebp esi edi f ic hsz hU hUc hdst hsrc hn hn0
    have r1 := exN_run (img := img) 20 _ _ e1 (by show ic.toNat + 20 < _; omega)
    have hS1 : H1.get.size = H.get.size := by rw [hm1]; exact hS1'
    have hic1 : (ic + 20).toNat = ic.toNat + 20 := by rw [u64_lit 20 (by decide), u64_toNat_add (by omega)]
    obtain ⟨H2, f2, ebx2, r2, ha2, hb2⟩ := memcpy_loop H1 U dst src n ebx ebp edi f1 (ic + 20) (by omega)
      (by rw [hS1]; exact hsz) (by rw [hS1]; exact hd) hdc (by rw [hS1]; exact hs) hsc hds
      (by rw [hic1]; omega) (n.toNat - 1) (by omega)
    have hS2 : H2.get.size = H.get.size := by rw [ha2.1, hS1]
    have hi32 : ((n.toNat - 1).toUInt32).toNat = n.toNat - 1 := toUInt32_toNat' (by omega)
    have hp : (dst.add (n.toNat - 1).toUInt32).toNat = dst.toNat + (n.toNat - 1) := toNat_addN (by omega)
    have hq : (src.add (n.toNat - 1).toUInt32).toNat = src.toNat + (n.toNat - 1) := toNat_addN (by omega)
    have hic2 : (ic + 20 + (5 * (n.toNat - 1)).toUInt64).toNat = ic.toNat + 20 + 5 * (n.toNat - 1) := by
      rw [u64_toNat_add (by rw [hic1]; omega), hic1]
    obtain ⟨H3, f3, e3, hm3⟩ := memcpy_exit H2 U dst src n (n.toNat - 1).toUInt32 ebx2 ebp edi f2
      (ic + 20 + (5 * (n.toNat - 1)).toUInt64) (by rw [hS2]; exact hsz) (by rw [hS2]; exact hd) (by omega)
      (by rw [hS2]; exact hs) (by omega) (by rw [hi32]; omega)
    have r3 := exN_run (img := img) 5 _ _ e3 (by show (ic + 20 + (5 * (n.toNat - 1)).toUInt64).toNat + 5 < _; rw [hic2]; omega)
    have hD3 : AgreeOn (fun a => dst.toNat ≤ a ∧ a < dst.toNat + n.toNat) H1.get H3.get := by
      rw [hm3]; exact agreeOn_wr1 ha2 (by rw [hp, hS2]; omega) (by rw [hp]; omega)
    have hS3 : H3.get.size = H.get.size := by rw [hD3.1, hS1]
    rw [hm1] at hD3
    obtain ⟨h1, h2, h3⟩ := rsv H3.get hS3 hD3
    have hic3 : (ic + 20 + (5 * (n.toNat - 1)).toUInt64 + 5).toNat = ic.toNat + 20 + 5 * (n.toNat - 1) + 5 := by
      rw [u64_lit 5 (by decide), u64_toNat_add (by rw [hic2]; omega), hic2]
    obtain ⟨f4, e4⟩ := memcpy_tail H3 U ra esi ebx dst n src _ ebp _ edi f3 _ (by rw [hS3]; exact hsz)
      (by rw [hS3]; exact hU) hUc h1 h2 h3
    have r4 := exN_run (img := img) 3 _ _ e4 (by show (ic + 20 + (5 * (n.toNat - 1)).toUInt64 + 5).toNat + 3 < _; rw [hic3]; omega)
    refine ⟨H3, _, _, _, f4, _, ?_, r1.trans (r2.trans (r3.trans r4)), ?_, fun i hi => ?_⟩
    · rw [u64_lit 3 (by decide), u64_toNat_add (by rw [hic3]; omega), hic3]; omega
    · exact hUw.trans (hD3.mono fun a h => Or.inr h)
    · have hsrc' : ∀ k, k < n.toNat → H1.get.get! (src.toNat + k) = H.get.get! (src.toNat + k) := by
        intro k hk; rw [hm1]; exact hUw.2 _ (by omega) (by omega)
      have hlt : (dst.add (n.toNat - 1).toUInt32).toNat < H2.get.size := by rw [hp, hS2]; omega
      rw [hm3, get!_wrBytes1 hlt]
      by_cases hi' : i = n.toNat - 1
      · subst hi'
        rw [if_pos hp.symm, rd1_byte (by rw [hq, hS2]; omega), hq, ← hsrc' _ (by omega)]
        exact ha2.2 _ (by rw [hS1]; omega) (by omega)
      · rw [if_neg (by rw [hp]; omega), hb2 i (by omega), hsrc' _ (by omega)]

end Solutions.ShaX
