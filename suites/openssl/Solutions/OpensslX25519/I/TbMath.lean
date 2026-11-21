import Solutions.OpensslX25519.I.ToBytesMath
import Solutions.OpensslX25519.Pair
import Solutions.Exec.Shift
import Solutions.Exec.Branch
/-!
# The arithmetic of `fe_tobytes`

The words of the run (`I/TbRun*`) as numbers: the carry chain (`sarl`, `addl`) as signed integers
(`tb_chain`: the residues of the ten chain words, read in radix 2^25.5, are `feValI h mod p` for limbs within the
`fe_mul` output bounds, by `qChain_spec`), and the byte operations (`shrl`, `shll`, `andl`, `orl`, `leal`) as
natural numbers (`tn_*`). The output byte `k` is `tbB V k`, byte `k` of `V` little-endian. Prover Q.
-/
namespace Solutions.OpensslX25519.I
open X86 Solutions.Exec Solutions.Exec.Mul Solutions.Exec.Shift Solutions.OpensslX25519 Ssl.OpensslX25519

/-! ## Words as natural numbers -/

theorem shlR_toNat (a : UInt32) (k : Nat) (hk : 0 < k) (hk' : k < 32) :
    (shlR a k.toUInt32).toNat = a.toNat * 2 ^ k % 2 ^ 32 := by
  have e : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have e1 : k.toUInt32 &&& 0x1F = k.toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_and, e, show (0x1F : UInt32).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hne : k.toUInt32 ≠ 0 := fun h => by
    have := congrArg UInt32.toNat h; rw [e] at this; simp at this; omega
  have hc : (k.toUInt32 &&& 0x1F == 0) = false := by rw [e1]; simpa using hne
  unfold shlR shiftOp
  simp only [hc]
  show ((((a.toUInt64 <<< (k.toUInt32 &&& 0x1F).toUInt64).toUInt32 &&& Sz.mask 4))).toNat = _
  rw [e1, Branch.mask4, UInt64.toNat_toUInt32]
  have u : (ShiftLeft.shiftLeft a.toUInt64 k.toUInt32.toUInt64).toNat =
      a.toUInt64.toNat * 2 ^ (k.toUInt32.toUInt64.toNat % 64) % 2 ^ 64 := by
    exact u64_shl _ _
  rw [u, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, e, Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem tn_add {v a b : UInt32} (e : v = UInt32.add a b) : v.toNat = (a.toNat + b.toNat) % 2 ^ 32 := by
  rw [e, toNat_uadd]

theorem tn_lea {v a b k : UInt32} (n : Nat) (e : v = UInt32.add a (UInt32.shiftLeft b k)) (hk : k.toNat % 32 = n) :
    v.toNat = (a.toNat + b.toNat * 2 ^ n % 2 ^ 32) % 2 ^ 32 := by
  rw [e, toNat_uadd, u32_shl, hk, nat_shl]

theorem tn_shr {v a k : UInt32} (n : Nat) (e : v = shrR a k) (hk : k = n.toUInt32) (h0 : 0 < n) (h1 : n < 32) :
    v.toNat = a.toNat / 2 ^ n := by
  rw [e, hk, shrR_toNat a n h0 h1]

theorem tn_shl {v a k : UInt32} (n : Nat) (e : v = shlR a k) (hk : k = n.toUInt32) (h0 : 0 < n) (h1 : n < 32) :
    v.toNat = a.toNat * 2 ^ n % 2 ^ 32 := by
  rw [e, hk, shlR_toNat a n h0 h1]

theorem tn_and {v a m : UInt32} (n : Nat) (e : v = (logicF 4 (UInt32.land a m)).1) (hm : m.toNat = 2 ^ n - 1) :
    v.toNat = a.toNat % 2 ^ n := by
  rw [e, show (logicF 4 (UInt32.land a m)).1 = UInt32.land a m from rfl, show UInt32.land a m = a &&& m from rfl,
    UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem tn_or {v a b : UInt32} (n : Nat) (e : v = (logicF 4 (UInt32.lor a b)).1) (ha : a.toNat % 2 ^ n = 0)
    (hb : b.toNat < 2 ^ n) : v.toNat = a.toNat + b.toNat := by
  rw [e, show (logicF 4 (UInt32.lor a b)).1 = UInt32.lor a b from rfl, show UInt32.lor a b = a ||| b from rfl,
    UInt32.toNat_or]
  have h1 : a.toNat = a.toNat / 2 ^ n * 2 ^ n := by
    have := Nat.div_add_mod a.toNat (2 ^ n); rw [ha, Nat.add_zero, Nat.mul_comm] at this; exact this.symm
  rw [Nat.or_comm, h1, or_high _ _ _ hb]
  omega

theorem tn_land {a m : UInt32} (n : Nat) (hm : m.toNat = 2 ^ n - 1) : (UInt32.land a m).toNat = a.toNat % 2 ^ n := by
  rw [show UInt32.land a m = a &&& m from rfl, UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem tn_shr8 (a : UInt32) : (UInt32.shiftRight a 8).toNat = a.toNat / 2 ^ 8 := by
  have := UInt32.toNat_shiftRight a 8
  rw [Nat.shiftRight_eq_div_pow] at this
  exact this

/-! ## The output bytes -/

/-- The value the ten chain words represent with their carries dropped. -/
def tbV (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : UInt32) : Nat :=
  t0.toNat % 2 ^ 26 + 2 ^ 26 * (t1.toNat % 2 ^ 25) + 2 ^ 51 * (t2.toNat % 2 ^ 26) + 2 ^ 77 * (t3.toNat % 2 ^ 25) +
    2 ^ 102 * (t4.toNat % 2 ^ 26) + 2 ^ 128 * (t5.toNat % 2 ^ 25) + 2 ^ 153 * (t6.toNat % 2 ^ 26) +
    2 ^ 179 * (t7.toNat % 2 ^ 25) + 2 ^ 204 * (t8.toNat % 2 ^ 26) + 2 ^ 230 * (t9.toNat % 2 ^ 25)

/-- Byte `k` of `V`, as `leBytes` writes it. -/
def tbB (V k : Nat) : UInt8 := ((V >>> (8 * k)) % 256).toUInt8

theorem u8_tbB (s : UInt32) (V k : Nat) (h : s.toNat % 256 = V / 2 ^ (8 * k) % 256) : s.toUInt8 = tbB V k := by
  apply UInt8.toNat_inj.1
  have e : V >>> (8 * k) = V / 2 ^ (8 * k) := Nat.shiftRight_eq_div_pow _ _
  rw [UInt32.toNat_toUInt8, tbB, Nat.toUInt8, UInt8.toNat_ofNat', e]
  omega

/-! ## The carry chain as signed integers -/

theorem M32_uadd {a b : UInt32} {A B : Int} (ha : M32 a A) (hb : M32 b B) : M32 (UInt32.add a b) (A + B) := by
  unfold M32 at *; rw [toNat_uadd]; omega

theorem M32_shl3 {a : UInt32} {A : Int} (ha : M32 a A) : M32 (UInt32.shiftLeft a 3) (A * 8) := by
  unfold M32 at *; rw [u32_shl, nat_shl]
  show ((a.toNat * 2 ^ 3 % 2 ^ 32 : Nat) : Int) = _
  omega

theorem M32_shl1 {a : UInt32} {A : Int} (ha : M32 a A) : M32 (UInt32.shiftLeft a 1) (A * 2) := by
  unfold M32 at *; rw [u32_shl, nat_shl]
  show ((a.toNat * 2 ^ 1 % 2 ^ 32 : Nat) : Int) = _
  omega

theorem sv_sar26 (c : UInt32) : sv (sarR c 26) = sv c / 2 ^ 26 := by
  have hc := c.toNat_lt
  apply sv_of_M32 _ (by rw [sv_eq]; split <;> omega)
  unfold M32; rw [sar_toNat26, sv_eq]
  split <;> split <;> omega

theorem sv_sar25 (c : UInt32) : sv (sarR c 25) = sv c / 2 ^ 25 := by
  have hc := c.toNat_lt
  apply sv_of_M32 _ (by rw [sv_eq]; split <;> omega)
  unfold M32; rw [sar_toNat25, sv_eq]
  split <;> split <;> omega

theorem sv_add_of {v a b : UInt32} (e : v = UInt32.add a b) (hr : -2 ^ 31 ≤ sv a + sv b ∧ sv a + sv b < 2 ^ 31) :
    sv v = sv a + sv b := by
  rw [e]; exact sv_of_M32 (M32_uadd (M32_sv a) (M32_sv b)) hr

/-- The residues of the chain words, as `fe_tobytes` stores them, are the value modulo `p`. -/
theorem tb_val_int (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 Q T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 : Int)
    (hb : InM ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩)
    (hq : Q * (2 ^ 255 - 19) ≤ L10.val ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ ∧
      L10.val ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ < (Q + 1) * (2 ^ 255 - 19))
    (h0 : T0 = 19 * Q + X0) (h1 : T1 = T0 / 2 ^ 26 + X1) (h2 : T2 = T1 / 2 ^ 25 + X2) (h3 : T3 = T2 / 2 ^ 26 + X3)
    (h4 : T4 = T3 / 2 ^ 25 + X4) (h5 : T5 = T4 / 2 ^ 26 + X5) (h6 : T6 = T5 / 2 ^ 25 + X6) (h7 : T7 = T6 / 2 ^ 26 + X7)
    (h8 : T8 = T7 / 2 ^ 25 + X8) (h9 : T9 = T8 / 2 ^ 26 + X9) :
    T0 % 2 ^ 26 + 2 ^ 26 * (T1 % 2 ^ 25) + 2 ^ 51 * (T2 % 2 ^ 26) + 2 ^ 77 * (T3 % 2 ^ 25) + 2 ^ 102 * (T4 % 2 ^ 26)
      + 2 ^ 128 * (T5 % 2 ^ 25) + 2 ^ 153 * (T6 % 2 ^ 26) + 2 ^ 179 * (T7 % 2 ^ 25) + 2 ^ 204 * (T8 % 2 ^ 26)
      + 2 ^ 230 * (T9 % 2 ^ 25) = L10.val ⟨X0, X1, X2, X3, X4, X5, X6, X7, X8, X9⟩ % pI := by
  dsimp only [InM] at hb
  obtain ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ := hb
  simp only [L10.val] at hq ⊢
  rw [pI_eq]
  omega

set_option maxRecDepth 20000 in
theorem tb_chain (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
    v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v34 v35 v55 v56 v57 v58 v59 v60 v61 v62 v65 v66 : UInt32)
    (e1 : v1 = UInt32.add x9 (UInt32.shiftLeft x9 3))
    (e2 : v2 = UInt32.add (UInt32.add x9 (UInt32.shiftLeft v1 1)) 16777216)
    (e3 : v3 = sarR v2 25) (e4 : v4 = UInt32.add v3 x0) (e5 : v5 = sarR v4 26) (e6 : v6 = UInt32.add v5 x1)
    (e7 : v7 = sarR v6 25) (e8 : v8 = UInt32.add v7 x2) (e9 : v9 = sarR v8 26) (e10 : v10 = UInt32.add v9 x3)
    (e11 : v11 = sarR v10 25) (e12 : v12 = UInt32.add v11 x4) (e13 : v13 = sarR v12 26)
    (e14 : v14 = UInt32.add v13 x5) (e15 : v15 = sarR v14 25) (e16 : v16 = UInt32.add v15 x6)
    (e17 : v17 = sarR v16 26) (e18 : v18 = UInt32.add v17 x7) (e19 : v19 = sarR v18 25)
    (e20 : v20 = UInt32.add v19 x8) (e21 : v21 = sarR v20 26) (e22 : v22 = UInt32.add v21 x9)
    (e23 : v23 = sarR v22 25) (e24 : v24 = UInt32.add v23 (UInt32.shiftLeft v23 3))
    (e25 : v25 = UInt32.add v23 (UInt32.shiftLeft v24 1)) (e26 : v26 = UInt32.add v25 x0)
    (e27 : v27 = sarR v26 26) (e28 : v28 = UInt32.add v27 x1) (e29 : v29 = sarR v28 25)
    (e30 : v30 = UInt32.add v29 x2) (e31 : v31 = sarR v30 26) (e32 : v32 = UInt32.add v31 x3)
    (e34 : v34 = sarR v32 25) (e35 : v35 = UInt32.add v34 x4) (e55 : v55 = sarR v35 26)
    (e56 : v56 = UInt32.add v55 x5) (e57 : v57 = sarR v56 25) (e58 : v58 = UInt32.add v57 x6)
    (e59 : v59 = sarR v58 26) (e60 : v60 = UInt32.add v59 x7) (e61 : v61 = sarR v60 25)
    (e62 : v62 = UInt32.add v61 x8) (e65 : v65 = sarR v62 26) (e66 : v66 = UInt32.add v65 x9)
    (hX : InM ⟨sv x0, sv x1, sv x2, sv x3, sv x4, sv x5, sv x6, sv x7, sv x8, sv x9⟩) :
    (tbV v26 v28 v30 v32 v35 v56 v58 v60 v62 v66 : Int) =
      L10.val ⟨sv x0, sv x1, sv x2, sv x3, sv x4, sv x5, sv x6, sv x7, sv x8, sv x9⟩ % pI := by
  have hq := qChain_spec _ hX
  dsimp only [InM] at hX
  obtain ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ := hX
  have m1 : M32 v1 (sv x9 + sv x9 * 8) := by rw [e1]; exact M32_uadd (M32_sv x9) (M32_shl3 (M32_sv x9))
  have s2 : sv v2 = sv x9 + (sv x9 + sv x9 * 8) * 2 + 16777216 := by
    rw [e2]
    exact sv_of_M32 (M32_uadd (M32_uadd (M32_sv x9) (M32_shl1 m1)) (by unfold M32; rfl)) (by omega)
  have s3 : sv v3 = sv v2 / 2 ^ 25 := by rw [e3]; exact sv_sar25 v2
  have s4 : sv v4 = sv v3 + sv x0 := sv_add_of e4 (by omega)
  have s5 : sv v5 = sv v4 / 2 ^ 26 := by rw [e5]; exact sv_sar26 v4
  have s6 : sv v6 = sv v5 + sv x1 := sv_add_of e6 (by omega)
  have s7 : sv v7 = sv v6 / 2 ^ 25 := by rw [e7]; exact sv_sar25 v6
  have s8 : sv v8 = sv v7 + sv x2 := sv_add_of e8 (by omega)
  have s9 : sv v9 = sv v8 / 2 ^ 26 := by rw [e9]; exact sv_sar26 v8
  have s10 : sv v10 = sv v9 + sv x3 := sv_add_of e10 (by omega)
  have s11 : sv v11 = sv v10 / 2 ^ 25 := by rw [e11]; exact sv_sar25 v10
  have s12 : sv v12 = sv v11 + sv x4 := sv_add_of e12 (by omega)
  have s13 : sv v13 = sv v12 / 2 ^ 26 := by rw [e13]; exact sv_sar26 v12
  have s14 : sv v14 = sv v13 + sv x5 := sv_add_of e14 (by omega)
  have s15 : sv v15 = sv v14 / 2 ^ 25 := by rw [e15]; exact sv_sar25 v14
  have s16 : sv v16 = sv v15 + sv x6 := sv_add_of e16 (by omega)
  have s17 : sv v17 = sv v16 / 2 ^ 26 := by rw [e17]; exact sv_sar26 v16
  have s18 : sv v18 = sv v17 + sv x7 := sv_add_of e18 (by omega)
  have s19 : sv v19 = sv v18 / 2 ^ 25 := by rw [e19]; exact sv_sar25 v18
  have s20 : sv v20 = sv v19 + sv x8 := sv_add_of e20 (by omega)
  have s21 : sv v21 = sv v20 / 2 ^ 26 := by rw [e21]; exact sv_sar26 v20
  have s22 : sv v22 = sv v21 + sv x9 := sv_add_of e22 (by omega)
  have s23 : sv v23 = sv v22 / 2 ^ 25 := by rw [e23]; exact sv_sar25 v22
  have hQ : sv v23 = qChain ⟨sv x0, sv x1, sv x2, sv x3, sv x4, sv x5, sv x6, sv x7, sv x8, sv x9⟩ := by
    simp only [qChain]; omega
  rw [← hQ] at hq
  have Qb : -4 ≤ sv v23 ∧ sv v23 ≤ 4 := by omega
  clear s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 hQ m1
  have m24 : M32 v24 (sv v23 + sv v23 * 8) := by rw [e24]; exact M32_uadd (M32_sv v23) (M32_shl3 (M32_sv v23))
  have s25 : sv v25 = sv v23 + (sv v23 + sv v23 * 8) * 2 := by
    rw [e25]; exact sv_of_M32 (M32_uadd (M32_sv v23) (M32_shl1 m24)) (by omega)
  have s26 : sv v26 = sv v25 + sv x0 := sv_add_of e26 (by omega)
  have s27 : sv v27 = sv v26 / 2 ^ 26 := by rw [e27]; exact sv_sar26 v26
  have s28 : sv v28 = sv v27 + sv x1 := sv_add_of e28 (by omega)
  have s29 : sv v29 = sv v28 / 2 ^ 25 := by rw [e29]; exact sv_sar25 v28
  have s30 : sv v30 = sv v29 + sv x2 := sv_add_of e30 (by omega)
  have s31 : sv v31 = sv v30 / 2 ^ 26 := by rw [e31]; exact sv_sar26 v30
  have s32 : sv v32 = sv v31 + sv x3 := sv_add_of e32 (by omega)
  have s34 : sv v34 = sv v32 / 2 ^ 25 := by rw [e34]; exact sv_sar25 v32
  have s35 : sv v35 = sv v34 + sv x4 := sv_add_of e35 (by omega)
  have s55 : sv v55 = sv v35 / 2 ^ 26 := by rw [e55]; exact sv_sar26 v35
  have s56 : sv v56 = sv v55 + sv x5 := sv_add_of e56 (by omega)
  have s57 : sv v57 = sv v56 / 2 ^ 25 := by rw [e57]; exact sv_sar25 v56
  have s58 : sv v58 = sv v57 + sv x6 := sv_add_of e58 (by omega)
  have s59 : sv v59 = sv v58 / 2 ^ 26 := by rw [e59]; exact sv_sar26 v58
  have s60 : sv v60 = sv v59 + sv x7 := sv_add_of e60 (by omega)
  have s61 : sv v61 = sv v60 / 2 ^ 25 := by rw [e61]; exact sv_sar25 v60
  have s62 : sv v62 = sv v61 + sv x8 := sv_add_of e62 (by omega)
  have s65 : sv v65 = sv v62 / 2 ^ 26 := by rw [e65]; exact sv_sar26 v62
  have s66 : sv v66 = sv v65 + sv x9 := sv_add_of e66 (by omega)
  have key := tb_val_int (sv x0) (sv x1) (sv x2) (sv x3) (sv x4) (sv x5) (sv x6) (sv x7) (sv x8) (sv x9) (sv v23)
    (sv v26) (sv v28) (sv v30) (sv v32) (sv v35) (sv v56) (sv v58) (sv v60) (sv v62) (sv v66)
    ⟨b0, b0', b1, b1', b2, b2', b3, b3', b4, b4', b5, b5', b6, b6', b7, b7', b8, b8', b9, b9'⟩ hq
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← key]
  have t0 := M32_sv v26; have t1 := M32_sv v28; have t2 := M32_sv v30; have t3 := M32_sv v32
  have t4 := M32_sv v35; have t5 := M32_sv v56; have t6 := M32_sv v58; have t7 := M32_sv v60
  have t8 := M32_sv v62; have t9 := M32_sv v66
  unfold M32 at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9
  unfold tbV
  clear key hq s25 s26 s27 s28 s29 s30 s31 s32 s34 s35 s55 s56 s57 s58 s59 s60 s61 s62 s65 s66 m24
  omega

end Solutions.OpensslX25519.I
