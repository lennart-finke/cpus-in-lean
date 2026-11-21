import Solutions.OpensslSha256.X.Glue
import Solutions.OpensslSha256.Facts
/-!
# Address facts of a call, and reading words back

`SpOk`/`BufOk`: the facts of `Ssl.Calls`/`Ssl.Buffer` the runs need, in `toNat` form. `rdw_eq`,
`rdw_ne`: a word read after a word store, the addresses compared through `toNat` (for `simp` with an
`omega` discharger, `rdw`).
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem rdw_eq {M : ByteArray} {a b v : UInt32} (hab : a.toNat = b.toNat) (ha : a.toNat + 4 ≤ M.size) :
    rdRaw (wrBytes M a 4 v) b 4 = v := by
  rw [← UInt32.toNat_inj.1 hab]; exact rdRaw_wr4_self ha

theorem rdw_ne {M : ByteArray} {a b v : UInt32} (ha : a.toNat + 4 ≤ M.size) (hb : b.toNat + 4 ≤ M.size)
    (hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) : rdRaw (wrBytes M a 4 v) b 4 = rdRaw M b 4 :=
  rdRaw_wr4_other ha hb hd

/-- Word reads through word stores, by `simp` with `omega` on the `toNat` facts in context. -/
macro "rdw" : tactic =>
  `(tactic| simp (disch := first | omega | (simp only [Solutions.Exec.size_wrBytes] at *; omega)) only [rdw_eq, rdw_ne])

/-- The stack facts of a call with `k` argument words. -/
structure SpOk (size : Nat) (sp : UInt32) (k : Nat) : Prop where
  lo : 512 ≤ sp.toNat
  hi : sp.toNat + 4 * (k + 1) ≤ size
  img : sp.toNat + 4 * (k + 1) ≤ 1048576 ∨ 1048576 + 4944 + 512 ≤ sp.toNat
  sz : size ≤ 4273995776

theorem spOk_of {c : Caller} {args : List UInt32} (h : Calls img c stackBound args) :
    SpOk c.mem.size c.sp args.length := by
  obtain ⟨h1, -, -, -, h5, h6, h7⟩ := h
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 512 := by
    unfold Caller.stackLo stackBound at *
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
  unfold Apart stackSize at h7
  rw [hlo] at h7
  have hb : img.base.toNat = 1048576 := rfl
  have hs : img.bytes.size = 4944 := Solutions.OpensslSha256.image_size
  rw [hb, hs] at h7
  unfold stackBound at h5
  refine ⟨h5, h6, ?_, h1⟩
  unfold stackBound at h7
  omega

/-- A buffer `[b, b + n)` of a call with `k` argument words, `n ≠ 0`. -/
structure BufOk (size : Nat) (sp : UInt32) (k : Nat) (b : UInt32) (n : Nat) : Prop where
  fit : b.toNat + n ≤ size
  img : b.toNat + n ≤ 1048576 ∨ 1048576 + 4944 ≤ b.toNat
  stk : b.toNat + n ≤ sp.toNat - 512 ∨ sp.toNat + 4 * (k + 1) ≤ b.toNat
  max : n ≤ 0x7FFFFFFF

theorem bufOk_of {c : Caller} {k : Nat} {b : UInt32} {n : Nat} (h : Buffer img c stackBound k b n) (hn : n ≠ 0)
    (hsp : 512 ≤ c.sp.toNat) : BufOk c.mem.size c.sp k b n := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlo : (c.stackLo stackBound).toNat = c.sp.toNat - 512 := by
    unfold Caller.stackLo stackBound at *
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
  unfold Apart stackSize at h4
  unfold Apart at h3
  unfold Fits at h1
  rw [hlo] at h4
  have hb : img.base.toNat = 1048576 := rfl
  have hs : img.bytes.size = 4944 := Solutions.OpensslSha256.image_size
  rw [hb, hs] at h3
  unfold stackBound at h4
  refine ⟨by omega, by omega, by omega, h2⟩

/-- `x.add y` in `toNat`, without overflow (`y` a numeral `k`). -/
theorem tN {x y : UInt32} (k : Nat) (hy : y.toNat = k) (h : x.toNat + k < 2 ^ 32) :
    (x.add y).toNat = x.toNat + k := by
  show (x + y).toNat = _
  rw [UInt32.toNat_add, hy]; exact Nat.mod_eq_of_lt h

/-- `x - y` in `toNat` (`y` a numeral `k`). -/
theorem tS {x y : UInt32} (k : Nat) (hy : y.toNat = k) (h : k ≤ x.toNat) : (x - y).toNat = x.toNat - k := by
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hy]; exact h), hy]

theorem add_sub_k {x y : UInt32} (k : Nat) (hy : y.toNat = k) (h : k ≤ x.toNat) : (x - y).add y = x := by
  apply UInt32.toNat_inj.1
  rw [tN k hy (by rw [tS k hy h]; have := x.toNat_lt; omega), tS k hy h]; omega

end Solutions.ShaX
