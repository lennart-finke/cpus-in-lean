import Solutions.OpensslSha256.X.Frame
/-!
# Address side conditions, cheaply

`omega` gets expensive (time and memory, measured: ~80 MB retained per call) when the context holds many
`toNat` facts of the form `(x.add k).toNat = x.toNat + k`. So no such facts are kept in context: the
side goals are normalized first (`(x.add y).toNat = (x.toNat + y.toNat) % 2^32`, literal `toNat`s
evaluated, sizes of store chains reduced to the memory below them) and then `omega` runs on the base
facts only (`ao`). No `<;>` in it: under `all_goals` a failure is logged as an error and the goal is
closed anyway, which inside a `simp` discharger lets a wrong rewrite through. `rdv`: word reads through word stores; `agw`: store chains keep memory outside the
stored words.
-/
namespace Solutions.ShaX
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Ssl.OpensslSha256

theorem uadd_toNat (x y : UInt32) : (x.add y).toNat = (x.toNat + y.toNat) % 4294967296 := UInt32.toNat_add x y

/-- An address side goal: normalized, then `omega`. -/
macro "ao" : tactic =>
  `(tactic| first
    | (simp only [Solutions.Exec.size_wrBytes, uadd_toNat, UInt32.reduceToNat]; done)
    | (simp only [Solutions.Exec.size_wrBytes, uadd_toNat, UInt32.reduceToNat]; omega)
    | omega)

/-- Word reads through word stores. -/
macro "rdv" : tactic => `(tactic| simp (disch := ao) only [rdw_ne, rdw_eq])

/-- Store chains keep memory outside the stored words. -/
macro "agw" : tactic =>
  `(tactic| repeat (first | (with_reducible exact AgreeOn.refl _ _) |
      (refine agreeOn_wr4 ?_ (by ao) (fun k hk => by ao))))

theorem u64_tN {ic : UInt64} (k : Nat) (hk : k < 2 ^ 64) (h : ic.toNat + k < 2 ^ 64) :
    (ic + (OfNat.ofNat k : UInt64)).toNat = ic.toNat + k := by
  rw [UInt64.toNat_add]
  have : (OfNat.ofNat k : UInt64).toNat = k := by
    show (UInt64.ofNat k).toNat = k
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  rw [this]; exact Nat.mod_eq_of_lt h

theorem rd_zero {M : ByteArray} {a : UInt32} (h : a.toNat + 4 ≤ M.size)
    (hz : ∀ k, k < 4 → M.get! (a.toNat + k) = 0) : rdRaw M a 4 = 0 := by
  unfold rdRaw
  rw [rdBytes4_eq h]
  have h0 := hz 0 (by decide); have h1 := hz 1 (by decide); have h2 := hz 2 (by decide); have h3 := hz 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]; rfl

/-- A word of zero bytes, at offset `j` of a zeroed region. -/
theorem rd_zero_at {M : ByteArray} {b : UInt32} {n : Nat} (j : Nat) (hj : j + 4 ≤ n) (hb : b.toNat + n ≤ M.size)
    (hM : M.size ≤ 4273995776) (hz : ∀ i, i < n → M.get! (b.toNat + i) = 0) :
    rdRaw M (b.add (OfNat.ofNat j)) 4 = 0 := by
  have cj : (b.add (OfNat.ofNat j)).toNat = b.toNat + j := by
    rw [uadd_toNat]; show (b.toNat + j % 4294967296) % 4294967296 = _; omega
  exact rd_zero (by omega) (fun k hk => by rw [cj, Nat.add_assoc]; exact hz (j + k) (by omega))

/-! ## The frame of a call

The stack pointer at the entry is written `U.add K` with `U = c.sp - K` below everything the call
writes on the stack. -/

theorem sp_frame (s K d : UInt32) : (s - K).add (K + d) = s + d := by
  show s - K + (K + d) = s + d
  rw [← UInt32.add_assoc, UInt32.sub_add_cancel]

theorem sp_frame0 (s K : UInt32) : (s - K).add K = s := by
  show s - K + K = s
  exact UInt32.sub_add_cancel s K

theorem enter_frame (c : Caller) (H : CMem) (hH : H.get = c.mem) (K fn : UInt32) :
    c.enter fn = St.m ⟨H.get, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, (c.sp - K).add K, c.regs.ebp,
      c.regs.esi, c.regs.edi, fn, efl c.regs.flags, 0⟩ := by
  rw [sp_frame0, hH]; rfl

theorem frame_ret {c : Caller} {args : List UInt32} (hC : Calls img c stackBound args) (H : CMem)
    (hH : H.get = c.mem) (K : UInt32) : rdRaw H.get ((c.sp - K).add K) 4 = Image.sym_halt := by
  rw [sp_frame0, hH]; exact calls_ret hC

theorem frame_tN {c : Caller} (K : UInt32) (k : Nat) (hK : K.toNat = k) (h : k ≤ c.sp.toNat) :
    (c.sp - K).toNat = c.sp.toNat - k := tS k hK h

/-- The region facts of `InRange` against the call's stack bytes. -/
theorem stack_lo (c : Caller) (h : 512 ≤ c.sp.toNat) : (c.sp - (512 : Nat).toUInt32).toNat = c.sp.toNat - 512 :=
  tS (y := (512 : Nat).toUInt32) 512 rfl h

end Solutions.ShaX
