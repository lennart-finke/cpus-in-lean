import Solutions.OpensslPoly1305.InitC
import Solutions.OpensslPoly1305.CtxSpec
/-!
# `Poly1305_Init`: the context after it is `GoodB key []`
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

theorem frame_cons {N : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l) (k : Nat)
    (v j : UInt32) (hj : j.toNat = k) (hk4 : k % 4 = 0) (hkn : k + 4 ≤ n)
    (hv : rdRaw N.get (UInt32.add b j) 4 = v) : Frame N b n ((k, v) :: l) := by
  intro k' v' hl
  rw [lookup_cons] at hl
  split at hl
  · rename_i h; subst h; simp only [Option.some.injEq] at hl; subst hl
    exact ⟨hk4, hkn, by rw [toUInt32_of_toNat hj]; exact hv⟩
  · exact hF k' v' hl

/-- The `MemOK` of a call at its entry. -/
theorem entry_memok {c : Caller} {args : List UInt32} (hc : Calls img c stackBound args) (C : UInt32) (nC mC : Nat)
    (hCm : C.toNat + nC ≤ c.mem.size) (hCi : C.toNat + nC ≤ 0x100000 ∨ 0x100000 + 1536 ≤ C.toNat)
    (hCU : C.toNat + nC ≤ c.sp.toNat - 256 ∨ c.sp.toNat + 4 * (args.length + 1) ≤ C.toNat)
    (l : List (Nat × UInt32)) (hl : Frame (pmem hc) (stk c) (256 + 4 * (args.length + 1)) l) (P : Nat → Prop)
    (hPU : ∀ x, P x → OutF (stk c) (256 + 4 * (args.length + 1)) x) (hPC : ∀ x, P x → OutF C mC x) :
    MemOK (pmem hc) (pmem hc) (stk c) (256 + 4 * (args.length + 1)) l C nC mC [] P := by
  have hf := calls_facts hc
  have hst := stk_toNat hf.2.2.1
  exact ⟨⟨hf.1, by rw [hst]; show _ ≤ c.mem.size; omega, by rw [hst]; omega⟩, ⟨hf.1, hCm, hCi⟩,
    by rw [hst]; omega, hl, Frame.nil _ _ _, Pres.refl _ _, hPU, hPC⟩

theorem enter_eq (c : Caller) (fn : UInt32) (h : 256 ≤ c.sp.toNat) :
    c.enter fn = St.m ⟨c.mem, c.regs.eax, c.regs.ecx, c.regs.edx, c.regs.ebx, UInt32.add (stk c) 256, c.regs.ebp,
      c.regs.esi, c.regs.edi, fn, efl c.regs.flags, icAdd 0 0⟩ := by
  rw [← sp_eq h]; rfl

theorem land_lt28 (x : UInt32) (m : UInt32) (hm : m.toNat < 2 ^ 28) : (UInt32.land x m).toNat < 2 ^ 28 := by
  show (x &&& m).toNat < _
  rw [UInt32.toNat_and]; exact Nat.and_lt_two_pow _ hm

theorem land_mod4 (x : UInt32) : (UInt32.land x 268435452).toNat % 4 = 0 := by
  show (x &&& 268435452).toNat % 4 = 0
  rw [UInt32.toNat_and, show (268435452 : UInt32).toNat = 268435452 from rfl]
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (268435452 &&& 2 ^ 2 - 1 : Nat) = 0 by decide, Nat.and_zero]

set_option maxHeartbeats 1000000 in
theorem init_ok (c : Caller) (ctx keyp : UInt32) (key : List UInt8) (hk : key.length = 32)
    (hpre : InitPre c ctx keyp key) :
    Returns img (c.enter Image.sym_Poly1305_Init) stackBound (InRange ctx ctxSize)
      (fun m => GoodB key [] (bytesAt m ctx 236)) := by
  obtain ⟨hc, hbc, hbk, hap, hkey⟩ := hpre
  have hf := calls_facts hc
  have bc := buffer_facts hc hbc (by decide)
  have bk := buffer_facts hc hbk (by decide)
  have hak := apart_nat hap (by decide) (by decide)
  simp only [ctxSize] at hak bc
  have hst := stk_toNat hf.2.2.1
  simp only [List.length] at hf bc bk
  let P : Nat → Prop := fun x => OutF (stk c) 268 x ∧ OutF ctx 236 x
  have hl : Frame (pmem hc) (stk c) 268 [(256, Image.sym_halt), (260, ctx), (264, keyp)] :=
    frame_cons (frame_cons (frame_cons (Frame.nil (pmem hc) (stk c) 268) 264 keyp 264 rfl rfl (by decide)
      (word_arg hc 1 (by simp) 264 rfl)) 260 ctx 260 rfl rfl (by decide) (word_arg hc 0 (by simp) 260 rfl))
      256 _ 256 rfl rfl (by decide) (word_ret hc)
  have hM0 := entry_memok hc ctx 236 236 bc.1 bc.2.1 (by simp only [List.length]; omega) _ hl P
    (fun x h => h.1) (fun x h => h.2)
  have E : ExtR (pmem hc) P keyp 32 :=
    ⟨bk.1, hf.1, fun x h1 h2 => ⟨by unfold OutF; rw [hst]; omega, by unfold OutF; omega⟩⟩
  obtain ⟨N', lU', lC', v17, v14, g18, v6, v9, v12, R, M, LU, LC, e6, e9, e12, e17⟩ :=
    ini_run 0 (by decide) (pmem hc) (pmem hc) (stk c) ctx _ [] P hM0 c.regs.eax c.regs.ecx c.regs.edx
      c.regs.ebx c.regs.ebp c.regs.esi c.regs.edi c.regs.flags Image.sym_halt keyp
      (rdRaw (pmem hc).get (UInt32.add keyp 16) 4) (rdRaw (pmem hc).get (UInt32.add keyp 20) 4)
      (rdRaw (pmem hc).get (UInt32.add keyp 24) 4) (rdRaw (pmem hc).get (UInt32.add keyp 28) 4)
      (rdRaw (pmem hc).get keyp 4) (rdRaw (pmem hc).get (UInt32.add keyp 4) 4)
      (rdRaw (pmem hc).get (UInt32.add keyp 8) 4) (rdRaw (pmem hc).get (UInt32.add keyp 12) 4)
      ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, trivial⟩ trivial E
      rfl rfl rfl rfl rfl rfl rfl rfl bk.1 (by rw [hst]; omega) (by omega)
  have hsz : N'.get.size = c.mem.size := M.size
  have R' : Run img (c.enter Image.sym_Poly1305_Init) (St.m ⟨N'.get, v17, v14, keyp, c.regs.ebx,
      UInt32.add (stk c) 260, c.regs.ebp, c.regs.esi, c.regs.edi, Image.sym_halt, efl g18, icAdd 0 68⟩) := by
    rw [enter_eq c _ hf.2.2.1]; exact R
  refine returns_of hc _ M ?_ ?_ R' ?_
  · intro a hW ha
    refine ⟨by unfold OutF; rw [hst]; simp only [List.length] at ha; omega, ?_⟩
    unfold OutF
    simp only [InRange, ctxSize, UInt32.le_iff_toNat_le] at hW
    omega
  · refine arg_bytes hc hsz (fun i hi => ?_)
    simp only [List.length] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact (M.rdU (k := 256) LU.1 _ rfl).trans (word_ret hc).symm
    · exact (M.rdU (k := 260) LU.2.1 _ rfl).trans (word_arg hc 0 (by simp) _ rfl).symm
    · exact (M.rdU (k := 264) LU.2.2.1 _ rfl).trans (word_arg hc 1 (by simp) _ rfl).symm
  · -- the context bytes
    have hw : ∀ (k : Nat) (j : UInt32), j.toNat = k → k + 4 ≤ 236 →
        wd (memBytes N'.get ctx 236) k = (rdRaw N'.get (UInt32.add ctx j) 4).toNat :=
      fun k j hj hk4 => wd_memBytes (by rw [hsz]; exact bc.1) (by rw [hsz]; exact hf.1) k hk4 j hj
    have hkw : ∀ (k : Nat) (j : UInt32), j.toNat = k → k + 4 ≤ 32 →
        wd key k = (rdRaw c.mem (UInt32.add keyp j) 4).toNat := by
      intro k j hj hk4
      rw [← hkey]; exact wd_memBytes bk.1 hf.1 k hk4 j hj
    have h0 : (rdRaw c.mem keyp 4).toNat = wd key 0 := by
      rw [hkw 0 0 rfl (by decide), uadd_zero]
    have z0 := hw 0 0 rfl (by decide)
    rw [uadd_zero, M.rdC0 LC.1] at z0
    have z4 := hw 4 4 rfl (by decide); rw [M.rdC (k := 4) LC.2.1 _ rfl] at z4
    have z8 := hw 8 8 rfl (by decide); rw [M.rdC (k := 8) LC.2.2.1 _ rfl] at z8
    have z12 := hw 12 12 rfl (by decide); rw [M.rdC (k := 12) LC.2.2.2.1 _ rfl] at z12
    have z16 := hw 16 16 rfl (by decide); rw [M.rdC (k := 16) LC.2.2.2.2.1 _ rfl] at z16
    have w20 := hw 20 20 rfl (by decide); rw [M.rdC (k := 20) LC.2.2.2.2.2.1 _ rfl, e6] at w20
    have w24 := hw 24 24 rfl (by decide); rw [M.rdC (k := 24) LC.2.2.2.2.2.2.1 _ rfl, e9] at w24
    have w28 := hw 28 28 rfl (by decide); rw [M.rdC (k := 28) LC.2.2.2.2.2.2.2.1 _ rfl, e12] at w28
    have w32 := hw 32 32 rfl (by decide); rw [M.rdC (k := 32) LC.2.2.2.2.2.2.2.2.1 _ rfl, e17] at w32
    have s0 := hw 192 192 rfl (by decide); rw [M.rdC (k := 192) LC.2.2.2.2.2.2.2.2.2.1 _ rfl] at s0
    have s4 := hw 196 196 rfl (by decide); rw [M.rdC (k := 196) LC.2.2.2.2.2.2.2.2.2.2.1 _ rfl] at s4
    have s8 := hw 200 200 rfl (by decide); rw [M.rdC (k := 200) LC.2.2.2.2.2.2.2.2.2.2.2.1 _ rfl] at s8
    have s12 := hw 204 204 rfl (by decide); rw [M.rdC (k := 204) LC.2.2.2.2.2.2.2.2.2.2.2.2.1 _ rfl] at s12
    have n0 := hw 224 224 rfl (by decide); rw [M.rdC (k := 224) LC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ rfl] at n0
    show GoodB key [] (memBytes N'.get ctx 236)
    refine ⟨by simp [memBytes], by rw [z16]; decide, ?_, ?_, ?_, ?_, by rw [n0]; rfl, fun j hj => absurd hj (by simp)⟩
    · unfold wd4; rw [z0, z4, z8, z12, z16]; rfl
    · unfold wd4; rw [r_eq key hk, w20, w24, w28, w32]
      simp only [UInt32.land, UInt32.toNat_and]
      rw [← h0, hkw 4 4 rfl (by decide), hkw 8 8 rfl (by decide), hkw 12 12 rfl (by decide)]
      rfl
    · rw [w20, w24, w28, w32]
      exact ⟨land_lt28 _ _ (by decide), land_lt28 _ _ (by decide), land_lt28 _ _ (by decide),
        land_lt28 _ _ (by decide), land_mod4 _, land_mod4 _, land_mod4 _⟩
    · unfold wd4; rw [s_eq key hk, s0, s4, s8, s12]
      unfold wd4
      rw [hkw 16 16 rfl (by decide), hkw 20 20 rfl (by decide), hkw 24 24 rfl (by decide),
        hkw 28 28 rfl (by decide)]
      rfl

end Solutions.OpensslPoly1305
