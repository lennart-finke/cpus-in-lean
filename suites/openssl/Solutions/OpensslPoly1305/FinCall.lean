import Solutions.OpensslPoly1305.FinMath
import Solutions.OpensslPoly1305.Memset
/-!
# Calls from `Poly1305_Final`: `poly1305_blocks` and `memset` in the caller's frame

As `UpdCall` for the `Final` frame (`[U, U + 268)`, entry stack pointer `U + 256`): `fin_blk` (callee
frame `U + 132`), `fin_ms` (`memset` through `OPENSSL_cleanse`, callee frame `U + 216`), and
`MemOK.switch` (the current memory as the reference of a run with another data region).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

variable {G N : PMem} {U C : UInt32} {nU nC mC : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

/-- What `poly1305_blocks` called from the `Final` frame keeps: outside its frame and `h`. -/
def FQ (U C : UInt32) (x : Nat) : Prop := OutF (UInt32.add U 132) 116 x ∧ OutF C 20 x

/-- The current memory as the reference memory of a run with another data region. -/
theorem MemOK.switch (h : MemOK G N U nU lU C nC mC lC P) (D : UInt32) (nD mD : Nat) (lD : List (Nat × UInt32))
    (hD : FB N.get.size D nD) (hDU : D.toNat + nD ≤ U.toNat ∨ U.toNat + nU ≤ D.toNat) (hlD : Frame N D nD lD)
    (Q : Nat → Prop) (hQU : ∀ x, Q x → OutF U nU x) (hQD : ∀ x, Q x → OutF D mD x) :
    MemOK N N U nU lU D nD mD lD Q :=
  ⟨h.fU, hD, hDU, h.wU, hlD, Pres.refl _ _, hQU, hQD⟩

/-- A run from `G'` continues a run from `G` (the preserved addresses compose). -/
theorem MemOK.rebase {G' : PMem} (h : MemOK G' N U nU lU C nC mC lC P) (hP : Pres G G' P) :
    MemOK G N U nU lU C nC mC lC P :=
  ⟨h.fU, h.fC, h.dUC, h.wU, h.wC, hP.trans h.pres, h.pU, h.pC⟩

/-- Words of a region survive a run that keeps their bytes. -/
theorem Frame.pres' {N' : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {Q : Nat → Prop} (hP : Pres N N' Q)
    (hin : ∀ k v, l.lookup k = some v → ∀ j, j < 4 → Q (b.toNat + k + j)) : Frame N' b n l := by
  intro k v hl
  obtain ⟨a1, a2, a3⟩ := hF k v hl
  refine ⟨a1, a2, ?_⟩
  have e := Frame.add_toNat hS (k := k) (by omega)
  rw [← a3]
  exact hP.rd hS.top (by rw [e]; have := hS.fit; omega) (fun j hj => by rw [e]; exact hin k v hl j hj)

set_option maxHeartbeats 1000000 in
/-- `poly1305_blocks(ctx, inp, 16 n, pad)` called from the `Final` frame (return address at `U + 236`). -/
theorem fin_blk (ic0 : UInt64) (hM : MemOK G N U 268 lU C 236 236 lC P) (n : Nat) (hn : 1 ≤ n)
    (hic : ic0.toNat + 61 + 184 * n < 2 ^ 63)
    (a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad w0 w1 w2 w3 w4 h0 h1 h2 h3 h4 r0 r1 r2 r3 : UInt32)
    (hlU : LK lU [(236, ret), (240, len), (244, pad), (248, w0), (252, w1), (256, w2), (260, w3), (264, w4)])
    (hlC : LK lC [(0, h0), (4, h1), (8, h2), (12, h3), (16, h4), (20, r0), (24, r1), (28, r2), (32, r3)])
    (lK : List (Nat × UInt32)) (hlK : LK lC lK) (hK : ∀ k v, (k, v) ∈ lK → 20 ≤ k ∧ k + 4 ≤ 236)

    (hlen : len.toNat = 16 * n) (E : ExtR N (FQ U C) inp (16 * n))
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0)
    (hh4 : h4.toNat ≤ 4) (hpad : pad.toNat ≤ 1) :
    ∃ (N' : PMem) (eax ecx edx gf o0 o1 o2 o3 o4 : UInt32),
      Run img (St.m ⟨N.get, a0, C, inp, ebx0, UInt32.add U 236, ebp0, esi0, edi0, 0x1001b0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 240, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (61 + 184 * n)⟩) ∧
      MemOK G N' U 268 [(248, w0), (252, w1), (256, w2), (260, w3), (264, w4)] C 236 236
        ((0, o0) :: (4, o1) :: (8, o2) :: (12, o3) :: (16, o4) :: (20, r0) :: (24, r1) :: (28, r2) :: (32, r3) :: lK) P ∧
      o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = accB N (val4 r0 r1 r2 r3) pad.toNat inp n (val5 h0 h1 h2 h3 h4 % p) := by
  have e120 := hM.fU.add_toNat (j := 132) (by decide)
  have hdUC := hM.dUC
  have hMb := hM.callee 132 116 (by decide) [(104, ret), (108, len), (112, pad)] (fun k v hm => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, by decide, hlU.1⟩
      · exact ⟨rfl, by decide, hlU.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.1⟩)
    C 236 20 lC hM.fC (by simp only [UInt32.reduceToNat]; omega) hM.wC (FQ U C) (fun x h => h.1) (fun x h => h.2)
  have hin : ∀ x, inp.toNat ≤ x → x < inp.toNat + 16 * n →
      x < (UInt32.add U 132).toNat ∨ (UInt32.add U 132).toNat + 116 ≤ x := fun x h1 h2 => (E.cov x h1 h2).1
  obtain ⟨N', lU', lC', eax, ecx, edx, gf, o0, o1, o2, o3, o4, R, M', LC', ho4, hv⟩ :=
    blocks_call ic0 N N (UInt32.add U 132) C _ lC (FQ U C) hMb n hn hic a0 inp ebx0 ebp0 esi0 edi0 g0 ret len
      pad h0 h1 h2 h3 h4 r0 r1 r2 r3 ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, trivial⟩
      hlC hlen E (range_out (by omega) (by decide) hin) hr0 hr1 hr2 hr3 hq1 hq2 hq3 hh4 hpad
  rw [uadd_assoc, uadd_assoc, show (132 : UInt32) + 104 = 236 from rfl, show (132 : UInt32) + 108 = 240 from rfl]
    at R
  refine ⟨N', eax, ecx, edx, gf, o0, o1, o2, o3, o4, R, ?_, ho4, hv⟩
  refine hM.back M' (fun x hx => ?_) _ _ (fun k v hm => ?_) (fun k v hm => ?_)
  · have h1 := hM.pU x hx; have h2 := hM.pC x hx
    unfold OutF at h1 h2
    exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩
  · refine ⟨lk_of_mem hlU k v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))),
      fun j hj => ?_⟩
    have hk : 248 ≤ k ∧ k ≤ 264 := by
      have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega
    exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩
  · rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    rcases List.mem_cons.1 hm with h | hm
    · exact Or.inr ⟨rfl, rfl, lk_of_mem LC' k v (by rw [h]; simp)⟩
    have hk := hK k v hm
    refine Or.inl ⟨lk_of_mem hlK k v hm, fun j hj => ?_⟩
    have hfc := hM.fC.fit
    exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩

set_option maxHeartbeats 1000000 in
/-- `memset(ctx, 0, 236)` called through `OPENSSL_cleanse` from the `Final` frame (return address
`0x100591` at `U + 220`); the caller's data region is the tag. -/
theorem fin_ms (ic0 : UInt64) (hic : ic0.toNat + 22 + 4 * 236 < 2 ^ 63) {mac : UInt32}
    (hM : MemOK G N U 268 lU mac 16 16 lC P)
    (a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 ctx w0 w1 w2 w3 w4 w5 w6 w7 : UInt32)
    (hlU : LK lU [(220, 1050001), (224, ctx), (228, 0), (232, 236), (236, w0), (240, w1), (244, w2), (248, w3),
      (252, w4), (256, w5), (260, w6), (264, w7)])
    (lK : List (Nat × UInt32)) (hlK : LK lC lK) (hK : ∀ k v, (k, v) ∈ lK → k + 4 ≤ 16)
    (hcf : FB N.get.size ctx 236) (hcU : ctx.toNat + 236 ≤ U.toNat ∨ U.toNat + 268 ≤ ctx.toNat)
    (hcm : ctx.toNat + 236 ≤ mac.toNat ∨ mac.toNat + 16 ≤ ctx.toNat)
    (hP : ∀ x, P x → x < ctx.toNat ∨ ctx.toNat + 236 ≤ x) :
    ∃ (N' : PMem) (eax ecx edx gf : UInt32),
      Run img (St.m ⟨N.get, a0, c0, d0, ebx0, UInt32.add U 220, ebp0, esi0, edi0, 0x1005d0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 224, ebp0, esi0, edi0, 1050001, efl gf,
          icAdd ic0 (msK 236)⟩) ∧
      MemOK G N' U 268 [(236, w0), (240, w1), (244, w2), (248, w3), (252, w4), (256, w5), (260, w6), (264, w7)]
        mac 16 16 lK P ∧
      ∀ j, j < 236 → memByte N'.get (ctx + j.toUInt32) = 0 := by
  have e216 := hM.fU.add_toNat (j := 216) (by decide)
  have hdUC := hM.dUC
  have hfc := hcf.fit; have hfi := hcf.img
  have hMm := hM.callee 216 20 (by decide) [(4, 1050001), (8, ctx), (12, 0), (16, 236)] (fun k v hm => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, by decide, hlU.1⟩
      · exact ⟨rfl, by decide, hlU.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.2.1⟩)
    ctx 236 0 [] hcf (by simp only [UInt32.reduceToNat]; omega) (Frame.nil _ _ _)
    (MsP (UInt32.add U 216) ctx 236) (fun x h => h.1) (fun x _ => by unfold OutF; omega)
  have hPQ : ∀ x, P x → MsP (UInt32.add U 216) ctx 236 x := by
    intro x hx
    have h1 := hM.pU x hx; have h2 := hP x hx
    unfold OutF at h1
    exact ⟨by unfold OutF; rw [e216]; simp only [UInt32.reduceToNat]; omega, by simp only [UInt32.reduceToNat]; omega⟩
  obtain ⟨N', lU', eax, ecx, edx, gf, R, M', hb⟩ :=
    memset_call ic0 N (UInt32.add U 216) ctx ctx 236 0 1050001 a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 _ hMm
      ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl,
        trivial⟩ (by simp only [UInt32.reduceToNat]; omega) (by simp only [UInt32.reduceToNat]; omega)
      (by rw [e216]; simp only [UInt32.reduceToNat]; omega) hic
  rw [uadd_assoc, uadd_assoc, show (216 : UInt32) + 4 = 220 from rfl, show (216 : UInt32) + 8 = 224 from rfl] at R
  refine ⟨N', eax, ecx, edx, gf, R, ?_, fun j hj => (hb j hj).trans rfl⟩
  have hmf := hM.fC.fit
  refine hM.back M' hPQ _ _ (fun k v hm => ?_) (fun k v hm => ?_)
  · refine ⟨lk_of_mem hlU k v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hm)))), fun j hj => ?_⟩
    have hk : 236 ≤ k ∧ k ≤ 264 := by
      have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega
    exact ⟨by unfold OutF; rw [e216]; simp only [UInt32.reduceToNat]; omega, by simp only [UInt32.reduceToNat]; omega⟩
  · have hk := hK k v hm
    exact Or.inl ⟨lk_of_mem hlK k v hm, fun j hj =>
      ⟨by unfold OutF; rw [e216]; simp only [UInt32.reduceToNat]; omega, by simp only [UInt32.reduceToNat]; omega⟩⟩

end Solutions.OpensslPoly1305
