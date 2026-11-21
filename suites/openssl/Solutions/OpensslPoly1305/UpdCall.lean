import Solutions.OpensslPoly1305.UpdC
import Solutions.OpensslPoly1305.BlkCall
import Solutions.OpensslPoly1305.Memcpy
import Solutions.OpensslPoly1305.InitOk
/-!
# Calls from `Poly1305_Update`: `poly1305_blocks` and `memcpy` in the caller's frame

The caller's memory is `MemOK G N U 272 lU C 236 236 lC P` (stack region `[U, U + 272)`, context
`[C, C + 236)`). A callee runs from the current memory `N` with its frame inside the caller's stack
region (`MemOK.callee`); afterwards `MemOK.back` gives the caller's stack words above the callee's
frame and the context words the callee keeps or states.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

variable {G N : PMem} {U C : UInt32} {nU nC mC : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

/-- A callee's memory: its frame `[U + b, U + b + nb)` inside the caller's stack region, its words
from the caller's, a data region `D`, and what it keeps (`Q`). -/
theorem MemOK.callee (h : MemOK G N U nU lU C nC mC lC P) (b : UInt32) (nb : Nat) (hb : b.toNat + nb ≤ nU)
    (lV : List (Nat × UInt32))
    (hV : ∀ k v, (k, v) ∈ lV → k % 4 = 0 ∧ k + 4 ≤ nb ∧ lU.lookup (b.toNat + k) = some v)
    (D : UInt32) (nD mD : Nat) (lD : List (Nat × UInt32)) (hD : FB N.get.size D nD)
    (hDV : D.toNat + nD ≤ U.toNat + b.toNat ∨ U.toNat + b.toNat + nb ≤ D.toNat) (hlD : Frame N D nD lD)
    (Q : Nat → Prop) (hQV : ∀ x, Q x → OutF (UInt32.add U b) nb x) (hQD : ∀ x, Q x → OutF D mD x) :
    MemOK N N (UInt32.add U b) nb lV D nD mD lD Q := by
  have eb := h.fU.add_toNat (j := b) (by omega)
  have hfit := h.fU.fit; have htop := h.fU.top; have himg := h.fU.img
  refine ⟨⟨htop, by rw [eb]; omega, by rw [eb]; omega⟩, hD, by rw [eb]; omega, ?_, hlD, Pres.refl _ _, hQV, hQD⟩
  refine Frame.ofMem lV (fun k v hm => ?_)
  obtain ⟨a1, a2, a3⟩ := hV k v hm
  obtain ⟨-, -, a4⟩ := h.wU (b.toNat + k) v a3
  refine ⟨a1, a2, ?_⟩
  rw [← a4, uadd_assoc]
  congr 2
  apply UInt32.toNat_inj.1
  unfold ramTop at htop
  simp only [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']
  omega

theorem FB.mono {s : Nat} {b : UInt32} {n n' : Nat} (h : FB s b n) (hn : n' ≤ n) : FB s b n' :=
  ⟨h.top, by have := h.fit; omega, by have := h.img; omega⟩

/-- A known word of the current memory. -/
theorem MemOK.addC (h : MemOK G N U nU lU C nC mC lC P) (k : Nat) (j : UInt32) (hj : j.toNat = k)
    (h4 : k % 4 = 0) (hk : k + 4 ≤ nC) :
    MemOK G N U nU lU C nC mC ((k, rdRaw N.get (UInt32.add C j) 4) :: lC) P :=
  ⟨h.fU, h.fC, h.dUC, h.wU, frame_cons h.wC k _ j hj h4 hk rfl, h.pres, h.pU, h.pC⟩

theorem range_out {a b L m : Nat} (hL : 0 < L) (hm : 0 < m) (h : ∀ x, a ≤ x → x < a + L → x < b ∨ b + m ≤ x) :
    a + L ≤ b ∨ b + m ≤ a := by
  by_cases hab : a ≤ b
  · by_cases hb : b < a + L
    · have := h b hab hb; omega
    · omega
  · have := h a (Nat.le_refl _) (by omega); omega

/-- What `poly1305_blocks` called from the `Update` frame keeps: outside its frame and `h`. -/
def BQ (U C : UInt32) (x : Nat) : Prop := OutF (UInt32.add U 120) 116 x ∧ OutF C 20 x

theorem ExtR.rdP {p : UInt32} {L : Nat} (E : ExtR G P p L) (hP : Pres G N P) (j : UInt32)
    (hj : j.toNat + 4 ≤ L) : rdRaw N.get (UInt32.add p j) 4 = rdRaw G.get (UInt32.add p j) 4 := by
  have e := E.add_toNat (j := j) (by omega)
  exact hP.rd E.top (by rw [e]; have := E.fit; omega) (fun k hk => by rw [e]; exact E.cov _ (by omega) (by omega))

theorem bval_congr {p : UInt32} (E : ExtR G P p 16) (hP : Pres G N P) : bval N p = bval G p := by
  unfold bval
  have h0 := E.rdP hP 0 (by decide)
  rw [uadd_zero] at h0
  rw [h0, E.rdP hP 4 (by decide), E.rdP hP 8 (by decide), E.rdP hP 12 (by decide)]

theorem accB_congr (hP : Pres G N P) (R padv : Nat) :
    ∀ (n : Nat) (a : UInt32) (x : Nat), ExtR G P a (16 * n) → accB N R padv a n x = accB G R padv a n x
  | 0, _, _, _ => rfl
  | n + 1, a, x, E => by
    have E' : ExtR G P a (16 + 16 * n) := by rw [show 16 + 16 * n = 16 * (n + 1) by omega]; exact E
    simp only [accB]
    rw [bval_congr (E'.mono (by omega)) hP]
    exact accB_congr hP R padv n _ _ E'.shift

set_option maxHeartbeats 1000000 in
/-- `poly1305_blocks(ctx, inp, 16 n, pad)` called from the `Update` frame (return address at `U + 224`). -/
theorem upd_blk (ic0 : UInt64) (hM : MemOK G N U 272 lU C 236 236 lC P) (n : Nat) (hn : 1 ≤ n)
    (hic : ic0.toNat + 61 + 184 * n < 2 ^ 63)
    (a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad w0 w1 w2 w3 w4 w5 w6 w7 w8 h0 h1 h2 h3 h4 r0 r1 r2 r3 : UInt32)
    (hlU : LK lU [(224, ret), (228, len), (232, pad), (236, w0), (240, w1), (244, w2), (248, w3), (252, w4),
      (256, w5), (260, w6), (264, w7), (268, w8)])
    (hlC : LK lC [(0, h0), (4, h1), (8, h2), (12, h3), (16, h4), (20, r0), (24, r1), (28, r2), (32, r3)])
    (lK : List (Nat × UInt32)) (hlK : LK lC lK) (hK : ∀ k v, (k, v) ∈ lK → 20 ≤ k ∧ k + 4 ≤ 236)

    (hlen : len.toNat = 16 * n) (E : ExtR N (BQ U C) inp (16 * n))
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0)
    (hh4 : h4.toNat ≤ 4) (hpad : pad.toNat ≤ 1) :
    ∃ (N' : PMem) (eax ecx edx gf o0 o1 o2 o3 o4 : UInt32),
      Run img (St.m ⟨N.get, a0, C, inp, ebx0, UInt32.add U 224, ebp0, esi0, edi0, 0x1001b0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 228, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (61 + 184 * n)⟩) ∧
      MemOK G N' U 272 [(236, w0), (240, w1), (244, w2), (248, w3), (252, w4), (256, w5), (260, w6), (264, w7),
        (268, w8)] C 236 236
        ((0, o0) :: (4, o1) :: (8, o2) :: (12, o3) :: (16, o4) :: (20, r0) :: (24, r1) :: (28, r2) :: (32, r3) :: lK) P ∧
      o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = accB N (val4 r0 r1 r2 r3) pad.toNat inp n (val5 h0 h1 h2 h3 h4 % p) := by
  have e120 := hM.fU.add_toNat (j := 120) (by decide)
  have hdUC := hM.dUC
  have hMb := hM.callee 120 116 (by decide) [(104, ret), (108, len), (112, pad)] (fun k v hm => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, by decide, hlU.1⟩
      · exact ⟨rfl, by decide, hlU.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.1⟩)
    C 236 20 lC hM.fC (by simp only [UInt32.reduceToNat]; omega) hM.wC (BQ U C) (fun x h => h.1) (fun x h => h.2)
  have hin : ∀ x, inp.toNat ≤ x → x < inp.toNat + 16 * n →
      x < (UInt32.add U 120).toNat ∨ (UInt32.add U 120).toNat + 116 ≤ x := fun x h1 h2 => (E.cov x h1 h2).1
  obtain ⟨N', lU', lC', eax, ecx, edx, gf, o0, o1, o2, o3, o4, R, M', LC', ho4, hv⟩ :=
    blocks_call ic0 N N (UInt32.add U 120) C _ lC (BQ U C) hMb n hn hic a0 inp ebx0 ebp0 esi0 edi0 g0 ret len
      pad h0 h1 h2 h3 h4 r0 r1 r2 r3 ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, trivial⟩
      hlC hlen E (range_out (by omega) (by decide) hin) hr0 hr1 hr2 hr3 hq1 hq2 hq3 hh4 hpad
  rw [uadd_assoc, uadd_assoc, show (120 : UInt32) + 104 = 224 from rfl, show (120 : UInt32) + 108 = 228 from rfl]
    at R
  refine ⟨N', eax, ecx, edx, gf, o0, o1, o2, o3, o4, R, ?_, ho4, hv⟩
  refine hM.back M' (fun x hx => ?_) _ _ (fun k v hm => ?_) (fun k v hm => ?_)
  · have h1 := hM.pU x hx; have h2 := hM.pC x hx
    unfold OutF at h1 h2
    exact ⟨by unfold OutF; rw [e120]; simp only [UInt32.reduceToNat]; omega, by unfold OutF; omega⟩
  · refine ⟨lk_of_mem hlU k v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))),
      fun j hj => ?_⟩
    have hk : 236 ≤ k ∧ k ≤ 268 := by
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
/-- `memcpy_call` for any length up to 16 (an empty copy reads nothing). -/
theorem memcpy_call' (ic0 : UInt64) (G : PMem) (V D dst n src ret a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 : UInt32)
    (lU : List (Nat × UInt32)) (hM : MemOK G G V 24 lU D 16 0 [] (McP V dst n))
    (hlU : LK lU [(8, ret), (12, dst), (16, src), (20, n)])
    (hn : n.toNat ≤ 16) (E : n.toNat ≠ 0 → ExtR G (McP V dst n) src n.toNat)
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 24 ≤ dst.toNat) (hic : ic0.toNat + 120 < 2 ^ 63) :
    ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (eax ecx edx gf : UInt32),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add V 8, ebp0, esi0, edi0, 0x1005a0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add V 12, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (mcK n.toNat)⟩) ∧
      MemOK G N' V 24 lU' D 16 0 [] (McP V dst n) ∧
      ∀ j, j < n.toNat → memByte N'.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32) := by
  by_cases h0 : n.toNat = 0
  · obtain ⟨N1, R1, M1⟩ := mc_z0 ic0 (by omega) G G V D lU [] _ hM a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 n dst _
      (hM.rdU (k := 20) hlU.2.2.2.1 20 rfl) (hM.rdU (k := 12) hlU.2.1 12 rfl) h0 rfl
    obtain ⟨N2, R2, M2⟩ := mc_e0 (icAdd ic0 6) (by rw [icAdd_toNat _ _ (by omega)]; omega) G N1 V D _ [] _ M1
      dst n d0 ebx0 ebp0 esi0 edi0 _ esi0 ebx0 ret (M1.rdU0 lk_here) (M1.rdU (k := 4) (lk_skip lk_here rfl) 4 rfl)
      (M1.rdU (k := 8) (lk_skip (lk_skip hlU.1 rfl) rfl) 8 rfl)
    rw [icAdd0, icAdd_add, show 6 + 3 = mcK n.toNat by simp [mcK, h0]] at R2
    exact ⟨N2, _, _, _, _, _, R1.trans R2, M2, fun j hj => absurd hj (by omega)⟩
  · exact memcpy_call ic0 G V D dst n src ret a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 lU hM hlU hn (E h0) hd hdimg hdV hic

set_option maxHeartbeats 1000000 in
/-- `memcpy(dst, src, n)` into the context's data called from the `Update` frame (return address at
`U + 220`); the source is read-only input of the caller. -/
theorem upd_mc (ic0 : UInt64) (hic : ic0.toNat + 120 < 2 ^ 63) (hM : MemOK G N U 272 lU C 236 236 lC P)
    (a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 ret dst src n w0 w1 w2 w3 w4 w5 w6 w7 w8 : UInt32)
    (hlU : LK lU [(220, ret), (224, dst), (228, src), (232, n), (236, w0), (240, w1), (244, w2), (248, w3),
      (252, w4), (256, w5), (260, w6), (264, w7), (268, w8)])
    (lK : List (Nat × UInt32)) (hlK : LK lC lK) (hK : ∀ k v, (k, v) ∈ lK → k + 4 ≤ 208)
    (hd1 : C.toNat + 208 ≤ dst.toNat) (hd2 : dst.toNat + n.toNat ≤ C.toNat + 224) (hn : n.toNat ≤ 16)
    (E : n.toNat ≠ 0 → ExtR G P src n.toNat) :
    ∃ (N' : PMem) (eax ecx edx gf : UInt32),
      Run img (St.m ⟨N.get, a0, c0, d0, ebx0, UInt32.add U 220, ebp0, esi0, edi0, 0x1005a0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 224, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (mcK n.toNat)⟩) ∧
      MemOK G N' U 272 [(236, w0), (240, w1), (244, w2), (248, w3), (252, w4), (256, w5), (260, w6), (264, w7),
        (268, w8)] C 236 236 lK P ∧
      (∀ a : UInt32, C.toNat ≤ a.toNat → a.toNat < dst.toNat → memByte N'.get a = memByte N.get a) ∧
      ∀ j, j < n.toNat → memByte N'.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32) := by
  have e212 := hM.fU.add_toNat (j := 212) (by decide)
  have hdUC := hM.dUC
  have hfc := hM.fC.fit; have hfi := hM.fC.img; have htop := hM.fC.top
  have hMm := hM.callee 212 24 (by decide) [(8, ret), (12, dst), (16, src), (20, n)] (fun k v hm => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, by decide, hlU.1⟩
      · exact ⟨rfl, by decide, hlU.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.1⟩
      · exact ⟨rfl, by decide, hlU.2.2.2.1⟩)
    C 16 0 [] (hM.fC.mono (by decide)) (by simp only [UInt32.reduceToNat]; omega) (Frame.nil _ _ _)
    (McP (UInt32.add U 212) dst n) (fun x h => h.1) (fun x _ => by unfold OutF; omega)
  have hPQ : ∀ x, P x → McP (UInt32.add U 212) dst n x := by
    intro x hx
    have h1 := hM.pU x hx; have h2 := hM.pC x hx
    unfold OutF at h1 h2
    exact ⟨by unfold OutF; rw [e212]; simp only [UInt32.reduceToNat]; omega, by omega⟩
  have E' : n.toNat ≠ 0 → ExtR N (McP (UInt32.add U 212) dst n) src n.toNat := fun h =>
    have E0 := E h
    ⟨by rw [hM.size]; exact E0.fit, by rw [hM.size]; exact E0.top, fun x h1 h2 => hPQ x (E0.cov x h1 h2)⟩
  obtain ⟨N', lU', eax, ecx, edx, gf, R, M', hb⟩ :=
    memcpy_call' ic0 N (UInt32.add U 212) C dst n src ret a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 _ hMm
      ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl,
        trivial⟩ hn E' (by omega) (by omega) (by rw [e212]; simp only [UInt32.reduceToNat]; omega) hic
  rw [uadd_assoc, uadd_assoc, show (212 : UInt32) + 8 = 220 from rfl, show (212 : UInt32) + 12 = 224 from rfl]
    at R
  refine ⟨N', eax, ecx, edx, gf, R, ?_, fun a h1 h2 => ?_, fun j hj => ?_⟩
  · refine hM.back M' hPQ _ _ (fun k v hm => ?_) (fun k v hm => ?_)
    · refine ⟨lk_of_mem hlU k v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hm)))), fun j hj => ?_⟩
      have hk : 236 ≤ k ∧ k ≤ 268 := by
        have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega
      exact ⟨by unfold OutF; rw [e212]; simp only [UInt32.reduceToNat]; omega, by omega⟩
    · have hk := hK k v hm
      exact Or.inl ⟨lk_of_mem hlK k v hm, fun j hj =>
        ⟨by unfold OutF; rw [e212]; simp only [UInt32.reduceToNat]; omega, by omega⟩⟩
  · exact M'.pres.2 a (by omega)
      ⟨by unfold OutF; rw [e212]; simp only [UInt32.reduceToNat]; omega, by omega⟩
  · rw [hb j hj]
    have E0 := E (by omega)
    have hj32 : (src + j.toUInt32).toNat = src.toNat + j := by
      have := E0.fit; have := E0.top; unfold ramTop at *
      rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; omega
    exact hM.pres.2 _ (by rw [hj32]; have := E0.fit; omega) (by rw [hj32]; exact E0.cov _ (by omega) (by omega))

end Solutions.OpensslPoly1305
