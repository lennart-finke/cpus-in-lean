import Solutions.OpensslPoly1305.FinPad
/-!
# The end of `Poly1305_Final`: `poly1305_emit`, `OPENSSL_cleanse`, the return

`fin_tail`: from `0x1004ac` (after the last block) with the accumulator `h` and `s` in the context: the
tag `emitW h s` is stored at `mac` (mac mode, the context read-only), the context is wiped by `memset`,
and the call returns. The run writes only the stack, the context and the tag (`PT`).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

/-- Outside the stack region and the tag. -/
def PM (U mac : UInt32) (x : Nat) : Prop := OutF U 268 x ∧ OutF mac 16 x

/-- Outside the stack region, the context and the tag. -/
def PT (U C mac : UInt32) (x : Nat) : Prop := OutF U 268 x ∧ OutF C 236 x ∧ OutF mac 16 x

variable {G N : PMem} {U C : UInt32} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

set_option maxHeartbeats 4000000 in
theorem fin_tail (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 40) (hM : MemOK G N U 268 lU C 236 236 lC P)
    (a1 c1 d1 ebx0 ebp0 g0 esi0 edi0 ret mac h0 h1 h2 h3 h4 s0 s1 s2 s3 : UInt32)
    (hP : ∀ x, PT U C mac x → P x)
    (hlU : LK lU [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)])
    (hlC : LK lC [(0, h0), (4, h1), (8, h2), (12, h3), (16, h4), (192, s0), (196, s1), (200, s2), (204, s3)])
    (hmf : mac.toNat + 16 ≤ N.get.size) (hmi : mac.toNat + 16 ≤ 0x100000 ∨ 0x100000 + 1536 ≤ mac.toNat)
    (hmU : mac.toNat + 16 ≤ U.toNat ∨ U.toNat + 268 ≤ mac.toNat)
    (hmC : mac.toNat + 16 ≤ C.toNat ∨ C.toNat + 236 ≤ mac.toNat) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨N.get, a1, c1, d1, ebx0, UInt32.add U 248, ebp0, C, mac, 0x1004ac, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK N N' U 268 lU' mac 16 16 lC' (PT U C mac) ∧ LK lU' [(256, ret), (260, C), (264, mac)] ∧
      memBytes N'.get mac 16 = Ssl.Spec.Poly1305.leBytes 16 (val4 (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).1
        (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.1 (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.2.1
        (emitW h0 h1 h2 h3 h4 s0 s1 s2 s3).2.2.2) ∧
      ∀ j, j < 236 → memByte N'.get (C + j.toUInt32) = 0 := by
  have hCf := hM.fC; have hfit := hCf.fit; have htop := hCf.top; have hCi := hCf.img
  have hUf := hM.fU.fit; have hUi := hM.fU.img
  have hdUC := hM.dUC
  have M0 := hM.switch C 236 236 lC hM.fC hM.dUC hM.wC P hM.pU hM.pC
  obtain ⟨N1, lU1, R1, M1, LU1, -⟩ := fin_f ic0 (by omega) N N U C lU lC P M0 a1 c1 d1 ebx0 ebp0 mac g0 esi0 edi0
    ret hlU trivial
  have hs1 := M1.size
  have Mm := M1.switch mac 16 16 [] ⟨by rw [hs1]; exact htop, by rw [hs1]; omega, hmi⟩ hmU (Frame.nil _ _ _)
    (PM U mac) (fun x h => h.1) (fun x h => h.2)
  have e192 := hCf.add_toNat (j := 192) (by decide)
  have Ec : ExtR N1 (PM U mac) C 20 :=
    ⟨by rw [hs1]; omega, by rw [hs1]; exact htop, fun x h1 h2 => ⟨by unfold OutF; omega, by unfold OutF; omega⟩⟩
  have Es : ExtR N1 (PM U mac) (UInt32.add C 192) 16 :=
    ⟨by rw [hs1, e192]; simp only [UInt32.reduceToNat]; omega, by rw [hs1]; exact htop,
      fun x h1 h2 => by
        rw [e192] at h1 h2; simp only [UInt32.reduceToNat] at h1 h2
        exact ⟨by unfold OutF; omega, by unfold OutF; omega⟩⟩
  obtain ⟨N2, lU2, v58, v56, g60, v53, v13, v47, v50, R2, M2, LU2, LC2, eW⟩ :=
    fin_g (icAdd ic0 5) (by have := icAdd_le ic0 5; omega) N1 N1 U mac lU1 [] (PM U mac) Mm
      (UInt32.add C 192) C ebx0 ebp0 g0 esi0 edi0 ret h0 h1 h2 h3 h4 s0 s1 s2 s3 LU1 trivial Ec Es
      (M1.rdC0 hlC.1) (M1.rdC (k := 4) hlC.2.1 4 rfl) (M1.rdC (k := 8) hlC.2.2.1 8 rfl)
      (M1.rdC (k := 12) hlC.2.2.2.1 12 rfl) (M1.rdC (k := 16) hlC.2.2.2.2.1 16 rfl)
      (M1.rdC (k := 192) hlC.2.2.2.2.2.1 192 rfl)
      (by rw [uadd_assoc]; exact M1.rdC (k := 196) hlC.2.2.2.2.2.2.1 _ rfl)
      (by rw [uadd_assoc]; exact M1.rdC (k := 200) hlC.2.2.2.2.2.2.2.1 _ rfl)
      (by rw [uadd_assoc]; exact M1.rdC (k := 204) hlC.2.2.2.2.2.2.2.2.1 _ rfl)
      (by rw [hs1]; omega) (by omega) (by omega) (by rw [hs1, e192]; simp only [UInt32.reduceToNat]; omega)
      (by rw [e192]; simp only [UInt32.reduceToNat]; omega) (by rw [e192]; simp only [UInt32.reduceToNat]; omega)
  have hs2 := M2.size
  have Mt := M2.switch mac 16 16 _ M2.fC M2.dUC M2.wC (PT U C mac) (fun x h => h.1) (fun x h => h.2.2)
  obtain ⟨N3, lU3, g1, R3, M3, LU3, -⟩ := fin_h (icAdd (icAdd ic0 5) 72)
    (by have := icAdd_le (icAdd ic0 5) 72; have := icAdd_le ic0 5; omega)
    N2 N2 U mac lU2 _ (PT U C mac) Mt (UInt32.add C 192) v58 v56 ebx0 ebp0 C g60 (UInt32.add C 192) esi0 edi0 ret
    ⟨LU2.2.2.2.2.2.2.2.2.2.2.1, LU2.2.2.2.2.2.2.2.2.2.2.2.1, LU2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      LU2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, LU2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, LU2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, trivial⟩
    trivial N2.fits
  have hs3 := M3.size
  obtain ⟨N4, eax4, ecx4, edx4, gf4, R4, M4, Hz⟩ := fin_ms
    (icAdd (icAdd (icAdd ic0 5) 72) 9)
    (by have := icAdd_le (icAdd (icAdd ic0 5) 72) 9; have := icAdd_le (icAdd ic0 5) 72; have := icAdd_le ic0 5; omega)
    M3 1050064 v58 v56 ebx0 C mac ebp0 g1 C 1049802 C 236 esi0 edi0 ret C mac LU3
    [(0, v47), (4, v50), (8, v53), (12, v56)] (by
      have := LC2
      exact ⟨lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl, lk_skip (lk_skip lk_here rfl) rfl,
        lk_skip lk_here rfl, lk_here, trivial⟩)
    (fun k v hm => by have := List.mem_map_of_mem (f := Prod.fst) hm; simp at this; omega)
    ⟨by rw [hs3, hs2, hs1]; exact htop, by rw [hs3, hs2, hs1]; exact hfit, hCi⟩ (by omega) (by omega)
    (fun x h => h.2.1)
  have hs4 := M4.size
  obtain ⟨N5, lU5, g2, R5, M5, LU5, -⟩ := fin_i (icAdd (icAdd (icAdd (icAdd ic0 5) 72) 9) (msK 236))
    (by
      have := icAdd_le (icAdd (icAdd (icAdd ic0 5) 72) 9) (msK 236)
      have := icAdd_le (icAdd (icAdd ic0 5) 72) 9
      have := icAdd_le (icAdd ic0 5) 72
      have := icAdd_le ic0 5
      have : msK 236 = 22 + 4 * 236 := rfl
      omega)
    N4 N4 U mac _ _ (PM U mac) (M4.self (PM U mac) (fun _ h => h.1) (fun _ h => h.2))
    eax4 ecx4 edx4 ebx0 ebp0 C gf4 esi0 edi0 ret
    ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip lk_here rfl) rfl, lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl,
      lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl,
      lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl,
      lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl,
      lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) rfl) rfl) rfl) rfl, trivial⟩
    trivial
  have M5' := M4.join M5 (fun x h => ⟨h.1, h.2.2⟩)
  rw [icAdd0] at R2 R3 R4 R5
  have hs5 := M5.size
  -- the run and the memory
  have P01 : Pres N N2 (PT U C mac) :=
    (M1.pres.mono (fun x h => hP x h)).trans (M2.pres.mono (fun x h => ⟨h.1, h.2.2⟩))
  refine ⟨N5, lU5, _, _, _, _, g2, _, R1.trans (R2.trans (R3.trans (R4.trans R5))), M5'.rebase P01,
    ⟨LU5.2.2.2.2.2.1, LU5.2.2.2.2.2.2.1, LU5.2.2.2.2.2.2.2.1, trivial⟩, ?_, fun j hj => ?_⟩
  · rw [← eW]
    have hmf5 : mac.toNat + 16 ≤ N5.get.size := by rw [hs5, hs4, hs2, hs1]; exact hmf
    exact tag_bytes N5.get mac v47 v50 v53 v56 hmf5 (by rw [hs5, hs4, hs2, hs1]; exact htop)
      (M5'.rdC0 lk_here) (M5'.rdC (k := 4) (lk_skip lk_here rfl) 4 rfl)
      (M5'.rdC (k := 8) (lk_skip (lk_skip lk_here rfl) rfl) 8 rfl)
      (M5'.rdC (k := 12) (lk_skip (lk_skip (lk_skip lk_here rfl) rfl) rfl) 12 rfl)
  · have hj32 : (C + j.toUInt32).toNat = C.toNat + j := by
      rw [UInt32.toNat_add]; simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at htop; omega
    rw [M5.pres.2 _ (by rw [hj32, hs4, hs2, hs1]; omega) ⟨by unfold OutF; rw [hj32]; omega,
      by unfold OutF; rw [hj32]; omega⟩]
    exact Hz j hj

end Solutions.OpensslPoly1305
