import Solutions.OpensslPoly1305.FinPad
/-!
# The whole padding of `Poly1305_Final` (`num ≠ 0`)

From `0x10047a` to `0x10049e`: `data[num] = 1`, `data[num + 1 .. 15] = 0`, the bytes before `num`
kept (`fin_padall`).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305

set_option autoImplicit false

variable {U C : UInt32} {lU : List (Nat × UInt32)}

set_option maxHeartbeats 4000000 in
theorem fin_padall (N1 : PMem) (num esi0 edi0 ret mac ebx0 ebp0 c0 g1 : UInt32) (ic0 : UInt64)
    (hic : ic0.toNat < 2 ^ 30) (hM : MemOK N1 N1 U 268 lU (UInt32.add C 208) 16 0 [] (PadP U C num))
    (hCf : FB N1.get.size C 236) (hCU : C.toNat + 236 ≤ U.toNat ∨ U.toNat + 268 ≤ C.toNat)
    (hl : LK lU [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)])
    (hn16 : num.toNat < 16) :
    ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (a' c' g' : UInt32) (ic : UInt64),
      Run img (St.m ⟨N1.get, num, c0, UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac, 0x10047a, efl g1,
          icAdd ic0 0⟩)
        (St.m ⟨N'.get, a', c', UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac, 0x10049e, efl g', ic⟩) ∧
      ic.toNat < 2 ^ 31 ∧
      MemOK N1 N' U 268 lU' (UInt32.add C 208) 16 0 [] (PadP U C num) ∧
      LK lU' [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)] ∧
      (∀ j, j < num.toNat → memByte N'.get (C + (208 + j).toUInt32) = memByte N1.get (C + (208 + j).toUInt32)) ∧
      memByte N'.get (C + (208 + num.toNat).toUInt32) = 1 ∧
      ∀ j, num.toNat < j → j < 16 → memByte N'.get (C + (208 + j).toUInt32) = 0 := by
  have hfit := hCf.fit; have htop := hCf.top
  have hCt : C.toNat + 236 ≤ ramTop := Nat.le_trans hfit htop
  have eq : (UInt32.add (UInt32.add C num) 208).toNat = C.toNat + 208 + num.toNat := by
    rw [uadd_sem, uadd_sem]; simp only [UInt32.reduceToNat]; unfold ramTop at hCt; omega
  have R1 := fp_one ic0 (by omega) N1 (UInt32.add U 248) C num c0 (UInt32.add C 208) ebx0 ebp0 mac g1 htop
    (by rw [eq]; omega)
  obtain ⟨ok, M1⟩ := pad_st num hM hCf hCU (UInt32.add (UInt32.add C num) 208) 1 (by omega) (by omega)
  rw [← wr1_get N1 _ _ ok] at R1
  have hsz : (CodeMem.wr1 N1 _ 1 ok).get.size = N1.get.size := wr1_get_size N1 _ 1 ok
  have b1 : ∀ j, j < 16 → j ≠ num.toNat →
      memByte (CodeMem.wr1 N1 _ 1 ok).get (C + (208 + j).toUInt32) = memByte N1.get (C + (208 + j).toUInt32) :=
    fun j hj hjn => by
      have ea := addr208 hCt j (by omega)
      exact memByte_wr1_other N1 _ 1 ok (by rw [ea]; omega) (by rw [ea, eq]; omega)
  have b1n : memByte (CodeMem.wr1 N1 _ 1 ok).get (C + (208 + num.toNat).toUInt32) = 1 := by
    rw [addr_cj hCt num.toNat (by omega) _ (by rw [eq]), memByte_wr1_self]; rfl
  have Ms := M1.self (OutF U 268) (fun _ h => h) (fun _ _ => by unfold OutF; omega)
  have hk : ∀ (N3 : PMem) {lU3 : List (Nat × UInt32)},
      MemOK (CodeMem.wr1 N1 _ 1 ok) N3 U 268 lU3 (UInt32.add C 208) 16 0 [] (OutF U 268) →
      ∀ j, j < 16 → memByte N3.get (C + (208 + j).toUInt32) =
        memByte (CodeMem.wr1 N1 _ 1 ok).get (C + (208 + j).toUInt32) := fun N3 _ M j hj => by
    have ea := addr208 hCt j (by omega)
    exact M.pres.2 _ (by rw [ea, hsz]; omega) (by unfold OutF; rw [ea]; omega)
  have hnum1 : (UInt32.add num 1).toNat = num.toNat + 1 := by rw [uadd_sem]; simp only [UInt32.reduceToNat]; omega
  by_cases h15 : num.toNat = 15
  · obtain ⟨N3, lU3, g2, R2, M3, L3, -⟩ := fin_b0 (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega) _ _ U
      (UInt32.add C 208) lU [] _ Ms num c0 (UInt32.add C 208) ebx0 ebp0 C mac g1 esi0 edi0 ret hl trivial
      (by rw [hnum1]; omega)
    rw [icAdd0, icAdd_add] at R2
    refine ⟨N3, lU3, num, _, g2, _, R1.trans R2, by rw [icAdd_toNat _ _ (by omega)]; omega,
      M1.join M3 (fun _ h => h.1), L3, fun j hj => ?_, ?_, fun j hj1 hj2 => absurd hj2 (by omega)⟩
    · rw [hk N3 M3 j (by omega), b1 j (by omega) (by omega)]
    · rw [hk N3 M3 _ (by omega), b1n]
  · have hb0 : ∀ j, num.toNat < j → j ≤ num.toNat →
        memByte (CodeMem.wr1 N1 _ 1 ok).get (C + (208 + j).toUInt32) = 0 := fun j h1 h2 => absurd h2 (by omega)
    have fin : ∀ (N3 : PMem) (lU3 : List (Nat × UInt32)) (g2 : UInt32) (r : Nat),
        num.toNat + r = 14 →
        Run img (St.m ⟨(CodeMem.wr1 N1 _ 1 ok).get, num, c0, UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac,
          0x100482, efl g1, icAdd (icAdd ic0 1) 0⟩)
          (St.m ⟨N3.get, num, UInt32.add num 1, UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac, 0x100490,
            efl g2, icAdd (icAdd ic0 1) 9⟩) →
        MemOK (CodeMem.wr1 N1 _ 1 ok) N3 U 268 lU3 (UInt32.add C 208) 16 0 [] (OutF U 268) →
        LK lU3 [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)] →
        ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (a' c' g' : UInt32) (ic : UInt64),
          Run img (St.m ⟨N1.get, num, c0, UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac, 0x10047a, efl g1,
              icAdd ic0 0⟩)
            (St.m ⟨N'.get, a', c', UInt32.add C 208, ebx0, UInt32.add U 248, ebp0, C, mac, 0x10049e, efl g', ic⟩) ∧
          ic.toNat < 2 ^ 31 ∧
          MemOK N1 N' U 268 lU' (UInt32.add C 208) 16 0 [] (PadP U C num) ∧
          LK lU' [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)] ∧
          (∀ j, j < num.toNat → memByte N'.get (C + (208 + j).toUInt32) = memByte N1.get (C + (208 + j).toUInt32)) ∧
          memByte N'.get (C + (208 + num.toNat).toUInt32) = 1 ∧
          ∀ j, num.toNat < j → j < 16 → memByte N'.get (C + (208 + j).toUInt32) = 0 := by
      intro N3 lU3 g2 r hr R2 M3 L3
      have M13 := M1.join M3 (fun _ h => h.1)
      have hb3 : ∀ j, num.toNat < j → j ≤ num.toNat → memByte N3.get (C + (208 + j).toUInt32) = 0 :=
        fun j h1 h2 => absurd h2 (by omega)
      obtain ⟨N4, lU4, a4, g4, R4, M4, L4, hk4, hz4⟩ := fin_loop (G := N1) num esi0 edi0 ret mac ebx0 ebp0 hCf hCU r
        num (icAdd (icAdd ic0 1) 9) N3 lU3 (UInt32.add num 1) (UInt32.add C 208) g2 hr (Nat.le_refl _)
        (by have := icAdd_le (icAdd ic0 1) 9; have := icAdd_le ic0 1; omega)
        M13 L3 hb3
      rw [icAdd0] at R2 R4
      refine ⟨N4, lU4, a4, _, g4, _, R1.trans (R2.trans R4), ?_, M4, L4, fun j hj => ?_, ?_, hz4⟩
      · have := icAdd_le (icAdd (icAdd ic0 1) 9) (4 * (r + 1)); have := icAdd_le (icAdd ic0 1) 9
        have := icAdd_le ic0 1; omega
      · rw [hk4 j (by omega), hk N3 M3 j (by omega), b1 j (by omega) (by omega)]
      · rw [hk4 _ (Nat.le_refl _), hk N3 M3 _ (by omega), b1n]
    by_cases h14 : num.toNat = 14
    · obtain ⟨N3, lU3, g2, R2, M3, L3, -⟩ := fin_b2 (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega) _ _ U
        (UInt32.add C 208) lU [] _ Ms num c0 (UInt32.add C 208) ebx0 ebp0 C mac g1 esi0 edi0 ret hl trivial
        (by rw [hnum1]; omega)
      exact fin N3 lU3 g2 0 (by omega) R2 M3 L3
    · obtain ⟨N3, lU3, g2, R2, M3, L3, -⟩ := fin_b1 (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega) _ _ U
        (UInt32.add C 208) lU [] _ Ms num c0 (UInt32.add C 208) ebx0 ebp0 C mac g1 esi0 edi0 ret hl trivial
        (by rw [hnum1]; omega)
      exact fin N3 lU3 g2 (14 - num.toNat) (by omega) R2 M3 L3

end Solutions.OpensslPoly1305
