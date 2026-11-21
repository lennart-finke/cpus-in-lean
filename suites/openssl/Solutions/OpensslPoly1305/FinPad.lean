import Solutions.OpensslPoly1305.FinCall
import Solutions.OpensslPoly1305.FinC
/-!
# The padding of the last block in `Poly1305_Final`

`data[num] = 1` (`movb $1, 0xd0(%esi,%eax)`), then `data[num + 1 .. 15] = 0` (the byte loop at
`0x100490`), run in "pad mode": `MemOK … D 16 0 [] (PadP U C num)` with nothing known in the data region
and the bytes `[C + 208 + num, C + 224)` the only context bytes that may change.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Solutions.Exec.Mul Solutions.Exec.Fast
open Solutions.OpensslPoly1305.Cbv Solutions.Logic.Cmp

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option cbv.maxSteps 50000000
set_option exec.addrSub true
set_option autoImplicit false

/-- `movb $0x1, 0xd0(%esi,%eax)` -/
theorem fp_one (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (U ctx num c0 d0 ebx0 ebp0 edi0 g0 : UInt32)
    (h1 : N.get.size ≤ ramTop) (hq : (UInt32.add (UInt32.add ctx num) 208).toNat < N.get.size) :
    Run img (St.m ⟨N.get, num, c0, d0, ebx0, U, ebp0, ctx, edi0, 0x10047a, efl g0, icAdd ic0 0⟩)
      (St.m ⟨wrBytes N.get (UInt32.add (UInt32.add ctx num) 208) 1 1, num, c0, d0, ebx0, U, ebp0, ctx, edi0,
        0x100482, efl g0, icAdd ic0 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  cbv

/-- `movb $0x0, 0xd1(%esi,%eax)` -/
theorem fp_zero (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (U ctx i c0 d0 ebx0 ebp0 edi0 g0 : UInt32)
    (h1 : N.get.size ≤ ramTop) (hq : (UInt32.add (UInt32.add ctx i) 209).toNat < N.get.size) :
    Run img (St.m ⟨N.get, i, c0, d0, ebx0, U, ebp0, ctx, edi0, 0x100490, efl g0, icAdd ic0 0⟩)
      (St.m ⟨wrBytes N.get (UInt32.add (UInt32.add ctx i) 209) 1 0, i, c0, d0, ebx0, U, ebp0, ctx, edi0,
        0x100498, efl g0, icAdd ic0 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  cbv

/-- Where the padding does not write. -/
def PadP (U C num : UInt32) (x : Nat) : Prop :=
  OutF U 268 x ∧ (x < C.toNat + 208 + num.toNat ∨ C.toNat + 224 ≤ x)

variable {G N : PMem} {U C : UInt32} {lU : List (Nat × UInt32)}

/-- A byte store into `[C + 208 + num, C + 224)` in pad mode. -/
theorem pad_st (num : UInt32) (hM : MemOK G N U 268 lU (UInt32.add C 208) 16 0 [] (PadP U C num))
    (hCf : FB N.get.size C 236) (hCU : C.toNat + 236 ≤ U.toNat ∨ U.toNat + 268 ≤ C.toNat) (q v : UInt32)
    (hq1 : C.toNat + 208 + num.toNat ≤ q.toNat) (hq2 : q.toNat < C.toNat + 224) :
    ∃ ok : StoreOk1 Image.base Image.size N.mem q,
      MemOK G (CodeMem.wr1 N q v ok) U 268 lU (UInt32.add C 208) 16 0 [] (PadP U C num) := by
  have hf := hCf.fit; have hi := hCf.img
  have ok : StoreOk1 Image.base Image.size N.mem q := by
    refine ⟨by show q.toNat < N.get.size; omega, ?_⟩
    rw [show Image.base.toNat = 0x100000 from rfl, show Image.size = 1536 from rfl]; omega
  exact ⟨ok, hM.st1 q v ok (by omega) (fun x hx => by unfold PadP at hx; omega)⟩

theorem addr_cj {C : UInt32} (hC : C.toNat + 236 ≤ ramTop) (j : Nat) (hj : j < 28) (q : UInt32)
    (hq : q.toNat = C.toNat + 208 + j) : C + (208 + j).toUInt32 = q := by
  apply UInt32.toNat_inj.1
  rw [addr208 hC j hj, hq]

set_option maxHeartbeats 2000000 in
/-- The zero loop: from `0x100490` with `eax = i` to `0x10049e`, `data[i + 1 .. 15] = 0`. -/
theorem fin_loop (num esi0 edi0 ret mac ebx0 ebp0 : UInt32) (hCf : FB G.get.size C 236)
    (hCU : C.toNat + 236 ≤ U.toNat ∨ U.toNat + 268 ≤ C.toNat) :
    ∀ (r : Nat) (i : UInt32) (ic0 : UInt64) (N : PMem) (lU : List (Nat × UInt32)) (c1 d1 g : UInt32),
      i.toNat + r = 14 → num.toNat ≤ i.toNat → ic0.toNat + 4 * (r + 1) < 2 ^ 63 →
      MemOK G N U 268 lU (UInt32.add C 208) 16 0 [] (PadP U C num) →
      LK lU [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)] →
      (∀ j, num.toNat < j → j ≤ i.toNat → memByte N.get (C + (208 + j).toUInt32) = 0) →
      ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (a' g' : UInt32),
        Run img (St.m ⟨N.get, i, c1, d1, ebx0, UInt32.add U 248, ebp0, C, mac, 0x100490, efl g, icAdd ic0 0⟩)
          (St.m ⟨N'.get, a', c1, d1, ebx0, UInt32.add U 248, ebp0, C, mac, 0x10049e, efl g',
            icAdd ic0 (4 * (r + 1))⟩) ∧
        MemOK G N' U 268 lU' (UInt32.add C 208) 16 0 [] (PadP U C num) ∧
        LK lU' [(248, esi0), (252, edi0), (256, ret), (260, C), (264, mac)] ∧
        (∀ j, j ≤ num.toNat → memByte N'.get (C + (208 + j).toUInt32) = memByte N.get (C + (208 + j).toUInt32)) ∧
        ∀ j, num.toNat < j → j < 16 → memByte N'.get (C + (208 + j).toUInt32) = 0 := by
  have hfit := hCf.fit; have htop := hCf.top
  have hCt : C.toNat + 236 ≤ ramTop := Nat.le_trans hfit htop
  intro r
  induction r with
  | zero =>
    intro i ic0 N lU c1 d1 g hi hn hic hM hl hb
    have hs := hM.size
    have eq : (UInt32.add (UInt32.add C i) 209).toNat = C.toNat + 208 + (i.toNat + 1) := by
      rw [uadd_sem, uadd_sem]; simp only [UInt32.reduceToNat]; unfold ramTop at hCt; omega
    have R1 := fp_zero ic0 (by omega) N (UInt32.add U 248) C i c1 d1 ebx0 ebp0 mac g (by rw [hs]; exact htop)
      (by rw [eq, hs]; omega)
    obtain ⟨ok, M1⟩ := pad_st num hM (hCf.size_eq hs) hCU (UInt32.add (UInt32.add C i) 209) 0 (by omega) (by omega)
    rw [← wr1_get N _ _ ok] at R1
    have hsz : (CodeMem.wr1 N _ 0 ok).get.size = G.get.size := (wr1_get_size N _ 0 ok).trans hs
    obtain ⟨N2, lU2, v1, g3, R2, M2, L2, -, ev1⟩ := fin_c1 (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega)
      _ _ U (UInt32.add C 208) lU [] _ (M1.self (OutF U 268) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      i c1 d1 ebx0 ebp0 C mac g esi0 edi0 ret hl trivial
      (by rw [uadd_sem]; simp only [UInt32.reduceToNat]; omega)
    rw [icAdd0, icAdd_add] at R2
    have hk : ∀ j, j < 16 → memByte N2.get (C + (208 + j).toUInt32) =
        memByte (CodeMem.wr1 N _ 0 ok).get (C + (208 + j).toUInt32) := fun j hj => by
      have ea := addr208 hCt j (by omega)
      exact M2.pres.2 _ (by rw [ea, hsz]; omega) (by unfold OutF; rw [ea]; omega)
    refine ⟨N2, lU2, v1, g3, R1.trans R2, M1.join M2 (fun _ h => h.1), L2, fun j hj => ?_,
      fun j hj1 hj2 => ?_⟩
    · have ea := addr208 hCt j (by omega)
      rw [hk j (by omega), memByte_wr1_other N _ 0 ok (by rw [ea, hs]; omega) (by rw [ea, eq]; omega)]
    · have ea := addr208 hCt j (by omega)
      rw [hk j hj2]
      by_cases hji : j ≤ i.toNat
      · rw [memByte_wr1_other N _ 0 ok (by rw [ea, hs]; omega) (by rw [ea, eq]; omega)]
        exact hb j hj1 hji
      · rw [addr_cj hCt j (by omega) _ (by rw [eq]; omega), memByte_wr1_self]; rfl
  | succ r ih =>
    intro i ic0 N lU c1 d1 g hi hn hic hM hl hb
    have hs := hM.size
    have eq : (UInt32.add (UInt32.add C i) 209).toNat = C.toNat + 208 + (i.toNat + 1) := by
      rw [uadd_sem, uadd_sem]; simp only [UInt32.reduceToNat]; unfold ramTop at hCt; omega
    have R1 := fp_zero ic0 (by omega) N (UInt32.add U 248) C i c1 d1 ebx0 ebp0 mac g (by rw [hs]; exact htop)
      (by rw [eq, hs]; omega)
    obtain ⟨ok, M1⟩ := pad_st num hM (hCf.size_eq hs) hCU (UInt32.add (UInt32.add C i) 209) 0 (by omega) (by omega)
    rw [← wr1_get N _ _ ok] at R1
    have hsz : (CodeMem.wr1 N _ 0 ok).get.size = G.get.size := (wr1_get_size N _ 0 ok).trans hs
    obtain ⟨N2, lU2, v1, g3, R2, M2, L2, -, ev1⟩ := fin_c0 (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega)
      _ _ U (UInt32.add C 208) lU [] _ (M1.self (OutF U 268) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      i c1 d1 ebx0 ebp0 C mac g esi0 edi0 ret hl trivial
      (by rw [uadd_sem]; simp only [UInt32.reduceToNat]; omega)
    rw [icAdd0, icAdd_add] at R2
    have hk : ∀ j, j < 16 → memByte N2.get (C + (208 + j).toUInt32) =
        memByte (CodeMem.wr1 N _ 0 ok).get (C + (208 + j).toUInt32) := fun j hj => by
      have ea := addr208 hCt j (by omega)
      exact M2.pres.2 _ (by rw [ea, hsz]; omega) (by unfold OutF; rw [ea]; omega)
    have hv1 : v1.toNat = i.toNat + 1 := by rw [ev1, uadd_sem]; simp only [UInt32.reduceToNat]; omega
    have hb2 : ∀ j, num.toNat < j → j ≤ v1.toNat → memByte N2.get (C + (208 + j).toUInt32) = 0 := by
      intro j hj1 hj2
      have ea := addr208 hCt j (by omega)
      rw [hk j (by omega)]
      by_cases hji : j ≤ i.toNat
      · rw [memByte_wr1_other N _ 0 ok (by rw [ea, hs]; omega) (by rw [ea, eq]; omega)]
        exact hb j hj1 hji
      · rw [addr_cj hCt j (by omega) _ (by rw [eq]; omega), memByte_wr1_self]; rfl
    obtain ⟨N3, lU3, a3, g4, R3, M3, L3, hk3, hb3⟩ := ih v1 (icAdd ic0 (1 + 3)) N2 lU2 c1 d1 g3 (by omega)
      (by omega) (by rw [icAdd_toNat _ _ (by omega)]; omega) (M1.join M2 (fun _ h => h.1)) L2 hb2
    rw [icAdd0, icAdd_add, show 1 + 3 + 4 * (r + 1) = 4 * (r + 1 + 1) by omega] at R3
    refine ⟨N3, lU3, a3, g4, R1.trans (R2.trans R3), M3, L3, fun j hj => ?_, hb3⟩
    have ea := addr208 hCt j (by omega)
    rw [hk3 j hj, hk j (by omega), memByte_wr1_other N _ 0 ok (by rw [ea, hs]; omega) (by rw [ea, eq]; omega)]

end Solutions.OpensslPoly1305
