import Solutions.OpensslX25519.I.FeSmallRun
import Solutions.OpensslX25519.I.MemCall
import Solutions.OpensslX25519.I.Cswap
/-!
# `fe_0`, `fe_1`, `fe_copy` as callees

`fe_0(h)` and `fe_1(h)` (`h` in `ecx`) clear the 40 bytes of `h` by `memset` (and `fe_1` then stores
the limb `1`); `fe_copy(h, f)` (`h` in `ecx`, `f` in `edx`) copies them by `memmove`, here for `h` below
`f` (`h + 40 ≤ f`, the forward copy). Each writes only `h` and its stack window (`W` = 20, 24, 24 bytes).
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-! ## Words from bytes -/

theorem rdBytes4_bytes {m1 m2 : ByteArray} {a1 a2 : UInt32} (h1 : a1.toNat + 4 ≤ m1.size)
    (h2 : a2.toNat + 4 ≤ m2.size) (h : ∀ j, j < 4 → m1.get! (a1.toNat + j) = m2.get! (a2.toNat + j)) :
    rdBytes m1 a1 4 = rdBytes m2 a2 4 := by
  rw [rdBytes4_eq h1, rdBytes4_eq h2, h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  have := h 0 (by decide)
  simp only [Nat.add_zero] at this
  rw [this]

theorem memWords_bytes {m1 m2 : ByteArray} {a1 a2 : UInt32} (t1 : m1.size < 2 ^ 32) (t2 : m2.size < 2 ^ 32)
    (h1 : a1.toNat + 40 ≤ m1.size) (h2 : a2.toNat + 40 ≤ m2.size)
    (h : ∀ k, k < 40 → m1.get! (a1.toNat + k) = m2.get! (a2.toNat + k)) :
    memWords m1 a1 10 = memWords m2 a2 10 := by
  unfold memWords
  congr 1
  funext i
  have hi := i.isLt
  have e1 := toNat_add4i (q := a1) (i := i.val) (by omega) (by omega)
  have e2 := toNat_add4i (q := a2) (i := i.val) (by omega) (by omega)
  show rdBytes _ _ 4 = rdBytes _ _ 4
  exact rdBytes4_bytes (by rw [e1]; omega) (by rw [e2]; omega) (fun j hj => by
    rw [e1, e2, Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega))

theorem get!_of_memByte {m : ByteArray} {a : UInt32} (t : m.size < 2 ^ 32) (k : Nat) (hk : a.toNat + k < m.size) :
    m.get! (a.toNat + k) = memByte m (a + k.toUInt32) := by
  have e : (a + k.toUInt32).toNat = a.toNat + k := by
    rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; omega
  rw [memByte_def (by rw [e]; exact hk), e]

theorem memWords_zero {m : ByteArray} {a : UInt32} (t : m.size < 2 ^ 32) (h1 : a.toNat + 40 ≤ m.size)
    (h : ∀ b : UInt32, a.toNat ≤ b.toNat → b.toNat < a.toNat + 40 → memByte m b = 0) :
    memWords m a 10 = #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  apply Array.ext (by simp [memWords])
  intro i hi _
  simp only [memWords, Array.getElem_ofFn]
  have hi' : i < 10 := by simpa [memWords] using hi
  have e1 := toNat_add4i (q := a) (i := i) (by omega) (by omega)
  show rdBytes _ _ 4 = _
  rw [rdBytes4_eq (by rw [e1]; omega)]
  have z : ∀ j, j < 4 → m.get! ((a + 4 * i.toUInt32).toNat + j) = 0 := by
    intro j hj
    rw [get!_of_memByte t _ (by rw [e1]; omega)]
    have e : (a + 4 * i.toUInt32 + j.toUInt32).toNat = a.toNat + 4 * i + j := by
      rw [UInt32.toNat_add, e1, Nat.toUInt32, UInt32.toNat_ofNat']; omega
    exact h _ (by rw [e]; omega) (by rw [e]; omega)
  have z0 := z 0 (by decide)
  simp only [Nat.add_zero] at z0
  rw [z0, z 1 (by decide), z 2 (by decide), z 3 (by decide)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## `fe_0` -/

theorem fe_0_call (G : XMem) (sp hp ret : UInt32) (F : Facts1W 20 G.get.size sp.toNat hp.toNat hp.toNat)
    (hret0 : rdRaw G.get sp 4 = ret) (a0 edx0 ebx0 ebp0 esi0 edi0 fl0 : UInt32)
    (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 62) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, hp, edx0, ebx0, sp, ebp0, esi0, edi0, 0x1021e0, efl fl0, ic0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, sp + 4, ebp0, esi0, edi0, ret, efl fl, icAdd ic0 188⟩) ∧
      Pres G N (OutH (sp - 20) 20 hp) ∧ memWords N.get hp 10 = #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  have htop : G.get.size ≤ ramTop := F.ram
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = sp - (20 : Nat).toUInt32 := ⟨_, rfl⟩
  have hLN : L.toNat = sp.toNat - 20 := by rw [hL]; exact fb_toNatW F.sp_lo 20 (by decide)
  have hspL : sp = UInt32.add L 20 := by
    apply UInt32.toNat_inj.1; rw [toNat_uadd, hLN]; have := F.sp_lo; have := sp.toNat_lt
    simp only [UInt32.reduceToNat]; omega
  have hS : FB G.get.size L 24 := ⟨htop, by have := F.sp_hi; have := F.sp_lo; omega,
    by have := F.sp_img; have := F.sp_lo; omega⟩
  have F0 : Frame G L 24 [(20, ret)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl
      refine ⟨rfl, by decide, ?_⟩
      rw [show UInt32.add L (20 : Nat).toUInt32 = sp from hspL.symm]; exact hret0
    · simp at hl
  have e0 : St.m ⟨G.get, a0, hp, edx0, ebx0, sp, ebp0, esi0, edi0, 0x1021e0, efl fl0, ic0⟩ =
      St.m ⟨G.get, a0, hp, edx0, ebx0, UInt32.add L 20, ebp0, esi0, edi0, 0x1021e0, efl fl0, icAdd ic0 0⟩ := by
    rw [← hspL]; rfl
  rw [e0]
  have R1 := f0_a ic0 (by omega) G L hS a0 hp edx0 ebx0 ebp0 esi0 edi0 fl0
  have F1 := (((F0.wrF 16 (j := 16) (v := 40) (h := hS) (hj := by decide) rfl rfl).wrF 12 (j := 12) (v := 0)
    (h := stF_FB) (hj := by decide) rfl rfl).wrF 8 (j := 8) (v := hp) (h := stF_FB) (hj := by decide) rfl rfl).wrF 4
    (j := 4) (v := 0x1021ea) (h := stF_FB) (hj := by decide) rfl rfl
  generalize hM1 : (stF (stF (stF (stF G L 24 16 40 hS (by decide)) L 24 12 0 stF_FB (by decide)) L 24 8 hp stF_FB
    (by decide)) L 24 4 0x1021ea stF_FB (by decide)) = M1 at R1 F1
  have P1 : Pres G M1 (OutF L 20) := by
    rw [← hM1]
    exact (((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))
  have hS1 : FB M1.get.size L 20 := ⟨by rw [P1.1]; exact htop, by rw [P1.1]; have := F.sp_hi; have := F.sp_lo; omega,
    by have := F.sp_img; have := F.sp_lo; omega⟩
  have hH := F.h_stk
  have hsp20 := F.sp_lo
  have h20 : (20 : UInt32).toNat = 20 := rfl
  have h40 : (40 : UInt32).toNat = 40 := rfl
  obtain ⟨N2, eax2, ecx2, edx2, fl2, R2, P2, B2⟩ := memset_call M1 L 0x1021ea hp 0 40 a0 hp edx0 ebx0 ebp0 esi0
    edi0 fl0 (icAdd ic0 4) hS1 (F1.rd (rfl : List.lookup 4 _ = some _) 4 rfl)
    (F1.rd (rfl : List.lookup 8 _ = some _) 8 rfl) (F1.rd (rfl : List.lookup 12 _ = some _) 12 rfl)
    (F1.rd (rfl : List.lookup 16 _ = some _) 16 rfl) (by decide) (by rw [P1.1]; exact F.h_mem)
    (by have := F.h_img; rw [h40]; omega) (by rw [h40]; omega) (by rw [icAdd_toNat _ _ (by omega)]; simp; omega)
  have e2 : icAdd (icAdd ic0 4) (4 * (40 : UInt32).toNat + 22) = icAdd ic0 186 := by rw [icAdd_add]; rfl
  rw [e2] at R2
  have R3 := f0_b (icAdd ic0 186) (by rw [icAdd_toNat _ _ (by omega)]; omega) N2 L (hS.pres (P1.trans P2))
    eax2 ecx2 edx2 ebx0 ebp0 esi0 edi0 fl2
  simp only [icAdd_add] at R3
  have hr2 : rdRaw N2.get (UInt32.add L 20) 4 = ret := by
    have e20 := hS.add_toNat (j := 20) (by decide)
    rw [P2.rd' (by rw [P1.1]; exact htop) (by rw [P1.1, e20, h20]; have := hS.fit; omega)
      (fun k hk => by rw [e20, h20, h40]; omega)]
    exact F1.rd (rfl : List.lookup 20 _ = some _) 20 rfl
  have hc187 : (icAdd (icAdd ic0 186) 1).toNat < 2 ^ 63 := by
    rw [icAdd_add, icAdd_toNat _ _ (by omega)]; omega
  have R4 := f0_c (icAdd (icAdd ic0 186) 1) hc187 N2 L (hS.pres (P1.trans P2)) eax2 ecx2 edx2 ebx0 ebp0 esi0 edi0
    (addF 4 (UInt32.add L 8) 12 0).2 ret hr2
  simp only [icAdd_add] at R4
  have hesp : UInt32.add L 24 = sp + 4 := by
    rw [hspL]; apply UInt32.toNat_inj.1
    rw [toNat_uadd, UInt32.toNat_add, toNat_uadd]
    have := hS.fit; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
  rw [hesp] at R4
  refine ⟨N2, _, _, _, _, R1.trans (R2.trans (R3.trans R4)), (P1.trans P2).mono fun x hx => ?_, ?_⟩
  · have hsL : (sp - 20).toNat = L.toNat := by rw [hL]; rfl
    unfold OutH OutF at hx; unfold OutF
    rw [hsL] at hx; rw [h40]; omega
  · have hsz : N2.get.size = G.get.size := (P1.trans P2).1
    exact memWords_zero (by rw [hsz]; exact hT) (by rw [hsz]; exact F.h_mem)
      (fun b h1 h2 => by rw [B2 b h1 (by rw [h40]; exact h2)]; decide)

/-! ## `fe_1` -/

theorem fe_1_call (G : XMem) (sp hp ret : UInt32) (F : Facts1W 24 G.get.size sp.toNat hp.toNat hp.toNat)
    (hret0 : rdRaw G.get sp 4 = ret) (a0 edx0 ebx0 ebp0 esi0 edi0 fl0 : UInt32)
    (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 62) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, hp, edx0, ebx0, sp, ebp0, esi0, edi0, 0x1021f0, efl fl0, ic0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, sp + 4, ebp0, esi0, edi0, ret, efl fl, icAdd ic0 192⟩) ∧
      Pres G N (OutH (sp - 24) 24 hp) ∧ memWords N.get hp 10 = #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  have htop : G.get.size ≤ ramTop := F.ram
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  have hsp24 := F.sp_lo
  have h20 : (20 : UInt32).toNat = 20 := rfl
  have h24 : (24 : UInt32).toNat = 24 := rfl
  have h40 : (40 : UInt32).toNat = 40 := rfl
  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = sp - (24 : Nat).toUInt32 := ⟨_, rfl⟩
  have hLN : L.toNat = sp.toNat - 24 := by rw [hL]; exact fb_toNatW F.sp_lo 24 (by decide)
  have hspL : sp = UInt32.add L 24 := by
    apply UInt32.toNat_inj.1; rw [toNat_uadd, hLN]; have := sp.toNat_lt
    simp only [UInt32.reduceToNat]; omega
  have hS : FB G.get.size L 28 := ⟨htop, by have := F.sp_hi; omega, by have := F.sp_img; omega⟩
  have F0 : Frame G L 28 [(24, ret)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl
      refine ⟨rfl, by decide, ?_⟩
      rw [show UInt32.add L (24 : Nat).toUInt32 = sp from hspL.symm]; exact hret0
    · simp at hl
  have e0 : St.m ⟨G.get, a0, hp, edx0, ebx0, sp, ebp0, esi0, edi0, 0x1021f0, efl fl0, ic0⟩ =
      St.m ⟨G.get, a0, hp, edx0, ebx0, UInt32.add L 24, ebp0, esi0, edi0, 0x1021f0, efl fl0, icAdd ic0 0⟩ := by
    rw [← hspL]; rfl
  rw [e0]
  have R1 := f1_a ic0 (by omega) G L hS a0 hp edx0 ebx0 ebp0 esi0 edi0 fl0
  have F1 := (F0.wrF 20 (j := 20) (v := esi0) (h := hS) (hj := by decide) rfl rfl).wrF 16 (j := 16) (v := 40)
    (h := stF_FB) (hj := by decide) rfl rfl
  generalize hM1 : stF (stF G L 28 20 esi0 hS (by decide)) L 28 16 40 stF_FB (by decide) = M1 at R1 F1
  have P1 : Pres G M1 (OutF L 24) := by
    rw [← hM1]; exact ((Pres.refl G _).wrF (by decide)).wrF (by decide)
  have hS1 : FB M1.get.size L 28 := hS.pres P1
  have R2 := f1_b (icAdd ic0 3) (by rw [icAdd_toNat _ _ (by omega)]; omega) M1 L hS1 a0 hp edx0 ebx0 ebp0 hp edi0 fl0
  simp only [icAdd_add] at R2
  have F2 := ((F1.wrF 12 (j := 12) (v := 0) (h := hS1) (hj := by decide) rfl rfl).wrF 8 (j := 8) (v := hp)
    (h := stF_FB) (hj := by decide) rfl rfl).wrF 4 (j := 4) (v := 0x1021fd) (h := stF_FB) (hj := by decide) rfl rfl
  generalize hM2 : stF (stF (stF M1 L 28 12 0 hS1 (by decide)) L 28 8 hp stF_FB (by decide)) L 28 4 0x1021fd
    stF_FB (by decide) = M2 at R2 F2
  have P2 : Pres M1 M2 (OutF L 24) := by
    rw [← hM2]; exact (((Pres.refl M1 _).wrF (by decide)).wrF (by decide)).wrF (by decide)
  have hS2 : FB M2.get.size L 20 := ⟨by rw [P2.1, P1.1]; exact htop, by rw [P2.1, P1.1]; have := F.sp_hi; omega,
    by have := F.sp_img; omega⟩
  have hH := F.h_stk
  obtain ⟨N3, eax3, ecx3, edx3, fl3, R3, P3, B3⟩ := memset_call M2 L 0x1021fd hp 0 40 a0 hp edx0 ebx0 ebp0 hp
    edi0 fl0 (icAdd ic0 (3 + 3)) hS2 (F2.rd (rfl : List.lookup 4 _ = some _) 4 rfl)
    (F2.rd (rfl : List.lookup 8 _ = some _) 8 rfl) (F2.rd (rfl : List.lookup 12 _ = some _) 12 rfl)
    (F2.rd (rfl : List.lookup 16 _ = some _) 16 rfl) (by decide) (by rw [P2.1, P1.1]; exact F.h_mem)
    (by have := F.h_img; rw [h40]; omega) (by rw [h40]; omega) (by rw [icAdd_toNat _ _ (by omega)]; rw [h40]; omega)
  simp only [icAdd_add] at R3
  have P13 := (P1.trans P2).trans P3
  have R4 := f1_c (icAdd ic0 (3 + 3 + (4 * (40 : UInt32).toNat + 22))) (by rw [icAdd_toNat _ _ (by rw [h40]; omega)]; rw [h40]; omega)
    N3 L (hS.pres P13) eax3 ecx3 edx3 ebx0 ebp0 hp edi0 fl3
  simp only [icAdd_add] at R4
  have e20 := hS.add_toNat (j := 20) (by decide)
  have e24 := hS.add_toNat (j := 24) (by decide)
  have l0 : rdRaw N3.get (UInt32.add L 20) 4 = esi0 := by
    rw [P3.rd' (by rw [P2.1, P1.1]; exact htop) (by rw [P2.1, P1.1, e20, h20]; have := hS.fit; omega)
      (fun k hk => by rw [e20, h20, h40]; omega)]
    exact F2.rd (rfl : List.lookup 20 _ = some _) 20 rfl
  have lr : rdRaw N3.get (UInt32.add L 24) 4 = ret := by
    rw [P3.rd' (by rw [P2.1, P1.1]; exact htop) (by rw [P2.1, P1.1, e24, h24]; have := hS.fit; omega)
      (fun k hk => by rw [e24, h24, h40]; omega)]
    exact F2.rd (rfl : List.lookup 24 _ = some _) 24 rfl
  have hsz3 : N3.get.size = G.get.size := P13.1
  have hH3 : FB N3.get.size hp 40 := ⟨by rw [hsz3]; exact htop, by rw [hsz3]; exact F.h_mem, F.h_img⟩
  have R5 := f1_d (icAdd ic0 (3 + 3 + (4 * (40 : UInt32).toNat + 22) + 1))
    (by rw [icAdd_toNat _ _ (by rw [h40]; omega)]; rw [h40]; omega) N3 L hp (hS.pres P13) hH3 (by omega)
    eax3 ecx3 edx3 ebx0 ebp0 edi0 (addF 4 (UInt32.add L 8) 12 0).2 esi0 ret l0 lr
  simp only [icAdd_add] at R5
  have hesp : UInt32.add L 28 = sp + 4 := by
    rw [hspL]; apply UInt32.toNat_inj.1
    rw [toNat_uadd, UInt32.toNat_add, toNat_uadd]
    have := hS.fit; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
  rw [hesp] at R5
  have hsL : (sp - 24).toNat = L.toNat := by rw [hL]; rfl
  have P4 : Pres G N3 (OutH (sp - 24) 24 hp) := P13.mono fun x hx => by
    unfold OutH OutF at hx; unfold OutF; rw [hsL] at hx; rw [h40]; omega
  refine ⟨_, _, _, _, _, R1.trans (R2.trans (R3.trans (R4.trans R5))), P4.wrH0, ?_⟩
  have hz := memWords_zero (by rw [hsz3]; exact hT) (by rw [hsz3]; exact F.h_mem)
      (fun b h1 h2 => by rw [B3 b h1 (by rw [h40]; exact h2)]; decide)
  have F5 := (frame10 N3 hp _ hz).wrF0 (v := 1) (h := hH3) (hn := by decide)
  rw [memWords_frame F5 (fun i => if i = 0 then 1 else 0) (fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)]
  rfl

/-! ## `fe_copy` -/

/-- `fe_copy(h, f)` with `h` below `f` (`h + 40 ≤ f`): the limbs of `f`. -/
theorem fe_copy_call (G : XMem) (sp hp fp ret : UInt32) (F : Facts1W 24 G.get.size sp.toNat hp.toNat fp.toNat)
    (hhf : hp.toNat + 40 ≤ fp.toNat) (hret0 : rdRaw G.get sp 4 = ret) (a0 ebx0 ebp0 esi0 edi0 fl0 : UInt32)
    (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 62) :
    ∃ (N : XMem) (eax ecx edx fl : UInt32),
      Run img (St.m ⟨G.get, a0, hp, fp, ebx0, sp, ebp0, esi0, edi0, 0x102280, efl fl0, ic0⟩)
        (St.m ⟨N.get, eax, ecx, edx, ebx0, sp + 4, ebp0, esi0, edi0, ret, efl fl, icAdd ic0 229⟩) ∧
      Pres G N (OutH (sp - 24) 24 hp) ∧ memWords N.get hp 10 = memWords G.get fp 10 := by
  have htop : G.get.size ≤ ramTop := F.ram
  have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  have hsp24 := F.sp_lo
  have h24 : (24 : UInt32).toNat = 24 := rfl
  have h40 : (40 : UInt32).toNat = 40 := rfl
  obtain ⟨L, hL⟩ : ∃ L : UInt32, L = sp - (24 : Nat).toUInt32 := ⟨_, rfl⟩
  have hLN : L.toNat = sp.toNat - 24 := by rw [hL]; exact fb_toNatW F.sp_lo 24 (by decide)
  have hspL : sp = UInt32.add L 24 := by
    apply UInt32.toNat_inj.1; rw [toNat_uadd, hLN]; have := sp.toNat_lt
    simp only [UInt32.reduceToNat]; omega
  have hS : FB G.get.size L 28 := ⟨htop, by have := F.sp_hi; omega, by have := F.sp_img; omega⟩
  have F0 : Frame G L 28 [(24, ret)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl
      refine ⟨rfl, by decide, ?_⟩
      rw [show UInt32.add L (24 : Nat).toUInt32 = sp from hspL.symm]; exact hret0
    · simp at hl
  have e0 : St.m ⟨G.get, a0, hp, fp, ebx0, sp, ebp0, esi0, edi0, 0x102280, efl fl0, ic0⟩ =
      St.m ⟨G.get, a0, hp, fp, ebx0, UInt32.add L 24, ebp0, esi0, edi0, 0x102280, efl fl0, icAdd ic0 0⟩ := by
    rw [← hspL]; rfl
  rw [e0]
  have R1 := fc_a ic0 (by omega) G L hS a0 hp fp ebx0 ebp0 esi0 edi0 fl0
  have F1 := (((F0.wrF 20 (j := 20) (v := 40) (h := hS) (hj := by decide) rfl rfl).wrF 16 (j := 16) (v := fp)
    (h := stF_FB) (hj := by decide) rfl rfl).wrF 12 (j := 12) (v := hp) (h := stF_FB) (hj := by decide) rfl rfl).wrF 8
    (j := 8) (v := 0x102289) (h := stF_FB) (hj := by decide) rfl rfl
  generalize hM1 : (stF (stF (stF (stF G L 28 20 40 hS (by decide)) L 28 16 fp stF_FB (by decide)) L 28 12 hp stF_FB
    (by decide)) L 28 8 0x102289 stF_FB (by decide)) = M1 at R1 F1
  have P1 : Pres G M1 (OutF L 24) := by
    rw [← hM1]
    exact (((((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF (by decide)).wrF (by decide))
  have hS1 : FB M1.get.size L 24 := ⟨by rw [P1.1]; exact htop, by rw [P1.1]; have := F.sp_hi; omega,
    by have := F.sp_img; omega⟩
  have hH := F.h_stk
  have hFs := F.f_stk
  obtain ⟨N2, eax2, ecx2, edx2, fl2, R2, P2, B2⟩ := memmove_call M1 L 0x102289 hp fp 40 a0 hp fp ebx0 ebp0 esi0
    edi0 fl0 (icAdd ic0 4) hS1 (F1.rd (rfl : List.lookup 8 _ = some _) 8 rfl)
    (F1.rd (rfl : List.lookup 12 _ = some _) 12 rfl) (F1.rd (rfl : List.lookup 16 _ = some _) 16 rfl)
    (F1.rd (rfl : List.lookup 20 _ = some _) 20 rfl) (by decide) (by rw [P1.1, h40]; exact F.h_mem)
    (by rw [P1.1, h40]; exact F.f_mem) (by have := F.h_img; rw [h40]; omega) (by have := F.f_img; rw [h40]; omega)
    (by rw [h40]; exact hhf) (by rw [h40]; omega) (by rw [h40]; omega)
    (by rw [icAdd_toNat _ _ (by omega)]; rw [h40]; omega)
  simp only [icAdd_add] at R2
  have P12 := P1.trans P2
  have R3 := fc_b (icAdd ic0 (4 + (5 * (40 : UInt32).toNat + 23)))
    (by rw [icAdd_toNat _ _ (by rw [h40]; omega)]; rw [h40]; omega) N2 L (hS.pres P12) eax2 ecx2 edx2 ebx0 ebp0 esi0
    edi0 fl2
  simp only [icAdd_add] at R3
  have e24 := hS.add_toNat (j := 24) (by decide)
  have lr : rdRaw N2.get (UInt32.add L 24) 4 = ret := by
    rw [P2.rd' (by rw [P1.1]; exact htop) (by rw [P1.1, e24, h24]; have := hS.fit; omega)
      (fun k hk => by rw [e24, h24, h40]; omega)]
    exact F1.rd (rfl : List.lookup 24 _ = some _) 24 rfl
  have R4 := fc_c (icAdd ic0 (4 + (5 * (40 : UInt32).toNat + 23) + 1))
    (by rw [icAdd_toNat _ _ (by rw [h40]; omega)]; rw [h40]; omega) N2 L (hS.pres P12) eax2 ecx2 edx2 ebx0 ebp0 esi0
    edi0 (addF 4 (UInt32.add L 12) 12 0).2 ret lr
  simp only [icAdd_add] at R4
  have hesp : UInt32.add L 28 = sp + 4 := by
    rw [hspL]; apply UInt32.toNat_inj.1
    rw [toNat_uadd, UInt32.toNat_add, toNat_uadd]
    have := hS.fit; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
  rw [hesp] at R4
  have hsL : (sp - 24).toNat = L.toNat := by rw [hL]; rfl
  refine ⟨_, _, _, _, _, R1.trans (R2.trans (R3.trans R4)), P12.mono fun x hx => ?_, ?_⟩
  · unfold OutH OutF at hx; unfold OutF; rw [hsL] at hx; rw [h40]; omega
  · have hsz : N2.get.size = G.get.size := P12.1
    apply memWords_bytes (by rw [hsz]; exact hT) hT (by rw [hsz]; exact F.h_mem) F.f_mem
    intro k hk
    have hk32 : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    have ea : (hp + k.toUInt32).toNat = hp.toNat + k := by
      rw [UInt32.toNat_add, hk32]; have := F.h_mem; omega
    have eb : (fp + k.toUInt32).toNat = fp.toNat + k := by
      rw [UInt32.toNat_add, hk32]; have := F.f_mem; omega
    rw [get!_of_memByte (by rw [hsz]; exact hT) k (by rw [hsz]; have := F.h_mem; omega),
      get!_of_memByte hT k (by have := F.f_mem; omega)]
    have b2 := B2 k (by rw [h40]; exact hk)
    have u1 : UInt32.add hp k.toUInt32 = hp + k.toUInt32 := rfl
    have u2 : UInt32.add fp k.toUInt32 = fp + k.toUInt32 := rfl
    rw [u1, u2] at b2
    rw [b2]
    exact P1.2 _ (by rw [eb]; have := F.f_mem; omega) (by unfold OutF; rw [eb]; omega)

end Solutions.OpensslX25519.I
