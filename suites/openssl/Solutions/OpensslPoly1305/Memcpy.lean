import Solutions.OpensslPoly1305.McRun
/-!
# `memcpy` as a callee

`memcpy_call`: entered at `0x1005a0` with the stack pointer at `V + 8` (return address, then `dst`,
`src`, `n ≤ 16`), the call returns having copied the `n` bytes from `src` to `dst` and written only
those and its 8 bytes of stack. The byte loop is `mc_cp` (load and store, by `cbv`; the store is
then a `CodeMem.wr1`) and `mc_st`/`mc_sn` (`incl; cmpl; jne`).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Solutions.Exec.Mul Solutions.Exec.Fast
open Solutions.OpensslPoly1305.Cbv Solutions.Logic.Cmp

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option cbv.maxSteps 50000000
set_option exec.addrSub true
set_option autoImplicit false

/-- `movzbl (%edx,%esi), %ebx ; movb %bl, (%eax,%esi)` -/
theorem mc_cp (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (U dst n src b0 ebp0 i edi0 g0 b : UInt32)
    (h1 : N.get.size ≤ ramTop) (hs : src.toNat + i.toNat < N.get.size) (hd : dst.toNat + i.toNat < N.get.size)
    (hb : rdBytes N.get (UInt32.add src i) 1 = b) :
    Run img (St.m ⟨N.get, dst, n, src, b0, U, ebp0, i, edi0, 0x1005c0, efl g0, icAdd ic0 0⟩)
      (St.m ⟨wrBytes N.get (UInt32.add dst i) 1 (UInt32.land b 255), dst, n, src, b, U, ebp0, i, edi0, 0x1005c7,
        efl g0, icAdd ic0 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  cbv

variable {G N : PMem} {U C : UInt32} {nU nC mC : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

theorem memByte_wr1_other (N : PMem) (a v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a) {b : UInt32}
    (hb : b.toNat < N.get.size) (hd : a.toNat ≠ b.toNat) :
    memByte (CodeMem.wr1 N a v ok).get b = memByte N.get b := by
  show (rdBytes (wrBytes N.mem a 1 v) b 1).toUInt8 = (rdBytes N.mem b 1).toUInt8
  rw [rdBytes1_wrBytes1_other ok.1 hb hd]

theorem memByte_wr1_self (N : PMem) (a v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a) :
    memByte (CodeMem.wr1 N a v ok).get a = v.toUInt8 := by
  show (rdBytes (wrBytes N.mem a 1 v) a 1).toUInt8 = _
  rw [rdBytes1_wrBytes1_self ok.1]
  apply UInt8.toNat_inj.1
  simp

/-- A byte store outside the stack region, where `P` does not hold, keeps a `MemOK` without data words. -/
theorem MemOK.st1 (h : MemOK G N U nU lU C nC mC [] P) (a v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a)
    (hU : a.toNat < U.toNat ∨ U.toNat + nU ≤ a.toNat) (hP : ∀ x, P x → x ≠ a.toNat) :
    MemOK G (CodeMem.wr1 N a v ok) U nU lU C nC mC [] P := by
  have hs : (CodeMem.wr1 N a v ok).get.size = N.get.size := wr1_get_size N a v ok
  refine ⟨h.fU.size_eq hs, h.fC.size_eq hs, h.dUC, ?_, Frame.nil _ _ _, ⟨hs.trans h.pres.1, ?_⟩, h.pU, h.pC⟩
  · intro k w hl
    obtain ⟨a1, a2, a3⟩ := h.wU k w hl
    refine ⟨a1, a2, ?_⟩
    have e := Frame.add_toNat h.fU (k := k) (by omega)
    have hf := h.fU.fit
    have hm : N.mem.size = N.get.size := rfl
    rw [← a3]
    show rdBytes (wrBytes N.mem a 1 v) _ 4 = rdBytes N.mem _ 4
    exact rdBytes4_wrBytes1_other ok.1 (by rw [e]; omega) (by rw [e]; omega)
  · intro x hx hp
    rw [← h.pres.2 x hx hp]
    exact memByte_wr1_other N a v ok (by rw [h.pres.1]; exact hx) (fun e => hP _ hp e.symm)

theorem toNat_addk {a : UInt32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + k.toUInt32).toNat = a.toNat + k := by
  rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; omega

/-- Where `memcpy` does not write: outside its stack region and outside the destination. -/
def McP (V dst n : UInt32) (x : Nat) : Prop := OutF V 24 x ∧ (x < dst.toNat ∨ dst.toNat + n.toNat ≤ x)

theorem byte_land (x : UInt8) : (UInt32.land x.toUInt32 255).toUInt8 = x := by
  apply UInt8.toNat_inj.1
  show ((x.toUInt32 &&& 255).toUInt8).toNat = _
  rw [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt8.toNat_toUInt32]
  rw [show (255 : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.toNat_lt; omega

set_option maxHeartbeats 1000000 in
theorem mc_step (G : PMem) (V D dst n src : UInt32) (E : ExtR G (McP V dst n) src n.toNat)
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 24 ≤ dst.toNat)
    (k : Nat) (hk : k < n.toNat) (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (lU : List (Nat × UInt32))
    (b g ebp0 edi0 : UInt32) (hM : MemOK G N V 24 lU D 16 0 [] (McP V dst n))
    (hb : ∀ j, j < k → memByte N.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32)) :
    ∃ (N1 : PMem) (b1 : UInt32),
      Run img (St.m ⟨N.get, dst, n, src, b, V, ebp0, k.toUInt32, edi0, 0x1005c0, efl g, icAdd ic0 0⟩)
        (St.m ⟨N1.get, dst, n, src, b1, V, ebp0, k.toUInt32, edi0, 0x1005c7, efl g, icAdd ic0 2⟩) ∧
      MemOK G N1 V 24 lU D 16 0 [] (McP V dst n) ∧
      ∀ j, j < k + 1 → memByte N1.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32) := by
  have hsz := hM.size
  have top := hM.fU.top
  have hsrc := E.fit
  have hk32 : k < 2 ^ 32 := by have := n.toNat_lt; omega
  have hkt : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have ha_s : (UInt32.add src k.toUInt32).toNat = src.toNat + k := by
    rw [toNat_uadd, hkt]; unfold ramTop at top; omega
  have ha_d : (UInt32.add dst k.toUInt32).toNat = dst.toNat + k := by
    rw [toNat_uadd, hkt]; unfold ramTop at top; omega
  obtain ⟨b0, hb0⟩ : ∃ y, rdBytes N.get (UInt32.add src k.toUInt32) 1 = y := ⟨_, rfl⟩
  have R1 := mc_cp ic0 hic N V dst n src b ebp0 k.toUInt32 edi0 g b0 top (by rw [hkt]; omega)
    (by rw [hkt]; omega) hb0
  have hm : N.mem.size = N.get.size := rfl
  have ok : StoreOk1 Image.base Image.size N.mem (UInt32.add dst k.toUInt32) := by
    refine ⟨by rw [ha_d]; omega, ?_⟩
    rw [ha_d, show Image.base.toNat = 0x100000 from rfl, show Image.size = 1536 from rfl]; omega
  rw [← wr1_get N _ _ ok] at R1
  refine ⟨CodeMem.wr1 N _ _ ok, b0, R1,
    hM.st1 _ _ ok (by rw [ha_d]; omega) (fun x hx => by unfold McP OutF at hx; rw [ha_d]; omega), ?_⟩
  intro j hj
  have hj32 : j < 2 ^ 32 := by have := n.toNat_lt; omega
  have hjt : (j.toUInt32).toNat = j := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  have hdj : (dst + j.toUInt32).toNat = dst.toNat + j := by
    rw [UInt32.toNat_add, hjt]; unfold ramTop at top; omega
  rcases Nat.lt_or_ge j k with hjk | hjk
  · rw [memByte_wr1_other N _ _ ok (by rw [hdj]; omega) (by rw [ha_d, hdj]; omega)]
    exact hb j hjk
  · have : j = k := by omega
    subst this
    show memByte (CodeMem.wr1 N (UInt32.add dst j.toUInt32) _ ok).get (UInt32.add dst j.toUInt32) = _
    rw [memByte_wr1_self]
    have e1 : b0 = (memByte N.get (UInt32.add src j.toUInt32)).toUInt32 := by
      rw [← hb0]; exact rdBytes1_eq (by rw [ha_s]; omega)
    have e2 : memByte N.get (UInt32.add src j.toUInt32) = memByte G.get (UInt32.add src j.toUInt32) :=
      hM.pres.2 _ (by rw [ha_s]; omega) (E.cov _ (by rw [ha_s]; omega) (by rw [ha_s]; omega))
    rw [e1, e2, byte_land]
    rfl

set_option maxHeartbeats 1000000 in
theorem mc_loop (G : PMem) (V D dst n src ret esi0 ebx0 ebp0 edi0 : UInt32)
    (hn : n.toNat ≤ 16) (E : ExtR G (McP V dst n) src n.toNat)
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 24 ≤ dst.toNat) :
    ∀ (r k : Nat) (ic0 : UInt64) (N : PMem) (lU : List (Nat × UInt32)) (i b g : UInt32),
      k + r + 1 = n.toNat → i.toNat = k → ic0.toNat + 5 * (r + 1) < 2 ^ 63 →
      MemOK G N V 24 lU D 16 0 [] (McP V dst n) → LK lU [(0, esi0), (4, ebx0), (8, ret)] →
      (∀ j, j < k → memByte N.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32)) →
      ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (b' i' g' : UInt32),
        Run img (St.m ⟨N.get, dst, n, src, b, V, ebp0, i, edi0, 0x1005c0, efl g, icAdd ic0 0⟩)
          (St.m ⟨N'.get, dst, n, src, b', V, ebp0, i', edi0, 0x1005cc, efl g', icAdd ic0 (5 * (r + 1))⟩) ∧
        MemOK G N' V 24 lU' D 16 0 [] (McP V dst n) ∧ LK lU' [(0, esi0), (4, ebx0), (8, ret)] ∧
        ∀ j, j < n.toNat → memByte N'.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32) := by
  intro r
  induction r with
  | zero =>
    intro k ic0 N lU i b g hk hi hic hM hl hb
    obtain rfl : i = k.toUInt32 := UInt32.toNat_inj.1 (by have := n.toNat_lt; rw [hi, Nat.toUInt32, UInt32.toNat_ofNat']; omega)
    obtain ⟨N1, b1, R1, M1, hb1⟩ := mc_step G V D dst n src E hd hdimg hdV k (by omega) ic0 (by omega) N lU b g
      ebp0 edi0 hM hb
    have hkt : (k.toUInt32).toNat = k := by have := n.toNat_lt; rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    obtain ⟨N2, R2, M2⟩ := mc_sn (icAdd ic0 2) (by rw [icAdd_toNat _ _ (by omega)]; omega) N1 N1 V D lU [] _
      (M1.self (OutF V 24) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      dst n src b1 ebp0 k.toUInt32 edi0 g _ _ _ (by rw [toNat_uadd, hkt]; simp; omega) rfl rfl rfl
    rw [icAdd0, icAdd_add] at R2
    refine ⟨N2, lU, _, _, _, R1.trans R2, M1.join M2 (fun _ h => h.1), hl, fun j hj => ?_⟩
    rw [← hb1 j (by omega)]
    have := M1.fU.top; have := M1.size
    exact M2.pres.2 _ (by rw [M1.size]; have := n.toNat_lt; rw [UInt32.toNat_add, Nat.toUInt32,
      UInt32.toNat_ofNat']; unfold ramTop at *; omega)
      (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
  | succ r ih =>
    intro k ic0 N lU i b g hk hi hic hM hl hb
    obtain rfl : i = k.toUInt32 := UInt32.toNat_inj.1 (by have := n.toNat_lt; rw [hi, Nat.toUInt32, UInt32.toNat_ofNat']; omega)
    obtain ⟨N1, b1, R1, M1, hb1⟩ := mc_step G V D dst n src E hd hdimg hdV k (by omega) ic0 (by omega) N lU b g
      ebp0 edi0 hM hb
    have hkt : (k.toUInt32).toNat = k := by have := n.toNat_lt; rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    have hk1 : (UInt32.add k.toUInt32 1).toNat = k + 1 := by rw [toNat_uadd, hkt]; simp; omega
    obtain ⟨N2, R2, M2⟩ := mc_st (icAdd ic0 2) (by rw [icAdd_toNat _ _ (by omega)]; omega) N1 N1 V D lU [] _
      (M1.self (OutF V 24) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      dst n src b1 ebp0 k.toUInt32 edi0 g _ _ _ (by rw [hk1]; omega) rfl rfl rfl
    rw [icAdd0, icAdd_add] at R2
    have hb2 : ∀ j, j < k + 1 → memByte N2.get (dst + j.toUInt32) = memByte G.get (src + j.toUInt32) := by
      intro j hj
      rw [← hb1 j hj]
      have := M1.fU.top; have := M1.size
      exact M2.pres.2 _ (by rw [M1.size]; have := n.toNat_lt; rw [UInt32.toNat_add, Nat.toUInt32,
        UInt32.toNat_ofNat']; unfold ramTop at *; omega)
        (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
    obtain ⟨N3, lU3, b3, i3, g3, R3, M3, L3, hb3⟩ := ih (k + 1) (icAdd ic0 (2 + 3)) N2 lU (UInt32.add k.toUInt32 1)
      b1 _ (by omega) hk1 (by rw [icAdd_toNat _ _ (by omega)]; omega) (M1.join M2 (fun _ h => h.1)) hl hb2
    rw [icAdd0, icAdd_add, show 2 + 3 + 5 * (r + 1) = 5 * (r + 1 + 1) by omega] at R3
    exact ⟨N3, lU3, b3, i3, g3, R1.trans (R2.trans R3), M3, L3, hb3⟩

/-- The instruction count of `memcpy` of `n` bytes. -/
def mcK (n : Nat) : Nat := if n = 0 then 9 else 23 + 5 * n

set_option maxHeartbeats 1000000 in
theorem memcpy_call (ic0 : UInt64) (G : PMem) (V D dst n src ret a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 : UInt32)
    (lU : List (Nat × UInt32)) (hM : MemOK G G V 24 lU D 16 0 [] (McP V dst n))
    (hlU : LK lU [(8, ret), (12, dst), (16, src), (20, n)])
    (hn : n.toNat ≤ 16) (E : ExtR G (McP V dst n) src n.toNat) (hd : dst.toNat + n.toNat ≤ G.get.size)
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
  · obtain ⟨N1, R1, M1⟩ := mc_p0 ic0 (by omega) G G V D lU [] _ hM a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 n dst src _ _
      (hM.rdU (k := 20) hlU.2.2.2.1 20 rfl) (hM.rdU (k := 12) hlU.2.1 12 rfl) (hM.rdU (k := 16) hlU.2.2.1 16 rfl)
      h0 rfl rfl
    obtain ⟨N2, R2, M2⟩ := mc_p1 ic0 (by omega) G N1 V D _ [] _ M1 dst n src ebx0 ebp0 edi0 _
    obtain ⟨N3, R3, M3⟩ := mc_p2 ic0 (by omega) G N2 V D _ [] _ M2 dst n src ebx0 ebp0 edi0 _
    obtain ⟨N4, lU4, b4, i4, g4, R4, M4, L4, hb4⟩ := mc_loop G V D dst n src ret esi0 ebx0 ebp0 edi0 hn E hd hdimg
      hdV (n.toNat - 1) 0 (icAdd ic0 20) N3 _ 0 ebx0 _ (by omega) rfl
      (by rw [icAdd_toNat _ _ (by omega)]; omega) M3
      ⟨lk_here, lk_skip lk_here rfl, lk_skip (lk_skip hlU.1 rfl) rfl, trivial⟩ (fun j hj => absurd hj (by omega))
    rw [icAdd0, icAdd_add] at R4
    obtain ⟨N5, R5, M5⟩ := mc_e0 (icAdd ic0 (20 + 5 * (n.toNat - 1 + 1)))
      (by rw [icAdd_toNat _ _ (by omega)]; omega) N4 N4 V D _ [] _
      (M4.self (OutF V 24) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      dst n src b4 ebp0 i4 edi0 g4 esi0 ebx0 ret (M4.rdU0 L4.1) (M4.rdU (k := 4) L4.2.1 4 rfl)
      (M4.rdU (k := 8) L4.2.2.1 8 rfl)
    rw [icAdd0, icAdd_add, show 20 + 5 * (n.toNat - 1 + 1) + 3 = mcK n.toNat by simp [mcK, h0]; omega] at R5
    refine ⟨N5, _, _, _, _, _, R1.trans (R2.trans (R3.trans (R4.trans R5))), M4.join M5 (fun _ h => h.1),
      fun j hj => ?_⟩
    rw [← hb4 j hj]
    have := M4.fU.top; have := M4.size; have := n.toNat_lt
    exact M5.pres.2 _ (by rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
      (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)

end Solutions.OpensslPoly1305
