import Solutions.OpensslPoly1305.MsRun
import Solutions.OpensslPoly1305.Memcpy
/-!
# `memset` as a callee

`memset_call`: entered at `0x1005d0` with the stack pointer at `V + 4` (return address, then `dst`,
the byte `cv`, `n`), the call returns having set the `n` bytes from `dst` to `cv`'s low byte and
written only those and its 4 bytes of stack.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Solutions.Exec.Mul Solutions.Exec.Fast
open Solutions.OpensslPoly1305.Cbv Solutions.Logic.Cmp

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option cbv.maxSteps 50000000
set_option exec.addrSub true
set_option autoImplicit false

/-- `movb %dl, (%esi)` -/
theorem ms_cp (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (U a0 k cv ebx0 ebp0 q edi0 g0 : UInt32)
    (h1 : N.get.size ≤ ramTop) (hq : q.toNat < N.get.size) :
    Run img (St.m ⟨N.get, a0, k, cv, ebx0, U, ebp0, q, edi0, 0x1005f0, efl g0, icAdd ic0 0⟩)
      (St.m ⟨wrBytes N.get q 1 (UInt32.land cv 255), a0, k, cv, ebx0, U, ebp0, q, edi0, 0x1005f2,
        efl g0, icAdd ic0 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  cbv

/-- Where `memset` does not write. -/
def MsP (V dst n : UInt32) (x : Nat) : Prop := OutF V 20 x ∧ (x < dst.toNat ∨ dst.toNat + n.toNat ≤ x)

set_option maxHeartbeats 1000000 in
theorem ms_store (G : PMem) (V D dst n cv a0 ebx0 ebp0 edi0 : UInt32)
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 20 ≤ dst.toNat)
    (i : Nat) (hi : i < n.toNat) (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : PMem) (lU : List (Nat × UInt32))
    (q k g : UInt32) (hq : q.toNat = dst.toNat + i) (hM : MemOK G N V 20 lU D 236 0 [] (MsP V dst n))
    (hb : ∀ j, j < i → memByte N.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8) :
    ∃ N1 : PMem, MemOK G N1 V 20 lU D 236 0 [] (MsP V dst n) ∧
      Run img (St.m ⟨N.get, a0, k, cv, ebx0, V, ebp0, q, edi0, 0x1005f0, efl g, icAdd ic0 0⟩)
        (St.m ⟨N1.get, a0, k, cv, ebx0, V, ebp0, q, edi0, 0x1005f2, efl g, icAdd ic0 1⟩) ∧
      ∀ j, j < i + 1 → memByte N1.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8 := by
  have hsz := hM.size
  have top := hM.fU.top
  have hm : N.mem.size = N.get.size := rfl
  have R := ms_cp ic0 hic N V a0 k cv ebx0 ebp0 q edi0 g top (by omega)
  have ok : StoreOk1 Image.base Image.size N.mem q := by
    refine ⟨by omega, ?_⟩
    rw [show Image.base.toNat = 0x100000 from rfl, show Image.size = 1536 from rfl]; omega
  rw [← wr1_get N _ _ ok] at R
  refine ⟨CodeMem.wr1 N _ _ ok, hM.st1 _ _ ok (by omega) (fun x hx => by unfold MsP OutF at hx; omega), R, ?_⟩
  intro j hj
  have hj32 : j < 2 ^ 32 := by have := n.toNat_lt; omega
  have hdj : (dst + j.toUInt32).toNat = dst.toNat + j := by
    rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at top; omega
  rcases Nat.lt_or_ge j i with hji | hji
  · rw [memByte_wr1_other N _ _ ok (by rw [hdj]; omega) (by rw [hdj]; omega)]
    exact hb j hji
  · have e : dst + j.toUInt32 = q := UInt32.toNat_inj.1 (by rw [hdj]; omega)
    rw [e, memByte_wr1_self]

set_option maxHeartbeats 1000000 in
theorem ms_loop (G : PMem) (V D dst n cv ret esi0 ebx0 ebp0 edi0 a0 : UInt32)
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 20 ≤ dst.toNat) :
    ∀ (r i : Nat) (ic0 : UInt64) (N : PMem) (lU : List (Nat × UInt32)) (q k g : UInt32),
      i + r + 1 = n.toNat → q.toNat = dst.toNat + i → k.toNat = r + 1 → ic0.toNat + 4 * (r + 1) < 2 ^ 63 →
      MemOK G N V 20 lU D 236 0 [] (MsP V dst n) → LK lU [(0, esi0), (4, ret)] →
      (∀ j, j < i → memByte N.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8) →
      ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (k' q' g' : UInt32),
        Run img (St.m ⟨N.get, a0, k, cv, ebx0, V, ebp0, q, edi0, 0x1005f0, efl g, icAdd ic0 0⟩)
          (St.m ⟨N'.get, a0, k', cv, ebx0, V, ebp0, q', edi0, 0x1005f6, efl g', icAdd ic0 (4 * (r + 1))⟩) ∧
        MemOK G N' V 20 lU' D 236 0 [] (MsP V dst n) ∧ LK lU' [(0, esi0), (4, ret)] ∧
        ∀ j, j < n.toNat → memByte N'.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8 := by
  intro r
  induction r with
  | zero =>
    intro i ic0 N lU q k g hi hq hk hic hM hl hb
    obtain ⟨N1, M1, R1, hb1⟩ := ms_store G V D dst n cv a0 ebx0 ebp0 edi0 hd hdimg hdV i (by omega) ic0 (by omega)
      N lU q k g hq hM hb
    obtain ⟨N2, R2, M2⟩ := ms_sn (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega) N1 N1 V D lU [] _
      (M1.self (OutF V 20) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      a0 k cv ebx0 ebp0 q edi0 g _ _ _ _ (by omega) rfl rfl rfl rfl
    rw [icAdd0, icAdd_add] at R2
    refine ⟨N2, lU, _, _, _, R1.trans R2, M1.join M2 (fun _ h => h.1), hl, fun j hj => ?_⟩
    rw [← hb1 j (by omega)]
    have := M1.fU.top; have := M1.size; have := n.toNat_lt
    exact M2.pres.2 _ (by rw [M1.size]; rw [UInt32.toNat_add, Nat.toUInt32,
      UInt32.toNat_ofNat']; unfold ramTop at *; omega)
      (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
  | succ r ih =>
    intro i ic0 N lU q k g hi hq hk hic hM hl hb
    obtain ⟨N1, M1, R1, hb1⟩ := ms_store G V D dst n cv a0 ebx0 ebp0 edi0 hd hdimg hdV i (by omega) ic0 (by omega)
      N lU q k g hq hM hb
    obtain ⟨N2, R2, M2⟩ := ms_st (icAdd ic0 1) (by rw [icAdd_toNat _ _ (by omega)]; omega) N1 N1 V D lU [] _
      (M1.self (OutF V 20) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      a0 k cv ebx0 ebp0 q edi0 g _ _ _ _ (by omega) rfl rfl rfl rfl
    rw [icAdd0, icAdd_add] at R2
    have hb2 : ∀ j, j < i + 1 → memByte N2.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8 := by
      intro j hj
      rw [← hb1 j hj]
      have := M1.fU.top; have := M1.size; have := n.toNat_lt
      exact M2.pres.2 _ (by rw [M1.size]; rw [UInt32.toNat_add, Nat.toUInt32,
        UInt32.toNat_ofNat']; unfold ramTop at *; omega)
        (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
    have top := M1.fU.top; have := M1.size
    obtain ⟨N3, lU3, k3, q3, g3, R3, M3, L3, hb3⟩ := ih (i + 1) (icAdd ic0 (1 + 3)) N2 lU (UInt32.add q 1)
      (UInt32.add k 4294967295) _ (by omega) (by rw [toNat_uadd, hq]; unfold ramTop at top; simp; omega)
      (by have := k.toNat_lt; rw [toNat_uadd, hk]; simp; omega) (by rw [icAdd_toNat _ _ (by omega)]; omega)
      (M1.join M2 (fun _ h => h.1)) hl hb2
    rw [icAdd0, icAdd_add, show 1 + 3 + 4 * (r + 1) = 4 * (r + 1 + 1) by omega] at R3
    exact ⟨N3, lU3, k3, q3, g3, R1.trans (R2.trans R3), M3, L3, hb3⟩

/-- The instruction count of `memset` of `n` bytes. -/
def msK (n : Nat) : Nat := if n = 0 then 7 else 22 + 4 * n

set_option maxHeartbeats 1000000 in
theorem memset_call (ic0 : UInt64) (G : PMem) (V D dst n cv ret a0 c0 d0 ebx0 esi0 edi0 ebp0 g0 : UInt32)
    (lU : List (Nat × UInt32)) (hM : MemOK G G V 20 lU D 236 0 [] (MsP V dst n))
    (hlU : LK lU [(4, ret), (8, dst), (12, cv), (16, n)])
    (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdimg : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 1536 ≤ dst.toNat)
    (hdV : dst.toNat + n.toNat ≤ V.toNat ∨ V.toNat + 20 ≤ dst.toNat) (hic : ic0.toNat + 22 + 4 * n.toNat < 2 ^ 63) :
    ∃ (N' : PMem) (lU' : List (Nat × UInt32)) (eax ecx edx gf : UInt32),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add V 4, ebp0, esi0, edi0, 0x1005d0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add V 8, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (msK n.toNat)⟩) ∧
      MemOK G N' V 20 lU' D 236 0 [] (MsP V dst n) ∧
      ∀ j, j < n.toNat → memByte N'.get (dst + j.toUInt32) = (UInt32.land cv 255).toUInt8 := by
  by_cases h0 : n.toNat = 0
  · obtain ⟨N1, R1, M1⟩ := ms_z0 ic0 (by omega) G G V D lU [] _ hM a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 n dst _
      (hM.rdU (k := 16) hlU.2.2.2.1 16 rfl) (hM.rdU (k := 8) hlU.2.1 8 rfl) h0 rfl
    obtain ⟨N2, R2, M2⟩ := ms_e0 (icAdd ic0 5) (by rw [icAdd_toNat _ _ (by omega)]; omega) G N1 V D _ [] _ M1
      dst n d0 ebx0 ebp0 esi0 edi0 _ esi0 ret (M1.rdU0 lk_here) (M1.rdU (k := 4) (lk_skip hlU.1 rfl) 4 rfl)
    rw [icAdd0, icAdd_add, show 5 + 2 = msK n.toNat by simp [msK, h0]] at R2
    exact ⟨N2, _, _, _, _, _, R1.trans R2, M2, fun j hj => absurd hj (by omega)⟩
  · obtain ⟨N1, R1, M1⟩ := ms_p0 ic0 (by omega) G G V D lU [] _ hM a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 n dst cv _
      (hM.rdU (k := 16) hlU.2.2.2.1 16 rfl) (hM.rdU (k := 8) hlU.2.1 8 rfl) (hM.rdU (k := 12) hlU.2.2.1 12 rfl)
      h0 rfl
    obtain ⟨N2, R2, M2⟩ := ms_p1 ic0 (by omega) G N1 V D _ [] _ M1 dst n cv ebx0 ebp0 edi0 _
    obtain ⟨N3, R3, M3⟩ := ms_p2 ic0 (by omega) G N2 V D _ [] _ M2 dst n cv ebx0 ebp0 edi0 _
    obtain ⟨N4, lU4, k4, q4, g4, R4, M4, L4, hb4⟩ := ms_loop G V D dst n cv ret esi0 ebx0 ebp0 edi0 dst hd hdimg
      hdV (n.toNat - 1) 0 (icAdd ic0 20) N3 _ dst n _ (by omega) (by omega) (by omega)
      (by rw [icAdd_toNat _ _ (by omega)]; omega) M3
      ⟨lk_here, lk_skip hlU.1 rfl, trivial⟩ (fun j hj => absurd hj (by omega))
    rw [icAdd0, icAdd_add] at R4
    obtain ⟨N5, R5, M5⟩ := ms_e0 (icAdd ic0 (20 + 4 * (n.toNat - 1 + 1)))
      (by rw [icAdd_toNat _ _ (by omega)]; omega) N4 N4 V D _ [] _
      (M4.self (OutF V 20) (fun _ h => h) (fun _ _ => by unfold OutF; omega))
      dst k4 cv ebx0 ebp0 q4 edi0 g4 esi0 ret (M4.rdU0 L4.1) (M4.rdU (k := 4) L4.2.1 4 rfl)
    rw [icAdd0, icAdd_add, show 20 + 4 * (n.toNat - 1 + 1) + 2 = msK n.toNat by simp [msK, h0]; omega] at R5
    refine ⟨N5, _, _, _, _, _, R1.trans (R2.trans (R3.trans (R4.trans R5))), M4.join M5 (fun _ h => h.1),
      fun j hj => ?_⟩
    rw [← hb4 j hj]
    have := M4.fU.top; have := M4.size; have := n.toNat_lt
    exact M5.pres.2 _ (by rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)
      (by unfold OutF; rw [UInt32.toNat_add, Nat.toUInt32, UInt32.toNat_ofNat']; unfold ramTop at *; omega)

end Solutions.OpensslPoly1305
