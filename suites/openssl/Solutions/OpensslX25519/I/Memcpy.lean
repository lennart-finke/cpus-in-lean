import Solutions.OpensslX25519.I.MemcpyRun
import Solutions.OpensslX25519.I.MemCall
/-!
# `memcpy` as a callee

The byte loop by induction on the number of bytes left (`memcpy_loop`) and the call
`memcpy(dst, src, n)` for `n ≥ 1` with the two regions apart (`memcpy_call`): copied from `memmove_loop`,
`memmove_call` (`I/MemCall`) with `memcpy`'s registers. Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

/-- The `memcpy` loop over the bytes `i … n-1` (`r = n - i ≥ 1` of them). -/
theorem memcpy_loop (L dst src n ebp edi : UInt32) (ic0 : UInt64) :
    ∀ (r : Nat) (M : XMem) (i ebx fl : UInt32) (m : Nat), 1 ≤ r → i.toNat + r = n.toNat →
      M.get.size ≤ ramTop → dst.toNat + n.toNat ≤ M.get.size → src.toNat + n.toNat ≤ M.get.size →
      (dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat) →
      (src.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ src.toNat) →
      (dst.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ dst.toNat) → ic0.toNat + m + 5 * r < 2 ^ 63 →
      ∃ (M' : XMem) (ebx' esi' fl' : UInt32),
        Run img (St.m ⟨M.get, dst, n, src, ebx, L, ebp, i, edi, 0x103f00, efl fl, icAdd ic0 m⟩)
          (St.m ⟨M'.get, dst, n, src, ebx', L, ebp, esi', edi, 0x103f0c, efl fl', icAdd ic0 (m + 5 * r)⟩) ∧
        Pres M M' (fun x => x < dst.toNat + i.toNat ∨ dst.toNat + n.toNat ≤ x) ∧
        ∀ k : Nat, i.toNat ≤ k → k < n.toNat →
          memByte M'.get (UInt32.add dst k.toUInt32) = memByte M.get (UInt32.add src k.toUInt32) := by
  intro r
  induction r with
  | zero => intro _ _ _ _ _ h; omega
  | succ r ih =>
    intro M i ebx fl m _ hi htop hd hs hdi hsi hds hic
    have hb : Image.base.toNat = 0x100000 := rfl
    have hsz : Image.size = 47024 := rfl
    have hT : M.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
    have edi' : (UInt32.add dst i).toNat = dst.toNat + i.toNat := by rw [toNat_uadd]; omega
    have esi' : (UInt32.add src i).toNat = src.toNat + i.toNat := by rw [toNat_uadd]; omega
    have hi1 : (UInt32.add i 1).toNat = i.toNat + 1 := by rw [toNat_uadd]; simp only [UInt32.reduceToNat]; omega
    have ok : StoreOk1 Image.base Image.size M.mem (UInt32.add dst i) :=
      ⟨by show (UInt32.add dst i).toNat < M.get.size; omega, by rw [hb, hsz]; omega⟩
    have kN : ∀ k : Nat, k < n.toNat → (UInt32.add dst k.toUInt32).toNat = dst.toNat + k ∧
        (UInt32.add src k.toUInt32).toNat = src.toNat + k := by
      intro k hk
      have : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
      constructor <;> rw [toNat_uadd, this] <;> omega
    have byte_i : ∀ k : Nat, k = i.toNat → (UInt32.add dst k.toUInt32) = UInt32.add dst i ∧
        UInt32.add src k.toUInt32 = UInt32.add src i := by
      intro k hk
      have h1 := kN k (by omega)
      exact ⟨UInt32.toNat_inj.1 (by rw [h1.1, edi', hk]), UInt32.toNat_inj.1 (by rw [h1.2, esi', hk])⟩
    by_cases hr : r = 0
    · subst hr
      have R := mc_last (icAdd ic0 m) (icB' (k := 5) (by omega)) M dst src i n _ ok htop (by omega) rfl
        (by rw [esi']; omega) ebx ebp edi fl L (by omega)
      rw [icAdd_add] at R
      refine ⟨_, _, _, _, R, ((Pres.refl M _).wr1 ok (fun x hx => by omega)), fun k h1 h2 => ?_⟩
      obtain ⟨e1, e2⟩ := byte_i k (by omega)
      rw [e1, e2, memByte_wr1_self, rdRaw1_byte _ _ (by rw [esi']; omega)]
    · have R1 := mc_iter (icAdd ic0 m) (icB' (k := 5) (by omega)) M dst src i n _ ok htop (by omega) rfl
        (by rw [esi']; omega) ebx ebp edi fl L (by omega)
      rw [icAdd_add] at R1
      obtain ⟨M', ebx', esi'', fl', R2, P2, B2⟩ := ih (CodeMem.wr1 M (UInt32.add dst i)
        (UInt32.land (rdRaw M.get (UInt32.add src i) 1) 255) ok) (UInt32.add i 1) _ _ (m + 5) (by omega)
        (by omega) (by rw [wr1_get_size]; exact htop) (by rw [wr1_get_size]; exact hd)
        (by rw [wr1_get_size]; exact hs) hdi hsi hds (by omega)
      rw [show m + 5 + 5 * r = m + 5 * (r + 1) by omega] at R2
      refine ⟨M', ebx', esi'', fl', R1.trans R2, ?_, fun k h1 h2 => ?_⟩
      · have := ((Pres.refl M (fun x => x < dst.toNat + i.toNat ∨ dst.toNat + n.toNat ≤ x)).wr1
          (v := UInt32.land (rdRaw M.get (UInt32.add src i) 1) 255) ok (fun x hx => by omega)).trans P2
        exact this.mono fun x hx => ⟨hx, by rw [hi1]; omega⟩
      · have kk := kN k (by omega)
        by_cases hk : k = i.toNat
        · obtain ⟨e1, e2⟩ := byte_i k hk
          rw [e1, e2]
          have e := P2.2 (UInt32.add dst i) (by rw [wr1_get_size]; omega) (by rw [hi1, edi']; omega)
          rw [e, memByte_wr1_self, rdRaw1_byte _ _ (by rw [esi']; omega)]
        · rw [B2 k (by rw [hi1]; omega) h2, memByte_wr1_other _ _ _ _ (by rw [kk.2]; omega)
            (by rw [kk.2, edi']; omega)]

/-- A call `memcpy(dst, src, n)` with `n ≥ 1` and the two regions apart: the return address at `L + 8`. -/
theorem memcpy_call (G : XMem) (L ret dst src n eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 24) (lr : rdRaw G.get (UInt32.add L 8) 4 = ret)
    (ld : rdRaw G.get (UInt32.add L 12) 4 = dst) (ls : rdRaw G.get (UInt32.add L 16) 4 = src)
    (ln : rdRaw G.get (UInt32.add L 20) 4 = n) (hn : 1 ≤ n.toNat) (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hs : src.toNat + n.toNat ≤ G.get.size)
    (hdi : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat)
    (hsi : src.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ src.toNat) (hds : dst.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ dst.toNat)
    (hdL : dst.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 24 ≤ dst.toNat)
    (hsL : src.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 8 ≤ src.toNat)
    (hic : ic0.toNat + 5 * n.toNat + 30 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103ee0, efl fl, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 12, ebp, esi, edi, ret, efl fl', icAdd ic0 (5 * n.toNat + 23)⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 8 ≤ x) ∧ (x < dst.toNat ∨ dst.toNat + n.toNat ≤ x)) ∧
      ∀ k : Nat, k < n.toNat → memByte N.get (UInt32.add dst k.toUInt32) = memByte G.get (UInt32.add src k.toUInt32) := by
  have htop := hS.top
  have F0 : Frame G L 24 [(8, ret), (16, src)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lr⟩
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, ls⟩
    · simp at hl
  have R1 := mc_a ic0 (by omega) G L hS eax ecx edx ebx ebp esi edi fl dst n ld ln
  have F1 := (F0.wrF 4 (j := 4) (v := ebx) (h := hS) (hj := by decide) rfl rfl).wrF0 (v := esi) (h := stF_FB) (hn := by decide)
  have P1 : Pres G (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)) (OutF L 8) :=
    ((Pres.refl G _).wrF (by decide)).wrF0 (by decide)
  have hS1 : FB (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get.size L 24 := stF0_FB
  have hsz1 : (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get.size = G.get.size := P1.1
  have ls1 : rdRaw (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get (UInt32.add L 16) 4 = src :=
    (F1.rd (rfl : List.lookup 16 _ = some src) 16 rfl)
  have R2 := mc_b (icAdd ic0 4) (icB' (k := 16) (by omega)) _ L hS1 dst n edx ebx ebp esi edi fl src (by omega) ls1
  simp only [icAdd_add] at R2
  obtain ⟨M2, ebx2, esi2, fl2, R3, P3, B3⟩ := memcpy_loop L dst src n ebp edi ic0 n.toNat _ 0 ebx
    (logicF 4 0).2 20 hn (by simp) (by rw [hsz1]; exact htop) (by rw [hsz1]; exact hd) (by rw [hsz1]; exact hs)
    hdi hsi hds (by omega)
  have F3 := F1.pres hS1 P3 (fun x h1 h2 => by simp at *; omega)
  have R4 := mc_tail (icAdd ic0 (20 + 5 * n.toNat)) (icB' (k := 3) (by omega)) M2 L (hS1.pres P3) dst n src ebx2 ebp
    esi2 edi fl2 esi ebx ret (F3.rd0 (rfl : List.lookup 0 _ = some esi)) (F3.rd (rfl : List.lookup 4 _ = some ebx) 4 rfl)
    (F3.rd (rfl : List.lookup 8 _ = some ret) 8 rfl)
  have e2 : icAdd (icAdd ic0 (20 + 5 * n.toNat)) 3 = icAdd ic0 (5 * n.toNat + 23) := by
    rw [icAdd_add]; congr 1; omega
  rw [e2] at R4
  refine ⟨M2, _, _, _, _, R1.trans (R2.trans (R3.trans R4)), (P1.trans P3).mono fun x hx => ⟨?_, ?_⟩,
    fun k hk => ?_⟩
  · unfold OutF; omega
  · first | omega | (simp at hx; omega) | (unfold OutF at hx; simp at hx; omega)
  · rw [B3 k (by simp) hk]
    have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
    have : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    have ea : (UInt32.add src k.toUInt32).toNat = src.toNat + k := by rw [toNat_uadd, this]; omega
    exact P1.2 _ (by omega) (by unfold OutF; omega)

end Solutions.OpensslX25519.I
