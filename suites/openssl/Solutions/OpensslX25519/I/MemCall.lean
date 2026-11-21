import Solutions.OpensslX25519.I.MemRun
import Solutions.OpensslX25519.I.Caller
/-!
# `memset` and the forward `memmove` as callees

The byte loops by induction on the number of bytes left (`memset_loop`, `memmove_loop`), then the
calls: `memset(dst, c, n)` for `n ≥ 1` writes `c` to the `n` bytes at `dst` (`memset_call`), and
`memmove(dst, src, n)` for `n ≥ 1` and `dst + n ≤ src` copies the `n` bytes (`memmove_call`), each
writing nothing else but its own stack words.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem _root_.Solutions.OpensslX25519.Pres.wr1 {G N : XMem} {P : Nat → Prop} (hP : Pres G N P) {a v : UInt32}
    (ok : StoreOk1 Image.base Image.size N.mem a) (hd : ∀ x, P x → x ≠ a.toNat) :
    Pres G (CodeMem.wr1 N a v ok) P := by
  refine ⟨(wr1_get_size _ _ _ _).trans hP.1, fun x hx hp => ?_⟩
  rw [← hP.2 x hx hp]
  show memByte (wrBytes N.get a 1 v) x = memByte N.get x
  rw [memByte_wrBytes1 (mem := N.get) (show a.toNat < N.get.size from ok.1) (by rw [hP.1]; exact hx),
    if_neg (fun e => hd _ hp (by rw [e]))]

theorem memByte_wr1_self (N : XMem) (a v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a) :
    memByte (CodeMem.wr1 N a v ok).get a = v.toUInt8 := by
  show memByte (wrBytes N.get a 1 v) a = _
  rw [memByte_wrBytes1 (mem := N.get) (show a.toNat < N.get.size from ok.1) (show a.toNat < N.get.size from ok.1),
    if_pos rfl]

theorem memByte_wr1_other (N : XMem) (a v : UInt32) (ok : StoreOk1 Image.base Image.size N.mem a) {b : UInt32}
    (hb : b.toNat < N.get.size) (hab : b.toNat ≠ a.toNat) :
    memByte (CodeMem.wr1 N a v ok).get b = memByte N.get b := by
  show memByte (wrBytes N.get a 1 v) b = _
  rw [memByte_wrBytes1 (mem := N.get) (show a.toNat < N.get.size from ok.1) hb, if_neg (fun e => hab (by rw [e]))]

theorem icB' {x : UInt64} {m k : Nat} (h : x.toNat + m + k < 2 ^ 63) : (icAdd x m).toNat < 2 ^ 63 := by
  rw [icAdd_toNat _ _ (by omega)]; omega

/-- The `memset` loop over the `r ≥ 1` bytes from `esi`. -/
theorem memset_loop (L eax edx ebx ebp edi : UInt32) (ic0 : UInt64) :
    ∀ (r : Nat) (M : XMem) (esi ecx fl : UInt32) (m : Nat), 1 ≤ r → ecx.toNat = r →
      M.get.size ≤ ramTop → esi.toNat + r ≤ M.get.size →
      (esi.toNat + r ≤ 0x100000 ∨ 0x100000 + 47024 ≤ esi.toNat) → ic0.toNat + m + 4 * r < 2 ^ 63 →
      ∃ (M' : XMem) (ecx' esi' fl' : UInt32),
        Run img (St.m ⟨M.get, eax, ecx, edx, ebx, L, ebp, esi, edi, 0x103f80, efl fl, icAdd ic0 m⟩)
          (St.m ⟨M'.get, eax, ecx', edx, ebx, L, ebp, esi', edi, 0x103f86, efl fl', icAdd ic0 (m + 4 * r)⟩) ∧
        Pres M M' (fun x => x < esi.toNat ∨ esi.toNat + r ≤ x) ∧
        ∀ a : UInt32, esi.toNat ≤ a.toNat → a.toNat < esi.toNat + r → memByte M'.get a = (UInt32.land edx 255).toUInt8 := by
  intro r
  induction r with
  | zero => intro _ _ _ _ _ h; omega
  | succ r ih =>
    intro M esi ecx fl m _ hc htop hfit himg hic
    have hb : Image.base.toNat = 0x100000 := rfl
    have hs : Image.size = 47024 := rfl
    have ok : StoreOk1 Image.base Image.size M.mem esi := ⟨by show esi.toNat < M.get.size; omega, by
      rw [hb, hs]; omega⟩
    by_cases hr : r = 0
    · subst hr
      have R := ms_last (icAdd ic0 m) (icB' (k := 4) (by omega)) M esi ok htop eax ecx edx ebx ebp edi fl L
        (by omega)
      rw [icAdd_add] at R
      refine ⟨_, _, _, _, R, ((Pres.refl M _).wr1 ok (fun x hx => by omega)), fun a h1 h2 => ?_⟩
      rw [show a = esi from UInt32.toNat_inj.1 (by omega)]
      exact memByte_wr1_self _ _ _ _
    · have R1 := ms_iter (icAdd ic0 m) (icB' (k := 4) (by omega)) M esi ok htop eax ecx edx ebx ebp edi fl L
        (by omega)
      rw [icAdd_add] at R1
      have hs1 : (UInt32.add esi 1).toNat = esi.toNat + 1 := by
        rw [toNat_uadd]; unfold ramTop at htop; simp only [UInt32.reduceToNat]; omega
      have hc1 : (subF 4 ecx 1 0).1.toNat = r := by
        rw [subF_fst, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
      obtain ⟨M', ecx', esi', fl', R2, P2, B2⟩ := ih (CodeMem.wr1 M esi (UInt32.land edx 255) ok)
        (UInt32.add esi 1) (subF 4 ecx 1 0).1 _ (m + 4) (by omega) hc1
        (by rw [wr1_get_size]; exact htop) (by rw [wr1_get_size, hs1]; omega) (by rw [hs1]; omega)
        (by omega)
      rw [show m + 4 + 4 * r = m + 4 * (r + 1) by omega] at R2
      refine ⟨M', ecx', esi', fl', R1.trans R2, ?_, fun a h1 h2 => ?_⟩
      · have := ((Pres.refl M (fun x => x < esi.toNat ∨ esi.toNat + (r + 1) ≤ x)).wr1 (v := UInt32.land edx 255) ok
          (fun x hx => by omega)).trans P2
        exact this.mono fun x hx => ⟨hx, by rw [hs1]; omega⟩
      · by_cases ha : a.toNat = esi.toNat
        · rw [show a = esi from UInt32.toNat_inj.1 ha]
          have e := P2.2 esi (by rw [wr1_get_size]; omega) (by rw [hs1]; omega)
          rw [e, memByte_wr1_self]
        · exact B2 a (by rw [hs1]; omega) (by rw [hs1]; omega)

/-- A call `memset(dst, c, n)`, `n ≥ 1`: the return address at `L + 4`, the arguments above it. -/
theorem memset_call (G : XMem) (L ret dst c n eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 20) (lr : rdRaw G.get (UInt32.add L 4) 4 = ret)
    (ld : rdRaw G.get (UInt32.add L 8) 4 = dst) (lc : rdRaw G.get (UInt32.add L 12) 4 = c)
    (ln : rdRaw G.get (UInt32.add L 16) 4 = n) (hn : 1 ≤ n.toNat) (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hdi : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat)
    (hdL : dst.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 20 ≤ dst.toNat)
    (hic : ic0.toNat + 4 * n.toNat + 22 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x103f60, efl fl, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 8, ebp, esi, edi, ret, efl fl', icAdd ic0 (4 * n.toNat + 22)⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 4 ≤ x) ∧ (x < dst.toNat ∨ dst.toNat + n.toNat ≤ x)) ∧
      ∀ a : UInt32, dst.toNat ≤ a.toNat → a.toNat < dst.toNat + n.toNat → memByte N.get a = (UInt32.land c 255).toUInt8 := by
  have htop := hS.top
  have F0 : Frame G L 20 [(4, ret), (12, c)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lr⟩
    · split at hl
      · rename_i _ h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lc⟩
      · simp at hl
  have R1 := ms_a ic0 (by omega) G L hS eax ecx edx ebx ebp esi edi fl dst n ld ln
  have F1 := F0.wrF0 (v := esi) (h := hS) (hn := by decide)
  have P1 : Pres G (stF0 G L 20 esi hS (by decide)) (OutF L 4) := (Pres.refl G _).wrF0 (by decide)
  have hS1 : FB (stF0 G L 20 esi hS (by decide)).get.size L 20 := stF0_FB
  have R2 := ms_b ic0 (by omega) _ L hS1 dst n edx ebx ebp esi edi (logicF 4 (UInt32.land n n)).2 c
    (Branch.zf_test_ne n (by omega)) (F1.rd (rfl : List.lookup 12 _ = some c) 12 rfl)
  have hsz1 : (stF0 G L 20 esi hS (by decide)).get.size = G.get.size := stF0_size
  obtain ⟨M2, ecx2, esi2, fl2, R3, P3, B3⟩ := memset_loop L dst c ebx ebp edi ic0 n.toNat
    (stF0 G L 20 esi hS (by decide)) dst n (logicF 4 (UInt32.land n n)).2 20 hn rfl (by rw [hsz1]; exact htop)
    (by rw [hsz1]; exact hd) hdi (by omega)
  have F3 := F1.pres hS1 P3 (fun x h1 h2 => by omega)
  have R4 := ms_tail (icAdd ic0 (20 + 4 * n.toNat)) (icB' (k := 2) (by omega)) M2 L (hS1.pres P3) dst ecx2 c ebx ebp
    esi2 edi fl2 esi ret (F3.rd0 (rfl : List.lookup 0 _ = some esi)) (F3.rd (rfl : List.lookup 4 _ = some ret) 4 rfl)
  have e2 : icAdd (icAdd ic0 (20 + 4 * n.toNat)) 2 = icAdd ic0 (4 * n.toNat + 22) := by
    rw [icAdd_add]; congr 1; omega
  rw [e2] at R4
  refine ⟨M2, _, _, _, _, R1.trans (R2.trans (R3.trans R4)), (P1.trans P3).mono fun x hx => ⟨?_, ?_⟩, B3⟩
  · unfold OutF; omega
  · omega

theorem u8_land255 (x : UInt8) : (UInt32.land x.toUInt32 255).toUInt8 = x := by
  have h := x.toNat_lt
  apply UInt8.toNat_inj.1
  show ((x.toUInt32 &&& 255).toUInt8).toNat = _
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt8.toNat_toUInt32, UInt32.reduceToNat]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem rdRaw1_byte (m : ByteArray) (a : UInt32) (h : a.toNat < m.size) :
    (UInt32.land (rdRaw m a 1) 255).toUInt8 = memByte m a := by
  show (UInt32.land (rdBytes m a 1) 255).toUInt8 = _
  rw [rdBytes1_eq h, memByte_def h, u8_land255]

/-- The forward `memmove` loop over the bytes `i … n-1` (`r = n - i ≥ 1` of them). -/
theorem memmove_loop (L dst src n ebp edi : UInt32) (ic0 : UInt64) :
    ∀ (r : Nat) (M : XMem) (i ebx fl : UInt32) (m : Nat), 1 ≤ r → i.toNat + r = n.toNat →
      M.get.size ≤ ramTop → dst.toNat + n.toNat ≤ M.get.size → src.toNat + n.toNat ≤ M.get.size →
      (dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat) →
      (src.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ src.toNat) →
      dst.toNat + n.toNat ≤ src.toNat → ic0.toNat + m + 5 * r < 2 ^ 63 →
      ∃ (M' : XMem) (ebx' esi' fl' : UInt32),
        Run img (St.m ⟨M.get, dst, src, n, ebx, L, ebp, i, edi, 0x103f50, efl fl, icAdd ic0 m⟩)
          (St.m ⟨M'.get, dst, src, n, ebx', L, ebp, esi', edi, 0x103f5c, efl fl', icAdd ic0 (m + 5 * r)⟩) ∧
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
      have R := mm_last (icAdd ic0 m) (icB' (k := 5) (by omega)) M dst src i n _ ok htop (by omega) rfl
        (by rw [esi']; omega) ebx ebp edi fl L (by omega)
      rw [icAdd_add] at R
      refine ⟨_, _, _, _, R, ((Pres.refl M _).wr1 ok (fun x hx => by omega)), fun k h1 h2 => ?_⟩
      obtain ⟨e1, e2⟩ := byte_i k (by omega)
      rw [e1, e2, memByte_wr1_self, rdRaw1_byte _ _ (by rw [esi']; omega)]
    · have R1 := mm_iter (icAdd ic0 m) (icB' (k := 5) (by omega)) M dst src i n _ ok htop (by omega) rfl
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

/-- A call `memmove(dst, src, n)` with `n ≥ 1` and `dst + n ≤ src`: the return address at `L + 8`. -/
theorem memmove_call (G : XMem) (L ret dst src n eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 24) (lr : rdRaw G.get (UInt32.add L 8) 4 = ret)
    (ld : rdRaw G.get (UInt32.add L 12) 4 = dst) (ls : rdRaw G.get (UInt32.add L 16) 4 = src)
    (ln : rdRaw G.get (UInt32.add L 20) 4 = n) (hn : 1 ≤ n.toNat) (hd : dst.toNat + n.toNat ≤ G.get.size)
    (hs : src.toNat + n.toNat ≤ G.get.size)
    (hdi : dst.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ dst.toNat)
    (hsi : src.toNat + n.toNat ≤ 0x100000 ∨ 0x100000 + 47024 ≤ src.toNat) (hds : dst.toNat + n.toNat ≤ src.toNat)
    (hdL : dst.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 24 ≤ dst.toNat)
    (hsL : src.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 8 ≤ src.toNat)
    (hic : ic0.toNat + 5 * n.toNat + 30 < 2 ^ 63) :
    ∃ (N : XMem) (eax' ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x103f10, efl fl, icAdd ic0 0⟩)
        (St.m ⟨N.get, eax', ecx', edx', ebx, UInt32.add L 12, ebp, esi, edi, ret, efl fl', icAdd ic0 (5 * n.toNat + 23)⟩) ∧
      Pres G N (fun x => (x < L.toNat ∨ L.toNat + 8 ≤ x) ∧ (x < dst.toNat ∨ dst.toNat + n.toNat ≤ x)) ∧
      ∀ k : Nat, k < n.toNat → memByte N.get (UInt32.add dst k.toUInt32) = memByte G.get (UInt32.add src k.toUInt32) := by
  have htop := hS.top
  have F0 : Frame G L 24 [(8, ret)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lr⟩
    · simp at hl
  have R1 := mm_a ic0 (by omega) G L hS eax ecx edx ebx ebp esi edi fl dst src n ld ls ln (by omega)
  have F1 := (F0.wrF 4 (j := 4) (v := ebx) (h := hS) (hj := by decide) rfl rfl).wrF0 (v := esi) (h := stF_FB) (hn := by decide)
  have P1 : Pres G (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)) (OutF L 8) :=
    ((Pres.refl G _).wrF (by decide)).wrF0 (by decide)
  have hS1 : FB (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get.size L 24 := stF0_FB
  have hsz1 : (stF0 (stF G L 24 4 ebx hS (by decide)) L 24 esi stF_FB (by decide)).get.size = G.get.size := P1.1
  have R2 := mm_b ic0 (by omega) _ L hS1 dst src n ebx ebp esi edi (subF 4 dst src 0).2 (by omega)
  obtain ⟨M2, ebx2, esi2, fl2, R3, P3, B3⟩ := memmove_loop L dst src n ebp edi ic0 n.toNat _ 0 ebx
    (logicF 4 0).2 20 hn (by simp) (by rw [hsz1]; exact htop) (by rw [hsz1]; exact hd) (by rw [hsz1]; exact hs)
    hdi hsi hds (by omega)
  have F3 := F1.pres hS1 P3 (fun x h1 h2 => by simp at *; omega)
  have R4 := mm_tail (icAdd ic0 (20 + 5 * n.toNat)) (icB' (k := 3) (by omega)) M2 L (hS1.pres P3) dst src n ebx2 ebp
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
