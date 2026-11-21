import Solutions.OpensslX25519.I.MemcmpRunI
import Solutions.OpensslX25519.I.MemCall
/-!
# `CRYPTO_memcmp` as a callee

The loop by induction on the number of bytes left (`memcmp_loop`): the accumulator stays below 256 and is
zero exactly when all bytes compared so far are equal; then the call `CRYPTO_memcmp(a, b, n)` for `n ≥ 1`
(`memcmp_call`), which writes only its own stack words. The buffers may be anywhere in memory (also inside
the image). Prover P.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519

theorem cmB (c d : UInt8) : ((c.toUInt32.land 4294967040).lor ((logicF 1 ((c.toUInt32.land 255).xor d.toUInt32)).1.land 255)).land 255
    = (c ^^^ d).toUInt32 := by
  rw [show (logicF 1 ((c.toUInt32.land 255).xor d.toUInt32)).1 = (c.toUInt32.land 255).xor d.toUInt32 from rfl]
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have k1 : ∀ j, j < 32 → (UInt32.toBitVec 4294967040).getLsbD j = decide (8 ≤ j) := by decide
  have k2 : ∀ j, j < 32 → (UInt32.toBitVec 255).getLsbD j = decide (j < 8) := by decide
  show ((((c.toUInt32 &&& 4294967040) ||| ((c.toUInt32 &&& 255) ^^^ d.toUInt32) &&& 255)) &&& 255).toBitVec.getLsbD i = _
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_xor, UInt8.toBitVec_toUInt32, UInt8.toBitVec_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, k1 i hi, k2 i hi]
  by_cases h : i < 8
  · simp [h, show ¬ 8 ≤ i by omega, show i < 32 by omega]
  · simp [h, show 8 ≤ i by omega]

theorem lor_byte (acc : UInt32) (e : UInt8) (h : acc.toNat < 256) :
    (acc.lor e.toUInt32).toNat < 256 ∧ (acc.lor e.toUInt32 = 0 ↔ acc = 0 ∧ e = 0) := by
  have he := e.toNat_lt
  have t : (acc.lor e.toUInt32).toNat = acc.toNat ||| e.toNat := by
    show (acc ||| e.toUInt32).toNat = _
    rw [UInt32.toNat_or, UInt8.toNat_toUInt32]
  refine ⟨?_, ?_⟩
  · rw [t]; exact Nat.or_lt_two_pow (n := 8) h he
  · constructor
    · intro h0
      have := congrArg UInt32.toNat h0
      rw [t] at this
      have := Nat.or_eq_zero_iff.1 this
      exact ⟨UInt32.toNat_inj.1 (by simpa using this.1), UInt8.toNat_inj.1 (by simpa using this.2)⟩
    · rintro ⟨rfl, rfl⟩; rfl

theorem xor_zero_iff (c d : UInt8) : c ^^^ d = 0 ↔ c = d := by
  constructor
  · intro h
    have := congrArg (· ^^^ d) h
    simpa [UInt8.xor_assoc] using this
  · rintro rfl; simp

theorem icAdd_zero'' (x : UInt64) : icAdd x 0 = x := rfl

theorem rdRaw1_memByte (m : ByteArray) (a : UInt32) (h : a.toNat < m.size) : rdRaw m a 1 = (memByte m a).toUInt32 :=
  rdBytes1_eq h

/-- The loop over the bytes `i … n-1` (`r = n - i ≥ 1` of them). -/
theorem memcmp_loop (L a b n ebp : UInt32) (ic0 : UInt64) (M : XMem) (htop : M.get.size ≤ ramTop)
    (ha : a.toNat + n.toNat ≤ M.get.size) (hb : b.toNat + n.toNat ≤ M.get.size) :
    ∀ (r : Nat) (i acc ebx fl : UInt32) (m : Nat), 1 ≤ r → i.toNat + r = n.toNat → acc.toNat < 256 →
      ic0.toNat + m + 7 * r < 2 ^ 63 →
      ∃ (acc' ebx' i' fl' : UInt32),
        Run img (St.m ⟨M.get, acc, n, b, ebx, L, ebp, a, i, 0x103ec0, efl fl, icAdd ic0 m⟩)
          (St.m ⟨M.get, acc', n, b, ebx', L, ebp, a, i', 0x103ed1, efl fl', icAdd ic0 (m + 7 * r)⟩) ∧
        acc'.toNat < 256 ∧
        (acc' = 0 ↔ acc = 0 ∧ ∀ k : Nat, i.toNat ≤ k → k < n.toNat →
          memByte M.get (UInt32.add a k.toUInt32) = memByte M.get (UInt32.add b k.toUInt32)) := by
  intro r
  have hT : M.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
  induction r with
  | zero => intro _ _ _ _ _ h; omega
  | succ r ih =>
    intro i acc ebx fl m _ hi hacc hic
    have eai : (UInt32.add a i).toNat = a.toNat + i.toNat := by rw [toNat_uadd]; omega
    have ebi : (UInt32.add b i).toNat = b.toNat + i.toNat := by rw [toNat_uadd]; omega
    have hi1 : (UInt32.add i 1).toNat = i.toNat + 1 := by rw [toNat_uadd]; simp only [UInt32.reduceToNat]; omega
    have kN : ∀ k : Nat, k < n.toNat → (UInt32.add a k.toUInt32).toNat = a.toNat + k ∧
        (UInt32.add b k.toUInt32).toNat = b.toNat + k := by
      intro k hk
      have : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
      constructor <;> rw [toNat_uadd, this] <;> omega
    have byte_i : ∀ k : Nat, k = i.toNat → UInt32.add a k.toUInt32 = UInt32.add a i ∧
        UInt32.add b k.toUInt32 = UInt32.add b i := by
      intro k hk
      have h1 := kN k (by omega)
      exact ⟨UInt32.toNat_inj.1 (by rw [h1.1, eai, hk]), UInt32.toNat_inj.1 (by rw [h1.2, ebi, hk])⟩
    have la := rdRaw1_memByte M.get (UInt32.add a i) (by omega)
    have lb := rdRaw1_memByte M.get (UInt32.add b i) (by omega)
    obtain ⟨hlt, hiff⟩ := lor_byte acc (memByte M.get (UInt32.add a i) ^^^ memByte M.get (UInt32.add b i)) hacc
    rw [← cmB] at hlt hiff
    have hx := xor_zero_iff (memByte M.get (UInt32.add a i)) (memByte M.get (UInt32.add b i))
    by_cases hr : r = 0
    · subst hr
      have R := cm_lastI (icAdd ic0 m) (icB' (k := 7) (by omega)) M L a b n i acc ebx ebp fl _ _ htop (by omega)
        (by omega) la lb (by omega)
      rw [icAdd_add] at R
      refine ⟨_, _, _, _, R, hlt, ?_⟩
      show acc.lor _ = 0 ↔ _
      rw [hiff, hx]
      constructor
      · rintro ⟨h0, he⟩; refine ⟨h0, fun k h1 h2 => ?_⟩
        obtain ⟨e1, e2⟩ := byte_i k (by omega); rw [e1, e2]; exact he
      · rintro ⟨h0, he⟩; refine ⟨h0, ?_⟩
        have := he i.toNat (Nat.le_refl _) (by omega)
        obtain ⟨e1, e2⟩ := byte_i i.toNat rfl; rw [e1, e2] at this; exact this
    · have R1 := cm_iterI (icAdd ic0 m) (icB' (k := 7) (by omega)) M L a b n i acc ebx ebp fl _ _ htop (by omega)
        (by omega) la lb (by omega)
      rw [icAdd_add] at R1
      obtain ⟨acc', ebx', i', fl', R2, hlt', hiff'⟩ := ih (UInt32.add i 1) _ _ _ (m + 7) (by omega) (by omega)
        hlt (by omega)
      rw [show m + 7 + 7 * r = m + 7 * (r + 1) by omega] at R2
      refine ⟨acc', ebx', i', fl', R1.trans R2, hlt', ?_⟩
      rw [hiff']
      show (acc.lor _ = 0 ∧ _) ↔ _
      rw [hiff, hx, hi1]
      constructor
      · rintro ⟨⟨h0, he⟩, hrest⟩; refine ⟨h0, fun k h1 h2 => ?_⟩
        by_cases hk : k = i.toNat
        · obtain ⟨e1, e2⟩ := byte_i k hk; rw [e1, e2]; exact he
        · exact hrest k (by omega) h2
      · rintro ⟨h0, he⟩
        have := he i.toNat (Nat.le_refl _) (by omega)
        obtain ⟨e1, e2⟩ := byte_i i.toNat rfl; rw [e1, e2] at this
        exact ⟨⟨h0, this⟩, fun k h1 h2 => he k (by omega) h2⟩

/-- A call `CRYPTO_memcmp(a, b, n)` with `n ≥ 1`: the return address at `L + 12`, the arguments above it;
`eax` is zero exactly when the `n` bytes at `a` and `b` are equal. -/
theorem memcmp_call (G : XMem) (L ret a b n eax ecx edx ebx ebp esi edi fl : UInt32) (ic0 : UInt64)
    (hS : FB G.get.size L 28) (lr : rdRaw G.get (UInt32.add L 12) 4 = ret)
    (la : rdRaw G.get (UInt32.add L 16) 4 = a) (lb : rdRaw G.get (UInt32.add L 20) 4 = b)
    (ln : rdRaw G.get (UInt32.add L 24) 4 = n) (hn : 1 ≤ n.toNat) (ha : a.toNat + n.toNat ≤ G.get.size)
    (hb : b.toNat + n.toNat ≤ G.get.size) (haL : a.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 12 ≤ a.toNat)
    (hbL : b.toNat + n.toNat ≤ L.toNat ∨ L.toNat + 12 ≤ b.toNat) (hic : ic0.toNat + 7 * n.toNat + 30 < 2 ^ 63) :
    ∃ (N : XMem) (r ecx' edx' fl' : UInt32),
      Run img (St.m ⟨G.get, eax, ecx, edx, ebx, UInt32.add L 12, ebp, esi, edi, 0x103ea0, efl fl, icAdd ic0 0⟩)
        (St.m ⟨N.get, r, ecx', edx', ebx, UInt32.add L 16, ebp, esi, edi, ret, efl fl', icAdd ic0 (7 * n.toNat + 23)⟩) ∧
      Pres G N (fun x => x < L.toNat ∨ L.toNat + 12 ≤ x) ∧
      (r = 0 ↔ ∀ k : Nat, k < n.toNat → memByte G.get (UInt32.add a k.toUInt32) = memByte G.get (UInt32.add b k.toUInt32)) := by
  have htop := hS.top
  have F0 : Frame G L 28 [(12, ret), (16, a), (20, b)] := by
    intro k v hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lr⟩
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, la⟩
    split at hl
    · rename_i h; simp at h; subst h; simp at hl; subst hl; exact ⟨rfl, by decide, lb⟩
    · simp at hl
  have R1 := cm_a ic0 (by omega) G L hS eax ecx edx ebx ebp esi edi fl n ln
  have F1 := ((F0.wrF 8 (j := 8) (v := ebx) (h := hS) (hj := by decide) rfl rfl).wrF 4 (j := 4) (v := edi)
    (h := stF_FB) (hj := by decide) rfl rfl).wrF0 (v := esi) (h := stF_FB) (hn := by decide)
  generalize hM1 : stF0 (stF (stF G L 28 8 ebx hS (by decide)) L 28 4 edi stF_FB (by decide)) L 28 esi stF_FB
    (by decide) = M1 at R1 F1
  have P1 : Pres G M1 (OutF L 12) := by
    rw [← hM1]; exact (((Pres.refl G _).wrF (by decide)).wrF (by decide)).wrF0 (by decide)
  have hS1 : FB M1.get.size L 28 := hS.pres P1
  have hsz1 : M1.get.size = G.get.size := P1.1
  have R2 := cm_b (icAdd ic0 5) (icB' (k := 14) (by omega)) M1 L hS1 eax n edx ebx ebp esi edi a b (by omega)
    (F1.rd (rfl : List.lookup 16 _ = some a) 16 rfl) (F1.rd (rfl : List.lookup 20 _ = some b) 20 rfl)
  rw [icAdd_add, icAdd_add] at R2
  obtain ⟨r, ebx2, i2, fl2, R3, _, hr⟩ := memcmp_loop L a b n ebp ic0 M1 (by rw [hsz1]; exact htop)
    (by rw [hsz1]; exact ha) (by rw [hsz1]; exact hb) n.toNat 0 0 ebx (logicF 4 0).2 19 hn (by simp) (by decide)
    (by omega)
  have R4 := cm_tail (icAdd ic0 (19 + 7 * n.toNat)) (icB' (k := 4) (by omega)) M1 L hS1 r n b ebx2 ebp a i2 fl2 esi
    edi ebx ret (F1.rd0 (rfl : List.lookup 0 _ = some esi)) (F1.rd (rfl : List.lookup 4 _ = some edi) 4 rfl)
    (F1.rd (rfl : List.lookup 8 _ = some ebx) 8 rfl) (F1.rd (rfl : List.lookup 12 _ = some ret) 12 rfl)
  have e4 : icAdd (icAdd ic0 (19 + 7 * n.toNat)) 4 = icAdd ic0 (7 * n.toNat + 23) := by
    rw [icAdd_add]; congr 1; omega
  rw [e4, icAdd_zero''] at R4
  refine ⟨M1, r, _, _, _, R1.trans (R2.trans (R3.trans R4)), P1, ?_⟩
  rw [hr]
  have hm : ∀ k : Nat, k < n.toNat → memByte M1.get (UInt32.add a k.toUInt32) = memByte G.get (UInt32.add a k.toUInt32) ∧
      memByte M1.get (UInt32.add b k.toUInt32) = memByte G.get (UInt32.add b k.toUInt32) := by
    intro k hk
    have hT : G.get.size < 2 ^ 32 := by unfold ramTop at htop; omega
    have e : (k.toUInt32).toNat = k := by rw [Nat.toUInt32, UInt32.toNat_ofNat']; omega
    have ea : (UInt32.add a k.toUInt32).toNat = a.toNat + k := by rw [toNat_uadd, e]; omega
    have eb : (UInt32.add b k.toUInt32).toNat = b.toNat + k := by rw [toNat_uadd, e]; omega
    exact ⟨P1.2 _ (by omega) (by unfold OutF; omega), P1.2 _ (by omega) (by unfold OutF; omega)⟩
  constructor
  · rintro ⟨_, he⟩ k hk; rw [← (hm k hk).1, ← (hm k hk).2]; exact he k (by simp) hk
  · intro he; refine ⟨rfl, fun k _ hk => ?_⟩; rw [(hm k hk).1, (hm k hk).2]; exact he k hk

end Solutions.OpensslX25519.I
