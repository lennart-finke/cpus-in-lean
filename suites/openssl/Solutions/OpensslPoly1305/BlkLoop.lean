import Solutions.OpensslPoly1305.BlkFacts
import Solutions.OpensslPoly1305.BlkEnds
/-!
# The loop of `poly1305_blocks`

From the loop head (`0x100220`) with `m + 1` blocks left, the loop runs `m + 1` iterations
(`blk_it`, then `ja` taken or not) and leaves the accumulator limbs `o0 … o4` with `o4 ≤ 4` and
value the fold of `x ↦ (x + block + pad·2^128) · r mod p` over the blocks (`accB`).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

/-- The five limbs as a number. -/
def val5 (a b c d e : UInt32) : Nat :=
  a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat + 2 ^ 96 * d.toNat + 2 ^ 128 * e.toNat

/-- The four words `r`. -/
def val4 (a b c d : UInt32) : Nat := a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat + 2 ^ 96 * d.toNat

/-- The 16-byte block at `a` as a number (four little-endian words). -/
def bval (G : PMem) (a : UInt32) : Nat :=
  val4 (rdRaw G.get a 4) (rdRaw G.get (UInt32.add a 4) 4) (rdRaw G.get (UInt32.add a 8) 4)
    (rdRaw G.get (UInt32.add a 12) 4)

/-- `m` blocks from `a`, folded into the accumulator `x`. -/
def accB (G : PMem) (R padv : Nat) : UInt32 → Nat → Nat → Nat
  | _, 0, x => x
  | a, m + 1, x => accB G R padv (UInt32.add a 16) m ((x + bval G a + 2 ^ 128 * padv) * R % p)

theorem ExtR.shift {G : PMem} {P : Nat → Prop} {p : UInt32} {L : Nat} (E : ExtR G P p (16 + L)) :
    ExtR G P (UInt32.add p 16) L := by
  have e := E.add_toNat (j := 16) (by simp)
  refine ⟨?_, E.top, ?_⟩
  · rw [e]; have := E.fit; simp at this ⊢; omega
  · intro x h1 h2; rw [e] at h1 h2; exact E.cov x (by simp at h1; omega) (by simp at h2; omega)

theorem ExtR.mono {G : PMem} {P : Nat → Prop} {p : UInt32} {L L' : Nat} (E : ExtR G P p L) (h : L' ≤ L) :
    ExtR G P p L' :=
  ⟨Nat.le_trans (by omega) E.fit, E.top, fun x h1 h2 => E.cov x h1 (by omega)⟩

theorem len_step0 {len : UInt32} (h : len.toNat = 16 * (0 + 1)) : (addF 4 len 4294967280 0).1.toNat = 0 := by
  rw [Solutions.OpensslPoly1305.add_lo, h]; rfl

theorem len_step {len : UInt32} {m : Nat} (h : len.toNat = 16 * (m + 1 + 1)) (hl : len.toNat < 2 ^ 32) :
    (addF 4 len 4294967280 0).1.toNat = 16 * (m + 1) := by
  rw [Solutions.OpensslPoly1305.add_lo, h]
  show (16 * (m + 1 + 1) + 4294967280 + 0) % 2 ^ 32 = _
  rw [h] at hl; omega

theorem modfold (a b c R : Nat) : ((a % p + b + c) * R) % p = ((a + b + c) * R) % p := by
  simp [Nat.mul_mod, Nat.add_mod]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- One iteration of the loop body, with its arithmetic. -/
theorem blk_one (G : PMem) (U C : UInt32) (P : Nat → Prop)
    (r0 r1 r2 r3 s1 s2 s3 esi0 edi0 ebx0 ebp0 ret len0 pad : UInt32)
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0)
    (hs1 : s1.toNat = r1.toNat + r1.toNat / 4) (hs2 : s2.toNat = r2.toNat + r2.toNat / 4)
    (hs3 : s3.toNat = r3.toNat + r3.toNat / 4) (hpad : pad.toNat ≤ 1)
    (ic0 : UInt64) (N : PMem) (lU lC : List (Nat × UInt32))
    (len inp c0 b0 d0 gf h0 h1 h2 h3 h4 : UInt32)
    (hM : MemOK G N U 116 lU C 236 20 lC P) (hic : ic0.toNat < 2 ^ 63) (E : ExtR G P inp 16)
    (hinpU : inp.toNat + 16 ≤ U.toNat ∨ U.toNat + 116 ≤ inp.toNat)
    (hl : LK lU [(4, h0), (8, h2), (12, h1), (24, r0), (28, s3), (36, s2), (40, r1), (44, s1), (48, r2), (52, C),
        (56, r3), (88, esi0), (92, edi0), (96, ebx0), (100, ebp0), (104, ret), (108, len0), (112, pad)])
    (hlC : LK lC [(20, r0), (24, r1), (28, r2), (32, r3)]) (hh4 : h4.toNat ≤ 4) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (o0 o1 o2 o3 o4 c0' b0' d0' gf' : UInt32),
      Run img (St.m ⟨N.get, len, c0, inp, h3, UInt32.add U 4, b0, h4, d0, 0x100220, efl gf, icAdd ic0 0⟩)
        (St.m ⟨N'.get, (addF 4 len 4294967280 0).1, c0', (addF 4 inp 16 0).1, o3, UInt32.add U 4, b0', o4, d0',
          0x100424, efl gf', icAdd ic0 182⟩) ∧
      MemOK G N' U 116 lU' C 236 20 lC' P ∧
      LK lU' [(4, o0), (8, o2), (12, o1), (24, r0), (28, s3), (36, s2), (40, r1), (44, s1), (48, r2), (52, C),
        (56, r3), (88, esi0), (92, edi0), (96, ebx0), (100, ebp0), (104, ret), (108, len0), (112, pad)] ∧
      LK lC' [(20, r0), (24, r1), (28, r2), (32, r3)] ∧ o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = (val5 h0 h1 h2 h3 h4 + bval G inp + 2 ^ 128 * pad.toNat) * val4 r0 r1 r2 r3 % p := by
  obtain ⟨N', lU', lC', v184, v172, v186, v174, v139, v182, v178, g187, v149, v167, v160, R, M, L, LC, hF, e184, e186⟩ :=
    blk_it ic0 hic G N U C lU lC P hM len c0 inp h3 b0 h4 d0 gf h0 h2 h1 r0 s3 s2 r1 s1 r2 r3 esi0 edi0 ebx0 ebp0
      ret len0 pad (rdRaw G.get inp 4) (rdRaw G.get (UInt32.add inp 4) 4) (rdRaw G.get (UInt32.add inp 8) 4)
      (rdRaw G.get (UInt32.add inp 12) 4) hl hlC E rfl rfl rfl rfl E.fit hinpU
  subst e184 e186
  have hs := blkF_spec (rdRaw G.get inp 4) h0 (rdRaw G.get (UInt32.add inp 4) 4) h1
    (rdRaw G.get (UInt32.add inp 8) 4) h2 (rdRaw G.get (UInt32.add inp 12) 4) h3 h4 pad r0 s3 s2 s1 r1 r2 r3
    len inp hr0 hr1 hr2 hr3 hq1 hq2 hq3 hs1 hs2 hs3 hh4 hpad
  rw [← hF] at hs
  exact ⟨N', lU', lC', v149, v160, v167, v174, v182, v172, v139, v178, g187, R, M, L, LC, hs.1, hs.2⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem blk_loop (G : PMem) (U C : UInt32) (P : Nat → Prop)
    (r0 r1 r2 r3 s1 s2 s3 esi0 edi0 ebx0 ebp0 ret len0 pad : UInt32)
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0)
    (hs1 : s1.toNat = r1.toNat + r1.toNat / 4) (hs2 : s2.toNat = r2.toNat + r2.toNat / 4)
    (hs3 : s3.toNat = r3.toNat + r3.toNat / 4) (hpad : pad.toNat ≤ 1) :
    ∀ (m : Nat) (ic0 : UInt64) (N : PMem) (lU lC : List (Nat × UInt32))
      (len inp c0 b0 d0 gf h0 h1 h2 h3 h4 : UInt32),
      MemOK G N U 116 lU C 236 20 lC P →
      ic0.toNat + 184 * (m + 1) < 2 ^ 63 →
      len.toNat = 16 * (m + 1) →
      ExtR G P inp (16 * (m + 1)) →
      (inp.toNat + 16 * (m + 1) ≤ U.toNat ∨ U.toNat + 116 ≤ inp.toNat) →
      LK lU [(4, h0), (8, h2), (12, h1), (24, r0), (28, s3), (36, s2), (40, r1), (44, s1), (48, r2), (52, C),
        (56, r3), (88, esi0), (92, edi0), (96, ebx0), (100, ebp0), (104, ret), (108, len0), (112, pad)] →
      LK lC [(20, r0), (24, r1), (28, r2), (32, r3)] → h4.toNat ≤ 4 →
      ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (o0 o1 o2 o3 o4 len' c0' inp' b0' d0' gf' : UInt32),
        Run img (St.m ⟨N.get, len, c0, inp, h3, UInt32.add U 4, b0, h4, d0, 0x100220, efl gf, icAdd ic0 0⟩)
          (St.m ⟨N'.get, len', c0', inp', o3, UInt32.add U 4, b0', o4, d0', 0x10042d, efl gf',
            icAdd ic0 (184 * (m + 1))⟩) ∧
        MemOK G N' U 116 lU' C 236 20 lC' P ∧
        LK lU' [(4, o0), (8, o2), (12, o1), (24, r0), (28, s3), (36, s2), (40, r1), (44, s1), (48, r2), (52, C),
          (56, r3), (88, esi0), (92, edi0), (96, ebx0), (100, ebp0), (104, ret), (108, len0), (112, pad)] ∧
        LK lC' [(20, r0), (24, r1), (28, r2), (32, r3)] ∧ o4.toNat ≤ 4 ∧
        val5 o0 o1 o2 o3 o4 % p =
          accB G (val4 r0 r1 r2 r3) pad.toNat inp (m + 1) (val5 h0 h1 h2 h3 h4 % p) := by
  intro m
  induction m with
  | zero =>
    intro ic0 N lU lC len inp c0 b0 d0 gf h0 h1 h2 h3 h4 hM hic hlen E hinpU hl hlC hh4
    obtain ⟨N1, lU1, lC1, o0, o1, o2, o3, o4, c1, b1, d1, g1, R1, M1, L1, LC1, ho4, hv⟩ :=
      blk_one G U C P r0 r1 r2 r3 s1 s2 s3 esi0 edi0 ebx0 ebp0 ret len0 pad hr0 hr1 hr2 hr3 hq1 hq2 hq3 hs1 hs2
        hs3 hpad ic0 N lU lC len inp c0 b0 d0 gf h0 h1 h2 h3 h4 hM (by omega) E (by omega) hl hlC hh4
    obtain ⟨N2, R2, M2⟩ := blk_jn (icAdd ic0 182) (by rw [icAdd_toNat _ _ (by omega)]; omega) G N1 U C lU1 lC1 P M1
      (addF 4 len 4294967280 0).1 c1 (addF 4 inp 16 0).1 o3 b1 o4 d1 g1 _ (len_step0 hlen) rfl
    have e : icAdd (icAdd ic0 182) 2 = icAdd ic0 (184 * (0 + 1)) := by rw [icAdd_add]
    rw [e, icAdd0] at R2
    refine ⟨N2, lU1, lC1, o0, o1, o2, o3, o4, _, c1, _, b1, d1, _, R1.trans R2, M2, L1, LC1, ho4, ?_⟩
    rw [hv]
    show _ = (val5 h0 h1 h2 h3 h4 % p + bval G inp + 2 ^ 128 * pad.toNat) * val4 r0 r1 r2 r3 % p
    rw [modfold]
  | succ m ih =>
    intro ic0 N lU lC len inp c0 b0 d0 gf h0 h1 h2 h3 h4 hM hic hlen E hinpU hl hlC hh4
    obtain ⟨N1, lU1, lC1, o0, o1, o2, o3, o4, c1, b1, d1, g1, R1, M1, L1, LC1, ho4, hv⟩ :=
      blk_one G U C P r0 r1 r2 r3 s1 s2 s3 esi0 edi0 ebx0 ebp0 ret len0 pad hr0 hr1 hr2 hr3 hq1 hq2 hq3 hs1 hs2
        hs3 hpad ic0 N lU lC len inp c0 b0 d0 gf h0 h1 h2 h3 h4 hM (by omega) (E.mono (by omega)) (by omega) hl hlC hh4
    have hl2 := len_step hlen len.toNat_lt
    obtain ⟨N2, R2, M2⟩ := blk_jt (icAdd ic0 182) (by rw [icAdd_toNat _ _ (by omega)]; omega) G N1 U C lU1 lC1 P M1
      (addF 4 len 4294967280 0).1 c1 (addF 4 inp 16 0).1 o3 b1 o4 d1 g1 _ (by omega) rfl
    have einp : (addF 4 inp 16 0).1 = UInt32.add inp 16 := addF_fst inp 16
    have E' : ExtR G P (UInt32.add inp 16) (16 * (m + 1)) :=
      ExtR.shift (E.mono (by omega))
    have ei := E.add_toNat (j := 16) (by simp; omega)
    rw [einp] at R1 R2
    rw [icAdd0] at R2
    obtain ⟨N3, lU3, lC3, p0, p1, p2, p3, p4, l3, c3, i3, b3, d3, g3, R3, M3, L3, LC3, hp4, hv3⟩ :=
      ih (icAdd (icAdd ic0 182) 2) N2 lU1 lC1 (addF 4 len 4294967280 0).1 (UInt32.add inp 16) c1 b1 d1
        (subF 4 (addF 4 len 4294967280 0).1 15 0).2 o0 o1 o2 o3 o4 M2
        (by rw [icAdd_toNat _ _ (by rw [icAdd_toNat _ _ (by omega)]; omega), icAdd_toNat _ _ (by omega)]; omega)
        hl2 E' (by rw [ei]; simp at hinpU ⊢; omega) L1 LC1 ho4
    have e : icAdd (icAdd (icAdd ic0 182) 2) (184 * (m + 1)) = icAdd ic0 (184 * (m + 1 + 1)) := by
      rw [icAdd_add, icAdd_add, show 182 + (2 + 184 * (m + 1)) = 184 * (m + 1 + 1) by omega]
    rw [e, icAdd0] at R3
    refine ⟨N3, lU3, lC3, p0, p1, p2, p3, p4, l3, c3, i3, b3, d3, g3, R1.trans (R2.trans R3), M3, L3, LC3, hp4, ?_⟩
    rw [hv3, hv]
    show _ = accB G _ _ (UInt32.add inp 16) (m + 1)
      ((val5 h0 h1 h2 h3 h4 % p + bval G inp + 2 ^ 128 * pad.toNat) * val4 r0 r1 r2 r3 % p)
    rw [modfold]

end Solutions.OpensslPoly1305
