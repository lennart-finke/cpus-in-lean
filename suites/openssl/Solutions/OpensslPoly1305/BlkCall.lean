import Solutions.OpensslPoly1305.BlkLoop
import Solutions.OpensslPoly1305.BlkPE
/-!
# `poly1305_blocks` as a callee

`blocks_call`: entered at `0x1001b0` with the stack pointer at `U + 104` (return address, then the
length `16 n` and `padbit` on the stack, context pointer in `ecx`, input pointer in `edx`), the call
returns to its return address after `61 + 184 n` instructions, having written only its 104 bytes
of stack and the five accumulator words of the context; the new accumulator keeps `h4 ≤ 4` and is
the fold of the `n` blocks modulo `p`.
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

theorem s_word {r v : UInt32} (hr : r.toNat < 2 ^ 28) (e : v = (addF 4 (UInt32.shiftRight r 2) r 0).1) :
    v.toNat = r.toNat + r.toNat / 4 := by
  rw [e, add_lo, shr_sem _ _ (by decide)]
  show (r.toNat / 2 ^ 2 + r.toNat + 0) % 2 ^ 32 = _
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem blocks_call (ic0 : UInt64) (G N : PMem) (U C : UInt32) (lU lC : List (Nat × UInt32)) (P : Nat → Prop)
    (hM : MemOK G N U 116 lU C 236 20 lC P) (n : Nat) (hn : 1 ≤ n) (hic : ic0.toNat + 61 + 184 * n < 2 ^ 63)
    (a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad h0 h1 h2 h3 h4 r0 r1 r2 r3 : UInt32)
    (hlU : LK lU [(104, ret), (108, len), (112, pad)])
    (hlC : LK lC [(0, h0), (4, h1), (8, h2), (12, h3), (16, h4), (20, r0), (24, r1), (28, r2), (32, r3)])
    (hlen : len.toNat = 16 * n) (E : ExtR G P inp (16 * n))
    (hinpU : inp.toNat + 16 * n ≤ U.toNat ∨ U.toNat + 116 ≤ inp.toNat)
    (hr0 : r0.toNat < 2 ^ 28) (hr1 : r1.toNat < 2 ^ 28) (hr2 : r2.toNat < 2 ^ 28) (hr3 : r3.toNat < 2 ^ 28)
    (hq1 : r1.toNat % 4 = 0) (hq2 : r2.toNat % 4 = 0) (hq3 : r3.toNat % 4 = 0)
    (hh4 : h4.toNat ≤ 4) (hpad : pad.toNat ≤ 1) :
    ∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf o0 o1 o2 o3 o4 : UInt32),
      Run img (St.m ⟨N.get, a0, C, inp, ebx0, UInt32.add U 104, ebp0, esi0, edi0, 0x1001b0, efl g0, icAdd ic0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 108, ebp0, esi0, edi0, ret, efl gf,
          icAdd ic0 (61 + 184 * n)⟩) ∧
      MemOK G N' U 116 lU' C 236 20 lC' P ∧
      LK lC' [(0, o0), (4, o1), (8, o2), (12, o3), (16, o4), (20, r0), (24, r1), (28, r2), (32, r3)] ∧
      o4.toNat ≤ 4 ∧
      val5 o0 o1 o2 o3 o4 % p = accB G (val4 r0 r1 r2 r3) pad.toNat inp n (val5 h0 h1 h2 h3 h4 % p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨N1, lU1, lC1, g13, v12, v8, v4, R1, M1, L1, LC1, e4, e8, e12⟩ :=
    blk_pro ic0 (by omega) G N U C lU lC P hM a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad h0 h1 h2 h3 h4 r0 r1 r2 r3
      hlU hlC (by have := E.fit; omega) (by omega)
  have hs1 := s_word hr1 e4
  have hs2 := s_word hr2 e8
  have hs3 := s_word hr3 e12
  obtain ⟨N2, lU2, lC2, o0, o1, o2, o3, o4, l2, c2, i2, b2, d2, g2, R2, M2, L2, LC2, ho4, hv⟩ :=
    blk_loop G U C P r0 r1 r2 r3 v4 v8 v12 esi0 edi0 ebx0 ebp0 ret len pad hr0 hr1 hr2 hr3 hq1 hq2 hq3 hs1 hs2 hs3
      hpad m (icAdd ic0 46) N1 lU1 lC1 len inp C ebp0 r3 g13 h0 h1 h2 h3 h4 M1
      (by rw [icAdd_toNat _ _ (by omega)]; omega) hlen E hinpU L1 LC1.2.2.2.2.2 hh4
  rw [icAdd0, icAdd_add] at R2
  obtain ⟨N3, lU3, lC3, g3, R3, M3, -, LC3⟩ :=
    blk_epi (icAdd (icAdd ic0 46) (184 * (m + 1)))
      (by rw [icAdd_toNat _ _ (by rw [icAdd_toNat _ _ (by omega)]; omega), icAdd_toNat _ _ (by omega)]; omega)
      G N2 U C lU2 lC2 P M2 l2 c2 i2 o3 b2 o4 d2 g2 o0 o2 o1 r0 v12 v8 r1 v4 r2 r3 esi0 edi0 ebx0 ebp0 ret len pad
      L2 LC2
  rw [icAdd0, icAdd_add, icAdd_add, show 46 + 184 * (m + 1) + 15 = 61 + 184 * (m + 1) by omega] at R3
  exact ⟨N3, lU3, lC3, C, o2, i2, g3, o0, o1, o2, o3, o4, R1.trans (R2.trans R3), M3, LC3, ho4, hv⟩

end Solutions.OpensslPoly1305
