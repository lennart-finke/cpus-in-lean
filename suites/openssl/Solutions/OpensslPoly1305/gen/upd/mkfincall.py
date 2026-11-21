"""Write Solutions/OpensslPoly1305/FinCall.lean: fin_blk adapted from UpdCall's upd_blk, plus fin_ms etc."""
import re
R = '/Users/pc/Code/cpus-in-lean/.claude/worktrees/suite-proofs/suites/openssl/Solutions/OpensslPoly1305/'
L = open(R + 'UpdCall.lean').read().split('\n')
blk = '\n'.join(L[82:155])   # set_option line .. end of upd_blk
reps = [
    ('theorem upd_blk', 'theorem fin_blk'),
    ('`poly1305_blocks(ctx, inp, 16 n, pad)` called from the `Update` frame (return address at `U + 224`)',
     '`poly1305_blocks(ctx, inp, 16 n, pad)` called from the `Final` frame (return address at `U + 236`)'),
    ('MemOK G N U 272 lU C 236 236 lC P', 'MemOK G N U 268 lU C 236 236 lC P'),
    ('(a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad w0 w1 w2 w3 w4 w5 w6 w7 w8 h0',
     '(a0 inp ebx0 ebp0 esi0 edi0 g0 ret len pad w0 w1 w2 w3 w4 h0'),
    ('''    (hlU : LK lU [(224, ret), (228, len), (232, pad), (236, w0), (240, w1), (244, w2), (248, w3), (252, w4),
      (256, w5), (260, w6), (264, w7), (268, w8)])''',
     '''    (hlU : LK lU [(236, ret), (240, len), (244, pad), (248, w0), (252, w1), (256, w2), (260, w3), (264, w4)])'''),
    ('E : ExtR N (BQ U C) inp (16 * n)', 'E : ExtR N (FQ U C) inp (16 * n)'),
    ('UInt32.add U 224, ebp0', 'UInt32.add U 236, ebp0'),
    ('UInt32.add U 228, ebp0', 'UInt32.add U 240, ebp0'),
    ('''      MemOK G N' U 272 [(236, w0), (240, w1), (244, w2), (248, w3), (252, w4), (256, w5), (260, w6), (264, w7),
        (268, w8)] C 236 236''', '''      MemOK G N' U 268 [(248, w0), (252, w1), (256, w2), (260, w3), (264, w4)] C 236 236'''),
    ('have e120 := hM.fU.add_toNat (j := 120) (by decide)', 'have e120 := hM.fU.add_toNat (j := 132) (by decide)'),
    ('hM.callee 120 116 (by decide)', 'hM.callee 132 116 (by decide)'),
    ('(BQ U C) (fun x h => h.1) (fun x h => h.2)', '(FQ U C) (fun x h => h.1) (fun x h => h.2)'),
    ('x < (UInt32.add U 120).toNat ∨ (UInt32.add U 120).toNat + 116 ≤ x', 'x < (UInt32.add U 132).toNat ∨ (UInt32.add U 132).toNat + 116 ≤ x'),
    ('blocks_call ic0 N N (UInt32.add U 120) C _ lC (BQ U C)', 'blocks_call ic0 N N (UInt32.add U 132) C _ lC (FQ U C)'),
    ('show (120 : UInt32) + 104 = 224 from rfl, show (120 : UInt32) + 108 = 228 from rfl',
     'show (132 : UInt32) + 104 = 236 from rfl, show (132 : UInt32) + 108 = 240 from rfl'),
    ('have hk : 236 ≤ k ∧ k ≤ 268 := by', 'have hk : 248 ≤ k ∧ k ≤ 264 := by'),
]
for a, b in reps:
    assert blk.count(a) >= 1, a
    blk = blk.replace(a, b)
hdr = '''import Solutions.OpensslPoly1305.FinMath
import Solutions.OpensslPoly1305.Memset
/-!
# Calls from `Poly1305_Final`: `poly1305_blocks` and `memset` in the caller's frame

As `UpdCall` for the `Final` frame (`[U, U + 268)`, entry stack pointer `U + 256`): `fin_blk` (callee
frame `U + 132`), `fin_ms` (`memset` through `OPENSSL_cleanse`, callee frame `U + 216`), and
`MemOK.switch` (the current memory as the reference of a run with another data region).
-/
namespace Solutions.OpensslPoly1305
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslPoly1305 Ssl.Spec.Poly1305

set_option autoImplicit false

variable {G N : PMem} {U C : UInt32} {nU nC mC : Nat} {lU lC : List (Nat × UInt32)} {P : Nat → Prop}

/-- What `poly1305_blocks` called from the `Final` frame keeps: outside its frame and `h`. -/
def FQ (U C : UInt32) (x : Nat) : Prop := OutF (UInt32.add U 132) 116 x ∧ OutF C 20 x

/-- The current memory as the reference memory of a run with another data region. -/
theorem MemOK.switch (h : MemOK G N U nU lU C nC mC lC P) (D : UInt32) (nD mD : Nat) (lD : List (Nat × UInt32))
    (hD : FB N.get.size D nD) (hDU : D.toNat + nD ≤ U.toNat ∨ U.toNat + nU ≤ D.toNat) (hlD : Frame N D nD lD)
    (Q : Nat → Prop) (hQU : ∀ x, Q x → OutF U nU x) (hQD : ∀ x, Q x → OutF D mD x) :
    MemOK N N U nU lU D nD mD lD Q :=
  ⟨h.fU, hD, hDU, h.wU, hlD, Pres.refl _ _, hQU, hQD⟩

/-- A run from `G'` continues a run from `G` (the preserved addresses compose). -/
theorem MemOK.rebase {G' : PMem} (h : MemOK G' N U nU lU C nC mC lC P) (hP : Pres G G' P) :
    MemOK G N U nU lU C nC mC lC P :=
  ⟨h.fU, h.fC, h.dUC, h.wU, h.wC, hP.trans h.pres, h.pU, h.pC⟩

/-- Words of a region survive a run that keeps their bytes. -/
theorem Frame.pres' {N' : PMem} {b : UInt32} {n : Nat} {l : List (Nat × UInt32)} (hF : Frame N b n l)
    (hS : FB N.get.size b n) {Q : Nat → Prop} (hP : Pres N N' Q)
    (hin : ∀ k v, l.lookup k = some v → ∀ j, j < 4 → Q (b.toNat + k + j)) : Frame N' b n l := by
  intro k v hl
  obtain ⟨a1, a2, a3⟩ := hF k v hl
  refine ⟨a1, a2, ?_⟩
  have e := Frame.add_toNat hS (k := k) (by omega)
  rw [← a3]
  exact hP.rd hS.top (by rw [e]; have := hS.fit; omega) (fun j hj => by rw [e]; exact hin k v hl j hj)

'''
open(R + 'FinCall.lean', 'w').write(hdr + blk + '\n' + open(
    '/Users/pc/Code/cpus-in-lean/.claude/worktrees/suite-proofs/suites/openssl/.lake/scratch/o/fincall_tail.part').read())
