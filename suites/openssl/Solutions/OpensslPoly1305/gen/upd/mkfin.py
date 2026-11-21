"""mkfin.py IN OUT : substitute FSIG/FCONCL/LK5/LK9S in FinOk.lean.in"""
import sys


def lk(i):
    pf = "lk_here"
    for _ in range(i):
        pf = "lk_skip lk_here rfl" if pf == "lk_here" else f"lk_skip ({pf}) rfl"
    return pf


s = open(sys.argv[1]).read()
FSIG = """(key msg : List UInt8) (G : PMem) (U C mac : UInt32) (lU : List (Nat × UInt32))
    (P : Nat → Prop) (hM : MemOK G G U 268 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hP : ∀ x, PT U C mac x → P x)
    (hmf : mac.toNat + 16 ≤ G.get.size) (hmi : mac.toNat + 16 ≤ 0x100000 ∨ 0x100000 + 1536 ≤ mac.toNat)
    (hmU : mac.toNat + 16 ≤ U.toNat ∨ U.toNat + 268 ≤ mac.toNat)
    (hmC : mac.toNat + 16 ≤ C.toNat ∨ C.toNat + 236 ≤ mac.toNat)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, mac)])"""
FCONCL = """∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x100460, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 268 lU' mac 16 16 lC' (PT U C mac) ∧ LK lU' [(256, ret), (260, C), (264, mac)] ∧
      memBytes N'.get mac 16 = poly1305 key msg ∧ ∀ j, j < 236 → memByte N'.get (C + j.toUInt32) = 0"""
s = s.replace(' FSIG\n', ' ' + FSIG + '\n').replace('    FCONCL := by', '    ' + FCONCL + ' := by')
s = s.replace('LK5', '⟨' + ', '.join([lk(i) for i in range(5)] + ['trivial']) + '⟩')
s = s.replace('LK9S', '⟨' + ', '.join([lk(i) for i in (0, 1, 2, 3, 4, 9, 10, 11, 12)] + ['trivial']) + '⟩')
open(sys.argv[2], 'w').write(s)
