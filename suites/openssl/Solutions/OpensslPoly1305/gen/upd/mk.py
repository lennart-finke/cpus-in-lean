"""mk.py IN OUT (e.g. python3 mk.py UpdOk.lean.in ../../UpdOk.lean): substitute tokens (LKn lookup proofs, SIG/CONCL of the Update paths, RCn rcases patterns)"""
import sys, re
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_lk_mod import chain
s = open(sys.argv[1]).read()
for n in (13, 9, 5, 4):
    s = s.replace('LK%d' % n + '\n', chain(n) + '\n')
SIG = """(key msg chunk : List UInt8) (G : PMem) (U C inp len : UInt32)
    (lU : List (Nat × UInt32)) (P : Nat → Prop) (hM : MemOK G G U 272 lU C 236 236 (lC0 G C) P)
    (hg : GoodB key msg (memBytes G.get C 236)) (hlen : len.toNat = chunk.length)
    (hch : memBytes G.get inp chunk.length = chunk) (E : chunk.length ≠ 0 → ExtR G P inp chunk.length)
    (ret a0 c0 d0 ebx0 ebp0 esi0 edi0 g0 : UInt32) (hlU : LK lU [(256, ret), (260, C), (264, inp), (268, len)])"""
CONCL = """∃ (N' : PMem) (lU' lC' : List (Nat × UInt32)) (eax ecx edx gf : UInt32) (ic : UInt64),
      Run img (St.m ⟨G.get, a0, c0, d0, ebx0, UInt32.add U 256, ebp0, esi0, edi0, 0x1000e0, efl g0, icAdd 0 0⟩)
        (St.m ⟨N'.get, eax, ecx, edx, ebx0, UInt32.add U 260, ebp0, esi0, edi0, ret, efl gf, ic⟩) ∧
      MemOK G N' U 272 lU' C 236 236 lC' P ∧ LK lU' [(256, ret), (260, C), (264, inp), (268, len)] ∧
      GoodB key (msg ++ chunk) (memBytes N'.get C 236)"""
s = s.replace(' SIG\n', ' ' + SIG + '\n').replace('    CONCL := by', '    ' + CONCL + ' := by')
s = re.sub(r'RC(\d+)', lambda m: ' | '.join(['⟨rfl, rfl⟩'] * int(m.group(1))), s)
open(sys.argv[2], 'w').write(s)
