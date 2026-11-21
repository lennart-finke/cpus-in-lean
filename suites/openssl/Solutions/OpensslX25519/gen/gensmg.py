"""x25519_scalar_mult_generic (0x103910) outside the ladder loop: run pieces I/SmgRun1.lean, I/SmgRun2.lean (prover R).

    python3 gensmg.py          (from this directory)

SmgRun1: frame base `Lb = L - 32`, `FB Lb 384` (`[L - 32, L + 352)`): entry esp `Lb + 376` (return address,
u pointer at `Lb + 380`), prologue (pushes, `subl`, output pointer, memcpy call), the clamp, the cleanse call and
the epilogue. SmgRun2: frame base `L` (the `CSt` region `[L, L + 344)`, esp `L + 8`): the calls between the
clamp and the cleanse (genlad.piece_thm), the loop entry and the fe_tobytes call. Hand-written pieces are in
gen/smgrun1.lean.in, gen/smgrun2.lean.in.
"""
import os
import genlad

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')


def ins_range(lo, hi):
    return [x for x in genlad.listing() if lo <= x[0] < hi]


def run2():
    out = []
    for (name, lo, hi) in [('smg_b1', 0x103946, 0x103956), ('smg_b2', 0x103956, 0x10395f),
                           ('smg_b3', 0x10395f, 0x10396b), ('smg_b4', 0x10396b, 0x103976),
                           ('smg_b5', 0x103976, 0x10397f), ('smg_b7', 0x103afd, 0x103b0d),
                           ('smg_b8', 0x103b0d, 0x103b1b)]:
        ins = ins_range(lo, hi)
        doc = ' ; '.join(f'{mn} {op}' for (a, mn, op, nxt) in ins)
        txt, inf = genlad.piece_thm(name, ins, 8, '`' + doc + '`')
        out.append(txt)
    out.append(genlad.addl_thm('smg_a9', 0x103b1b))
    return ''.join(out)


if __name__ == '__main__':
    t1 = open(os.path.join(G, 'smgrun1.lean.in')).read()
    open(os.path.join(D, 'I', 'SmgRun1.lean'), 'w').write(t1)
    t2 = open(os.path.join(G, 'smgrun2.lean.in')).read().replace('-- @@PIECES', run2())
    open(os.path.join(D, 'I', 'SmgRun2.lean'), 'w').write(t2)
    print('ok')
