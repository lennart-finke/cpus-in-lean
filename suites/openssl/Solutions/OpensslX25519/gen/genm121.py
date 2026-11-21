"""fe_mul121666: listing m121.txt and the call-level run pieces I/M121Run*.lean (gensq + icall).

    python3 genm121.py          (from this directory)
"""
import os, re
import gensq
import icall

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
DIS = os.path.join(D, '..', '..', 'targets', 'openssl_x25519', 'image', 'openssl_x25519.dis')

lines = []
for l in open(DIS):
    m = re.match(r'\s+([0-9a-f]+):\s+(\S+)\s*([^#]*)', l)
    if m and 0x103c00 <= int(m.group(1), 16) < 0x103e80 and m.group(2) != 'int3':
        lines.append(('%s %s %s' % (m.group(1), m.group(2), m.group(3).strip())).strip())
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm121.txt'), 'w').write('\n'.join(lines) + '\n')

gensq.FS = 88
gensq.WS = 84
gensq.PRE = 'm121'
gensq.BODY = (0x103c07, 0x103e38)
gensq.SLOTS = {0x50: 'ebp0', 0x4c: 'ebx0', 0x48: 'edi0', 0x44: 'esi0'}
gensq.PTRS = ['fp']
gensq.HDR = gensq.HDR.replace("import Solutions.OpensslX25519.ShapesSq4\n",
                              "import Solutions.OpensslX25519.ShapesSq4\nimport Solutions.OpensslX25519.ShapesMul1\n"
                              "import Solutions.OpensslX25519.ShapesMul2\nimport Solutions.OpensslX25519.I.ShapesM121\n")

if __name__ == '__main__':
    out, m = gensq.run(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm121.txt'))
    doc = '''/-!
# The run of `fe_mul121666`, pieces {a}–{b}

Generated (`gen/genm121.py`, via gensq and icall) from the disassembly: each piece runs at most eight
instructions by `cbv` from a memory `N` whose frame words are listed in `l`, and states the values it
computes as single-operation equations over its inputs.
-/
'''
    hdr = gensq.HDR.replace("namespace Solutions", doc + "namespace Solutions", 1)
    PER = 6
    names = []
    for f in range(0, len(out), PER):
        a_, b_ = f, min(f + PER - 1, len(out) - 1)
        nm = "M121Run%02d" % (f // PER + 1)
        txt = hdr.format(a=a_, b=b_) + "".join(gensq.lemma(p) for p in out[a_:b_ + 1]) + \
            "\nend Solutions.OpensslX25519\n"
        txt, ns = icall.piece(txt)
        names += ns
        open(os.path.join(D, 'I', nm + '.lean'), 'w').write(txt)
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm121names.txt'), 'w').write('\n'.join(names) + '\n')
    print(len(out), 'pieces', out[-1]['ic1'], 'last count')
    G = os.path.dirname(os.path.abspath(__file__))
    txt, ns = icall.piece(open(os.path.join(G, 'm121ends.lean.in')).read())
    open(os.path.join(D, 'I', 'M121Ends.lean'), 'w').write(txt)
    open(os.path.join(G, 'm121names.txt'), 'a').write('\n'.join(ns) + '\n')
    print('ends', ns)
