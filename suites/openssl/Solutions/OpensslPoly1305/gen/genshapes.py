"""Shape modules of the Poly1305 image: the decode_shape commands (Solutions/Exec/shapes.py) for
0x100000..0x1005f8 that the committed X25519 shape modules do not already define, in 4 modules
Solutions/OpensslPoly1305/Shapes{1..4}.lean.

    cd suites/openssl
    python3 Solutions/Exec/shapes.py Ssl/OpensslPoly1305/Image.lean \
        targets/openssl_poly1305/image/openssl_poly1305.dis 100000 1005f8 > /tmp/all.txt
    python3 Solutions/OpensslPoly1305/gen/genshapes.py /tmp/all.txt
"""
import glob, os, re, sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
ROOT = os.path.join(D, '..', '..')
pat = re.compile(r'^decode_shape \[[^]]*\] [0-9]+', re.M)
have = set()
for f in glob.glob(os.path.join(ROOT, 'Solutions', 'OpensslX25519', '**', '*.lean'), recursive=True):
    have |= set(pat.findall(open(f).read()))
alls = sorted(set(pat.findall(open(sys.argv[1]).read())))
new = [s for s in alls if s not in have]
N = 4
per = (len(new) + N - 1) // N
for k in range(N):
    part = new[k * per:(k + 1) * per]
    txt = f"""import Solutions.Exec.Shape
/-!
# Decoded instruction shapes of the Poly1305 image ({k + 1}/{N})

The `decode_shape` theorems (`Solutions.Exec.Shape`) for the instructions of the image
(`targets/openssl_poly1305`) that the X25519 shape modules (imported by `Solutions.OpensslPoly1305.Shapes`)
do not define; written by `gen/genshapes.py` from `Solutions/Exec/shapes.py`.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

""" + "\n".join(part) + "\n"
    open(os.path.join(D, f'Shapes{k + 1}.lean'), 'w').write(txt)
print(len(new), 'new shapes,', per, 'per module')
