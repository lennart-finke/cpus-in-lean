"""The ladder loop of x25519_scalar_mult_generic (0x103910): run pieces I/LadRun1.lean, I/LadRun2.lean.

    python3 genlad.py          (from this directory)

Frame [L, L + 344) (CSt region), esp in the body = L + 8: out pointer at L+8, bit at L+12, the scalar copy e
at L+16..L+47, buffers z3 L+48, x2 L+88, x3 L+128, tmp0 L+168, z2 L+208, x1 L+248, tmp1 L+288, saved
esi/edi/ebx/ebp at L+328..L+340, the return address at L+344, the u pointer at L+348.
The loop head (0x103990..0x1039aa) is in I/LadHead (lh1, lh2) and the hand-written pieces below (lh3, lp1);
the loop control (lc1, lc2t, lc2x) is hand-written too; the rest are the generic call pieces.
"""
import os, re

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
DIS = os.path.join(D, '..', '..', 'targets', 'openssl_x25519', 'image', 'openssl_x25519.dis')
N = 344
REGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']
LO, HI = 0x1039b8, 0x103aed   # after lp1's push (the call of lp1 is its own), up to the last `addl $4`


def listing(lo=0x103910, hi=0x103b3f):
    L = []
    for l in open(DIS):
        m = re.match(r'\s+([0-9a-f]+):\s+(\S+)\s*([^#<]*)', l)
        if m and lo <= int(m.group(1), 16) < hi and m.group(2) != 'int3':
            L.append((int(m.group(1), 16), m.group(2), m.group(3).strip().rstrip(',').strip()))
    for i, (a, mn, op) in enumerate(L):
        nxt = L[i + 1][0] if i + 1 < len(L) else hi
        L[i] = (a, mn, op, nxt)
    return L


def ladd(k):
    return 'L' if k == 0 else f'UInt32.add L {k}'


def sim(ins, esp0):
    r = {x: x for x in REGS}
    esp = esp0
    stores = []
    target = None
    for (a, mn, op, nxt) in ins:
        ops = [o.strip() for o in op.split(',')] if op else []
        if mn == 'movl' and ops[0].startswith('%') and ops[1].startswith('%'):
            r[ops[1][1:]] = r[ops[0][1:]]
        elif mn == 'leal':
            m = re.match(r'(0x[0-9a-f]+)?\(%esp\)', ops[0])
            k = int(m.group(1), 16) if m.group(1) else 0
            r[ops[1][1:]] = ('L', esp + k)
        elif mn == 'pushl':
            esp -= 4
            stores.append((esp, r[ops[0][1:]]))
        elif mn == 'calll':
            esp -= 4
            stores.append((esp, ('lit', nxt)))
            target = int(ops[0], 16)
        else:
            raise Exception(f'unhandled {mn} {op}')
    return r, stores, esp, target


def ex(v):
    if isinstance(v, str):
        return v
    if v[0] == 'L':
        return ladd(v[1])
    return '0x%x' % v[1]


def pex(v):
    e = ex(v)
    return f'({e})' if ' ' in e else e


def mem_of(stores):
    m = 'N'
    first = True
    for (off, v) in stores:
        hs = 'hS' if first else 'stF_FB'
        if off == 0:
            m = f'(stF0 {m} L {N} {pex(v)} {hs} (by decide))'
        else:
            m = f'(stF {m} L {N} {off} {pex(v)} {hs} (by decide))'
        first = False
    return m


def piece_thm(name, ins, esp0, doc):
    r, stores, esp, target = sim(ins, esp0)
    a0 = ins[0][0]
    a1 = target if target is not None else ins[-1][3]
    n = len(ins)
    out = ', '.join(ex(r[x]) for x in REGS[:4]) + f', {ladd(esp)}, ' + ', '.join(ex(r[x]) for x in REGS[4:])
    inp = f'N.get, eax, ecx, edx, ebx, {ladd(esp0)}, ebp, esi, edi'
    pre = 'set_option exec.addrSub true in\n' if stores else ''
    return f"""
{pre}/-- {doc} -/
theorem {name} (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L {N})
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨{inp}, 0x{a0:x}, efl fl, icAdd ic 0⟩)
      (St.m ⟨{mem_of(stores)}.get, {out}, 0x{a1:x}, efl fl, icAdd ic {n}⟩) := by
  refine run_of_runI (k := {n}) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
""", dict(regs=r, stores=stores, esp=esp, target=target, n=n, a0=a0, a1=a1)


def addl_thm(name, a0):
    return f"""
/-- `addl $0x4, %esp` -/
theorem {name} (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L {N})
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x{a0:x}, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x{a0 + 3:x},
        efl (addF 4 (UInt32.add L 4) 4 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
"""


def segments():
    segs, cur = [], []
    for ins in listing(LO, HI + 3):
        cur.append(ins)
        if ins[1] == 'calll':
            segs.append(cur)
            cur = []
    assert len(cur) == 1 and cur[0][1] == 'addl', cur
    return segs, cur[0]


def pieces():
    segs, last = segments()
    ps, calls = [], []
    # the first segment is lp1's tail? no: LO is lp1's push, handled by hand; segs[0] = [push, call]
    assert segs[0][0][1] == 'pushl' and segs[0][1][1] == 'calll'
    k = 1
    for s in segs[1:]:
        ins = list(s)
        addl = None
        if ins[0][1] == 'addl':
            addl = f'lad_a{k}'
            ps.append((addl, addl_thm(addl, ins[0][0]), dict(n=1)))
            ins = ins[1:]
        name = f'lad_p{k}'
        doc = ' ; '.join(f'{mn} {op}' for (a, mn, op, nxt) in ins)
        txt, inf = piece_thm(name, ins, 8, '`' + doc + '`')
        ps.append((name, txt, inf))
        calls.append(dict(piece=name, info=inf, addl=addl))
        k += 1
    ps.append(('lad_a_end', addl_thm('lad_a_end', last[0]), dict(n=1)))
    return ps, calls


HDR = """import Solutions.OpensslX25519.Frame
import Solutions.OpensslX25519.I.Base
import Solutions.OpensslX25519.ShapesSq1
import Solutions.OpensslX25519.ShapesSq2
import Solutions.OpensslX25519.ShapesSq3
import Solutions.OpensslX25519.ShapesSq4
import Solutions.OpensslX25519.ShapesMul1
import Solutions.OpensslX25519.ShapesMul2
import Solutions.OpensslX25519.I.ShapesM121
import Solutions.OpensslX25519.I.ShapesX1
import Solutions.OpensslX25519.I.ShapesX2
import Solutions.OpensslX25519.I.ShapesX3
import Solutions.OpensslX25519.I.ShapesX4
import Solutions.Exec.Mul
import Solutions.Exec.Alu
import Solutions.Exec.Branch
import Solutions.Exec.Byte
/-!
# The ladder loop of `x25519_scalar_mult_generic` between its calls, part {part}

Generated by `gen/genlad.py`: the instructions that load the arguments of each call in the loop body
and execute the `call` (memory: the return address, and the pushed argument, stored below `L + 8`), and
the release of the argument after the calls with one. The frame is `[L, L + 344)`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000
"""

if __name__ == '__main__':
    ps, calls = pieces()
    PER = 20
    chunks = [ps[i:i + PER] for i in range(0, len(ps), PER)]
    for fi, ch in enumerate(chunks):
        txt = HDR.replace('{part}', str(fi + 1)) + ''.join(p[1] for p in ch)
        txt += '\nend Solutions.OpensslX25519.I\n'
        open(os.path.join(D, 'I', 'LadRun%d.lean' % (fi + 1)), 'w').write(txt)
    print(len(ps), 'pieces', len(calls), 'calls', len(chunks), 'files')
