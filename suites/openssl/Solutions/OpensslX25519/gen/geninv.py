"""fe_invert (0x1005d0) as a callee: run pieces I/InvRun*.lean and the main proof I/InvCall.lean.

    python3 geninv.py          (from this directory)

Frame: entry stack pointer S = L + 188 (L = the lowest stack pointer, below the argument and return address
of a `fe_mul` call), fb = L + 8 (esp in the body); out pointer at L+8, buffers t3 = L+12, t0 = L+52,
t2 = L+92, t1 = L+132, saved esi/edi/ebx/ebp at L+172..L+184, the return address at L+188.
"""
import os, re

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
DIS = os.path.join(D, '..', '..', 'targets', 'openssl_x25519', 'image', 'openssl_x25519.dis')
SQ, MUL = 0x102360, 0x100c20
N = 192
REGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']


def listing():
    L = []
    for l in open(DIS):
        m = re.match(r'\s+([0-9a-f]+):\s+(\S+)\s*([^#<]*)', l)
        if m and 0x1005d0 <= int(m.group(1), 16) < 0x100c11 and m.group(2) != 'int3':
            L.append((int(m.group(1), 16), m.group(2), m.group(3).strip().rstrip(',').strip()))
    for i, (a, mn, op) in enumerate(L):
        nxt = L[i + 1][0] if i + 1 < len(L) else 0x100c11
        L[i] = (a, mn, op, nxt)
    return L


def ladd(k):
    return 'L' if k == 0 else f'UInt32.add L {k}'


class Piece:
    def __init__(self, name, ins, esp0, kind):
        self.name, self.ins, self.esp0, self.kind = name, ins, esp0, kind


def sim(ins, esp0):
    """registers (input names or L-offsets), stores [(off, val)], loads [(off, var)], end esp, target"""
    r = {x: x for x in REGS}
    esp = esp0
    stores, loads = [], []
    target = None
    for (a, mn, op, nxt) in ins:
        ops = [o.strip() for o in op.split(',')] if op else []
        if mn == 'movl' and ops[0].startswith('%') and ops[1].startswith('%'):
            r[ops[1][1:]] = r[ops[0][1:]]
        elif mn == 'leal':
            m = re.match(r'(0x[0-9a-f]+)?\(%esp\)', ops[0])
            k = int(m.group(1), 16) if m.group(1) else 0
            r[ops[1][1:]] = ('L', esp + k)
        elif mn == 'movl' and ops[1] == '(%esp)':
            stores.append((esp, r[ops[0][1:]]))
        elif mn == 'movl' and ops[0] == '(%esp)':
            loads.append((esp, 'o'))
            r[ops[1][1:]] = 'o'
        elif mn == 'pushl':
            esp -= 4
            stores.append((esp, r[ops[0][1:]]))
        elif mn == 'calll':
            esp -= 4
            stores.append((esp, ('lit', nxt)))
            target = int(ops[0], 16)
        elif mn == 'nop':
            pass
        elif mn == 'movl' and ops[0].startswith('$'):
            r[ops[1][1:]] = ('lit', int(ops[0][1:], 16))
        else:
            raise Exception(f'unhandled {mn} {op}')
    return r, stores, loads, esp, target


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
    r, stores, loads, esp, target = sim(ins, esp0)
    a0 = ins[0][0]
    a1 = target if target is not None else ins[-1][3]
    n = len(ins)
    params = 'eax ecx edx ebx ebp esi edi fl' + (' o' for _ in loads).__next__() if loads else 'eax ecx edx ebx ebp esi edi fl'
    hyps = ''.join(f'\n    (l{off} : rdRaw N.get (UInt32.add L {off}) 4 = o)' for (off, _) in loads)
    subst = ''.join(f'\n  subst l{off}' for (off, _) in loads)
    out = ', '.join(ex(r[x]) for x in REGS[:4]) + f', {ladd(esp)}, ' + ', '.join(ex(r[x]) for x in REGS[4:])
    inp = f'N.get, eax, ecx, edx, ebx, {ladd(esp0)}, ebp, esi, edi'
    pre = 'set_option exec.addrSub true in\n' if stores else ''
    return f"""
{pre}/-- {doc} -/
theorem {name} (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L {N})
    ({params} : UInt32){hyps} :
    Run img (St.m ⟨{inp}, 0x{a0:x}, efl fl, icAdd ic 0⟩)
      (St.m ⟨{mem_of(stores)}.get, {out}, 0x{a1:x}, efl fl, icAdd ic {n}⟩) := by
  refine run_of_runI (k := {n}) ?_ (icB hic (by decide)){subst}
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
""", dict(regs=r, stores=stores, loads=loads, esp=esp, target=target, n=n, a0=a0, a1=a1)


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
# The run of `fe_invert` between its calls, part {part}

Generated by `gen/geninv.py`: the instructions that load the arguments of each call of `fe_sq`/`fe_mul`
and execute the `call` (memory: the return address, and the third argument of `fe_mul`, stored below
`L + 8`), the release of the argument after `fe_mul`, the loop control. The frame is `[L, L + 192)`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Branch Solutions.Exec.Byte

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000
"""


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
    L = listing()
    # prologue: pushes, sub, the stores before the first call
    i = 0
    segs = []
    cur = []
    for ins in L:
        if ins[1] == 'nop' and not cur:
            continue
        cur.append(ins)
        if ins[1] in ('calll', 'retl'):
            segs.append(cur)
            cur = []
    return segs


def main_pieces():
    segs = segments()
    pieces = []   # (name, text, info)
    calls = []    # per call: dict
    # segment 0: pro (4 pushes) | sub | c0a (4 instrs) | c0b (call)
    s0 = segs[0]
    pro, sub, c0a, c0b = s0[0:4], s0[4:5], s0[5:9], s0[9:10]
    txt, inf = piece_thm('inv_c0a', c0a, 8, '`movl %edx, %esi ; movl %ecx, (%esp) ; leal 0x2c(%esp), %edi ; movl %edi, %ecx`')
    pieces.append(('inv_c0a', txt, inf))
    txt, inf = piece_thm('inv_c0b', c0b, 8, '`calll fe_sq`')
    pieces.append(('inv_c0b', txt, inf))
    calls.append(dict(piece='inv_c0b', info=inf, addl=None))
    k = 1
    for s in segs[1:]:
        if s[-1][1] == 'retl':
            break
        ins = [x for x in s]
        addl = None
        if ins[0][1] == 'addl':
            addl = f'inv_a{k}'
            pieces.append((addl, addl_thm(addl, ins[0][0]), dict(n=1)))
            ins = ins[1:]
        if ins[0][1] == 'decl':
            # the loop exit `decl %edi ; jne` (handwritten pieces), then the call
            ins = ins[2:]
            while ins[0][1] == 'nop':
                ins = ins[1:]
            loopx = True
        else:
            loopx = False
        if ins[0][1] == 'movl' and ins[0][2].startswith('$0x63'):
            # `movl $0x63, %edi ; nop ; nop`, then the loop
            name = 'inv_l0'
            pre = [x for x in ins[:1]]
            txt, inf = piece_thm(name, pre + [x for x in listing() if 0x1009de <= x[0] < 0x1009e0], 8,
                                 '`movl $0x63, %edi ; nop ; nop`')
            pieces.append((name, txt, inf))
            calls.append(dict(loop=True, addl=addl, pre=name))
            k += 1
            continue
        name = f'inv_p{k}'
        doc = ' ; '.join(f'{mn} {op}' for (a, mn, op, nxt) in ins)
        txt, inf = piece_thm(name, ins, 8, '`' + doc + '`')
        pieces.append((name, txt, inf))
        calls.append(dict(piece=name, info=inf, addl=addl, loopx=loopx))
        k += 1
    return pieces, calls


LOOP = """
set_option exec.addrSub true in
/-- The loop body: `movl %esi, %ecx ; movl %esi, %edx ; calll fe_sq` -/
theorem inv_lb (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1009e0, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF N L 192 4 0x1009e9 hS (by decide)).get, eax, esi, esi, ebx, UInt32.add L 4, ebp, esi, edi, 0x102360,
        efl fl, icAdd ic 3⟩) := by
  refine run_of_runI (k := 3) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `decl %edi ; jne` (taken) -/
theorem inv_lj (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) (hx : edi.toNat ≠ 1) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1009e9, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, (subF 4 edi 1 0).1, 0x1009e0,
        efl (mixF fl (subF 4 edi 1 0).2 2260), icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `decl %edi ; jne` (not taken) -/
theorem inv_lx (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) (hx : edi.toNat = 1) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1009e9, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, (subF 4 edi 1 0).1, 0x1009ec,
        efl (mixF fl (subF 4 edi 1 0).2 2260), icAdd ic 2⟩) := by
  refine run_of_runI (k := 2) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

set_option exec.addrSub true in
/-- `pushl %ebp ; pushl %ebx ; pushl %edi ; pushl %esi` -/
theorem inv_pro (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 188, ebp, esi, edi, 0x1005d0, efl fl, icAdd ic 0⟩)
      (St.m ⟨(stF (stF (stF (stF N L 192 184 ebp hS (by decide)) L 192 180 ebx stF_FB (by decide)) L 192 176 edi
        stF_FB (by decide)) L 192 172 esi stF_FB (by decide)).get, eax, ecx, edx, ebx, UInt32.add L 172, ebp, esi, edi,
        0x1005d4, efl fl, icAdd ic 4⟩) := by
  refine run_of_runI (k := 4) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

theorem inv_esp_sub (L : UInt32) : (subF 4 (UInt32.add L 172) 164 0).1 = UInt32.add L 8 := by
  rw [subF_fst]; show L + 172 - 164 = L + 8
  rw [UInt32.sub_eq_add_neg, UInt32.add_assoc]; rfl

/-- `subl $0xa4, %esp` -/
theorem inv_sub (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 172, ebp, esi, edi, 0x1005d4, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 8, ebp, esi, edi, 0x1005da,
        efl (subF 4 (UInt32.add L 172) 164 0).2, icAdd ic 1⟩) := by
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  have h : runI img 1 (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 172, ebp, esi, edi, 0x1005d4, efl fl, icAdd ic 0⟩) =
      some (St.m ⟨N.get, eax, ecx, edx, ebx, (subF 4 (UInt32.add L 172) 164 0).1, ebp, esi, edi, 0x1005da,
        efl (subF 4 (UInt32.add L 172) 164 0).2, icAdd ic 1⟩) := by
    cbv
  rw [inv_esp_sub] at h
  exact run_of_runI h (icB hic (by decide))

/-- `addl $0xa8, %esp` -/
theorem inv_add (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl : UInt32) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 4, ebp, esi, edi, 0x100c06, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 172, ebp, esi, edi, 0x100c0c,
        efl (addF 4 (UInt32.add L 4) 168 0).2, icAdd ic 1⟩) := by
  refine run_of_runI (k := 1) ?_ (icB hic (by decide))
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv

/-- `popl %esi ; popl %edi ; popl %ebx ; popl %ebp ; retl` -/
theorem inv_epi (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (N : XMem) (L : UInt32) (hS : FB N.get.size L 192)
    (eax ecx edx ebx ebp esi edi fl esi0 edi0 ebx0 ebp0 ret : UInt32)
    (l1 : rdRaw N.get (UInt32.add L 172) 4 = esi0) (l2 : rdRaw N.get (UInt32.add L 176) 4 = edi0)
    (l3 : rdRaw N.get (UInt32.add L 180) 4 = ebx0) (l4 : rdRaw N.get (UInt32.add L 184) 4 = ebp0)
    (l5 : rdRaw N.get (UInt32.add L 188) 4 = ret) :
    Run img (St.m ⟨N.get, eax, ecx, edx, ebx, UInt32.add L 172, ebp, esi, edi, 0x100c0c, efl fl, icAdd ic 0⟩)
      (St.m ⟨N.get, eax, ecx, edx, ebx0, UInt32.add L 192, ebp0, esi0, edi0, ret, efl fl, icAdd ic 5⟩) := by
  refine run_of_runI (k := 5) ?_ (icB hic (by decide))
  subst l1 l2 l3 l4 l5
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
"""


if __name__ == '__main__':
    pieces, calls = main_pieces()
    PER = 30
    files = []
    chunks = [pieces[i:i + PER] for i in range(0, len(pieces), PER)]
    for fi, ch in enumerate(chunks):
        txt = HDR.replace('{part}', str(fi + 1)) + ''.join(p[1] for p in ch)
        if fi == 0:
            txt += LOOP
        txt += '\nend Solutions.OpensslX25519.I\n'
        open(os.path.join(D, 'I', 'InvRun%d.lean' % (fi + 1)), 'w').write(txt)
        files.append(fi + 1)
    print(len(pieces), 'pieces', len(calls), 'calls', 'files', files)
