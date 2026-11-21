"""fe_frombytes (0x1036f0): run pieces I/FbRun*.lean (prover Q).

    python3 gentfb.py [PER]      (from this directory)

Frame: L = sp - 68 (FB L 72): the return address of the calls to load_3/load_4 at L, the body's esp = L + 4
(slot o at L + 4 + o: h pointer at 0x2c), saved esi/edi/ebx/ebp at L + 52 … L + 64, the return address at L + 68.
Each call (`calll`, the callee's body, `retl`) runs inside one piece. Values are SSA names with defining equations;
the body pieces run from 0x1036f7 to 0x1038cf (the output stores, prologue and epilogue are in FbEnds).
"""
import os, re, json
from asm import parse_op, split_ops

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
STREGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']
BODY = (0x1036f7, 0x1038cf)
LOAD3, LOAD4 = 0x101e00, 0x101e10


def lit(v):
    return str(v & 0xFFFFFFFF)


def addr_t(base, d):
    return base if d == 0 else f"(UInt32.add {base} {d})"


class Ins:
    def __init__(self, addr, mn, ops, nxt, target=None):
        self.addr, self.mn, self.ops, self.nxt, self.target = addr, mn, ops, nxt, target


def read():
    rows = []
    for line in open(os.path.join(G, 'frombytes.txt')):
        parts = line.strip().split(' ', 2)
        a = int(parts[0], 16)
        mn = parts[1]
        if mn == 'calll':
            rows.append((a, mn, [], int(parts[2].split()[0], 16)))
        else:
            rows.append((a, mn, split_ops(parts[2]) if len(parts) > 2 else [], None))
    out = []
    for i, (a, mn, ops, t) in enumerate(rows):
        out.append(Ins(a, mn, ops, rows[i + 1][0] if i + 1 < len(rows) else None, t))
    return out


class M:
    def __init__(self):
        self.regs = {'eax': 'a0', 'ecx': 'hp', 'edx': 's', 'ebx': 'ebx0', 'ebp': 'ebp0', 'esi': 'esi0', 'edi': 'edi0'}
        self.flag = 'g0'
        self.slots = {}
        self.n = 0
        self.ng = 0
        self.nx = 0
        self.defs = []
        self.loads = []     # all ext loads (addr term, size, name)

    def reset(self):
        self.p_in = dict(self.regs)
        self.p_inflag = self.flag
        self.p_defs, self.p_sl, self.p_xl, self.p_fs = [], [], [], []
        self.p_written = set()
        self.p_xdefs = []

    def new(self, t, flag=False):
        if flag:
            self.ng += 1
            nm = f"g{self.ng}"
        else:
            self.n += 1
            nm = f"v{self.n}"
        self.p_defs.append((nm, t))
        self.defs.append((nm, t))
        return nm

    def slot_load(self, off):
        nm = self.slots[off]
        if off not in self.p_written and (off, nm) not in self.p_sl:
            self.p_sl.append((off, nm))
        return nm

    def slot_store(self, off, v):
        self.slots[off] = v
        self.p_written.add(off)
        self.p_fs.append((off, v))

    def ext(self, a, size):
        for (aa, ss, nm, _) in self.p_xl:
            if aa == a and ss == size:
                return nm
        self.nx += 1
        nm = f"y{self.nx}"
        self.p_xl.append((a, size, nm, len(self.p_fs) if size == 2 else 0))
        self.loads.append((a, size, nm))
        return nm

    def get(self, o):
        if o.kind == 'reg':
            return self.regs[o.r]
        if o.kind == 'imm':
            return lit(o.v)
        assert o.base == 'esp' and o.idx is None
        return self.slot_load(o.disp + 4)

    def put(self, o, v):
        if o.kind == 'reg':
            self.regs[o.r] = v
        else:
            assert o.base == 'esp'
            self.slot_store(o.disp + 4, v)

    def sreg(self):
        """the input pointer register value as `s + k`"""
        e = self.regs['ecx']
        if e == 's':
            return 's', 0
        if e not in [n for (n, _) in self.p_defs] and e not in [n for (n, _) in self.p_xdefs]:
            self.p_xdefs.append((e, dict(self.defs)[e]))
        m = re.fullmatch(r'v\d+', e)
        t = dict(self.defs)[e]
        mm = re.fullmatch(r'UInt32\.add s (\d+)', t)
        assert mm, (e, t)
        return 's', int(mm.group(1))

    def call(self, i):
        # pushl return address at frame offset 0 (esp = L)
        self.slot_store(0, lit(i.nxt))
        base, k = self.sreg()
        if i.target == LOAD4:
            w = self.ext(addr_t('s', k), 4)
            self.regs['eax'] = w
        else:
            lo = self.ext(addr_t('s', k), 2)
            hi = self.ext(addr_t('s', k + 2), 1)
            sh = self.new(f"shlR {hi} 16")
            self.new(f"shlF {hi} 16", True)
            r = self.new(f"(logicF 4 (UInt32.lor {sh} {lo})).1")
            self.new(f"(logicF 4 (UInt32.lor {sh} {lo})).2", True)
            self.regs['eax'] = r
        self.regs['edx'] = '0'
        self.flag = self.new("(logicF 4 0).2", True)
        return 3 if i.target == LOAD4 else 6

    def step(self, i):
        mn, ops = i.mn, i.ops
        if mn == 'calll':
            return 1 + self.call(i)
        if mn == 'movl':
            self.put(ops[1], self.get(ops[0]))
        elif mn == 'leal':
            m = ops[0]
            b = self.regs[m.base] if m.base else None
            if m.idx:
                ix = self.regs[m.idx]
                sh = {1: 0, 2: 1, 4: 2, 8: 3}[m.sc]
                it = ix if sh == 0 else f"(UInt32.shiftLeft {ix} {sh})"
                t = f"UInt32.add {b} {it}" if b else f"UInt32.add 0 {it}"
            else:
                t = b
            if m.disp:
                t = f"UInt32.add {t if ' ' not in t else '(' + t + ')'} {lit(m.disp)}"
            self.regs[ops[1].r] = self.new(t)
        elif mn in ('shrl', 'shll'):
            k = ops[0].v
            a = self.get(ops[1])
            f = {'shrl': ('shrR', 'shrF'), 'shll': ('shlR', 'shlF')}[mn]
            r = self.new(f"{f[0]} {a} {k}")
            self.flag = self.new(f"{f[1]} {a} {k}", True)
            self.put(ops[1], r)
        elif mn == 'addl':
            a = self.get(ops[1])
            b = self.get(ops[0])
            r = self.new(f"UInt32.add {a} {b}")
            self.flag = self.new(f"(addF 4 {a} {b} 0).2", True)
            self.put(ops[1], r)
        elif mn == 'adcl':
            a = self.get(ops[1])
            b = self.get(ops[0])
            r = self.new(f"(addF 4 {a} {b} (cfBit {self.flag})).1")
            self.flag = self.new(f"(addF 4 {a} {b} (cfBit {self.flag})).2", True)
            self.put(ops[1], r)
        elif mn == 'subl':
            a = self.get(ops[1])
            b = self.get(ops[0])
            r = self.new(f"(subF 4 {a} {b} 0).1")
            self.flag = self.new(f"(subF 4 {a} {b} 0).2", True)
            self.put(ops[1], r)
        elif mn == 'andl':
            a = self.get(ops[1])
            b = self.get(ops[0])
            r = self.new(f"(logicF 4 (UInt32.land {a} {b})).1")
            self.flag = self.new(f"(logicF 4 (UInt32.land {a} {b})).2", True)
            self.put(ops[1], r)
        elif mn == 'xorl':
            assert ops[0].r == ops[1].r
            self.regs[ops[1].r] = '0'
            self.flag = self.new("(logicF 4 0).2", True)
        elif mn == 'mull':
            a = self.regs['eax']
            assert self.get(ops[0]) == '19'
            p = f"UInt64.mul (UInt32.toUInt64 {a}) 19"
            lo = self.new(f"UInt64.toUInt32 ({p})")
            hi = self.new(f"UInt64.toUInt32 (UInt64.shiftRight ({p}) 32)")
            self.flag = self.new(f"mixF {self.flag} (ovfBits (UInt64.shiftRight ({p}) 32 != 0)) 2049", True)
            self.regs['eax'], self.regs['edx'] = lo, hi
        elif mn == 'setb':
            r8 = ops[0].r
            r32 = {'bl': 'ebx', 'dl': 'edx'}[r8]
            assert self.regs[r32] == '0'
            self.regs[r32] = self.new(f"UInt32.lor 0 (UInt32.land (bitU (cfB {self.flag})) 255)")
        elif mn == 'shldl':
            k = ops[0].v
            src = self.get(ops[1])
            a = self.get(ops[2])
            r = self.new(f"sdR true {a} {src} {k}")
            self.flag = self.new(f"sdF true {a} {src} {k}", True)
            self.put(ops[2], r)
        else:
            raise Exception(f"unhandled {mn}")
        return 1


def cut(ins):
    pieces, cur, n, st = [], [], 0, 0
    for i in ins:
        w = 7 if (i.mn == 'calll' and i.target == LOAD3) else 4 if i.mn == 'calll' else 1
        s = 1 if (i.mn == 'calll' or (i.ops and i.ops[-1].kind == 'mem' and i.mn != 'leal')) else 0
        if cur and (n + w > 8 or st + s > 4 or (i.mn in ('adcl', 'setb') and cur) or
                    (i.mn == 'movl' and i.ops[0].kind == 'imm') or (i.mn == 'leal' and i.ops[0].base is None) or (i.addr in (0x1038b8, 0x1038bf, 0x1038c4, 0x1038c8))):
            if cur[-1].mn == 'mull':
                last = cur.pop()
                pieces.append(cur)
                cur, n, st = [last], 1, 0
            else:
                pieces.append(cur)
                cur, n, st = [], 0, 0
        cur.append(i)
        n += w
        st += s
        if (i.mn in ('addl', 'andl', 'adcl') and i.ops[0].kind == 'imm') or (i.mn == 'leal' and i.ops[0].base is None) or i.mn == 'setb':
            pieces.append(cur)
            cur, n, st = [], 0, 0
    if cur:
        pieces.append(cur)
    return pieces


def st(mem, regs, eip, flag, ic):
    r = [regs[x] for x in STREGS]
    return f"St.m ⟨{mem}, {r[0]}, {r[1]}, {r[2]}, {r[3]}, UInt32.add L 4, {r[4]}, {r[5]}, {r[6]}, 0x{eip:x}, efl {flag}, icAdd ic {ic}⟩"


def run():
    ins = [i for i in read() if BODY[0] <= i.addr < BODY[1]]
    m = M()
    ps = []
    ic = 5
    for pc in cut(ins):
        m.reset()
        k = 0
        for i in pc:
            k += m.step(i)
        ps.append(dict(ic0=ic, ic1=ic + k, inregs=m.p_in, inflag=m.p_inflag, defs=m.p_defs, xdefs=m.p_xdefs, sl=m.p_sl,
                       xl=m.p_xl, fs=m.p_fs, outregs=dict(m.regs), outflag=m.flag, eip0=pc[0].addr,
                       eip1=pc[-1].nxt, txt=' ; '.join(i.mn for i in pc), setb=any(i.mn == 'setb' for i in pc)))
        ic += k
    return ps, m


def params_of(p):
    seen, out = set(), []

    def add(n):
        if n not in seen and not n[0].isdigit() and n not in ('L', 's', 'hp'):
            seen.add(n)
            out.append(n)
    for r in STREGS:
        add(p['inregs'][r])
    add(p['inflag'])
    for (_, n) in p['sl']:
        add(n)
    for (_, _, n, _) in p['xl']:
        add(n)
    for (n, _) in p['defs']:
        add(n)
    return out


def lemma(k, p):
    ps = params_of(p)
    hyps, pre = [], []
    for (o, n) in p['sl']:
        hyps.append(f"(l_{n} : l.lookup {o} = some {n})")
        pre.append(f"have r_{n} := hF.rd0 l_{n}; subst r_{n}" if o == 0 else f"have r_{n} := hF.rd l_{n} {o} rfl; subst r_{n}")
    mems = ["N"]
    m_ = "N"
    for (j, (off, v)) in enumerate(p['fs']):
        hs = "hS" if j == 0 else ("stF0_FB" if m_.startswith("(stF0") else "stF_FB")
        m_ = f"(stF0 {m_} L 72 {v} {hs} (by decide))" if off == 0 else f"(stF {m_} L 72 {off} {v} {hs} (by decide))"
        mems.append(m_)
    for (a, sz, n, j) in p['xl']:
        hyps.append(f"(l_{n} : rdRaw {mems[j]}.get {a} {sz} = {n})")
        pre.append(f"subst l_{n}")
    if p['xl']:
        hyps.append("(hsm : s.toNat + 32 ≤ N.get.size) (hsi : s.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ s.toNat)")
        hyps.append("(hsL : s.toNat + 32 ≤ L.toNat ∨ L.toNat + 72 ≤ s.toNat)")
    for (n, t) in p['defs'] + p['xdefs']:
        hyps.append(f"(e_{n} : {n} = {t})")
    substs = [f"subst e_{n}" for (n, _) in reversed(p['defs'] + p['xdefs'])]
    mem, fr, pres, lst, first = "N", "hF", "hP", "l", True
    for (off, v) in p['fs']:
        hs = "hS" if first else ("stF0_FB" if mem.startswith("(stF0") else "stF_FB")
        if off == 0:
            mem = f"(stF0 {mem} L 72 {v} {hs} (by decide))"
            fr = f"({fr}.wrF0)"
            pres = f"({pres}.wrF0 (by decide))"
        else:
            mem = f"(stF {mem} L 72 {off} {v} {hs} (by decide))"
            fr = f"({fr}.wrF {off} rfl rfl)"
            pres = f"({pres}.wrF (by decide))"
        lst = f"({off}, {v}) :: {lst}"
        first = False
    s0 = st("N.get", p['inregs'], p['eip0'], p['inflag'], 0)
    s1 = st("N'.get", p['outregs'], p['eip1'], p['outflag'], p['ic1'] - p['ic0'])
    post = "\n  all_goals simp only [ite_bitU, ite_bitU_cf]" if p['setb'] else ""
    return f"""
set_option exec.addrSub true in
/-- {p['txt']} -/
theorem fb_p{k} (ic : UInt64) (hic : ic.toNat < 2 ^ 63) (G N : XMem) (L s : UInt32) (hS : FB N.get.size L 72)
    (l : List (Nat × UInt32)) (hF : Frame N L 72 l) (hP : Pres G N (OutF L 68)) ({' '.join(ps)} : UInt32)
    {chr(10).join('    ' + h for h in hyps).strip()} :
    ∃ N' : XMem, Run img ({s0})
      ({s1}) ∧
      Frame N' L 72 ({lst}) ∧ Pres G N' (OutF L 68) := by
  refine ⟨{mem}, run_of_runI (k := {p['ic1'] - p['ic0']}) ?_ (icB hic (by decide)), {fr}, {pres}⟩
  {chr(10).join('  ' + x for x in substs).strip()}
  {chr(10).join('  ' + x for x in pre).strip()}
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv{post}
"""


HDR = """import Solutions.OpensslX25519.I.TbBase
import Solutions.Exec.Bit
/-!
# The run of `fe_frombytes`, pieces {a}–{b}

Generated by `gen/gentfb.py` (prover Q): each piece runs a few instructions (a call of `load_3`/`load_4` with its
body inside one piece) by `cbv` and states the values it computes as single-operation equations over its inputs.
The frame is `[L, L + 72)` with `esp = L + 4`.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Byte Solutions.Exec.Shift Solutions.Exec.Bit Solutions.Exec.Branch

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000
"""

if __name__ == '__main__':
    import sys
    ps, m = run()
    PER = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    only = sys.argv[2] if len(sys.argv) > 2 else None
    nf = 0
    for f in range(0, len(ps), PER):
        nf += 1
        a_, b_ = f, min(f + PER - 1, len(ps) - 1)
        txt = HDR.format(a=a_, b=b_) + "".join(lemma(k, ps[k]) for k in range(a_, b_ + 1)) + \
            "\nend Solutions.OpensslX25519.I\n"
        if only is None or only == str(nf):
            open(os.path.join(D, 'I', f'FbRun{nf}.lean'), 'w').write(txt)
    print(len(ps), 'pieces', nf, 'files', ps[-1]['ic1'], [(hex(p['eip0']), p['ic1'] - p['ic0']) for p in ps])
