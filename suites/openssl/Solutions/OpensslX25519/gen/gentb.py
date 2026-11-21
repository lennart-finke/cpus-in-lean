"""fe_tobytes (0x101c30): run pieces I/TbRun*.lean (prover Q).

    python3 gentb.py            (from this directory)   writes ../I/TbRun1.lean ... and tbpieces.json

Frame L = sp - 40 (FB L 44): slots 0 (h4), 4 (h8), 8 (h7), 0xc (h6), 0x10 (h5), 0x14 (h9), saved esi/edi/ebx/ebp
at 24/28/32/36, the return address at 40. Every value is an SSA name with a defining equation `e_v`.
Piece kinds: 'fs' (frame stores, Frame/Pres style), 'c' (no store), 'b' (one byte store into the output),
'w' (one 2-byte store, as two `CodeMem.wr1`).
"""
import os, json
from asm import read

G = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(G, '..')
REG8 = {'al': ('eax', 0), 'ah': ('eax', 8), 'bl': ('ebx', 0), 'bh': ('ebx', 8), 'cl': ('ecx', 0), 'ch': ('ecx', 8),
        'dl': ('edx', 0), 'dh': ('edx', 8)}
REG16 = {'ax': 'eax', 'bx': 'ebx', 'cx': 'ecx', 'dx': 'edx', 'di': 'edi', 'si': 'esi'}
STREGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']


def lit(v):
    return str(v & 0xFFFFFFFF)


def addr_t(base, d):
    return base if d == 0 else f"(UInt32.add {base} {d})"


class M:
    def __init__(self):
        self.regs = {'eax': 'a0', 'ecx': 'out', 'edx': 'hp', 'ebx': 'ebx0', 'ebp': 'ebp0', 'esi': 'esi0',
                     'edi': 'edi0'}
        self.flag = 'g0'
        self.slots = {}
        self.n = 0
        self.ng = 0
        self.defs = []

    def reset(self):
        self.p_in = dict(self.regs)
        self.p_inflag = self.flag
        self.p_defs = []
        self.p_sl = []      # slot loads (off, name)
        self.p_xl = []      # hp loads (off, name)
        self.p_fs = []      # frame stores (off, name)
        self.p_bs = []      # byte stores (off, value term)
        self.p_ws = []      # word stores (off, value term)

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

    def get(self, o):
        if o.kind == 'reg':
            return self.regs[o.r]
        if o.kind == 'imm':
            return lit(o.v)
        if o.base == 'esp':
            nm = self.slots[o.disp]
            if (o.disp, nm) not in self.p_sl and o.disp not in [x for (x, _) in self.p_fs]:
                self.p_sl.append((o.disp, nm))
            return nm
        assert o.base == 'edx' and self.regs['edx'] == 'hp'
        nm = f"x{o.disp // 4}"
        self.p_xl.append((o.disp, nm))
        return nm

    def step(self, i):
        mn, ops = i.mn, i.ops
        if mn == 'movl':
            v = self.get(ops[0])
            d = ops[1]
            if d.kind == 'reg':
                self.regs[d.r] = v
            else:
                assert d.base == 'esp'
                self.slots[d.disp] = v
                self.p_fs.append((d.disp, v))
        elif mn == 'leal':
            m = ops[0]
            b = self.regs[m.base] if m.base else None
            ix = self.regs[m.idx]
            sh = {1: 0, 2: 1, 4: 2, 8: 3}[m.sc]
            it = ix if sh == 0 else f"(UInt32.shiftLeft {ix} {sh})"
            t = f"UInt32.add {b} {it}" if b else it
            if m.disp:
                t = f"UInt32.add ({t}) {lit(m.disp)}"
            self.regs[ops[1].r] = self.new(t)
        elif mn in ('sarl', 'shrl', 'shll'):
            k = ops[0].v
            a = self.get(ops[1])
            f = {'sarl': ('sarR', 'sarF'), 'shrl': ('shrR', 'shrF'), 'shll': ('shlR', 'shlF')}[mn]
            r = self.new(f"{f[0]} {a} {k}")
            self.flag = self.new(f"{f[1]} {a} {k}", True)
            self.regs[ops[1].r] = r
        elif mn == 'addl':
            a = self.get(ops[1])
            b = self.get(ops[0])
            r = self.new(f"UInt32.add {a} {b}")
            self.flag = self.new(f"(addF 4 {a} {b} 0).2", True)
            self.regs[ops[1].r] = r
        elif mn in ('andl', 'orl'):
            a = self.get(ops[1])
            b = self.get(ops[0])
            op = 'UInt32.land' if mn == 'andl' else 'UInt32.lor'
            r = self.new(f"(logicF 4 ({op} {a} {b})).1")
            self.flag = self.new(f"(logicF 4 ({op} {a} {b})).2", True)
            self.regs[ops[1].r] = r
        elif mn == 'movb':
            r, sh = REG8[ops[0].r]
            x = self.regs[r]
            v = f"(UInt32.land {x} 255)" if sh == 0 else f"(UInt32.land (UInt32.shiftRight {x} 8) 255)"
            assert ops[1].base == 'esi'
            self.p_bs.append((ops[1].disp, v))
        elif mn == 'movw':
            x = self.regs[REG16[ops[0].r]]
            assert ops[1].base == 'esi'
            self.p_ws.append((ops[1].disp, f"(UInt32.land {x} 65535)"))
        else:
            raise Exception(f"unhandled {i}")


def cut(ins):
    """pieces of the body 5..156 (indices into ins)"""
    fixed = [(5, 12), (12, 20), (20, 24)]
    out = list(fixed)
    cur = []
    for k in range(24, 157):
        i = ins[k]
        cur.append(k)
        end = (i.mn in ('movb', 'movw')) or (i.mn in ('andl', 'addl') and i.ops[0].kind == 'imm') or len(cur) >= 8
        if end:
            out.append((cur[0], cur[-1] + 1))
            cur = []
    if cur:
        out.append((cur[0], cur[-1] + 1))
    return out


def st(mem, regs, eip, flag, ic):
    r = [regs[x] for x in STREGS]
    return f"St.m ⟨{mem}, {r[0]}, {r[1]}, {r[2]}, {r[3]}, L, {r[4]}, {r[5]}, {r[6]}, 0x{eip:x}, efl {flag}, icAdd ic0 {ic}⟩"


def run():
    ins = read(os.path.join(G, 'tobytes.txt'))
    m = M()
    # prologue/sub (0..4): registers unchanged (esp handled by the ends pieces)
    ps = []
    for (a, b) in cut(ins):
        m.reset()
        for k in range(a, b):
            m.step(ins[k])
        kind = 'fs' if m.p_fs else 'b' if m.p_bs else 'w' if m.p_ws else 'c'
        ps.append(dict(a=a, b=b, kind=kind, inregs=m.p_in, inflag=m.p_inflag, defs=m.p_defs, sl=m.p_sl,
                       xl=m.p_xl, fs=m.p_fs, bs=m.p_bs, ws=m.p_ws, outregs=dict(m.regs), outflag=m.flag,
                       eip0=ins[a].addr, eip1=ins[b].addr,
                       txt=' ; '.join(f"{ins[k].mn}" for k in range(a, b))))
    return ps, m, ins


def params_of(p):
    seen, out = set(), []

    def add(n):
        if n not in seen and not n[0].isdigit() and n not in ('L', 'out', 'hp'):
            seen.add(n)
            out.append(n)
    for r in STREGS:
        add(p['inregs'][r])
    add(p['inflag'])
    for (_, n) in p['sl'] + p['xl']:
        add(n)
    for (n, _) in p['defs']:
        add(n)
    return out


def slot_t(o):
    return "L" if o == 0 else f"(UInt32.add L {o})"


def lemma(k, p):
    ps = params_of(p)
    hyps = []
    pre = []
    for (o, n) in p['sl']:
        if p['kind'] == 'fs':
            hyps.append(f"(l_{n} : l.lookup {o} = some {n})")
            pre.append(f"have r_{n} := hF.rd0 l_{n}; subst r_{n}" if o == 0 else f"have r_{n} := hF.rd l_{n} {o} rfl; subst r_{n}")
        else:
            hyps.append(f"(l_{n} : rdRaw N.get {slot_t(o)} 4 = {n})")
            pre.append(f"subst l_{n}")
    for (o, n) in p['xl']:
        hyps.append(f"(l_{n} : rdRaw N.get {addr_t('hp', o)} 4 = {n})")
        pre.append(f"subst l_{n}")
    if p['xl']:
        hyps.append("(hpm : hp.toNat + 40 ≤ N.get.size) (hpi : hp.toNat + 40 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ hp.toNat)")
        hyps.append("(hpL : hp.toNat + 40 ≤ L.toNat ∨ L.toNat + 44 ≤ hp.toNat)")
    for (n, t) in p['defs']:
        hyps.append(f"(e_{n} : {n} = {t})")
    substs = [f"subst e_{n}" for (n, _) in reversed(p['defs'])]
    s0 = st("N.get", p['inregs'], p['eip0'], p['inflag'], p['a'])
    name = f"tb_p{k}"
    if p['kind'] == 'fs':
        mem, fr, pres, lst, first = "N", "hF", "hP", "l", True
        for (off, v) in p['fs']:
            hs = "hS" if first else ("stF0_FB" if mem.startswith("(stF0") else "stF_FB")
            if off == 0:
                mem = f"(stF0 {mem} L 44 {v} {hs} (by decide))"
                fr = f"({fr}.wrF0)"
                pres = f"({pres}.wrF0 (by decide))"
            else:
                mem = f"(stF {mem} L 44 {off} {v} {hs} (by decide))"
                fr = f"({fr}.wrF {off} rfl rfl)"
                pres = f"({pres}.wrF (by decide))"
            lst = f"({off}, {v}) :: {lst}"
            first = False
        s1 = st("N'.get", p['outregs'], p['eip1'], p['outflag'], p['b'])
        return f"""
/-- {p['txt']} -/
theorem {name} (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (G N : XMem) (L hp : UInt32) (hS : FB N.get.size L 44)
    (l : List (Nat × UInt32)) (hF : Frame N L 44 l) (hP : Pres G N (OutF L 40)) ({' '.join(ps)} : UInt32)
    {chr(10).join('    ' + h for h in hyps).strip()} :
    ∃ N' : XMem, Run img ({s0})
      ({s1}) ∧
      Frame N' L 44 ({lst}) ∧ Pres G N' (OutF L 40) := by
  refine ⟨{mem}, run_of_runI (k := {p['b'] - p['a']}) ?_ (icB hic (by decide)), {fr}, {pres}⟩
  {chr(10).join('  ' + x for x in substs).strip()}
  {chr(10).join('  ' + x for x in pre).strip()}
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  clear hF hP
  cbv
"""
    oks = ""
    rw = ""
    if p['kind'] == 'c':
        mem = "N.get"
    elif p['kind'] == 'b':
        (o, v), = p['bs']
        mem = f"(CodeMem.wr1 N {addr_t('out', o)} {v} ok).get"
        oks = f"(ok : StoreOk1 Image.base Image.size N.mem {addr_t('out', o)})"
    else:
        (o, v), = p['ws']
        mem = f"(CodeMem.wr1 (CodeMem.wr1 N {addr_t('out', o)} {v} ok) {addr_t('out', o + 1)} (UInt32.shiftRight {v} 8) ok').get"
        oks = (f"(ok : StoreOk1 Image.base Image.size N.mem {addr_t('out', o)})\n"
               f"    (ok' : StoreOk1 Image.base Image.size (CodeMem.wr1 N {addr_t('out', o)} {v} ok).mem {addr_t('out', o + 1)})")
        rw = (f"rw [wr1_wr1_eq N _ _ _ ok ok' (by simp only [toNat_uadd, UInt32.reduceToNat]; "
              f"have := ok.1; have := hS.top; unfold ramTop at *; omega) hS.top]")
    s1 = st(mem, p['outregs'], p['eip1'], p['outflag'], p['b'])
    return f"""
/-- {p['txt']} -/
theorem {name} (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (N : XMem) (L out hp : UInt32) (hS : FB N.get.size L 44)
    (hom : out.toNat + 32 ≤ N.get.size) (hoi : out.toNat + 32 ≤ 0x100000 ∨ 0x100000 + 47024 ≤ out.toNat)
    ({' '.join(ps)} : UInt32)
    {chr(10).join('    ' + h for h in hyps).strip()} {oks} :
    Run img ({s0})
      ({s1}) := by
  refine run_of_runI (k := {p['b'] - p['a']}) ?_ (icB hic (by decide))
  {rw}
  {chr(10).join('  ' + x for x in substs).strip()}
  {chr(10).join('  ' + x for x in pre).strip()}
  have h1 := hS.top; have h2 := hS.fit; have h3 := hS.img
  cbv
"""


HDR = """import Solutions.OpensslX25519.I.TbBase
/-!
# The run of `fe_tobytes`, pieces {a}–{b}

Generated by `gen/gentb.py` (prover Q): each piece runs a few instructions by `cbv` and states the values it
computes as single-operation equations over its inputs.
-/
namespace Solutions.OpensslX25519.I
open X86 Ssl Solutions.Logic Solutions.Exec Ssl.OpensslX25519 Solutions.Exec.Mul Solutions.Exec.Fast
  Solutions.Exec.Byte Solutions.Exec.Shift

attribute [local cbv_opaque] Image.bytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000
"""

if __name__ == '__main__':
    import sys
    ps, m, ins = run()
    PER = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    only = sys.argv[2] if len(sys.argv) > 2 else None
    nf = 0
    for f in range(0, len(ps), PER):
        nf += 1
        a_, b_ = f, min(f + PER - 1, len(ps) - 1)
        txt = HDR.format(a=a_, b=b_) + "".join(lemma(k, ps[k]) for k in range(a_, b_ + 1)) + \
            "\nend Solutions.OpensslX25519.I\n"
        if only is None or only == str(nf):
            open(os.path.join(D, 'I', f'TbRun{nf}.lean'), 'w').write(txt)
    json.dump([{k: v for k, v in p.items()} for p in ps], open(os.path.join(G, 'tbpieces.json'), 'w'), indent=0)
    print(len(ps), 'pieces', nf, 'files', [(p['a'], p['b'], p['kind']) for p in ps])
