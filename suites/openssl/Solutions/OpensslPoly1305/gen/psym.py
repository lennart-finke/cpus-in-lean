"""Symbolic execution of straight-line runs of the Poly1305 image into `cbv` pieces.

A segment is a run of instructions (following jumps and calls to inline callees) from a start
state; values are kept in the normal forms `cbv` produces (Solutions.Exec + Exec.Mul + Exec.Fast +
OpensslPoly1305.Cbv).  The stack is addressed from a base `U` (stack pointer `U + k`), a data region
from `C`; other loads are "ext" (hypotheses `rdRaw N.get a 4 = x`).

Each piece is a theorem
  (ic0 hic) (G N : PMem) (U C) (lU lC) (P) (hM : MemOK G N U nU lU C nC mC lC P) (vars) (loads)
  (facts) (defs) : ∃ N', Run img (St.m s0) (St.m s1) ∧ MemOK G N' U nU lU' C nC mC lC' P
"""
import re, os

MASK = 0xFFFFFFFF
REGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']   # St order without esp
DIS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'targets', 'openssl_poly1305',
                   'image', 'openssl_poly1305.dis')


class Op:
    def __init__(self, kind, **kw):
        self.kind = kind
        self.__dict__.update(kw)


def parse_op(s):
    s = s.strip()
    if s.startswith('%'):
        return Op('reg', r=s[1:])
    if s.startswith('$'):
        return Op('imm', v=int(s[1:], 0) & MASK)
    if s.startswith('*%'):
        return Op('ireg', r=s[2:])
    if re.match(r'^0x[0-9a-f]+$', s) or re.match(r'^\d+$', s):
        return Op('abs', v=int(s, 0))
    m = re.match(r'^(-?0x[0-9a-f]+|-?\d+)?\((%\w+)?(?:,(%\w+)(?:,(\d))?)?\)$', s)
    assert m, s
    disp = int(m.group(1), 0) if m.group(1) else 0
    base = m.group(2)[1:] if m.group(2) else None
    idx = m.group(3)[1:] if m.group(3) else None
    sc = int(m.group(4)) if m.group(4) else 1
    return Op('mem', disp=disp, base=base, idx=idx, sc=sc)


def split_ops(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            depth += 1
        if ch == ')':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [parse_op(x) for x in out]


class Ins:
    def __init__(self, addr, mn, ops, nxt, text):
        self.addr, self.mn, self.ops, self.nxt, self.text = addr, mn, ops, nxt, text


def read_dis():
    rows = []
    for l in open(DIS):
        m = re.match(r'\s+([0-9a-f]+):\s+(\S+)\s*([^#<]*)', l)
        if m:
            rows.append((int(m.group(1), 16), m.group(2), m.group(3).strip()))
    ins = {}
    for i, (a, mn, ops) in enumerate(rows):
        nxt = rows[i + 1][0] if i + 1 < len(rows) else None
        if mn in ('calll', 'jmp', 'je', 'jne', 'jb', 'jae', 'ja', 'jbe'):
            o = [Op('abs', v=int(ops.split()[0], 16))] if not ops.startswith('*') else split_ops(ops)
        else:
            o = split_ops(ops) if ops else []
        ins[a] = Ins(a, mn, o, nxt, (mn + ' ' + ops).strip())
    return ins


INS = read_dis()


def lit(v):
    return str(v & MASK)


class V:
    """a 32-bit value: `base + off` (base a term or None for a literal)"""
    def __init__(self, base=None, off=0):
        self.base, self.off = base, off & MASK

    def term(self):
        if self.base is None:
            return lit(self.off)
        if self.off == 0:
            return self.base
        return f"(UInt32.add {self.base} {self.off})"

    def is_lit(self):
        return self.base is None

    def __eq__(self, o):
        return isinstance(o, V) and self.base == o.base and self.off == o.off

    def __repr__(self):
        return self.term()


def atom(t):
    return t if re.match(r'^[\w.]+$', t) else f"({t})"


class Seg:
    """a segment: configuration + symbolic machine; `run(path)` produces pieces"""

    def __init__(self, pre, regs, esp, eip, flag, nU, nC, mC, Cname='C', slots=None, cslots=None,
                 facts=None, ic=0, extfacts=None):
        self.pre = pre
        self.regs = {r: v for r, v in regs.items()}   # reg -> V
        self.esp = esp                                  # stack offset from U
        self.eip = eip
        self.flag = flag                                # term (a name)
        self.nU, self.nC, self.mC, self.Cname = nU, nC, mC, Cname
        self.slots = dict(slots or {})                  # U offset -> V
        self.cslots = dict(cslots or {})                # C offset -> V
        self.facts = list(facts or [])                  # (name, prop, vars mentioned)  always passed
        self.ic = ic
        self.n = 0
        self.defs = {}                                  # name -> term
        self.pieces = []
        self.branch = {}                                # addr -> (taken: bool, hyp prop)

    # ---------- values ----------
    def new(self, term, pre='v'):
        self.n += 1
        nm = f"{pre}{self.n}"
        self.defs[nm] = term
        self.p_defs.append((nm, term))
        return V(nm)

    def reset_piece(self):
        self.p_ins = []
        self.p_defs = []
        self.p_loads = []      # (kind, key, V)  kind: 'U' off, 'C' off, 'ext' addr term
        self.p_stores = []     # ('U'|'C', off, V)
        self.p_wU, self.p_wC = set(), set()
        self.p_in = (dict(self.regs), self.esp, self.eip, self.flag, self.ic)
        self.p_hyps = []       # extra hypotheses (branch conditions)
        self.p_espfix = None   # (kind, a, b, c) for a sub/add of esp
        self.p_litload = False

    # ---------- memory ----------
    def addr(self, o):
        assert o.kind == 'mem' and o.idx is None, o.__dict__
        if o.base == 'esp':
            return ('U', self.esp + o.disp)
        v = self.regs[o.base]
        if v.base == self.Cname:
            return ('C', v.off + o.disp)
        cp = getattr(self, 'cptr', {})
        if v.base in cp:
            # an SSA value that is the data pointer moved by a literal (`addl $k, %reg`)
            return ('C', cp[v.base] + v.off + o.disp)
        if v.base == 'U':
            return ('U', v.off + o.disp)
        return ('ext', V(v.base, v.off + o.disp))

    def load(self, o):
        kind, a = self.addr(o)
        if kind == 'U':
            if a in self.p_wU:
                return self.slots[a]
            v = self.slots.get(a)
            if v is None:
                raise Exception(f"load of unknown stack slot U+{a} at {self.eip:x}")
            if v.is_lit() and getattr(self, 'allow_lit', False):
                self.p_litload = True
            elif v.is_lit() or v.off != 0:
                raise Exception(f"load of non-variable stack slot U+{a} = {v} at {self.eip:x}")
            if ('U', a) not in [(k, x) for (k, x, _) in self.p_loads]:
                self.p_loads.append(('U', a, v))
            return v
        if kind == 'C':
            if a in self.p_wC:
                return self.cslots[a]
            v = self.cslots.get(a)
            if v is None:
                raise Exception(f"load of unknown ctx word C+{a} at {self.eip:x}")
            if v.is_lit() or v.off != 0:
                raise Exception(f"load of non-variable ctx word C+{a} = {v}")
            if ('C', a) not in [(k, x) for (k, x, _) in self.p_loads]:
                self.p_loads.append(('C', a, v))
            return v
        key = a.term()
        for (k, kk, v) in self.p_loads:
            if k == 'ext' and kk == key:
                return v
        self.n += 1
        v = V(f"x{self.n}")
        self.p_loads.append(('ext', key, v))
        return v

    def store(self, o, v):
        kind, a = self.addr(o)
        self.store_at(kind, a, v)

    def store_at(self, kind, a, v):
        if kind == 'U':
            assert a % 4 == 0 and 0 <= a and a + 4 <= self.nU, a
            self.slots[a] = v
            self.p_wU.add(a)
            self.p_stores.append(('U', a, v))
        elif kind == 'C':
            assert a % 4 == 0 and a + 4 <= self.mC, a
            self.cslots[a] = v
            self.p_wC.add(a)
            self.p_stores.append(('C', a, v))
        else:
            raise Exception(f"store to ext address {a}")

    def get(self, o):
        if o.kind == 'reg':
            return self.regs[o.r]
        if o.kind == 'imm':
            return V(None, o.v)
        return self.load(o)

    def put(self, o, v):
        if o.kind == 'reg':
            self.regs[o.r] = v
        else:
            self.store(o, v)

    # ---------- instructions ----------
    def step(self, i):
        mn, ops = i.mn, i.ops
        self.p_ins.append(i)
        nxt = i.nxt
        f = self.flag
        if mn == 'nop':
            pass
        elif mn == 'movl':
            if ops[0].kind == 'abs':
                # the memset pointer of the image
                assert ops[0].v == 0x1005fc
                v = V(None, 0x1005d0)
                if getattr(self, 'img_load', False):
                    # a load of the image word (the piece takes `rdRaw N.get 1050108 4 = 1050064`)
                    self.p_loads.append(('ext', '1050108', v))
                self.put(ops[1], v)
            else:
                self.put(ops[1], self.get(ops[0]))
        elif mn == 'leal':
            m = ops[0]
            if m.idx is None:
                b = self.regs[m.base] if m.base != 'esp' else V('U', self.esp)
                self.put(ops[1], V(b.base, b.off + m.disp))
            else:
                b, x = self.regs[m.base], self.regs[m.idx]
                assert m.sc == 1
                t = f"UInt32.add {atom(b.term())} {atom(x.term())}"
                if m.disp:
                    t = f"UInt32.add ({t}) {lit(m.disp)}"
                self.put(ops[1], self.new(t))
        elif mn in ('addl', 'adcl', 'subl', 'sbbl'):
            src, dst = ops
            if dst.kind == 'reg' and dst.r == 'esp':
                assert src.kind == 'imm'
                a = self.esp
                if mn == 'subl':
                    c = self.esp - src.v
                    self.flag = self.new(f"(subF 4 {V('U', a).term()} {lit(src.v)} 0).2", 'g').term()
                    self.p_espfix = ('sub', a, src.v, c)
                else:
                    c = self.esp + src.v
                    self.flag = self.new(f"(addF 4 {V('U', a).term()} {lit(src.v)} 0).2", 'g').term()
                    self.p_espfix = ('add', a, src.v, c)
                self.esp = c
            else:
                av = self.get(dst)
                a = av.term()
                b = self.get(src).term()
                fn = 'addF' if mn in ('addl', 'adcl') else 'subF'
                cin = '0' if mn in ('addl', 'subl') else f"(cfBit {f})"
                r = self.new(f"({fn} 4 {atom(a)} {atom(b)} {cin}).1")
                if (mn == 'addl' and src.kind == 'imm' and av.base is not None and av.off == 0
                        and av.base not in ('U', self.Cname) and dst.kind == 'reg'):
                    # a pointer moved by a literal: loads through it are `p + k` (pchain: rdEa)
                    if not hasattr(self, 'alias'):
                        self.alias = {}
                    self.alias[r.term()] = (av.base, src.v)
                if (mn == 'addl' and src.kind == 'imm' and av.base == self.Cname and dst.kind == 'reg'):
                    if not hasattr(self, 'cptr'):
                        self.cptr = {}
                    self.cptr[r.term()] = av.off + src.v
                g = self.new(f"({fn} 4 {atom(a)} {atom(b)} {cin}).2", 'g')
                self.put(dst, r)
                self.flag = g.term()
        elif mn == 'andl':
            src, dst = ops
            a = self.get(dst).term()
            b = self.get(src).term()
            r = self.new(f"UInt32.land {atom(a)} {atom(b)}")
            self.flag = self.new(f"(logicF 4 (UInt32.land {atom(a)} {atom(b)})).2", 'g').term()
            self.put(dst, r)
        elif mn in ('xorl', 'orl'):
            src, dst = ops
            if mn == 'xorl' and src.kind == 'reg' and dst.kind == 'reg' and src.r == dst.r:
                self.put(dst, V(None, 0))
                self.flag = self.new("(logicF 4 0).2", 'g').term()
            else:
                a = self.get(dst).term()
                b = self.get(src).term()
                op = 'UInt32.xor' if mn == 'xorl' else 'UInt32.lor'
                r = self.new(f"(logicF 4 ({op} {atom(a)} {atom(b)})).1")
                self.flag = self.new(f"(logicF 4 ({op} {atom(a)} {atom(b)})).2", 'g').term()
                self.put(dst, r)
        elif mn == 'notl':
            a = self.get(ops[0]).term()
            self.put(ops[0], self.new(f"UInt32.land (UInt32.complement {atom(a)}) 4294967295"))
        elif mn == 'negl':
            a = self.get(ops[0]).term()
            self.put(ops[0], self.new(f"UInt32.sub 0 {atom(a)}"))
            self.flag = None   # not modelled: must be overwritten in the piece
        elif mn == 'incl':
            a = self.get(ops[0]).term()
            self.put(ops[0], self.new(f"UInt32.add {atom(a)} 1"))
            self.flag = self.new(f"mixF {f} (addF 4 {atom(a)} 1 0).2 2260", 'g').term()
        elif mn == 'decl':
            a = self.get(ops[0]).term()
            self.put(ops[0], self.new(f"UInt32.add {atom(a)} 4294967295"))
            self.flag = self.new(f"mixF {f} (subF 4 {atom(a)} 1 0).2 2260", 'g').term()
        elif mn == 'shrl':
            k = ops[0].v
            a = self.get(ops[1]).term()
            self.put(ops[1], self.new(f"UInt32.shiftRight {atom(a)} {k}"))
            self.flag = self.new(f"Solutions.Logic.Cmp.shFl 5 {atom(a)} {k}", 'g').term()
        elif mn == 'mull':
            a = self.regs['eax'].term()
            b = self.get(ops[0]).term()
            p = f"UInt64.mul (UInt32.toUInt64 {atom(a)}) (UInt32.toUInt64 {atom(b)})"
            lo = self.new(f"UInt64.toUInt32 ({p})")
            hi = self.new(f"UInt64.toUInt32 (UInt64.shiftRight ({p}) 32)")
            self.flag = self.new(f"mixF {f} (ovfBits (UInt64.shiftRight ({p}) 32 != 0)) 2049", 'g').term()
            self.regs['eax'], self.regs['edx'] = lo, hi
        elif mn == 'imull':
            assert len(ops) == 2
            a = self.get(ops[1]).term()
            b = self.get(ops[0]).term()
            r = self.new(f"UInt32.land (UInt64.toUInt32 (imulCore 4 {atom(a)} {atom(b)}).1) 4294967295")
            self.flag = self.new(f"mixF {f} (ovfBits (imulCore 4 {atom(a)} {atom(b)}).2) 2049", 'g').term()
            self.put(ops[1], r)
        elif mn == 'testl':
            a = self.get(ops[0]).term()
            b = self.get(ops[1]).term()
            assert a == b
            self.flag = self.new(f"(logicF 4 {atom(a)}).2", 'g').term()
        elif mn == 'cmpl':
            a = self.get(ops[1]).term()
            b = self.get(ops[0]).term()
            self.flag = self.new(f"(subF 4 {atom(a)} {atom(b)} 0).2", 'g').term()
        elif mn == 'pushl':
            v = self.get(ops[0])
            self.esp -= 4
            self.store_at('U', self.esp, v)
        elif mn == 'popl':
            v = self.load(Op('mem', disp=0, base='esp', idx=None, sc=1))
            self.esp += 4
            self.put(ops[0], v)
        elif mn == 'calll':
            if ops[0].kind == 'ireg':
                tgt = self.regs[ops[0].r]
                assert tgt.is_lit()
                tgt = tgt.off
            else:
                tgt = ops[0].v
            self.esp -= 4
            self.store_at('U', self.esp, V(None, nxt))
            nxt = tgt
        elif mn == 'retl':
            v = self.slots[self.esp] if self.esp in self.p_wU else self.load(Op('mem', disp=0, base='esp', idx=None, sc=1))
            self.esp += 4
            if v.is_lit():
                nxt = v.off
            else:
                self.p_ret = v
                nxt = None
        elif mn == 'jmp':
            nxt = ops[0].v
        elif mn in ('je', 'jne', 'jb', 'jae', 'ja', 'jbe'):
            taken, hyp = self.branch[i.addr]
            if hyp:
                self.p_hyps.append(hyp)
            if taken:
                nxt = ops[0].v
        else:
            raise Exception(f"unhandled {i.text}")
        self.eip = nxt
        self.ic += 1

    # ---------- pieces ----------
    def cut_here(self, cur, i):
        """cut before instruction i?"""
        st = sum(1 for (k, _, _) in self.p_stores)
        will_store = (i.mn in ('pushl', 'calll') or (i.ops and i.ops[-1].kind == 'mem' and i.mn not in
                      ('leal', 'cmpl', 'testl', 'mull', 'imull')))
        if len(cur) >= 8 or (will_store and st >= 4):
            return True
        if i.mn == 'adcl' and any(c.mn in ('addl',) and c.ops[0].kind == 'imm' for c in cur):
            return True
        if i.mn in ('addl', 'subl') and i.ops[1].kind == 'reg' and i.ops[1].r == 'esp' and cur:
            return True
        return False

    def run(self, stop, maxi=8):
        """run from self.eip until eip == stop (or a symbolic return); returns the pieces"""
        out = []
        self.reset_piece()
        self.p_ret = None
        while True:
            i = INS[self.eip]
            if self.p_ins and self.cut_here(self.p_ins, i) and not self.in_call():
                out.append(self.finish())
                self.reset_piece()
            self.step(i)
            end = False
            if i.mn in ('addl', 'andl', 'subl') and i.ops[0].kind == 'imm' and not self.in_call():
                end = True
            if self.p_espfix:
                end = True
            if self.eip is None or self.eip == stop:
                end = True
            if self.p_litload and i.mn == 'retl':
                end = True
            if end:
                if i.mn == 'mull':
                    raise Exception("piece ends with mull")
                out.append(self.finish())
                if self.eip is None or self.eip == stop:
                    break
                self.reset_piece()
        self.pieces += out
        return out

    def in_call(self):
        # inside an inlined call of U8TOU32 / U32TO8 (the return must be in the same piece)
        return self.eip in (0x100068, 0x10006a, 0x100578, 0x10057a)

    def finish(self):
        regs0, esp0, eip0, fl0, ic0 = self.p_in
        p = dict(ins=list(self.p_ins), defs=list(self.p_defs), loads=list(self.p_loads),
                 stores=list(self.p_stores), regs0=regs0, esp0=esp0, eip0=eip0, fl0=fl0, ic0=ic0,
                 regs1=dict(self.regs), esp1=self.esp, eip1=self.eip, fl1=self.flag, ic1=self.ic,
                 hyps=list(self.p_hyps), espfix=self.p_espfix, ret=getattr(self, 'p_ret', None),
                 k=len(self.pieces) + 0)
        if self.flag is None:
            raise Exception(f"piece ends with unmodelled flags at {self.eip:x}")
        return p

    # ---------- Lean text ----------
    def st(self, mem, regs, esp, eip, fl, ic):
        r = [regs[x].term() for x in REGS]
        e = 'U' if esp == 0 else f"UInt32.add U {esp}"
        eipt = eip if isinstance(eip, str) else f"0x{eip:x}"
        return (f"St.m ⟨{mem}, {r[0]}, {r[1]}, {r[2]}, {r[3]}, {e}, {r[4]}, {r[5]}, {r[6]}, {eipt}, "
                f"efl {fl}, icAdd ic0 {ic}⟩")

    def free_names(self, t):
        return [x for x in re.findall(r'[A-Za-z_][\w.]*', t)]

    def sig(self, p):
        """the parameters and hypotheses of a piece: params (names), hyps [(name, prop, kind, data)]"""
        C = self.Cname
        params, seen = [], set(['U', C])

        def addp(t):
            for n in re.findall(r'(?<![\w.])([a-z][a-z_]*\d*)(?![\w.])', t):
                if n in seen or n in KEYWORDS:
                    continue
                seen.add(n)
                params.append(n)
        for r in REGS:
            addp(p['regs0'][r].term())
        addp(p['fl0'])
        for (_, _, v) in p['loads']:
            addp(v.term())
        for (nm, t) in p['defs']:
            addp(t)
            if nm not in seen:
                seen.add(nm)
                params.append(nm)
        if p['ret'] is not None:
            addp(p['ret'].term())
        hyps = []
        names = set()
        for j, (kind, key, v) in enumerate(p['loads']):
            if kind == 'U':
                a = 'U' if key == 0 else f"(UInt32.add U {key})"
            elif kind == 'C':
                a = C if key == 0 else f"(UInt32.add {C} {key})"
            else:
                a = key
            hn = f"l_{v.term()}" if not v.is_lit() else f"lu_{key}"
            if hn in names:
                hn = f"l{j}_{v.term()}"
            names.add(hn)
            hyps.append((hn, f"rdRaw N.get {a} 4 = {v.term()}", 'load' if not v.is_lit() else 'loadlit',
                         (kind, key, v)))
        al = getattr(self, 'alias', {})
        for (kind, key, v) in p['loads']:
            if kind == 'ext' and key in al:
                hyps.append((f"ha1_{key}", f"{key}.toNat + 4 ≤ N.get.size", 'alias1', key))
                hyps.append((f"ha2_{key}", f"{key}.toNat + 4 ≤ U.toNat ∨ U.toNat + {self.nU} ≤ {key}.toNat",
                             'alias2', key))
                hyps.append((f"ha3_{key}", f"{key}.toNat + 4 ≤ {C}.toNat ∨ {C}.toNat + {self.nC} ≤ {key}.toNat",
                             'alias2', key))
        used = set(params) | {'U', C}
        for (nm, prop, vs) in self.facts:
            if all(x in used for x in vs):
                hyps.append((nm, prop, 'fact', nm))
        # data pointers moved by a literal in an earlier piece: their value as `C + k`
        for n, off in sorted(getattr(self, 'cptr', {}).items()):
            if n in params and n not in [nm for (nm, _) in p['defs']]:
                hyps.append((f"hcp_{n}", f"{n} = UInt32.add {C} {off}", 'cptr', n))
        for j, h in enumerate(p['hyps']):
            hyps.append((f"hb{j}", h, 'branch', j))
        for (nm, t) in p['defs']:
            hyps.append((f"e_{nm}", f"{nm} = {t}", 'def', nm))
        return params, hyps

    def lemma(self, p, name):
        C = self.Cname
        params, hl = self.sig(p)
        hyps = [f"({a} : {b})" for (a, b, _, _) in hl]
        pre = [f"subst {a}" for (a, _, k, _) in hl if k in ('load', 'cptr')] + \
              [f"rw [← {a}]" for (a, _, k, _) in hl if k == 'loadlit']
        substs = [f"subst e_{nm}" for (nm, _) in reversed(p['defs'])]
        # stores
        mem_lines = []
        M = "hM"
        lU, lC = "lU", "lC"
        for j, (kind, off, v) in enumerate(p['stores']):
            nm = f"M{j + 1}"
            if kind == 'U':
                if off == 0:
                    mem_lines.append(f"have {nm} := {M}.stU0 {v.term()} (by decide)")
                else:
                    mem_lines.append(f"have {nm} := {M}.stU {off} {off} {v.term()} (by decide) rfl rfl")
                lU = f"({off}, {v.term()}) :: {lU}"
            else:
                if off == 0:
                    mem_lines.append(f"have {nm} := {M}.stC0 {v.term()} (by decide) (by decide)")
                else:
                    mem_lines.append(f"have {nm} := {M}.stC {off} {off} {v.term()} (by decide) rfl rfl (by decide)")
                lC = f"({off}, {v.term()}) :: {lC}"
            M = nm
        k = len(p['ins'])
        s0 = self.st("N.get", p['regs0'], p['esp0'], p['eip0'], p['fl0'], p['ic0'])
        eip1 = p['eip1'] if p['eip1'] is not None else p['ret'].term()
        s1 = self.st("N'.get", p['regs1'], p['esp1'], eip1, p['fl1'], p['ic1'])
        sig = f"MemOK G N U {self.nU} lU {C} {self.nC} {self.mC} lC P"
        sig1 = f"MemOK G N' U {self.nU} ({lU}) {C} {self.nC} {self.mC} ({lC}) P"
        doc = ' ; '.join(i.text for i in p['ins'])
        txt = f"""
/-- {doc} -/
theorem {name} (ic0 : UInt64) (hic : ic0.toNat < 2 ^ 63) (G N : PMem) (U {C} : UInt32)
    (lU lC : List (Nat × UInt32)) (P : Nat → Prop) (hM : {sig})
    ({' '.join(params)} : UInt32)
    {chr(10).join('    ' + h for h in hyps)} :
    ∃ N' : PMem, Run img ({s0})
      ({s1}) ∧
      {sig1} := by
"""
        body = []
        body += mem_lines
        if p['espfix']:
            kind, a, b, c = p['espfix']
            espt = f"(subF 4 (UInt32.add U {a}) {b} 0).1" if kind == 'sub' else f"(addF 4 (UInt32.add U {a}) {b} 0).1"
            lem = 'esp_subF' if kind == 'sub' else 'esp_addF'
            s1x = s1.replace("N'.get", "N.get")
            ce = 'U' if c == 0 else f"UInt32.add U {c}"
            s1x = s1x.replace(f", {ce}, ", f", {espt}, ", 1)
            body.append(f"refine ⟨N, ?_, {M}⟩")
            body.append("have q1 := hM.fU.top; have q2 := hM.fU.fit; have q3 := hM.fU.img")
            inner = "".join("    " + x + "\n" for x in substs + pre)
            body.append(f"have h : runI img {k} ({s0}) =\n      some ({s1x}) := by\n{inner}    cbv")
            cc = c if c != 0 else 0
            body.append(f"rw [{lem} U {a} {b} {cc} (by decide)] at h")
            if c == 0:
                body.append("rw [uadd_zero] at h")
            body.append("exact run_of_runI h (icB hic (by decide))")
        else:
            body.append(f"refine ⟨_, run_of_runI (k := {k}) ?_ (icB hic (by decide)), {M}⟩")
            body += substs + pre
            body.append("have q1 := hM.fU.top; have q2 := hM.fU.fit; have q3 := hM.fU.img")
            body.append("have q4 := hM.fC.fit; have q5 := hM.fC.img; have q6 := hM.dUC")
            body.append("cbv")
        return txt + "".join("  " + b + "\n" for b in body)


KEYWORDS = {'by', 'decide', 'rfl', 'efl', 'fun', 'if', 'then', 'else', 'true', 'false'}
