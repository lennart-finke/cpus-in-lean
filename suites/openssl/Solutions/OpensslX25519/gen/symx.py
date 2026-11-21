# Symbolic execution of straight-line i386 code into SSA values in the normal forms of `cbv`
# (Solutions.Exec + Solutions.Exec.Mul + Solutions.Exec.Fast).
from asm import Op

R32 = ['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi']
STREGS = ['eax', 'ecx', 'edx', 'ebx', 'ebp', 'esi', 'edi']   # St order without esp


class Val:
    """an SSA value: name, defining term (over names), kind tags for the semantic generator"""
    def __init__(self, name, term, op, args):
        self.name, self.term, self.op, self.args = name, term, op, args


def lit(v):
    return str(v & 0xFFFFFFFF)


class Machine:
    def __init__(self, regs, flag, fb='fb'):
        self.regs = dict(regs)       # reg -> name (esp handled as frame base)
        self.flag = flag
        self.slots = {}              # frame offset -> name
        self.defs = []               # Vals, in order
        self.n = 0
        self.fb = fb
        # per piece
        self.reset_piece()

    def reset_piece(self):
        self.p_loads = []        # (kind, key, name)  kind 'slot' (off) or 'ext' (address term)
        self.p_defs = []
        self.p_stores = []       # (off, name)  frame stores
        self.p_xstores = []      # (address term, name) other stores
        self.p_written = set()   # slots written in this piece
        self.p_inregs = dict(self.regs)
        self.p_inflag = self.flag
        self.p_loaded_names = {}

    def new(self, term, op, args, prefix='v'):
        self.n += 1
        name = f"{prefix}{self.n}"
        v = Val(name, term, op, args)
        self.defs.append(v)
        self.p_defs.append(v)
        return name

    # --- addressing ---
    def addr(self, o):
        """frame offset (int) for esp-relative operands, else ('ext', term)"""
        assert o.kind == 'mem'
        if o.base == 'esp' and o.idx is None:
            return o.disp
        assert o.idx is None, o
        b = self.regs[o.base]
        d = o.disp & 0xFFFFFFFF
        return ('ext', b if d == 0 else f"(UInt32.add {b} {d})")

    def load(self, o):
        a = self.addr(o)
        if isinstance(a, int):
            if a in self.p_written:
                return self.slots[a]
            if a not in self.slots:
                raise Exception(f"load of unknown slot {a:#x}")
            nm = self.slots[a]
            self.p_loads.append(('slot', a, nm))
            return nm
        key = a[1]
        for (k, kk, nm) in self.p_loads:
            if k == 'ext' and kk == key:
                return nm
        self.n += 1
        nm = f"x{self.n}"
        self.p_loads.append(('ext', key, nm))
        return nm

    def store(self, o, v):
        a = self.addr(o)
        if isinstance(a, int):
            self.slots[a] = v
            self.p_written.add(a)
            self.p_stores.append((a, v))
        else:
            self.p_xstores.append((a[1], v))

    def get(self, o):
        if o.kind == 'reg':
            return self.regs[o.r]
        if o.kind == 'imm':
            return lit(o.v)
        return self.load(o)

    def put(self, o, v):
        if o.kind == 'reg':
            self.regs[o.r] = v
        else:
            self.store(o, v)

    # --- instructions ---
    def step(self, ins):
        mn, ops = ins.mn, ins.ops
        if mn == 'movl':
            self.put(ops[1], self.get(ops[0]))
        elif mn == 'leal':
            m = ops[0]
            b = self.regs[m.base]
            assert m.disp == 0
            if m.idx is None:
                raise Exception("lea without index")
            i = self.regs[m.idx]
            sh = {1: 0, 2: 1, 4: 2, 8: 3}[m.sc]
            idx = i if sh == 0 else f"(UInt32.shiftLeft {i} {sh})"
            t = f"UInt32.add {b} {idx}"
            self.put(ops[1], self.new(t, 'lea', (b, i, m.sc)))
        elif mn in ('addl', 'adcl', 'subl', 'sbbl', 'andl'):
            src, dst = ops
            a = self.get(dst)
            b = self.get(src)
            if mn == 'andl':
                r = self.new(f"(logicF 4 (UInt32.land {a} {b})).1", 'and', (a, b))
                g = self.new(f"(logicF 4 (UInt32.land {a} {b})).2", 'andF', (a, b), 'g')
            else:
                fn = 'addF' if mn in ('addl', 'adcl') else 'subF'
                cin = '0' if mn in ('addl', 'subl') else f"(cfBit {self.flag})"
                r = self.new(f"({fn} 4 {a} {b} {cin}).1", mn, (a, b, self.flag))
                g = self.new(f"({fn} 4 {a} {b} {cin}).2", mn + 'F', (a, b, self.flag), 'g')
            self.put(dst, r)
            self.flag = g
        elif mn == 'imull' and len(ops) == 1:
            a = self.regs['eax']
            b = self.get(ops[0])
            lo = self.new(f"UInt64.toUInt32 (imulCore 4 {a} {b}).1", 'imulLo', (a, b))
            hi = self.new(f"UInt64.toUInt32 (UInt64.shiftRight (imulCore 4 {a} {b}).1 32)", 'imulHi', (a, b))
            g = self.new(f"mixF {self.flag} (ovfBits (imulCore 4 {a} {b}).2) 2049", 'imulF', (a, b, self.flag), 'g')
            self.regs['eax'] = lo
            self.regs['edx'] = hi
            self.flag = g
        elif mn == 'imull' and len(ops) == 3:
            k = ops[0].v
            a = self.get(ops[1])
            lo = self.new(f"UInt32.land (UInt64.toUInt32 (imulCore 4 {a} {lit(k)}).1) 4294967295", 'imul3', (a, k))
            g = self.new(f"mixF {self.flag} (ovfBits (imulCore 4 {a} {lit(k)}).2) 2049", 'imulF', (a, k, self.flag), 'g')
            self.put(ops[2], lo)
            self.flag = g
        elif mn == 'mull':
            a = self.regs['eax']
            b = self.get(ops[0])
            assert b == '19'
            p = f"UInt64.mul (UInt32.toUInt64 {a}) 19"
            lo = self.new(f"UInt64.toUInt32 ({p})", 'mulLo', (a, b))
            hi = self.new(f"UInt64.toUInt32 (UInt64.shiftRight ({p}) 32)", 'mulHi', (a, b))
            g = self.new(f"mixF {self.flag} (ovfBits (UInt64.shiftRight ({p}) 32 != 0)) 2049", 'mulF', (a, b, self.flag), 'g')
            self.regs['eax'] = lo
            self.regs['edx'] = hi
            self.flag = g
        elif mn == 'sarl':
            k = ops[0].v
            a = self.get(ops[1])
            r = self.new(f"sarR {a} {k}", 'sar', (a, k))
            g = self.new(f"sarF {a} {k}", 'sarF', (a, k), 'g')
            self.put(ops[1], r)
            self.flag = g
        elif mn in ('shrdl', 'shldl'):
            k = ops[0].v
            src = self.get(ops[1])
            a = self.get(ops[2])
            left = 'true' if mn == 'shldl' else 'false'
            r = self.new(f"sdR {left} {a} {src} {k}", mn, (a, src, k))
            g = self.new(f"sdF {left} {a} {src} {k}", mn + 'F', (a, src, k), 'g')
            self.put(ops[2], r)
            self.flag = g
        else:
            raise Exception(f"unhandled {ins}")
