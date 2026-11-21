# The semantic facts of the SSA values of fe_sq/fe_mul: which 32-bit word or 64-bit pair holds which
# integer (modulo 2^32 / 2^64), as `have`s applying the lemmas of Solutions/OpensslX25519/Pair.lean.
from fractions import Fraction

B_EVEN, B_ODD = 110729625, 55364812


class Poly:
    """integer polynomial over atoms (monomials: sorted tuples of atom names)"""
    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def atom(a):
        return Poly({(a,): 1})

    @staticmethod
    def const(c):
        return Poly({(): c})

    def __add__(self, o):
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return Poly(d)

    def __neg__(self):
        return Poly({k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        d = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(sorted(k1 + k2))
                d[k] = d.get(k, 0) + v1 * v2
        return Poly(d)

    def scale(self, c):
        return Poly({k: v * c for k, v in self.d.items()})

    def __eq__(self, o):
        return self.d == o.d

    def __repr__(self):
        return ' + '.join(f"{v}*{'*'.join(k) or '1'}" for k, v in sorted(self.d.items()))


def mulraw_limbs(two=False):
    """the limbs of mulRaw f g (MulMath.lean) as polynomials in X0..X9 (and Y0..Y9 for g, if two)"""
    X = [Poly.atom(f"X{i}") for i in range(10)]
    Yv = [Poly.atom(f"Y{i}") for i in range(10)] if two else X
    limbs = []
    for k in range(10):
        p = Poly()
        for i in range(10):
            for j in range(10):
                if (i + j) % 10 != k:
                    continue
                m = 2 if (i % 2 == 1 and j % 2 == 1) else 1
                c = m * (19 if i + j >= 10 else 1)
                p = p + (X[i] * Yv[j]).scale(c)
        limbs.append(p)
    return limbs


class Fact:
    def __init__(self, name, es, poly, bound=None):
        self.name, self.es, self.poly, self.bound = name, es, poly, bound


def par(s):
    return s if s.replace('_', '').isalnum() else f"({s})"


class Sem:
    """walks the SSA definitions in order and emits the facts (Lean `have`/`obtain` lines)"""

    def __init__(self, inputs, two=False, pre='sq'):
        # inputs: name -> index i (f limbs) or ('Y', i) (g limbs)
        self.pre = pre
        self.hargs = "X0 X1 X2 X3 X4 X5 X6 X7 X8 X9" + (" Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9" if two else "")
        inputs = {nm: (v if isinstance(v, tuple) else ('X', v)) for nm, v in inputs.items()}
        # inputs: name -> (index i)  : sv name = X{i}
        self.sv = {}       # name -> Fact (sv name = es), with numeric bound
        self.m32 = {}      # name -> Fact (M32 name es)
        self.pair = {}     # (lo, hi) -> Fact (M64 lo hi es)
        self.defs = {}     # name -> Val
        self.lea9 = {}     # name -> base (x + 8x)
        self.flagof = {}   # flag name -> value name of the same op
        self.limbs = mulraw_limbs(two)
        self.nC = 0
        self.carries = []  # (Cname, es of T, shift)
        self.hlemmas = []  # (k, es) canonicalization lemmas to emit
        self.blemmas = []  # bound lemmas
        for nm, (A, i) in inputs.items():
            b = B_EVEN if i % 2 == 0 else B_ODD
            self.sv[nm] = Fact(f"sx_{nm}", f"{A}{i}", Poly.atom(f"{A}{i}"), b)
            self.bfact = {}
        self.bname = {}    # name -> bound fact name (-B ≤ X ∧ X ≤ B)
        for nm, (A, i) in inputs.items():
            self.bname[nm] = f"b{A}{i}"
        self.pending_mul = {}
        self.cof = {}

    def lo_of(self, lo):
        for (l, h), f in self.pair.items():
            if l == lo:
                return (l, h), f
        return None, None

    def m32fact(self, nm, out):
        if nm in self.m32:
            return self.m32[nm]
        if nm.isdigit():
            return None
        (l, h), f = self.lo_of(nm)
        if f is None:
            return None
        fn = f"w_{nm}"
        out.append(f"have {fn} := M32_lo {f.name}")
        self.m32[nm] = Fact(fn, f.es, f.poly)
        return self.m32[nm]

    def constpair(self, lo, hi):
        if hi == '0' and lo in ('33554432', '16777216'):
            v = int(lo)
            return Fact('M64_c25' if v == 33554432 else 'M64_c24', lo, Poly.const(v))
        return None

    def getpair(self, lo, hi):
        if (lo, hi) in self.pair:
            return self.pair[(lo, hi)]
        return self.constpair(lo, hi)

    def canon(self, key, out):
        """a complete product sum: rewrite it to the limb R{k}"""
        f = self.pair[key]
        for k, L in enumerate(self.limbs):
            if f.poly == L:
                ln = f"sq_h{k}"
                self.hlemmas.append((k, f.es))
                fn = f"{f.name}c"
                out.append(f"have {fn} := {f.name}.congr (({self.pre}_h{k} {self.hargs}).trans hR{k}.symm)")
                self.pair[key] = Fact(fn, f"R{k}", Poly.atom(f"R{k}"))
                return

    def step(self, v, out):
        self.defs[v.name] = v
        op, a = v.op, v.args
        n = v.name
        if op.endswith('F'):
            return
        if op == 'lea':
            b, i, sc = a
            if sc == 1 and b == i and b in self.sv:
                x = self.sv[b]
                out.append(f"have sv_{n} := sv_add2 e_{n} {x.name} {self.bname[b]} (by decide)")
                self.sv[n] = Fact(f"sv_{n}", f"2 * {par(x.es)}", x.poly.scale(2), 2 * x.bound)
            elif sc == 8 and b == i:
                self.lea9[n] = b
            elif sc == 2 and self.lea9.get(i) == b:
                if b in self.sv:
                    x = self.sv[b]
                    out.append(f"have sv_{n} := sv_lea19 e_{i} e_{n} {x.name} {self.bname[b]} (by decide)")
                    self.sv[n] = Fact(f"sv_{n}", f"19 * {par(x.es)}", x.poly.scale(19), 19 * x.bound)
                else:
                    self.pending_mul.setdefault('lea19', {})[b] = (i, n)
            else:
                raise Exception(f"lea {v.term}")
            return
        if op == 'imul3':
            x, k = a
            assert k == 38 and x in self.sv
            f = self.sv[x]
            out.append(f"have sv_{n} := sv_imul38 e_{n} {f.name} {self.bname[x]} (by decide)")
            self.sv[n] = Fact(f"sv_{n}", f"38 * {par(f.es)}", f.poly.scale(38), 38 * f.bound)
            return
        if op == 'imulLo':
            return
        if op == 'imulHi':
            x, y = a
            lo = [d for d in self.defs.values() if d.op == 'imulLo' and d.args == a][-1].name
            fx, fy = self.sv[x], self.sv[y]
            fn = f"m_{lo}"
            out.append(f"have {fn} := imul_pair e_{lo} e_{n} {fx.name} {fy.name}")
            self.pair[(lo, n)] = Fact(fn, f"{par(fx.es)} * {par(fy.es)}", fx.poly * fy.poly)
            return
        if op in ('addl', 'subl'):
            x, y, _ = a
            mp = self.pending_mul.get('mul')
            if op == 'addl' and mp and mp[1] == x:
                clo, hi1 = mp
                l19 = {r: b for b, r in self.pending_mul.get('lea19', {}).items()}
                chi = [b for b, (d, r) in self.pending_mul['lea19'].items() if r == y][0]
                d, _ = self.pending_mul['lea19'][chi]
                T = self.pair[(clo, chi)]
                lo = [dd for dd in self.defs.values() if dd.op == 'mulLo' and dd.args == (clo, '19')][-1].name
                fn = f"m_{lo}"
                out.append(f"have {fn} := mul19_pair {T.name} e_{lo} e_{hi1} e_{d} e_{y} e_{n}")
                self.pair[(lo, n)] = Fact(fn, f"19 * {par(T.es)}", T.poly.scale(19))
                return
            if op == 'addl' and x == y and x in self.sv:
                f = self.sv[x]
                out.append(f"have sv_{n} := sv_addF2 e_{n} {f.name} {self.bname[x]} (by decide)")
                self.sv[n] = Fact(f"sv_{n}", f"2 * {par(f.es)}", f.poly.scale(2), 2 * f.bound)
                self.bname[n] = None
            return
        if op in ('adcl', 'sbbl'):
            c, d, g = a
            gd = self.defs[g]
            lo = [dd for dd in self.defs.values() if dd.op == gd.op[:-1] and dd.args == gd.args][-1]
            x, y, _ = lo.args
            p, q = self.getpair(x, c), self.getpair(y, d)
            if p is None or q is None:
                raise Exception(f"pair unknown for {n}: {(x, c)} {(y, d)}")
            lem = 'add_pair' if op == 'adcl' else 'sub_pair'
            fn = f"m_{lo.name}"
            out.append(f"have {fn} := {lem} {p.name} {q.name} e_{lo.name} e_{g} e_{n}")
            sym = '+' if op == 'adcl' else '-'
            poly = p.poly + q.poly if op == 'adcl' else p.poly - q.poly
            self.pair[(lo.name, n)] = Fact(fn, f"{par(p.es)} {sym} {par(q.es)}", poly)
            self.canon((lo.name, n), out)
            return
        if op == 'sar':
            c, k = a
            self.pending_mul.setdefault('sar', {})[(c, k)] = n
            self.try_shift(c, k, out)
            return
        if op == 'shrdl':
            x, c, k = a
            self.pending_mul.setdefault('shrd', {})[(c, k)] = (x, n)
            self.try_shift(c, k, out)
            return
        if op == 'shldl':
            c, x, k = a           # shld $k, x(src = lo), c(dst = hi)
            T = self.pair[(x, c)]
            s = 32 - k
            self.nC += 1
            C = f"C{self.nC}"
            fn = f"w_{n}"
            out.append(f"obtain ⟨{C}, h{C}, {fn}⟩ := shld{s} {T.name} e_{n}")
            self.carries.append((C, T.es, s))
            self.cof[(x, c)] = (C, s)
            self.m32[n] = Fact(fn, C, Poly.atom(C))
            return
        if op == 'and':
            x, k = a
            (lo, hi), T = self.lo_of(x)
            C, s = self.cof[(lo, hi)]
            assert int(k) == (2 ** 32 - 2 ** s)
            fn = f"m_{n}"
            out.append(f"have {fn} := mask_pair{s} {T.name} h{C} e_{n}")
            self.pair[(n, hi)] = Fact(fn, f"{C} * {2 ** s}", Poly.atom(C).scale(2 ** s))
            return
        if op == 'mulLo':
            return
        if op == 'mulHi':
            x, y = a
            assert y == '19'
            self.pending_mul['mul'] = (x, n)
            return
        raise Exception(f"unhandled op {op} {v.term}")

    def try_shift(self, c, k, out):
        sar = self.pending_mul.get('sar', {}).get((c, k))
        sh = self.pending_mul.get('shrd', {}).get((c, k))
        if sar is None or sh is None:
            return
        x, lo = sh
        T = self.pair[(x, c)]
        self.nC += 1
        C = f"C{self.nC}"
        fn = f"m_{lo}"
        j = len(self.carries)
        out.append(f"obtain ⟨{C}, h{C}, {fn}⟩ := shr_pair{k} {T.name} ({self.pre}_b{j} {self.bargs()}) e_{lo} e_{sar}")
        self.blemmas.append((j, T.es, list(self.carries)))
        self.carries.append((C, T.es, k))
        self.cof[(x, c)] = (C, k)
        self.pair[(lo, sar)] = Fact(fn, C, Poly.atom(C))

    def bargs(self):
        return ' '.join(['R0 R1 R2 R3 R4 R5 R6 R7 R8 R9'] + [c for (c, _, _) in self.carries] + ['hRB'] +
                        [f"h{c}" for (c, _, _) in self.carries])


    def word(self, nm, out):
        """the M32 fact of a final word"""
        if nm in self.m32:
            return self.m32[nm]
        key, f = self.lo_of(nm)
        if f is not None:
            fn = f"w_{nm}"
            out.append(f"have {fn} := M32_lo {f.name}")
            self.m32[nm] = Fact(fn, f.es, f.poly)
            return self.m32[nm]
        d = self.defs[nm]
        assert d.op in ('addl', 'subl'), d.term
        x, y, _ = d.args
        fx, fy = self.word(x, out), self.word(y, out)
        lem = 'add32' if d.op == 'addl' else 'sub32'
        sym = '+' if d.op == 'addl' else '-'
        fn = f"w_{nm}"
        out.append(f"have {fn} := {lem} {fx.name} {fy.name} e_{nm}")
        self.m32[nm] = Fact(fn, f"{par(fx.es)} {sym} {par(fy.es)}", None)
        return self.m32[nm]
