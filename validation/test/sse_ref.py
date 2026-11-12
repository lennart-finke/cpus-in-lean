#!/usr/bin/env python3
"""Independent reference for the computed SSE3..SSE4.2/SSE4a instructions of the IA-32 model.

Written from the manuals, not from the Lean code (x86_32/X86/Ext/Sse.lean): AMD64 APM vol. 4
(1.5 "String Compare Instructions", DPPS, DPPD, MPSADBW, ROUNDPS/PD/SS/SD, EXTRQ, INSERTQ), APM vol. 1
4.10 (SIMD floating-point exceptions: tininess on the result rounded with an unbounded exponent,
masked underflow only when inexact, FZ), Intel SDM vol. 2B 4.1 (PCMPxSTRx override table) and
FISTTP. Floating point is exact rational arithmetic (fractions.Fraction) rounded once per operation.

    sse_ref.py check TRANSCRIPT    recompute every sstr, sse4a, fisttp line and the ROUND*, DPPS,
                                   DPPD and MPSADBW 'sse' lines of a system-test transcript
                                   (test/sys/out/model.txt or qemu.txt); exit status 1 on a mismatch

Only masked SIMD exceptions are modelled here (the fuzzers keep every MXCSR mask set).

Where the manuals differ: for the equal-ordered (sub-string) aggregation, APM vol. 4 1.5.3 gives
pseudo code in which an empty prototype matches only at positions 0..l2 and no partial match is
recorded at the end of a full-length string under test; the SDM's override table (an invalid
prototype element matches anything, an invalid string element after a valid prototype element does
not, positions beyond the 128-bit operand are not compared) gives all ones for an empty prototype and
records partial matches at the end. This reference follows the SDM, as the model and QEMU do; the
native hardware family 'sse42_strings' (fp_cases.py) records what Zen 2 does.
"""
import re
import sys
from fractions import Fraction

# ---------------------------------------------------------------- binary32 / binary64

FORMATS = {32: (8, 23), 64: (11, 52)}
IE, DE, ZE, OE, UE, PE = 1, 2, 4, 8, 16, 32


class Fmt:
    def __init__(self, width):
        self.w = width
        self.e, self.p = FORMATS[width]
        self.bias = (1 << (self.e - 1)) - 1
        self.emin = 1 - self.bias
        self.emax = self.bias
        self.quiet = 1 << (self.p - 1)
        self.expmask = (1 << self.e) - 1
        self.sign = 1 << (width - 1)

    def indefinite(self):
        return self.sign | (self.expmask << self.p) | self.quiet

    def isnan(self, b):
        return (b >> self.p) & self.expmask == self.expmask and b & ((1 << self.p) - 1) != 0

    def issnan(self, b):
        return self.isnan(b) and not b & self.quiet


def classify(f, b, daz):
    """('nan', b) / ('inf', sign) / ('num', sign, Fraction magnitude, denormal flag)."""
    s = b >> (f.w - 1) & 1
    ex = (b >> f.p) & f.expmask
    fr = b & ((1 << f.p) - 1)
    if ex == f.expmask:
        return ('nan', b) if fr else ('inf', s)
    if ex == 0:
        if fr == 0:
            return ('num', s, Fraction(0), False)
        if daz:
            return ('num', s, Fraction(0), False)
        return ('num', s, Fraction(fr) * Fraction(2) ** (f.emin - f.p), True)
    return ('num', s, Fraction((1 << f.p) | fr) * Fraction(2) ** (ex - f.bias - f.p), False)


def round_int(x, negative, rc):
    """Round a non-negative Fraction to an integer: RC 0 nearest-even, 1 down, 2 up, 3 truncate
    (directions refer to the signed value)."""
    q, r = divmod(x.numerator, x.denominator)
    rem = Fraction(r, x.denominator)
    if rem == 0:
        return q
    if rc == 0:
        return q + 1 if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and q % 2) else q
    if rc == 1:
        return q + 1 if negative else q
    if rc == 2:
        return q if negative else q + 1
    return q


def ilog2(x):
    """floor(log2 x) for a positive Fraction."""
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fraction(2) ** e > x:
        e -= 1
    return e


def encode(f, s, x, rc, ftz):
    """Round the exact value (-1)^s * x into the format with masked exceptions (APM vol. 1 4.10.2)."""
    if x == 0:
        return s << (f.w - 1), 0
    e = ilog2(x)
    m = round_int(x / Fraction(2) ** (e - f.p), s, rc)
    if m == 1 << (f.p + 1):
        m //= 2
        e += 1
    inexact = Fraction(m) * Fraction(2) ** (e - f.p) != x
    if e > f.emax:
        big = rc == 0 or (rc == 1 and s) or (rc == 2 and not s)
        mag = (f.expmask << f.p) if big else ((f.expmask << f.p) - 1)
        return (s << (f.w - 1)) | mag, OE | PE
    if e < f.emin:   # tiny (Resultround below Minnormal)
        if ftz:
            return s << (f.w - 1), UE | PE
        q = round_int(x / Fraction(2) ** (f.emin - f.p), s, rc)
        inexact = Fraction(q) * Fraction(2) ** (f.emin - f.p) != x
        return (s << (f.w - 1)) | q, (UE | PE) if inexact else 0
    return (s << (f.w - 1)) | ((e + f.bias) << f.p) | (m - (1 << f.p)), PE if inexact else 0


def arith(f, op, a, b, mx):
    """a op b ('add', 'mul') with MXCSR mx (RC, DAZ, FZ); returns (bits, flags)."""
    daz, ftz, rc = bool(mx & 0x40), bool(mx & 0x8000), (mx >> 13) & 3
    if f.isnan(a) or f.isnan(b):
        r = (a if f.isnan(a) else b) | f.quiet
        return r, IE if f.issnan(a) or f.issnan(b) else 0
    ca, cb = classify(f, a, daz), classify(f, b, daz)
    de = DE if (ca[0] == 'num' and ca[3]) or (cb[0] == 'num' and cb[3]) else 0
    if op == 'mul':
        s = (a ^ b) >> (f.w - 1) & 1
        if ca[0] == 'inf' or cb[0] == 'inf':
            other = cb if ca[0] == 'inf' else ca
            if other[0] == 'num' and other[2] == 0:
                return f.indefinite(), IE
            return (s << (f.w - 1)) | (f.expmask << f.p), de
        r, fl = encode(f, s, ca[2] * cb[2], rc, ftz)
        return r, fl | de
    # add
    if ca[0] == 'inf' and cb[0] == 'inf':
        if ca[1] != cb[1]:
            return f.indefinite(), IE
        return a, 0
    if ca[0] == 'inf':
        return (ca[1] << (f.w - 1)) | (f.expmask << f.p), de
    if cb[0] == 'inf':
        return (cb[1] << (f.w - 1)) | (f.expmask << f.p), de
    va = -ca[2] if ca[1] else ca[2]
    vb = -cb[2] if cb[1] else cb[2]
    v = va + vb
    if v == 0:   # exact zero: -0 only for (-0) + (-0), or opposite signs rounding down (IEEE 754 6.3)
        s = 1 if (ca[1] and cb[1]) or (ca[1] != cb[1] and rc == 1) else 0
        return s << (f.w - 1), de
    r, fl = encode(f, 1 if v < 0 else 0, abs(v), rc, ftz)
    return r, fl | de


def lanes(v, bits):
    return [(v >> (bits * k)) & ((1 << bits) - 1) for k in range(128 // bits)]


def join(ls, bits):
    return sum(x << (bits * k) for k, x in enumerate(ls))


def dp(width, a, b, imm, mx):
    """DPPS (32) / DPPD (64), APM vol. 4: products selected by imm[7:4] (others +0), summed pairwise
    (lower index first), the sum written where imm[3:0] says (others +0)."""
    f = Fmt(width)
    n = 128 // width
    A, B = lanes(a, width), lanes(b, width)
    flags = 0
    prods = []
    for k in range(n):
        if imm >> (4 + k) & 1:
            p, fl = arith(f, 'mul', A[k], B[k], mx)
            flags |= fl
        else:
            p = 0
        prods.append(p)
    if n == 4:
        t2, f2 = arith(f, 'add', prods[0], prods[1], mx)
        t3, f3 = arith(f, 'add', prods[2], prods[3], mx)
        t4, f4 = arith(f, 'add', t2, t3, mx)
        flags |= f2 | f3 | f4
    else:
        t4, f4 = arith(f, 'add', prods[0], prods[1], mx)
        flags |= f4
    return join([t4 if imm >> k & 1 else 0 for k in range(n)], width), flags


def hop(width, sub, a, b, mx):
    """HADDPS/HADDPD/HSUBPS/HSUBPD (SDM vol. 2 and AMD APM vol. 4 instruction pages): the pairs of
    adjacent elements of a, then of b. HADD: element 2j + element 2j+1 (the lower element first: the
    order the AMD EPYC 7742 shows with two NaN operands, native campaign family sse3_hadd_nan; the
    current manuals write SRC1[63:32] + SRC1[31:0], older SDM editions xmm1[0..31] + xmm1[32..63]);
    HSUB: element 2j - element 2j+1 (SDM HSUBPS "DEST[31:0] := SRC1[31:0] - SRC1[63:32]"). With two
    NaN operands the first operand's NaN is returned (SDM vol. 1, table 4-7). Returns (bits, flags)."""
    f = Fmt(width)
    out, flags = [], 0
    for src in (a, b):
        ls = lanes(src, width)
        for j in range(0, len(ls), 2):
            if sub:
                nb = ls[j + 1] ^ (1 << (width - 1)) if not f.isnan(ls[j + 1]) else ls[j + 1]
                r, fl = arith(f, 'add', ls[j], nb, mx)
            else:
                r, fl = arith(f, 'add', ls[j], ls[j + 1], mx)
            out.append(r)
            flags |= fl
    return join(out, width), flags


def round_lane(f, b, imm, mx):
    """ROUND* of one lane, APM vol. 4 ROUNDPS: imm[1:0] RC unless imm[2] (MXCSR.RC); imm[3]
    suppresses PE; SNaN -> QNaN with IE; DAZ zeroes denormals; no DE."""
    rc = (mx >> 13) & 3 if imm & 4 else imm & 3
    if f.isnan(b):
        return b | f.quiet, IE if f.issnan(b) else 0
    c = classify(f, b, bool(mx & 0x40))
    if c[0] == 'inf':
        return b, 0
    s, x = c[1], c[2]
    q = round_int(x, s, rc)
    if q == 0:
        r = s << (f.w - 1)
    else:
        r, _ = encode(f, s, Fraction(q), 0, False)
    return r, (PE if Fraction(q) != x and not imm & 8 else 0)


def round_op(op, a, b, imm, mx):
    width = 32 if op in (0x08, 0x0A) else 64
    f = Fmt(width)
    if op in (0x08, 0x09):
        out, flags = [], 0
        for x in lanes(b, width):
            r, fl = round_lane(f, x, imm, mx)
            out.append(r)
            flags |= fl
        return join(out, width), flags
    r, fl = round_lane(f, lanes(b, width)[0], imm, mx)
    A = lanes(a, width)
    A[0] = r
    return join(A, width), fl


def mpsadbw(a, b, imm):
    """APM vol. 4 MPSADBW: word i = SumAbsDiff(src1[i1+i+3:i1+i], src2[j1+3:j1]), i1 = 4*imm[2],
    j1 = 4*imm[1:0]."""
    A, B = lanes(a, 8), lanes(b, 8)
    i1, j1 = 4 * (imm >> 2 & 1), 4 * (imm & 3)
    return join([sum(abs(A[i1 + i + k] - B[j1 + k]) for k in range(4)) for i in range(8)], 16)

# ---------------------------------------------------------------- PCMPxSTRx


def str_elems(v, imm):
    bits = 16 if imm & 1 else 8
    out = []
    for x in lanes(v, bits):
        if imm & 2 and x >> (bits - 1):
            x -= 1 << bits
        out.append(x)
    return out


def implicit_len(elems):
    for k, x in enumerate(elems):
        if x == 0:
            return k
    return len(elems)


def explicit_len(r, m):
    r = r - (1 << 32) if r >> 31 else r
    return min(abs(r), m)


def pcmpstr(imm, a, b, l1, l2):
    """pCmprSumm (IntRes2) of prototype a (xmm1) and string under test b (xmm2/m128)."""
    P, S = str_elems(a, imm), str_elems(b, imm)
    m = len(P)
    agg = imm >> 2 & 3

    def ok(i, j):     # BoolRes with the SDM's override for invalid elements
        vi, vj = i < l1, j < l2
        if agg == 0 or agg == 1:
            if not (vi and vj):
                return False
        elif agg == 2:
            if not vi and not vj:
                return True
            if vi != vj:
                return False
        else:
            if not vi:
                return True
            if not vj:
                return False
        if agg == 1:
            return S[j] >= P[i] if i % 2 == 0 else S[j] <= P[i]
        return P[i] == S[j]
    res = 0
    for j in range(m):
        if agg == 0:
            bit = any(ok(i, j) for i in range(m))
        elif agg == 1:
            bit = any(ok(i, j) and ok(i + 1, j) for i in range(0, m, 2))
        elif agg == 2:
            bit = ok(j, j)
        else:
            bit = all(ok(i, j + i) for i in range(m - j))
        res |= bit << j
    pol = imm >> 4 & 3
    if pol == 1:
        res ^= (1 << m) - 1
    elif pol == 3:
        res ^= (1 << l2) - 1
    return res


def pcmpstr_full(op, imm, a, b, eax, edx):
    """(ecx or None, xmm0 or None, eflags & 0x8D5) of PCMPESTRM (60), PCMPESTRI (61), PCMPISTRM (62),
    PCMPISTRI (63)."""
    m = 8 if imm & 1 else 16
    if op in (0x60, 0x61):
        l1, l2 = explicit_len(eax, m), explicit_len(edx, m)
    else:
        l1, l2 = implicit_len(str_elems(a, imm)), implicit_len(str_elems(b, imm))
    r = pcmpstr(imm, a, b, l1, l2)
    fl = (1 if r else 0) | (0x40 if l2 < m else 0) | (0x80 if l1 < m else 0) | (0x800 if r & 1 else 0)
    if op & 1:
        if r == 0:
            ecx = m
        elif imm & 0x40:
            ecx = r.bit_length() - 1
        else:
            ecx = (r & -r).bit_length() - 1
        return ecx, None, fl
    if imm & 0x40:
        bits = 16 if imm & 1 else 8
        x0 = join([((1 << bits) - 1) if r >> k & 1 else 0 for k in range(m)], bits)
    else:
        x0 = r
    return None, x0, fl

# ---------------------------------------------------------------- SSE4a, FISTTP


def field(len_, idx):
    len_ &= 63
    return ((1 << 64) - 1) if len_ == 0 else (1 << len_) - 1, idx & 63


def extrq(v, len_, idx):
    """APM vol. 4 EXTRQ on bits 63:0; bits idx+len > 64 read as zero (the model's choice for the
    undefined case)."""
    mask, idx = field(len_, idx)
    return (v >> idx) & mask


def insertq(d, s, len_, idx):
    mask, idx = field(len_, idx)
    return ((d & ~(mask << idx)) | ((s & mask) << idx)) & ((1 << 64) - 1)


def fisttp(se, sig, size):
    """(stored integer, FSW exception bits) of FISTTP m16/m32/m64 (truncation; masked IE stores the
    integer indefinite)."""
    bits = size * 8
    ex = se & 0x7FFF
    neg = se >> 15
    indef = 1 << (bits - 1)
    if ex == 0x7FFF:
        return indef, IE
    x = Fraction(sig) * Fraction(2) ** (ex - 16383 - 63) if ex else Fraction(sig) * Fraction(2) ** (-16382 - 63)
    q = x.numerator // x.denominator
    v = -q if neg else q
    if v < -(1 << (bits - 1)) or v >= 1 << (bits - 1):
        return indef, IE
    return v & ((1 << bits) - 1), (PE if Fraction(q) != x else 0)

# ---------------------------------------------------------------- transcript checker


def hx(s):
    return int(s, 16)


def check_line(line):
    """None if the line is not checked here, else a list of (what, expected, got) mismatches."""
    w = line.split()
    if not w:
        return None
    if w[0] == 'sstr' and 'vec=' not in line:
        code = bytes.fromhex(w[2])
        op, imm = code[3], code[5]
        kv = dict(x.split('=') for x in w[3:] if '=' in x)
        a, b = hx(kv['a']), hx(kv['b'])
        ecx, x0, fl = pcmpstr_full(op, imm, a, b, hx(kv['eax']), hx(kv['edx']))
        bad = []
        if ecx is not None and ecx != hx(kv['ecx']):
            bad.append(('ecx', ecx, hx(kv['ecx'])))
        if x0 is not None and x0 != hx(kv['x0']):
            bad.append(('x0', x0, hx(kv['x0'])))
        if fl != hx(kv['fl']):
            bad.append(('fl', fl, hx(kv['fl'])))
        return bad
    if w[0] == 'sse4a' and 'vec=' not in line:
        code = bytes.fromhex(w[2])
        arrow = w.index('->')
        before = dict(x.split('=') for x in w[3:arrow])
        after = dict(x.split('=') for x in w[arrow + 1:])
        x = {k: hx(v) for k, v in before.items()}
        lo = lambda v: v & ((1 << 64) - 1)
        # bits 127:64 of the destination: undefined in the APM, cleared by the EPYC 7742 (native family sse4a)
        if code[2] == 0x78 and code[0] == 0x66:
            k = 'x%d' % (code[3] & 7)
            exp = {k: extrq(lo(x[k]), code[4], code[5])}
        elif code[2] == 0x78:
            exp = {'x0': insertq(lo(x['x0']), lo(x['x1']), code[4], code[5])}
        elif code[0] == 0x66:
            exp = {'x0': extrq(lo(x['x0']), x['x1'] & 63, (x['x1'] >> 8) & 63)}
        else:
            hi = x['x1'] >> 64
            exp = {'x0': insertq(lo(x['x0']), lo(x['x1']), hi & 63, (hi >> 8) & 63)}
        return [(k, v, hx(after[k])) for k, v in exp.items() if hx(after[k]) != v]
    if w[0] in ('ssem.hnanps:', 'ssem.hnanpd:'):
        # mx=M a=X b=Y then (name=vec r=R mxo=M) for haddps, hsubps, haddpd, hsubpd; all masked
        mx = hx(w[1].split('=')[1])
        a, b = hx(w[2].split('=')[1]), hx(w[3].split('=')[1])
        bad = []
        k = 4
        while k + 2 < len(w):
            name, vec = w[k].split('=')
            r, mxo = hx(w[k + 1].split('=')[1]), hx(w[k + 2].split('=')[1])
            width = 32 if name.endswith('ps') else 64
            er, fl = hop(width, name.startswith('hsub'), a, b, mx)
            if hx(vec) != 0xFFFF:
                bad.append((name + ' vec', 0xFFFF, hx(vec)))
            if er != r:
                bad.append((name, er, r))
            if mx | fl != mxo:
                bad.append((name + ' mxcsr', mx | fl, mxo))
            k += 3
        return bad
    if w[0] == 'fisttp':
        kv = dict(x.split('=') for x in w[2:] if '=' in x)
        size = int(kv['size'])
        a = kv['a']
        se, sig = hx(a[:8]) & 0xFFFF, hx(a[8:])
        v, fl = fisttp(se, sig, size)
        got = hx(kv['mem']) & ((1 << (8 * size)) - 1)
        sw = hx(kv['sw']) & 0x3F
        bad = []
        if v != got:
            bad.append(('mem', v, got))
        if fl != sw:
            bad.append(('sw', fl, sw))
        return bad
    if w[0] == 'sse' and len(w) > 2 and re.fullmatch('660f3a(0[89ab]|4[012])[0-9a-f]{4}', w[2]):
        code = bytes.fromhex(w[2])
        op, imm = code[3], code[5]
        kv = {}
        for x in w[3:]:
            if '=' in x:
                k, v = x.split('=', 1)
                kv.setdefault(k, v)
        mx_in = hx(kv['mx'])
        a, b = hx(kv['a']), hx(kv['b'])
        arrow = w.index('->')
        x0 = hx(w[arrow + 1])
        mx_out = hx(w[-1].split('=')[1]) if w[-1].startswith('mx=') else hx([t for t in w[arrow:] if t.startswith('mx=')][0][3:])
        if op == 0x42:
            return [('x0', mpsadbw(a, b, imm), x0)] if mpsadbw(a, b, imm) != x0 else []
        if op in (0x40, 0x41):
            r, fl = dp(32 if op == 0x40 else 64, a, b, imm, mx_in)
        else:
            r, fl = round_op(op, a, b, imm, mx_in)
        bad = []
        if r != x0:
            bad.append(('x0', r, x0))
        if mx_in | fl != mx_out:
            bad.append(('mxcsr', mx_in | fl, mx_out))
        return bad
    return None


def check(path):
    n = bad = 0
    with open(path, errors='replace') as fh:
        text = fh.read().splitlines()
    for line in text:
        line = line.strip()
        r = check_line(line)
        if r is None:
            continue
        n += 1
        if r:
            bad += 1
            if bad <= 20:
                print('MISMATCH', line)
                for what, exp, got in r:
                    print('   %s: reference %x, transcript %x' % (what, exp, got))
    print('sse_ref: %d lines checked, %d mismatches' % (n, bad))
    return bad == 0 and n > 0


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2]) else 1)
    print(__doc__)
    sys.exit(2)
