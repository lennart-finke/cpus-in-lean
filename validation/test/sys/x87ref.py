#!/usr/bin/env python3
"""Reference for the x87 transcendental instructions, written independently of the Lean model
(x86_32/X86/Transcendental.lean) to test it. Masked exceptions only.

Specification (the model's, see x86_32/README.md):
* Results are the correctly rounded values (64-bit significand, rounding control; precision control
  does not apply) of the exact functions.
* FSIN/FCOS/FPTAN/FSINCOS reduce exactly by Pi/2, Pi = 0.C90FDAA22168C234C * 2^2 (the SDM's 66-bit pi,
  vol. 1, 8.3.8), with the nearest quotient; |x| >= 2^63 is out of range (C2 = 1, ST0 unchanged).
* Special operands follow the SDM instruction tables. Outside the documented domains the AMD EPYC 7742
  defines the result (the native campaign's x87_transcendental/x87_trans_boundary families,
  validation/README.md): F2XM1 returns a finite x with |x| > 1 unchanged with PE, +inf for +inf and
  -1 for -inf (no flags), -0.5 with PE for -1 and, for +1, the rounding of a value just below 1 with
  PE; FYL2XP1 computes y * log2(1 + x) for every finite x > -1 and returns x with PE for x <= -1, except
  x = -1 with y = +-0 or +-inf (-+0, -+inf); x = +inf gives +-inf by the sign of y (y = +-0: invalid),
  x = -inf stays invalid (native x87_trans_special). F2XM1, FYL2X and FYL2XP1 report PE for every finite
  nonzero result, also an exact one (and UE if that result is a denormal).

Method (deliberately unlike the model's ball arithmetic): exp, ln, sqrt and division come from Python's
decimal module (correctly rounded at the working precision P digits), pi from the decimal
documentation's series, atan by argument halving and Taylor, sin/cos by Taylor. A value computed at
P digits is trusted to a relative 10^(20-P) (a wide margin; formulas are chosen without catastrophic
cancellation). The enclosure is rounded when it contains no rounding breakpoint (a multiple of
2^(E-65) for a value in [2^E, 2^(E+1)), which covers representable values, midpoints, the denormal
grid and the underflow/overflow thresholds); otherwise P grows.

Usage:
  x87ref.py table OUT.h        write the model-only test table (t_x87t.c): inputs and expected results
  x87ref.py qemu QEMU.txt      deviation rules for x87t lines where QEMU's transcript differs from the
                               reference (writes them to stdout, a summary to stderr)
  x87ref.py eval OP CW A [B]   one case; operands as hex se_sig, e.g. 3fff_8000000000000000
"""
import decimal
import random
import re
import sys
from decimal import Decimal as D
from fractions import Fraction as Fr

IE, DE, ZE, OE, UE, PE, SF, C1, C2 = 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x200, 0x400
INDEF = (0xFFFF, 0xC000000000000000)
ONE = (0x3FFF, 1 << 63)
J = 1 << 63
OPS = ['f2xm1', 'fyl2x', 'fyl2xp1', 'fpatan', 'fsin', 'fcos', 'fptan', 'fsincos']
PI66 = Fr(0xC90FDAA22168C234C, 2 ** 66)   # SDM vol. 1, 8.3.8

# ---------------------------------------------------------------- encodings

def sgn(x): return x[0] >> 15
def ex(x): return x[0] & 0x7FFF
def unsupported(x): return ex(x) != 0 and not x[1] >> 63
def iszero(x): return ex(x) == 0 and x[1] == 0
def isden(x): return ex(x) == 0 and x[1] != 0
def isinf(x): return ex(x) == 0x7FFF and x[1] == J
def isnan(x): return ex(x) == 0x7FFF and x[1] >> 63 and x[1] & (J - 1) != 0
def issnan(x): return isnan(x) and not (x[1] >> 62) & 1
def finite(x): return not unsupported(x) and ex(x) != 0x7FFF
def quiet(x): return (x[0], x[1] | 1 << 62)
def zero(s): return (s << 15, 0)
def inf(s): return ((s << 15) | 0x7FFF, J)
def val(x):
    """Exact value of a finite operand (pseudo-denormals read with exponent 1)."""
    v = Fr(x[1]) * Fr(2) ** (max(ex(x), 1) - 16383 - 63)
    return -v if sgn(x) else v

def nan2(a, b):
    """Two-operand NaN result (SDM vol. 1, table 4-7): an SNaN and a QNaN give the QNaN; NaNs of
    the same kind give the larger significand (ties: the positive one); quieted."""
    if isnan(a) and isnan(b):
        if issnan(a) != issnan(b):
            return quiet(b if issnan(a) else a)
        if a[1] != b[1]:
            return quiet(a if a[1] > b[1] else b)
        return quiet(a if not sgn(a) else b)
    return quiet(a if isnan(a) else b)

# ---------------------------------------------------------------- rounding

def log2floor(v):
    """E with 2^E <= v < 2^(E+1), v > 0 rational."""
    e = v.numerator.bit_length() - v.denominator.bit_length()
    p = Fr(2) ** e
    if p > v:
        e -= 1
    elif p * 2 <= v:
        e += 1
    return e

def rint(x, rc, neg):
    """Round x >= 0 to an integer in mode rc (0 nearest-even, 1 down, 2 up, 3 zero) for a value of
    sign `neg`; returns (q, inexact)."""
    q, r = divmod(x.numerator, x.denominator)
    if r == 0:
        return q, False
    if rc == 0:
        up = 2 * r > x.denominator or (2 * r == x.denominator and q % 2 == 1)
    else:
        up = (rc == 1 and neg) or (rc == 2 and not neg)
    return q + up, True

def round80(v, rc):
    """Correctly round a nonzero rational to extended precision (masked OE/UE)."""
    neg = v < 0
    a = abs(v)
    s = 0x8000 if neg else 0
    E = log2floor(a)
    q, inexact = rint(a / Fr(2) ** (E - 63), rc, neg)
    Eu = E
    if q == 1 << 64:
        q, Eu = q >> 1, E + 1
    if Eu > 16383:
        if rc == 0 or (rc == 1 and neg) or (rc == 2 and not neg):
            return (s | 0x7FFF, J), OE | PE | C1
        return (s | 0x7FFE, (1 << 64) - 1), OE | PE
    tiny = Eu < -16382
    if E < -16382:
        q, inexact = rint(a * Fr(2) ** 16445, rc, neg)
        up = Fr(q) / Fr(2) ** 16445 > a
        fl = (PE | (UE if tiny else 0) if inexact else 0) | (C1 if up else 0)
        if q == 0:
            return (s, 0), fl
        if q >= J:
            return (s | 1, q), fl
        return (s, q), fl
    up = Fr(q) * Fr(2) ** (Eu - 63) > a
    return (s | (Eu + 16383), q), (PE if inexact else 0) | (C1 if up else 0)

def round_open(neg, lo, hi, rc):
    """The rounding of every value in the open interval (lo, hi) of magnitudes, or None if the
    interval contains a breakpoint."""
    if not (0 < lo < hi):
        return None
    g = Fr(2) ** (log2floor(lo) - 65)
    k = lo // g
    if (k + 1) * g < hi:
        return None
    m = (k + Fr(1, 2)) * g
    return round80(-m if neg else m, rc)

# ---------------------------------------------------------------- decimal arithmetic

def ctx(P):
    """A P-digit context, also installed as the thread's context (for unary minus etc.)."""
    c = decimal.Context(prec=P, rounding=decimal.ROUND_HALF_EVEN, Emin=-10 ** 9, Emax=10 ** 9)
    decimal.setcontext(c)
    return c

def dec(c, f):
    return c.divide(D(f.numerator), D(f.denominator))

def pi_dec(c):
    c2 = ctx(c.prec + 5)
    lasts, t, s, n, na, d, da = 0, D(3), D(3), 1, 0, 0, 24
    while s != lasts:
        lasts = s
        n, na = n + na, na + 8
        d, da = d + da, da + 32
        t = c2.divide(c2.multiply(t, n), d)
        s = c2.add(s, t)
    return c.plus(s)

def small(t, c):
    """|t| below 10^-(P+5) relative to 1."""
    return t == 0 or t.adjusted() < -(c.prec + 5)

def expm1_dec(t, c):
    if abs(t) < D('0.01'):
        s, term, k = t, t, 1
        while True:
            k += 1
            term = c.divide(c.multiply(term, t), k)
            if small(c.divide(term, s), c):
                return s
            s = c.add(s, term)
    return c.subtract(c.exp(t), 1)

def ln1p_dec(x, c):
    """ln(1 + x) for a rational |x| < 1/2."""
    if abs(x) < Fr(1, 2 ** 20):
        xd = dec(c, x)
        s, pw, k = xd, xd, 1
        while True:
            k += 1
            pw = c.multiply(pw, xd)
            term = c.divide(pw, k if k % 2 else -k)
            if small(c.divide(term, s), c):
                return s
            s = c.add(s, term)
    return c.ln(dec(c, 1 + x))

def atan_dec(z, c):
    """atan z for 0 < z <= 1: five argument halvings z/(1 + sqrt(1 + z^2)), then Taylor."""
    h = 5
    for _ in range(h):
        z = c.divide(z, c.add(1, c.sqrt(c.add(1, c.multiply(z, z)))))
    z2 = c.multiply(z, z)
    s, term, k = z, z, 0
    while True:
        k += 1
        term = c.multiply(term, -z2)
        t = c.divide(term, 2 * k + 1)
        if small(c.divide(t, s), c):
            break
        s = c.add(s, t)
    return c.multiply(s, 2 ** h)

def sin_dec(r, c):
    s, term, k, r2 = r, r, 0, c.multiply(r, r)
    while True:
        k += 1
        term = c.divide(c.multiply(term, -r2), (2 * k) * (2 * k + 1))
        if small(c.divide(term, s), c):
            return s
        s = c.add(s, term)

def cos_dec(r, c):
    s, term, k, r2 = D(1), D(1), 0, c.multiply(r, r)
    while True:
        k += 1
        term = c.divide(c.multiply(term, -r2), (2 * k - 1) * (2 * k))
        if small(term, c):
            return s
        s = c.add(s, term)

# ---------------------------------------------------------------- correctly rounded evaluation

def evaluate(f, rc, bounds=None):
    """f(c) returns a nonzero Decimal approximation trusted to a relative 10^(20-P). `bounds` gives
    exact (lo, hi) magnitude bounds known a priori (tiny-argument cases)."""
    for P in (60, 150, 400, 1200, 4000):
        c = ctx(P)
        v = Fr(f(c))
        ctx(P)
        eps = Fr(1, 10 ** (P - 20))
        neg = v < 0
        lo, hi = abs(v) * (1 - eps), abs(v) * (1 + eps)
        if bounds:
            lo, hi = max(lo, bounds[0]), min(hi, bounds[1])
        r = round_open(neg, lo, hi, rc)
        if r is not None:
            return r
    raise RuntimeError('no decision at 4000 digits')

def rounded_exact(v, rc):
    return (zero(0), 0) if v == 0 else round80(v, rc)

def pi_mult(k, neg, rc):
    """Round +-k*pi/4."""
    return evaluate(lambda c: c.multiply(pi_dec(c), D(-k if neg else k) / 4), rc)

# ---------------------------------------------------------------- instructions
# Each returns (value, flags) for the destination.

def special2(x, y):
    if unsupported(x) or unsupported(y):
        return INDEF, IE
    if isnan(x) or isnan(y):
        return nan2(x, y), IE if issnan(x) or issnan(y) else 0
    return None

def denf(*xs):
    return DE if any(isden(x) for x in xs) else 0

def exact_pe(r):
    """An exact result reported inexact, as the EPYC 7742 does for F2XM1/FYL2X/FYL2XP1: PE, and UE for
    a denormal (masked underflow)."""
    v, fl = r
    if iszero(v) or ex(v) == 0x7FFF:
        return r
    return v, fl | PE | (UE if ex(v) == 0 else 0)

def f2xm1(x, rc):
    if unsupported(x):
        return INDEF, IE
    if isnan(x):
        return quiet(x), IE if issnan(x) else 0
    if iszero(x):
        return x, 0
    if isinf(x):
        return ((0xBFFF, J) if sgn(x) else x), 0
    if abs(val(x)) > 1:
        return x, PE
    v = val(x)
    if v == 1:
        return round80(1 - Fr(1, 2 ** 200), rc)
    if v == -1:
        return round80(Fr(-1, 2), rc)[0], PE
    def f(c):
        return expm1_dec(c.multiply(dec(c, v), c.ln(D(2))), c)
    r, fl = evaluate(f, rc)
    return r, fl | denf(x)

def fyl2x(x, y, rc):
    sp = special2(x, y)
    if sp:
        return sp
    de = denf(x, y)
    if sgn(x) and not iszero(x):
        return INDEF, IE
    if iszero(x):
        if iszero(y):
            return INDEF, IE
        if isinf(y):
            return inf(1 - sgn(y)), de
        return inf(1 - sgn(y)), ZE
    if isinf(x):
        return (INDEF, IE) if iszero(y) else (inf(sgn(y)), de)
    vx = val(x)
    below = vx < 1
    if isinf(y):
        return (INDEF, IE) if vx == 1 else (inf(sgn(y) ^ below), de)
    if iszero(y):
        return zero(sgn(y) ^ below), de
    vy = val(y)
    k = log2floor(vx)
    if vx == Fr(2) ** k:
        if k == 0:
            return zero(sgn(y)), de
        r, fl = exact_pe(round80(vy * k, rc))
        return r, fl | de
    def f(c):
        cc = ctx(c.prec + 25)
        l2 = cc.divide(cc.ln(dec(cc, vx)), cc.ln(D(2)))
        return c.multiply(dec(c, vy), l2)
    r, fl = evaluate(f, rc)
    return r, fl | de

LNP1_LO = -Fr(0x95F619980C4336F7, 2 ** 65)   # floor((1 - sqrt2/2) 2^65) / 2^65
LNP1_HI = Fr(0xD413CCCFE7799211, 2 ** 65)    # floor((sqrt2 - 1) 2^65) / 2^65

def fyl2xp1(x, y, rc):
    sp = special2(x, y)
    if sp:
        return sp
    de = denf(x, y)
    # x = +inf: +-inf by the sign of y without an exception (y = +-0: invalid); x = -1 with y = +-0 or
    # +-inf: y * log2(0) = -+0, -+inf without an exception (EPYC 7742, native x87_trans_special)
    if not finite(x):
        return (inf(sgn(y)), de) if not sgn(x) and not iszero(y) else (INDEF, IE)
    if not iszero(x) and val(x) == -1 and (iszero(y) or isinf(y)):
        return (zero(1 - sgn(y)) if iszero(y) else inf(1 - sgn(y))), de
    if not iszero(x) and val(x) <= -1:
        return x, PE | de
    if iszero(x):
        return (INDEF, IE) if isinf(y) else (zero(sgn(x) ^ sgn(y)), de)
    if isinf(y):
        return inf(sgn(x) ^ sgn(y)), de
    if iszero(y):
        return zero(sgn(x) ^ sgn(y)), de
    vx, vy = val(x), val(y)
    k = log2floor(1 + vx)
    if 1 + vx == Fr(2) ** k:
        r, fl = exact_pe(round80(vy * k, rc))
        return r, fl | de
    def f(c):
        if LNP1_LO <= vx <= LNP1_HI:
            return c.multiply(dec(c, vy), c.divide(ln1p_dec(vx, c), c.ln(D(2))))
        cc = ctx(c.prec + 25)
        l2 = cc.divide(cc.ln(dec(cc, 1 + vx)), cc.ln(D(2)))
        return c.multiply(dec(c, vy), l2)
    r, fl = evaluate(f, rc)
    return r, fl | de

def fpatan(x, y, rc):
    """atan2(y, x), x = ST0, y = ST1."""
    sp = special2(x, y)
    if sp:
        return sp
    de = denf(x, y)
    sy = sgn(y)
    def piq(k):
        r, fl = pi_mult(k, sy, rc)
        return r, fl | de
    if iszero(y):
        return piq(4) if sgn(x) else (zero(sy), de)
    if isinf(y):
        if isinf(x):
            return piq(3 if sgn(x) else 1)
        return piq(2)
    if iszero(x):
        return piq(2)
    if isinf(x):
        return piq(4) if sgn(x) else (zero(sy), de)
    q = abs(val(y)) / abs(val(x))
    def f(c):
        if q <= 1:
            a = atan_dec(dec(c, q), c)
        else:
            a = c.subtract(c.divide(pi_dec(c), 2), atan_dec(dec(c, 1 / q), c))
        if sgn(x):
            a = c.subtract(pi_dec(c), a)
        return -a if sy else a
    bounds = (q - q ** 3 / 3, q) if q <= 1 and not sgn(x) else None
    r, fl = evaluate(f, rc, bounds)
    return r, fl | de

def reduce_pi66(v):
    """|v| = k Pi/2 + r with the nearest integer k (no ties for 64-bit operands)."""
    a = abs(v)
    k = int(a / (PI66 / 2) + Fr(1, 2))
    return k, a - k * PI66 / 2

def trig(which, x, rc):
    """sin, cos or tan of a finite in-range operand."""
    if iszero(x):
        return (ONE if which == 'cos' else x), 0
    v = val(x)
    k, r = reduce_pi66(v)
    q = k % 4
    rho = abs(r)
    s = sgn(x)
    # sin(|v|) = sin(r + q pi/2) etc.; the exact value as a function of r, with |v|'s sign applied
    if which == 'sin':
        fn, neg = [('sin', 0), ('cos', 0), ('sin', 1), ('cos', 1)][q]
        neg ^= s
    elif which == 'cos':
        fn, neg = [('cos', 0), ('sin', 1), ('cos', 1), ('sin', 0)][q]
    else:
        fn, neg = [('tan', 0), ('cot', 1), ('tan', 0), ('cot', 1)][q]
        neg ^= s
    if fn in ('sin', 'tan', 'cot') and r < 0:
        neg ^= 1
    def f(c):
        rd = dec(c, rho)
        if fn == 'sin':
            out = sin_dec(rd, c)
        elif fn == 'cos':
            out = cos_dec(rd, c)
        elif fn == 'tan':
            out = c.divide(sin_dec(rd, c), cos_dec(rd, c))
        else:
            out = c.divide(cos_dec(rd, c), sin_dec(rd, c))
        return -out if neg else out
    bounds = {'sin': (rho - rho ** 3 / 6, rho), 'cos': (1 - rho ** 2 / 2, Fr(1)),
              'tan': (rho, rho + rho ** 3 / 2), 'cot': (1 / rho - rho / 2, 1 / rho)}[fn]
    r_, fl = evaluate(f, rc, bounds)
    return r_, fl | denf(x)

# ---------------------------------------------------------------- whole-instruction effect

def trig_special(x):
    if unsupported(x) or isinf(x):
        return INDEF, IE
    if isnan(x):
        return quiet(x), IE if issnan(x) else 0
    return None

def out_of_range(x):
    return finite(x) and abs(val(x)) >= 2 ** 63

def run(op, cw, a, b):
    """The test sequence FNINIT; FLDCW cw; FLD b; FLD a; op (masked exceptions): returns ST(0),
    ST(1) (None if empty) and the status word bits checked by t_x87t.c."""
    rc = (cw >> 10) & 3
    st = [a, b]          # st[0] = ST(0)
    fl, c2 = 0, None
    name = OPS[op]
    if name == 'f2xm1':
        st[0], fl = f2xm1(a, rc)
    elif name in ('fyl2x', 'fyl2xp1', 'fpatan'):
        r, fl = {'fyl2x': fyl2x, 'fyl2xp1': fyl2xp1, 'fpatan': fpatan}[name](a, b, rc)
        st = [r]
    else:
        c2 = 0
        sp = trig_special(a)
        if sp:
            v, fl = sp
            st = [v, v, b] if name in ('fptan', 'fsincos') else [v, b]
        elif out_of_range(a):
            c2 = C2
        elif name in ('fsin', 'fcos'):
            st[0], fl = trig(name[1:], a, rc)
        elif name == 'fptan':
            t, fl = trig('tan', a, rc)
            st = [ONE, t, b]
        else:
            s_, f1 = trig('sin', a, rc)
            c_, f2 = trig('cos', a, rc)
            st, fl = [c_, s_, b], f1 | f2
    top = (8 - len(st)) % 8
    sw = (fl & (0x3F | C1)) | (c2 or 0) | (top << 11)
    return st[0], (st[1] if len(st) > 1 else None), sw, c2 is not None

# ---------------------------------------------------------------- test-case generation

def f80(v, rc=0):
    return round80(Fr(v), rc)[0] if v != 0 else zero(0)

def neg_(x): return (x[0] ^ 0x8000, x[1])

def nextup(x, n=1):
    """Step the magnitude by n units in the last place (within normal/denormal encodings)."""
    m = x[1] + n
    e = ex(x)
    if m >= 1 << 64:
        m, e = m >> 1, e + 1
    if e > 0 and m < J:
        m, e = (m << 1) | 1, e - 1
    return (x[0] & 0x8000 | e, m & ((1 << 64) - 1))

def rand_class(rng, lo_e=16383 - 70, hi_e=16383 + 70):
    k = rng.randrange(12)
    s = rng.getrandbits(64)
    sg = rng.randrange(2) << 15
    if k == 0: return (sg, 0)
    if k == 1: return (sg, s >> rng.randrange(1, 64) or 1)
    if k == 2: return (sg, s | J)                                     # pseudo-denormal
    if k == 3: return (sg | 0x7FFF, J)
    if k == 4: return (sg | 0x7FFF, s | 3 << 62)                      # QNaN
    if k == 5: return (sg | 0x7FFF, (s & ~(3 << 62)) | J | 1)         # SNaN
    if k == 6: return (sg | rng.randrange(1, 0x7FFF), s & (J - 1))    # unnormal
    if k == 7: return (sg | rng.randrange(1, 0x7FFF), s | J)
    if k == 8: return (sg | rng.choice([1, 2, 0x7FFE, 0x7FFD]), s | J)
    return (sg | rng.randrange(lo_e, hi_e), s | J)

def gen_cases():
    rng = random.Random(87)
    cases = []
    def add(op, a, b=ONE, cw=None):
        if cw is None:
            cw = 0x7F | (rng.randrange(4) << 8) | (rng.randrange(4) << 10)
        cases.append((op, cw, a, b))
    def rnd_fin(lo_e, hi_e):
        return ((rng.randrange(2) << 15) | rng.randrange(lo_e, hi_e), rng.getrandbits(64) | J)
    one_m = (0x3FFE, (1 << 64) - 1)
    # F2XM1
    for a in [zero(0), zero(1), ONE, neg_(ONE), f80(Fr(1, 2)), f80(Fr(-1, 2)), (0, 1), (0x8000, 1),
              (0, J), one_m, neg_(one_m), nextup(ONE), (0x7FFF, J), (0xFFFF, J), (0x3FFF, J | 1)]:
        for rc in range(4):
            add(0, a, cw=0x37F | rc << 10)
    for _ in range(150):
        add(0, rnd_fin(16383 - 80, 16383))
    for _ in range(40):
        add(0, rand_class(rng))
    # FYL2X
    for _ in range(150):
        add(1, (rng.randrange(1, 0x7FFF), rng.getrandbits(64) | J), rnd_fin(16383 - 40, 16383 + 40))
    for k in (-16445, -16382, -1, 1, 63, 16383):
        add(1, f80(Fr(2) ** k), rnd_fin(16383 - 3, 16383 + 3))
    for n in (1, 2, 3, -1, -2):
        add(1, nextup(ONE, n) if n > 0 else nextup(one_m, n + 1), rnd_fin(16383 - 3, 16383 + 3))
    add(1, (0x7FFE, (1 << 64) - 1), (0x7FFE, (1 << 64) - 1))      # overflow
    add(1, (0x3FFF, J | 1), (0x0001, J))                            # underflow
    for _ in range(60):
        add(1, rand_class(rng), rand_class(rng))
    # FYL2XP1
    for _ in range(150):
        add(2, rnd_fin(16383 - 70, 16381), rnd_fin(16383 - 40, 16383 + 40))
    for x in [(0x3FFD, 0xD413CCCFE7799211), (0x3FFD, 0xD413CCCFE7799212), (0xBFFD, 0x95F619980C4336F7),
              (0xBFFD, 0x95F619980C4336F8), (0, 1), (0x8000, 5), (0x0001, J)]:
        add(2, x, rnd_fin(16383 - 3, 16383 + 3))
    for _ in range(60):
        add(2, rand_class(rng, 16383 - 70, 16382), rand_class(rng))
    # FPATAN
    for _ in range(150):
        add(3, rnd_fin(16383 - 30, 16383 + 30), rnd_fin(16383 - 30, 16383 + 30))
    for _ in range(40):
        e = rng.randrange(1, 0x7FFE)
        add(3, rnd_fin(e, e + 1), rnd_fin(max(1, e - 200), max(2, e - 64)))   # tiny ratio
    specials = [zero(0), zero(1), inf(0), inf(1), ONE, neg_(ONE), (0, 3), (0x8000, 3)]
    for x in specials:
        for y in specials:
            add(3, x, y)
    for _ in range(60):
        add(3, rand_class(rng), rand_class(rng))
    # FSIN, FCOS, FPTAN, FSINCOS
    trig_args = [zero(0), zero(1), (0, 1), (0x8000, J), (0x0001, J), f80(PI66 / 4), f80(PI66 / 4, 2),
                 f80(PI66 / 2), f80(PI66), f80(-PI66), f80(PI66 * 3 / 2), f80(2 * PI66),
                 (0x403D, (1 << 64) - 1), (0xC03D, (1 << 64) - 1), (0x403E, J), (0xC03E, J),
                 (0x7FFE, J), (0x7FFF, J), (0xFFFF, J), (0x7FFF, 0xC000000000000001),
                 (0x7FFF, J | 1), (0x4000, 0x4000000000000000), (0x3FBF, J)]
    for k in [1, 2, 3, 4, 5, 7, 100, 12345, 2 ** 20 + 1, 2 ** 40 - 3, 2 ** 61 + 7, 2 ** 62 + 1]:
        x = f80(k * PI66 / 2)
        trig_args += [x, nextup(x), nextup(x, -1) if x[1] > J else x]
    for _ in range(60):
        trig_args.append(rnd_fin(16383 - 80, 16383 + 63))
    for _ in range(15):
        trig_args.append(rand_class(rng))
    for op in (4, 5, 6, 7):
        for a in trig_args:
            add(op, a)
    return cases

def hx(x):
    return f'{{0x{x[1]:016x}ULL, 0x{x[0]:04x}}}'

def table(path):
    cases = gen_cases()
    lines = ['/* Generated by x87ref.py table (the exact reference); do not edit. */',
             f'#define X87T_N {len(cases)}', 'static const struct x87tcase x87t_cases[X87T_N] = {']
    for op, cw, a, b in cases:
        r1, r2, sw, trigop = run(op, cw, a, b)
        r2 = r2 if r2 is not None else INDEF       # FSTP of an empty ST(1) stores the indefinite
        lines.append(f'\t{{{op}, 0x{cw:04x}, 0x{sw:04x}, {hx(a)}, {hx(b)}, {hx(r1)}, {hx(r2)}}},')
    lines.append('};')
    open(path, 'w').write('\n'.join(lines) + '\n')
    print(f'{len(cases)} cases', file=sys.stderr)

# ---------------------------------------------------------------- QEMU transcript check

LINE = re.compile(r'^x87t (\d+) op=(\d+) cw=([0-9a-f]{8}) a ([0-9a-f]{8})_([0-9a-f]{16}) '
                  r'b ([0-9a-f]{8})_([0-9a-f]{16}) -> ([0-9a-f]{8})_([0-9a-f]{16}) sw=([0-9a-f]{8}) de=(\d)$')

def pf(se, sig):
    return (int(se, 16), int(sig, 16))

def fmt(i, op, cw, a, b, r, sw):
    return (f'x87t {i} op={op} cw={cw:08x} a {a[0]:08x}_{a[1]:016x} b {b[0]:08x}_{b[1]:016x} -> '
            f'{r[0]:08x}_{r[1]:016x} sw={sw & 0x3D:08x} de={(sw >> 1) & 1}')

def ulp_error(r, t):
    """|r - t| in units of the last place of t (finite nonzero)."""
    e = log2floor(abs(t))
    return float(abs(val(r) - t) / Fr(2) ** (max(e, -16382) - 63))

def exact_value(op, a, b):
    """A 200-digit approximation of the exact result (for error reports)."""
    c = ctx(200)
    va, vb = val(a), val(b)
    if op == 0:
        return Fr(expm1_dec(c.multiply(dec(c, va), c.ln(D(2))), c))
    if op == 1:
        return vb * Fr(c.divide(c.ln(dec(c, va)), c.ln(D(2))))
    if op == 2:
        return vb * Fr(c.divide(ln1p_dec(va, c), c.ln(D(2))))
    pi = pi_dec(c)
    q = abs(vb / va)
    t = atan_dec(dec(c, q), c) if q <= 1 else c.subtract(c.divide(pi, 2), atan_dec(dec(c, 1 / q), c))
    if va < 0:
        t = c.subtract(pi, t)
    return Fr(-t if vb < 0 else t)

def hw_rule(op, a, b):
    """The hardware-defined case (EPYC 7742, native campaign) a line falls under, if any."""
    if op == 0 and finite(a) and not iszero(a) and abs(val(a)) >= 1:
        return ('outside the documented domain (or at its ends): the EPYC 7742 returns x for |x| > 1 and '
                'reports PE for +-1 (native x87_transcendental); TCG raises an invalid operation or reports '
                'the exact value')
    if op == 0 and isinf(a):
        return 'F2XM1 of +-inf: the EPYC 7742 returns +inf / -1 without exceptions (native x87_transcendental); TCG raises an invalid operation'
    if op == 2 and ((isinf(a) and not sgn(a)) or (finite(a) and not iszero(a) and val(a) == -1 and (iszero(b) or isinf(b)))):
        return ('outside the documented domain: the EPYC 7742 returns +-inf by the sign of y for FYL2XP1(+inf, y) '
                'and y * log2(0) = -+0, -+inf for FYL2XP1(-1, +-0 or +-inf), without an exception (native '
                'x87_trans_special); TCG raises an invalid operation')
    if op == 2 and finite(a) and not iszero(a) and not (LNP1_LO <= val(a) <= LNP1_HI):
        return ('outside the documented domain: the EPYC 7742 computes y log2(1 + x) for x > -1 and returns x '
                'with PE for x <= -1 (native x87_transcendental); TCG raises an invalid operation')
    if op in (1, 2) and finite(a) and finite(b) and not iszero(a) and not iszero(b):
        v = val(a) + (1 if op == 2 else 0)
        if v > 0 and v == Fr(2) ** log2floor(v) and v != 1:
            return ('exact result reported inexact: the EPYC 7742 sets PE for every finite nonzero FYL2X/FYL2XP1 '
                    'result (native x87_transcendental); TCG does not')
    return None

def reason(op, cw, a, b, rq, swq, rr, swr):
    """Why the reference (the model's specification) differs from QEMU on this line."""
    hw = hw_rule(op, a, b)
    if hw:
        return hw
    if rq != rr:
        if finite(rq) and finite(rr) and not iszero(rq) and not iszero(rr) and sgn(rq) == sgn(rr):
            t = exact_value(op, a, b)
            if op == 1 and isden(b) and t != 0 and abs(val(rq) / t - 2) < Fr(1, 100):
                return ('denormal ST(1): TCG\'s FYL2X returns about twice the exact value (it scales a denormal '
                        'multiplier by 2); the model and this exact reference agree')
            err = ulp_error(rq, t)
            bound = 1.0 if (cw >> 10) & 3 == 0 else 1.5
            ok = 'within' if err < bound else 'OUTSIDE'
            return (f'QEMU result is not correctly rounded: error {err:.3f} ulp ({ok} the SDM bound of '
                    f'{bound} ulp, vol. 1 8.3.10); the model rounds correctly')
        if isnan(rq) and isnan(rr):
            return 'NaN operands: the result is the NaN with the larger significand (SDM vol. 1 4.8.3.5, table 4-7)'
        return 'result differs'
    d = (swq ^ swr) & 0x3F
    if d == DE and swr & DE:
        return ('denormal operand: #D is in the SDM exception list of F2XM1, FYL2X, FYL2XP1 and FPATAN; '
                'TCG does not report it for them')
    names = [n for bit, n in ((IE, 'IE'), (DE, 'DE'), (ZE, 'ZE'), (OE, 'OE'), (UE, 'UE'), (PE, 'PE')) if d & bit]
    return 'status differs: ' + ','.join(names)

HEADER = '''# Generated by `x87ref.py qemu out/qemu.txt > x87t-deviations.txt` (test/sys): one rule per x87t line
# (test_x87_trans in t_x87t.c) where QEMU's transcript differs from the exact reference x87ref.py, which
# implements the SDM-specified results independently of the model. Each rule replaces QEMU's line by the
# reference's; run.sh then requires the model to match. Regenerate after changing the test kernel's
# fuzzing (and check the stated reasons). Format as in qemu-deviations.txt.'''

def qemu(path):
    print(HEADER)
    n = dev = 0
    kinds = {}
    for line in open(path):
        line = line.rstrip('\r\n')
        m = LINE.match(line)
        if not m:
            continue
        n += 1
        i, op, cw = int(m[1]), int(m[2]), int(m[3], 16)
        a, b, rq = pf(m[4], m[5]), pf(m[6], m[7]), pf(m[8], m[9])
        swq = int(m[10], 16) | (int(m[11]) << 1)
        r1, _, sw, _ = run(op, cw, a, b)
        want = fmt(i, op, cw, a, b, r1, sw)
        if want == line:
            continue
        dev += 1
        why = reason(op, cw, a, b, rq, swq, r1, sw)
        key = why.split(':')[0]
        kinds[key] = kinds.get(key, 0) + 1
        print(f'^{re.escape(line)}$\t{want}\t# {OPS[op]}: {why}')
    print(f'{n} x87t lines, {dev} differ from the reference: {kinds}', file=sys.stderr)

def main():
    if sys.argv[1] == 'table':
        table(sys.argv[2])
    elif sys.argv[1] == 'qemu':
        qemu(sys.argv[2])
    else:
        op = OPS.index(sys.argv[2]) if sys.argv[2] in OPS else int(sys.argv[2])
        cw = int(sys.argv[3], 16)
        a = pf(*sys.argv[4].split('_'))
        b = pf(*sys.argv[5].split('_')) if len(sys.argv) > 5 else ONE
        r1, r2, sw, _ = run(op, cw, a, b)
        print(f'st0 {r1[0]:04x}_{r1[1]:016x}', f'st1 {r2[0]:04x}_{r2[1]:016x}' if r2 else '', f'sw {sw:04x}')

if __name__ == '__main__':
    main()
