#!/usr/bin/env python3
"""Independent reference for the AVX2, FMA3 and F16C instructions of the IA-32 model, written from
the manuals (AMD APM vol. 4 instruction pages; Intel SDM vol. 2 instruction pages and vol. 1, 14.4.1
(half precision) and 14.5 (FMA numeric behaviour, table 14-17); IEEE 754-2008 for the rounding), not
from the Lean code (x86_32/X86/Ext/Avx2.lean). Floating point is exact rational arithmetic
(fractions.Fraction) rounded once: the fused multiply-add rounds the exact x*y + z.

    python3 avx2_ref.py check test/sys/out/model.txt [model-only.expected ...]

recomputes every `avx2k`, `avx2m` and `avx2g` line of a system-test transcript (test/sys/t_avx2.c):
operands are the printed register/memory values (256-bit, high word first): d = YMM0 before (the
destination and first FMA operand, or the source of VCVTPS2PH/VEXTRACTI128/VPMASKMOV stores), a =
YMM1 (VEX.vvvv), b = YMM2 or m = the memory operand ([ESI], 32 bytes), c = YMM3 (is4), imm, mx =
MXCSR in; results r = YMM0 (YMM1 for VPSLLDQ, whose destination is VEX.vvvv), r2 = YMM2, mem = the 32
bytes at [ESI] afterwards, eax, mx = MXCSR out. `avx2g` lines are gathers: d = YMM0 (destination),
x = YMM1 (index), m = YMM2 (mask), memory = the gfill() pattern of the case number; results r = YMM0,
mo = YMM2. Exit status 1 on a mismatch.

Choices that the manuals leave open follow the model's documented choices (and QEMU): 0 * inf + QNaN
returns the QNaN without IE (SDM table 14-17); NaN operands are chosen in the order x, y, z of
x * y + z; masked-out VPMASKMOV elements are not accessed.
"""
import re
import sys
from fractions import Fraction

M32, M64, M128, M256 = (1 << 32) - 1, (1 << 64) - 1, (1 << 128) - 1, (1 << 256) - 1
IE, DE, ZE, OE, UE, PE = 1, 2, 4, 8, 16, 32


# ---------------------------------------------------------------- floating point

class Fmt:
    def __init__(self, w, e, p):
        self.w, self.e, self.p = w, e, p
        self.bias = (1 << (e - 1)) - 1
        self.emin, self.emax = 1 - self.bias, self.bias
        self.quiet = 1 << (p - 1)
        self.expmask = (1 << e) - 1
        self.sign = 1 << (w - 1)
        self.inf = self.expmask << p

    def indefinite(self):
        return self.sign | self.inf | self.quiet

    def isnan(self, b):
        return (b >> self.p) & self.expmask == self.expmask and b & ((1 << self.p) - 1) != 0

    def issnan(self, b):
        return self.isnan(b) and not b & self.quiet


F16, F32, F64 = Fmt(16, 5, 10), Fmt(32, 8, 23), Fmt(64, 11, 52)


def value(f, b, daz):
    """('nan',) / ('inf', s) / ('num', s, magnitude, denormal) of the encoding b."""
    s = b >> (f.w - 1) & 1
    ex, fr = (b >> f.p) & f.expmask, b & ((1 << f.p) - 1)
    if ex == f.expmask:
        return ('nan',) if fr else ('inf', s)
    if ex == 0:
        if fr == 0 or daz:
            return ('num', s, Fraction(0), False)
        return ('num', s, Fraction(fr, 1 << (f.p - f.emin)), True)
    return ('num', s, Fraction((1 << f.p) | fr) * Fraction(2) ** (ex - f.bias - f.p), False)


def round_int(x, neg, rc):
    q, r = divmod(x.numerator, x.denominator)
    if r == 0:
        return q
    half = Fraction(r, x.denominator)
    if rc == 0:
        return q + 1 if half > Fraction(1, 2) or (half == Fraction(1, 2) and q % 2) else q
    if rc == 1:
        return q + 1 if neg else q
    if rc == 2:
        return q if neg else q + 1
    return q


def encode(f, s, x, rc, ftz):
    """Round (-1)^s * x (x > 0) to the format, masked responses: overflow to infinity or the largest
    finite value by the rounding direction (OE, PE); tininess after rounding with unbounded exponent;
    with FTZ a tiny result is a zero (UE, PE), otherwise denormalized (UE and PE if inexact)."""
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fraction(2) ** e > x:
        e -= 1
    m = round_int(x / Fraction(2) ** (e - f.p), s, rc)
    if m == 1 << (f.p + 1):
        m, e = m // 2, e + 1
    sb = s << (f.w - 1)
    if e > f.emax:
        big = rc == 0 or (rc == 1 and s) or (rc == 2 and not s)
        return sb | (f.inf if big else f.inf - 1), OE | PE
    if e < f.emin:
        if ftz:
            return sb, UE | PE
        q = round_int(x / Fraction(2) ** (f.emin - f.p), s, rc)
        exact = Fraction(q) * Fraction(2) ** (f.emin - f.p) == x
        return sb | q, 0 if exact else UE | PE      # q = 2^p is the smallest normal: encoded alike
    exact = Fraction(m) * Fraction(2) ** (e - f.p) == x
    return sb | ((e + f.bias) << f.p) | (m - (1 << f.p)), 0 if exact else PE


def fma(f, x, y, z, negp, negz, mx):
    """(-1)^negp * x*y + (-1)^negz * z, one rounding (SDM vol. 1 14.5.2, table 14-17)."""
    daz, ftz, rc = bool(mx & 0x40), bool(mx & 0x8000), (mx >> 13) & 3
    if f.isnan(x) or f.isnan(y) or f.isnan(z):
        n = x if f.isnan(x) else y if f.isnan(y) else z
        return n | f.quiet, IE if any(f.issnan(v) for v in (x, y, z)) else 0
    cx, cy, cz = value(f, x, daz), value(f, y, daz), value(f, z, daz)
    if (cx[0] == 'inf' and cy[0] == 'num' and cy[2] == 0) or (cy[0] == 'inf' and cx[0] == 'num' and cx[2] == 0):
        return f.indefinite(), IE
    de = DE if any(c[0] == 'num' and c[3] for c in (cx, cy, cz)) else 0
    sp = cx[1] ^ cy[1] ^ negp
    sz = cz[1] ^ negz
    if cx[0] == 'inf' or cy[0] == 'inf':
        if cz[0] == 'inf' and cz[1] ^ negz != sp:
            return f.indefinite(), IE
        return (sp << (f.w - 1)) | f.inf, de
    if cz[0] == 'inf':
        return (sz << (f.w - 1)) | f.inf, de
    p = cx[2] * cy[2] * (-1 if sp else 1)
    q = cz[2] * (-1 if sz else 1)
    v = p + q
    if v == 0:
        s = 1 if (sp and sz) or (sp != sz and rc == 1) else 0
        return s << (f.w - 1), de
    r, fl = encode(f, 1 if v < 0 else 0, abs(v), rc, ftz)
    return r, fl | de


def half_to_single(h):
    """VCVTPH2PS lane: exact; DAZ ignored, no DE; SNaN -> quiet NaN and IE (AMD APM VCVTPH2PS)."""
    s = h >> 15
    if F16.isnan(h):
        return (s << 31) | F32.inf | F32.quiet | ((h & 0x3FF) << 13), IE if F16.issnan(h) else 0
    c = value(F16, h, False)
    if c[0] == 'inf':
        return (s << 31) | F32.inf, 0
    if c[2] == 0:
        return s << 31, 0
    r, _ = encode(F32, s, c[2], 0, False)
    return r, 0


def single_to_half(x, rc, mx):
    """VCVTPS2PH lane: rounding `rc`, FTZ ignored, DAZ honoured (DE otherwise for denormals)."""
    daz = bool(mx & 0x40)
    s = x >> 31
    if F32.isnan(x):
        return (s << 15) | F16.inf | F16.quiet | ((x & 0x7FFFFF) >> 13), IE if F32.issnan(x) else 0
    c = value(F32, x, daz)
    if c[0] == 'inf':
        return (s << 15) | F16.inf, 0
    de = DE if c[3] else 0
    if c[2] == 0:
        return s << 15, de
    r, fl = encode(F16, s, c[2], rc, False)
    return r, fl | de


# ---------------------------------------------------------------- integer helpers

def el(v, bits, k):
    return (v >> (bits * k)) & ((1 << bits) - 1)


def pack(vals, bits):
    return sum((x & ((1 << bits) - 1)) << (bits * k) for k, x in enumerate(vals))


def sx(x, bits):
    return x - (1 << bits) if x >> (bits - 1) & 1 else x


def lane(v, h):
    return (v >> (128 * h)) & M128


def per_lane(L, f):
    """Apply f(h) for each 128-bit lane h (one lane for VEX.128)."""
    return sum(f(h) << (128 * h) for h in range(2 if L else 1))


def sat(x, bits, signed):
    lo, hi = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)
    return min(max(x, lo), hi) & ((1 << bits) - 1)


FMA_FORM = {0x9: 0, 0xA: 1, 0xB: 2}   # opcode high nibble: 132, 213, 231


def fma_neg(kind, k):
    """(negate product, negate addend) for opcode low nibble `kind` and element k."""
    if kind == 6:
        return 0, int(k % 2 == 0)     # VFMADDSUB: subtract in even elements
    if kind == 7:
        return 0, int(k % 2 == 1)     # VFMSUBADD: subtract in odd elements
    return int(kind >= 0xC), int(kind in (0xA, 0xB, 0xE, 0xF))


FMA_OPS = {'vfmadd132p': 0x98, 'vfmadd213p': 0xA8, 'vfmadd231p': 0xB8, 'vfmsub132p': 0x9A,
           'vfnmadd213p': 0xAC, 'vfnmsub231p': 0xBE, 'vfmaddsub132p': 0x96, 'vfmsubadd213p': 0xA7,
           'vfmadd231s': 0xB9, 'vfmsub213s': 0xAB, 'vfnmadd132s': 0x9D, 'vfnmsub213s': 0xAF}


def fma_op(op, L, W, d, a, src, mx):
    f = F64 if W else F32
    bits = f.w
    form, kind = FMA_FORM[op >> 4], op & 0xF
    scalar = kind >= 8 and kind % 2 == 1
    n = 1 if scalar else (256 if L else 128) // bits
    out, flags = [], 0
    for k in range(n):
        o1, o2, o3 = el(d, bits, k), el(a, bits, k), el(src, bits, k)
        x, y, z = [(o1, o3, o2), (o2, o1, o3), (o2, o3, o1)][form]
        np_, nz = fma_neg(kind, k)
        r, fl = fma(f, x, y, z, np_, nz, mx)
        out.append(r)
        flags |= fl
    if scalar:
        res = (d & M128 & ~((1 << bits) - 1)) | out[0]
    else:
        res = pack(out, bits)
    return res, flags


def expected(name, L, W, imm, mx, d, a, src, c, mem_in):
    """(result kind, value, MXCSR flags) of one avx2k/avx2m line."""
    if name in FMA_OPS:
        r, fl = fma_op(FMA_OPS[name], L, W, d, a, src, mx)
        return 'r', r, fl
    if name == 'vcvtph2ps':
        n = 8 if L else 4
        rs = [half_to_single(el(src, 16, k)) for k in range(n)]
        return 'r', pack([x for x, _ in rs], 32), sum_flags(rs)
    if name == 'vcvtps2ph':
        n = 8 if L else 4
        rc = (mx >> 13) & 3 if imm & 4 else imm & 3
        rs = [single_to_half(el(d, 32, k), rc, mx) for k in range(n)]
        v = pack([x for x, _ in rs], 16)
        fl = sum_flags(rs)
        if mem_in is not None:
            nb = 16 * n
            return 'mem', (mem_in & ~((1 << nb) - 1)) | v, fl
        return 'r2', v, fl
    if name in ('vpermd', 'vpermps'):
        return 'r', pack([el(src, 32, el(a, 32, k) & 7) for k in range(8)], 32), 0
    if name in ('vpermq', 'vpermpd'):
        return 'r', pack([el(src, 64, (imm >> (2 * k)) & 3) for k in range(4)], 64), 0
    if name == 'vperm2i128':
        def pick(s):
            return 0 if s & 8 else [lane(a, 0), lane(a, 1), lane(src, 0), lane(src, 1)][s & 3]
        return 'r', pick(imm) | (pick(imm >> 4) << 128), 0
    if name == 'vpblendd':
        n = 8 if L else 4
        return 'r', pack([el(src, 32, k) if imm >> k & 1 else el(a, 32, k) for k in range(n)], 32), 0
    if name in ('vpsllv', 'vpsrlv', 'vpsravd'):
        bits = 64 if W and name != 'vpsravd' else 32
        n = (256 if L else 128) // bits
        out = []
        for k in range(n):
            x, cnt = el(a, bits, k), el(src, bits, k)
            if name == 'vpsllv':
                out.append(0 if cnt >= bits else x << cnt)
            elif name == 'vpsrlv':
                out.append(0 if cnt >= bits else x >> cnt)
            else:
                out.append(sx(x, bits) >> min(cnt, bits - 1))
        return 'r', pack(out, bits), 0
    if name == 'vpshufb':
        return 'r', per_lane(L, lambda h: pack([0 if el(lane(src, h), 8, k) & 0x80 else
                                                el(lane(a, h), 8, el(lane(src, h), 8, k) & 15) for k in range(16)], 8)), 0
    if name == 'vpalignr':
        return 'r', per_lane(L, lambda h: ((lane(a, h) << 128 | lane(src, h)) >> (8 * imm) if imm < 32 else 0) & M128), 0
    if name == 'vpblendw':
        return 'r', per_lane(L, lambda h: pack([el(lane(src, h), 16, k) if imm >> k & 1 else el(lane(a, h), 16, k)
                                                for k in range(8)], 16)), 0
    if name == 'vmpsadbw':
        def msad(h):
            ib = imm >> (3 * h)
            x, y = lane(a, h), lane(src, h)
            o1, o2 = 4 * (ib >> 2 & 1), 4 * (ib & 3)
            return pack([sum(abs(el(x, 8, o1 + i + j) - el(y, 8, o2 + j)) for j in range(4)) for i in range(8)], 16)
        return 'r', per_lane(L, msad), 0
    if name == 'vphaddw':
        def hadd(h):
            x, y = lane(a, h), lane(src, h)
            return pack([el(x, 16, 2 * i) + el(x, 16, 2 * i + 1) for i in range(4)] +
                        [el(y, 16, 2 * i) + el(y, 16, 2 * i + 1) for i in range(4)], 16)
        return 'r', per_lane(L, hadd), 0
    if name == 'vpacksswb':
        return 'r', per_lane(L, lambda h: pack([sat(sx(el(lane(a, h), 16, k), 16), 8, True) for k in range(8)] +
                                               [sat(sx(el(lane(src, h), 16, k), 16), 8, True) for k in range(8)], 8)), 0
    if name == 'vpunpcklbw':
        return 'r', per_lane(L, lambda h: pack([el(lane(a if k % 2 == 0 else src, h), 8, k // 2) for k in range(16)], 8)), 0
    if name in ('vpsllw', 'vpsrad'):
        cnt = src & M64      # one count in bits 63:0 of xmm/m128, for both lanes
        if name == 'vpsllw':
            return 'r', pack([0 if cnt > 15 else el(a, 16, k) << cnt for k in range(16 if L else 8)], 16), 0
        return 'r', pack([sx(el(a, 32, k), 32) >> min(cnt, 31) for k in range(8 if L else 4)], 32), 0
    if name == 'vpshufd':
        return 'r', per_lane(L, lambda h: pack([el(lane(src, h), 32, (imm >> (2 * k)) & 3) for k in range(4)], 32)), 0
    if name.startswith('vpbroadcast') or name in ('vbroadcastss', 'vbroadcastsd'):
        bits = {'vbroadcastss': 32, 'vbroadcastsd': 64}.get(name) or {'b': 8, 'w': 16, 'd': 32, 'q': 64}[name[-1]]
        return 'r', pack([el(src, bits, 0)] * ((256 if L else 128) // bits), bits), 0
    if name == 'vbroadcasti128':
        return 'r', (src & M128) * ((1 << 128) + 1), 0
    if name == 'vinserti128':
        return 'r', (a & ~(M128 << 128)) | ((src & M128) << 128) if imm & 1 else (a & ~M128) | (src & M128), 0
    if name == 'vextracti128':
        v = lane(d, imm & 1)
        if mem_in is not None:
            return 'mem', (mem_in & ~M128) | v, 0
        return 'r2', v, 0
    if name in ('vpmovsxbw', 'vpmovzxbd', 'vpmovsxdq'):
        fb, tb, signed = {'vpmovsxbw': (8, 16, 1), 'vpmovzxbd': (8, 32, 0), 'vpmovsxdq': (32, 64, 1)}[name]
        n = (256 if L else 128) // tb
        return 'r', pack([sx(el(src, fb, k), fb) if signed else el(src, fb, k) for k in range(n)], tb), 0
    if name == 'vpmaskmov_ld':
        bits = 64 if W else 32
        return 'r', pack([el(src, bits, k) if el(a, bits, k) >> (bits - 1) else 0
                          for k in range((256 if L else 128) // bits)], bits), 0
    if name == 'vpmaskmov_st':
        bits = 64 if W else 32
        out = [el(d, bits, k) if k < (256 if L else 128) // bits and el(a, bits, k) >> (bits - 1) else el(mem_in, bits, k)
               for k in range(256 // bits)]
        return 'mem', pack(out, bits), 0
    if name == 'vpblendvb':
        return 'r', pack([el(src, 8, k) if el(c, 8, k) >> 7 else el(a, 8, k) for k in range(32 if L else 16)], 8), 0
    if name == 'vpmovmskb':
        return 'eax', sum((el(src, 8, k) >> 7) << k for k in range(32)), 0
    if name == 'vpslldq':
        return 'r', per_lane(L, lambda h: (lane(src, h) << (8 * imm)) & M128 if imm < 16 else 0), 0
    raise KeyError(name)


def sum_flags(rs):
    fl = 0
    for _, f in rs:
        fl |= f
    return fl


def gmem(n):
    """The gfill() pattern of case n: word w = (w * 0x9E3779B1) ^ (n * 0x85EBCA6B), as bytes."""
    out = bytearray()
    for w in range(1024):
        out += (((w * 0x9E3779B1) ^ (n * 0x85EBCA6B)) & M32).to_bytes(4, 'little')
    return out


def gather(n, op, L, W, s, disp, d, x, m):
    """VPGATHER*/VGATHER* with base ESI = GM + 2048 (SDM VPGATHERDD/DQ/QD/QQ pseudocode; AMD APM
    VGATHERDPS): selected elements loaded, the others kept; bits above the gathered elements zero; mask
    zero."""
    mem = gmem(n)
    db = 64 if W else 32
    ib = 64 if op & 1 else 32
    cnt = (256 if L else 128) // max(db, ib)
    out = []
    for k in range(cnt):
        if el(m, db, k) >> (db - 1):
            addr = 2048 + disp + sx(el(x, ib, k), ib) * (1 << s)
            out.append(int.from_bytes(mem[addr:addr + db // 8], 'little'))
        else:
            out.append(el(d, db, k))
    return pack(out, db), 0


def parse(line):
    kv = dict(re.findall(r'(\w+)=([0-9a-f-]+)', line))
    return kv


def check_line(line):
    head = line.split()
    tag, n = head[0], int(head[1])
    pre, post = line.split(' -> ')
    pk, qk = parse(pre), parse(post)
    if qk['vec'] != '0000ffff':
        return None if tag != 'avx2g' else 'fault %s' % qk['vec']
    h = lambda k: int(pk[k], 16)
    if tag == 'avx2g':
        r, _ = gather(n, int(pk['op'], 16), int(pk['l']), int(pk['w']), int(pk['s']), sx(int(pk['disp']) & M32, 32), h('d'), h('x'), h('m'))
        got_r, got_m = int(qk['r'], 16), int(qk['mo'], 16)
        if got_r != r or got_m != 0:
            return 'expected r=%064x mo=0' % r
        return None
    name = head[2]
    L, W = int(pk['l']), int(pk['w'])
    mx = h('mx')
    imm = h('imm') if 'imm' in pk else 0
    src = h('m') if 'm' in pk else h('b')
    mem_in = h('m') if 'm' in pk else None
    kind, v, fl = expected(name, L, W, imm, mx, h('d'), h('a') if 'a' in pk else 0, src,
                           h('c') if 'c' in pk else 0, mem_in)
    got = int(qk[kind], 16)
    if got != v:
        return 'expected %s=%x' % (kind, v)
    want_mx = mx | fl
    if int(qk['mx'], 16) != want_mx:
        return 'expected mx=%x' % want_mx
    return None


def check(paths):
    bad = n = skipped = 0
    for path in paths:
        with open(path, errors='replace') as fh:
            lines = fh.read().splitlines()
        for line in lines:
            line = line.strip()
            if not re.match(r'^avx2[kmg] \d+ ', line):
                continue
            n += 1
            try:
                err = check_line(line)
            except (KeyError, ValueError) as e:
                err = 'unparsed (%r)' % e
            if err:
                bad += 1
                if bad <= 20:
                    print('MISMATCH %s\n   %s' % (line[:200], err))
    print('avx2_ref: %d lines checked, %d mismatches' % (n, bad))
    return bad == 0


if __name__ == '__main__':
    if len(sys.argv) >= 3 and sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2:]) else 1)
    print(__doc__)
    sys.exit(2)
