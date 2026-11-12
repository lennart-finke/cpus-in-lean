#!/usr/bin/env python3
"""Independent reference for the AVX-only data-movement instructions and the 32 VCMP predicates,
written from the Intel SDM vol. 2 instruction pages (VPERMILPS, VPERMILPD, VPERM2F128, VSHUFPS,
VSHUFPD, VUNPCKLPS, VUNPCKHPD, VBROADCASTSS/SD/F128, VINSERTF128, VEXTRACTF128, VMASKMOVPS/PD,
VBLENDPS/PD, VBLENDVPS/PD, VTESTPS/PD, VPTEST, VMOVDDUP, VMOVSLDUP, VMOVSHDUP, CMPPS/CMPPD/CMPSS/CMPSD
with table 3-1 of the predicates) and AMD APM vol. 4, not from the Lean model.

    python3 avx_ref.py check test/sys/out/model.txt

recomputes every `avxk` line of a system-test transcript (test/sys/t_avx.c): the operands are the
printed register/memory values (256-bit, high word first): d = YMM0 before (destination, or the source
of the stores), a = YMM1 (VEX.vvvv), b = YMM2 or m = the memory operand ([ESI], 32 bytes), c = YMM3
(the is4 operand), imm; the results r = YMM0, r2 = YMM2, mem = the 32 bytes at [ESI] afterwards, fl =
EFLAGS & 0x8D5, mx = MXCSR (all exceptions masked; its DAZ bit is the input's).
"""
import math
import struct
import sys

M32, M64, M128 = (1 << 32) - 1, (1 << 64) - 1, (1 << 128) - 1
IE, DE = 1, 2


def el(v, bits, k):
    return (v >> (bits * k)) & ((1 << bits) - 1)


def pack(vals, bits):
    out = 0
    for k, x in enumerate(vals):
        out |= (x & ((1 << bits) - 1)) << (bits * k)
    return out


def half(v, h):
    return (v >> (128 * h)) & M128


def halves(lo, hi):
    return lo | (hi << 128)


def lanes(L, f):
    """Apply f(h) to the halves of a VEX.128 (L = 0: upper half zero) or VEX.256 result."""
    return halves(f(0), f(1) if L else 0)


# ---- permutes, shuffles, broadcasts ----

def permilps_i(L, imm, src):
    return lanes(L, lambda h: pack([el(half(src, h), 32, (imm >> (2 * j)) & 3) for j in range(4)], 32))


def permilpd_i(L, imm, src):
    return lanes(L, lambda h: pack([el(half(src, h), 64, (imm >> (2 * h + j)) & 1) for j in range(2)], 64))


def permilps_v(L, a, ctrl):
    return lanes(L, lambda h: pack([el(half(a, h), 32, el(half(ctrl, h), 32, j) & 3) for j in range(4)], 32))


def permilpd_v(L, a, ctrl):
    return lanes(L, lambda h: pack([el(half(a, h), 64, (el(half(ctrl, h), 64, j) >> 1) & 1) for j in range(2)], 64))


def perm2f128(imm, a, b):
    def sel(s):
        if s & 8:
            return 0
        return [half(a, 0), half(a, 1), half(b, 0), half(b, 1)][s & 3]
    return halves(sel(imm & 15), sel(imm >> 4))


def shufps(L, imm, a, b):
    def f(h):
        x, y = half(a, h), half(b, h)
        return pack([el(x, 32, imm & 3), el(x, 32, (imm >> 2) & 3), el(y, 32, (imm >> 4) & 3),
                     el(y, 32, (imm >> 6) & 3)], 32)
    return lanes(L, f)


def shufpd(L, imm, a, b):
    return lanes(L, lambda h: pack([el(half(a, h), 64, (imm >> (2 * h)) & 1),
                                    el(half(b, h), 64, (imm >> (2 * h + 1)) & 1)], 64))


def unpcklps(L, a, b):
    return lanes(L, lambda h: pack([el(half(a, h), 32, 0), el(half(b, h), 32, 0), el(half(a, h), 32, 1),
                                    el(half(b, h), 32, 1)], 32))


def unpckhpd(L, a, b):
    return lanes(L, lambda h: pack([el(half(a, h), 64, 1), el(half(b, h), 64, 1)], 64))


def broadcast(L, bits, x):
    n = (256 if L else 128) // bits
    return pack([x] * n, bits)


def blend(L, bits, imm, a, b):
    n = (256 if L else 128) // bits
    return pack([el(b if (imm >> k) & 1 else a, bits, k) for k in range(n)], bits)


def blendv(L, bits, a, b, c):
    n = (256 if L else 128) // bits
    return pack([el(b if el(c, bits, k) >> (bits - 1) else a, bits, k) for k in range(n)], bits)


def test_flags(L, bits, a, b):
    """(ZF, CF) of VTESTPS (bits 32), VTESTPD (64) and VPTEST (1)."""
    width = 256 if L else 128
    if bits == 1:
        m = (1 << width) - 1
    else:
        m = sum(1 << (bits * k + bits - 1) for k in range(width // bits))
    return (a & b & m) == 0, (~a & b & m) == 0


def movddup(L, s):
    return lanes(L, lambda h: pack([el(half(s, h), 64, 0)] * 2, 64))


def movsldup(L, s, odd):
    return lanes(L, lambda h: pack([el(half(s, h), 32, 2 * (j // 2) + odd) for j in range(4)], 32))


def maskload(L, bits, mask, m):
    n = (256 if L else 128) // bits
    return pack([el(m, bits, k) if el(mask, bits, k) >> (bits - 1) else 0 for k in range(n)], bits)


def maskstore(L, bits, mask, data, old):
    n = (256 if L else 128) // bits
    vals = [el(data, bits, k) if el(mask, bits, k) >> (bits - 1) else el(old, bits, k) for k in range(n)]
    return pack(vals, bits) | (old & ~((1 << (n * bits)) - 1) & ((1 << 256) - 1))


# ---- compares (SDM vol. 2 CMPPS table 3-1) ----

def decode(bits, x, daz):
    """(value as a Python float or 'nan', is a signaling NaN, is a denormal before DAZ)."""
    eb, fb = (8, 23) if bits == 32 else (11, 52)
    e = (x >> fb) & ((1 << eb) - 1)
    f = x & ((1 << fb) - 1)
    s = x >> (bits - 1)
    if e == (1 << eb) - 1:
        if f:
            return 'nan', not (f >> (fb - 1)) & 1, False
        return -math.inf if s else math.inf, False, False
    if e == 0 and f and daz:
        return (-0.0 if s else 0.0), False, True
    fmt = '<I' if bits == 32 else '<Q'
    v = struct.unpack('<f' if bits == 32 else '<d', struct.pack(fmt, x))[0]
    return v, False, e == 0 and f != 0


def compare(bits, pred, x, y, daz):
    """(all-ones or 0, MXCSR flags) of one element."""
    a, sa, da = decode(bits, x, daz)
    b, sb, db = decode(bits, y, daz)
    unord = a == 'nan' or b == 'nan'
    p = pred & 31
    lt = not unord and a < b
    eq = not unord and a == b
    gt = not unord and a > b
    rel = {0: eq, 1: lt, 2: lt or eq, 3: unord, 4: not eq, 5: not lt, 6: not (lt or eq), 7: not unord,
           8: unord or eq, 9: unord or lt, 10: unord or lt or eq, 11: False, 12: not unord and not eq,
           13: gt or eq, 14: gt, 15: True}[p & 15]
    # signaling predicates (_S): a QNaN operand also raises IE
    signaling = (p & 15) in (1, 2, 5, 6, 9, 10, 13, 14)
    if p >= 16:
        signaling = not signaling
    if sa or sb or (signaling and unord):
        fl = IE
    elif unord:
        fl = 0
    else:
        fl = DE if ((da or db) and not daz) else 0
    return ((1 << bits) - 1 if rel else 0), fl


def cmp_packed(L, bits, pred, a, b, daz):
    n = (256 if L else 128) // bits
    out, fl = [], 0
    for k in range(n):
        v, f = compare(bits, pred, el(a, bits, k), el(b, bits, k), daz)
        out.append(v)
        fl |= f
    return pack(out, bits), fl


def cmp_scalar(bits, pred, a, b, daz):
    v, fl = compare(bits, pred, el(a, bits, 0), el(b, bits, 0), daz)
    low = a & M128 & ~((1 << bits) - 1) | v
    return low, fl


# ---- DPPS (VEX.256) and horizontal adds, with sse_ref's exact binary32/binary64 arithmetic ----

def vdpps(L, a, b, imm, mx):
    """VDPPS (SDM DPPS "DP_primitive" per 128-bit lane; "Exceptions are determined separately for each
    add and multiply operation, in the order of their execution. Unmasked exceptions will leave the
    destination operands unchanged"). The three stages are the multiplies, the two first additions and
    the last addition; for VEX.256 a stage comprises the operations of that kind in both lanes. Within a
    stage, an unmasked IE/DE/ZE suppresses OE/UE/PE (the SSE rule for one operation over all elements);
    a stage with an unmasked exception ends the instruction (#XM). Returns (result, mxcsr after,
    faulted)."""
    import sse_ref as S
    f = S.Fmt(32)
    stage = [0, 0, 0]
    res = []
    for h in range(2 if L else 1):
        A, B = S.lanes(half(a, h), 32), S.lanes(half(b, h), 32)
        p = []
        for k in range(4):
            if imm >> (4 + k) & 1:
                v, fl = S.arith(f, 'mul', A[k], B[k], mx)
                stage[0] |= fl
            else:
                v = 0
            p.append(v)
        s1, f1 = S.arith(f, 'add', p[0], p[1], mx)
        s2, f2 = S.arith(f, 'add', p[2], p[3], mx)
        t, f3 = S.arith(f, 'add', s1, s2, mx)
        stage[1] |= f1 | f2
        stage[2] |= f3
        res.append(S.join([t if imm >> k & 1 else 0 for k in range(4)], 32))
    out = mx
    for fl in stage:
        unmasked = fl & ~(mx >> 7) & 0x3F
        out |= (fl & 7) if unmasked & 7 else fl
        if unmasked:
            return None, out, True
    return halves(res[0], res[1] if L else 0), out, False


def vhop(L, width, sub, a, b, mx):
    """VHADDPx/VHSUBPx: sse_ref.hop on each 128-bit lane (SDM: the VEX.256 form repeats the 128-bit
    operation on bits 255:128). Returns (result, flags)."""
    import sse_ref as S
    lo, f0 = S.hop(width, sub, half(a, 0), half(b, 0), mx)
    if not L:
        return lo, f0
    hi, f1 = S.hop(width, sub, half(a, 1), half(b, 1), mx)
    return halves(lo, hi), f0 | f1


def check_avxm(line):
    """The model-only lines avxm.dpps256 and avxm.hnan256/hnan256pd (t_avx.c); None for other lines."""
    t = line.split()
    if not t or t[0] not in ('avxm.dpps256:', 'avxm.hnan256:', 'avxm.hnan256pd:'):
        return None
    if t[0] == 'avxm.dpps256:':
        kv = dict(x.split('=', 1) for x in t[1:] if '=' in x)
        r, mxo, xm = vdpps(1, int(kv['a'], 16), int(kv['b'], 16), int(kv['imm'], 16), int(kv['mx'], 16))
        bad = []
        if (0x13 if xm else 0xFFFF) != int(kv['vec'], 16):
            bad.append(('vec', 0x13 if xm else 0xFFFF, int(kv['vec'], 16)))
        if mxo != int(kv['mxo'], 16):
            bad.append(('mxcsr', mxo, int(kv['mxo'], 16)))
        if xm and kv['unchanged'] != '1':
            bad.append(('unchanged', 1, int(kv['unchanged'])))
        return bad
    mx, a, b = (int(t[k].split('=')[1], 16) for k in (1, 2, 3))
    bad, k = [], 4
    while k + 2 < len(t):
        name, vec = t[k].split('=')
        r, mxo = int(t[k + 1].split('=')[1], 16), int(t[k + 2].split('=')[1], 16)
        er, fl = vhop(1, 32 if name.endswith('ps') else 64, 'hsub' in name, a, b, mx)
        if int(vec, 16) != 0xFFFF:
            bad.append((name + ' vec', 0xFFFF, int(vec, 16)))
        if er != r:
            bad.append((name, er, r))
        if mx | fl != mxo:
            bad.append((name + ' mxcsr', mx | fl, mxo))
        k += 3
    return bad


# ---- transcript lines ----

def expected(name, L, imm, d, a, src, c, mx_in):
    """The expected outcome: dict with 'r', 'r2', 'mem', 'fl', 'mx' (those that apply)."""
    if name == 'permilps_i':
        return {'r': permilps_i(L, imm, src)}
    if name == 'permilpd_i':
        return {'r': permilpd_i(L, imm, src)}
    if name == 'permilps_v':
        return {'r': permilps_v(L, a, src)}
    if name == 'permilpd_v':
        return {'r': permilpd_v(L, a, src)}
    if name == 'perm2f128':
        return {'r': perm2f128(imm, a, src)}
    if name == 'shufps':
        return {'r': shufps(L, imm, a, src)}
    if name == 'shufpd':
        return {'r': shufpd(L, imm, a, src)}
    if name == 'unpcklps':
        return {'r': unpcklps(L, a, src)}
    if name == 'unpckhpd':
        return {'r': unpckhpd(L, a, src)}
    if name == 'broadcastss':
        return {'r': broadcast(L, 32, el(src, 32, 0))}
    if name == 'broadcastsd':
        return {'r': broadcast(L, 64, el(src, 64, 0))}
    if name == 'broadcastf128':
        return {'r': halves(src & M128, src & M128)}
    if name == 'insertf128':
        return {'r': halves(src & M128, half(a, 1)) if imm & 1 == 0 else halves(half(a, 0), src & M128)}
    if name == 'extractf128':
        return {'mem': (src & ~M128) | half(d, imm & 1), 'r2': half(d, imm & 1)}
    if name == 'maskmovps_ld':
        return {'r': maskload(L, 32, a, src)}
    if name == 'maskmovpd_ld':
        return {'r': maskload(L, 64, a, src)}
    if name == 'maskmovps_st':
        return {'mem': maskstore(L, 32, a, d, src)}
    if name == 'maskmovpd_st':
        return {'mem': maskstore(L, 64, a, d, src)}
    if name == 'blendps':
        return {'r': blend(L, 32, imm, a, src)}
    if name == 'blendpd':
        return {'r': blend(L, 64, imm, a, src)}
    if name == 'blendvps':
        return {'r': blendv(L, 32, a, src, c)}
    if name == 'blendvpd':
        return {'r': blendv(L, 64, a, src, c)}
    if name in ('testps', 'testpd', 'ptest'):
        zf, cf = test_flags(L, {'testps': 32, 'testpd': 64, 'ptest': 1}[name], d, src)
        return {'r': d, 'fl': (0x40 if zf else 0) | (1 if cf else 0)}
    if name == 'movddup':
        return {'r': movddup(L, src)}
    if name == 'movsldup':
        return {'r': movsldup(L, src, 0)}
    if name == 'movshdup':
        return {'r': movsldup(L, src, 1)}
    daz = mx_in & 0x40 != 0
    if name in ('cmpps', 'cmppd'):
        r, fl = cmp_packed(L, 32 if name == 'cmpps' else 64, imm, a, src, daz)
        return {'r': r, 'mx': mx_in | fl}
    if name in ('cmpss', 'cmpsd'):
        r, fl = cmp_scalar(32 if name == 'cmpss' else 64, imm, a, src, daz)
        return {'r': r, 'mx': mx_in | fl}
    return None


def parse(line):
    t = line.split()
    if len(t) < 4 or t[0] != 'avxk':
        return None
    kv = {}
    for x in t[3:]:
        if '=' in x:
            k, v = x.split('=', 1)
            kv[k] = int(v, 16)
    return t[2], kv


def check_line(line):
    """None if not an avxk line; else a list of (what, expected, got) mismatches."""
    p = parse(line)
    if p is None:
        return None
    name, kv = p
    if kv.get('vec', 0xFFFF) != 0xFFFF:
        return [('vec', 0xFFFF, kv['vec'])]
    L = kv['l']
    src = kv['m'] if 'm' in kv else kv['b']
    mx_in = kv.get('mx', 0x1F80) & ~0x3F
    e = expected(name, L, kv.get('imm', 0), kv['d'], kv.get('a', 0), src, kv.get('c', 0), mx_in)
    if e is None:
        return [('unknown operation ' + name, 0, 0)]
    if name.startswith('cmp'):
        e.setdefault('fl', 0)
    else:
        e.setdefault('mx', mx_in)
        e.setdefault('fl', 0)
    bad = []
    for what in ('r', 'r2', 'mem', 'fl', 'mx'):
        if what in e and what in kv and e[what] != kv[what]:
            bad.append((what, e[what], kv[what]))
    return bad


def check(path):
    n = bad = 0
    with open(path, errors='replace') as fh:
        for line in fh:
            r = check_line(line.strip())
            if r is None:
                r = check_avxm(line.strip())
            if r is None:
                continue
            n += 1
            if r:
                bad += 1
                if bad <= 20:
                    print('MISMATCH', line.strip()[:160])
                    for what, exp, got in r:
                        print('   %s: reference %x, transcript %x' % (what, exp, got))
    print('avx_ref: %d lines checked, %d mismatches' % (n, bad))
    return bad == 0 and n > 0


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2]) else 1)
    print(__doc__)
    sys.exit(2)
