"""Native families that deepen the floating-point coverage where the first EPYC 7742 run was thin
(bundle format v3; FP-HARDWARE.md, "The extended bundle"). Inputs only; the cases run through
native_ext.select like the other extended families (safety, observability).

* `fma_random`: every FMA3 form (VFMADD/VFMSUB/VFNMADD/VFNMSUB/VFMADDSUB/VFMSUBADD 132/213/231, PS/PD/
  SS/SD, VEX.128/256, register and memory operands) with random lanes from operand classes (zeros,
  normals, denormals, infinities, NaNs with distinct payloads in every position, values near the overflow
  and underflow thresholds, exact and near cancellation z = -(x*y)), every rounding mode, DAZ/FTZ, and a
  sixth of the cases with unmasked exceptions;
* `f16c_exhaustive`: VCVTPH2PS of every one of the 65,536 binary16 values (eight per VEX.256 instruction),
  part of them again as a memory operand with random MXCSR (unmasked IE/DE included), and VCVTPS2PH of
  boundary and random singles under every imm8 rounding control (imm8[2] = 1: MXCSR.RC), every MXCSR
  rounding mode, register and memory destinations, unmasked exceptions (a memory destination must stay
  unchanged on #XM);
* `avx_unmasked`: the AVX/AVX2/FMA floating-point instructions with one or all exceptions unmasked and
  lanes built to raise a given exception in a given lane (the #XM, the destination preserved, MXCSR's
  flags, the priority among lanes and exception kinds);
* `sse_unmasked_ext`: the same for the SSE3 and SSE4.1 floating-point instructions (ADDSUBPS/PD, HADD/
  HSUB, ROUNDPS/PD/SS/SD, DPPS/DPPD). With CR4.OSXMMEXCPT = 0 an unmasked exception is #UD; Linux
  always sets OSXMMEXCPT, so that rule cannot be observed natively (the KVM tests own it);
* `avx_random`: random operands for every AVX/AVX2 form (gen_avx/gen_avx2 SPECS: floating point and
  integer), memory operands at random offsets including across the arena's page boundary, with
  read-only and unmapped second pages (stores, masked moves) and gathers whose elements fault midway.
"""
import random
import struct

import gen_avx
import gen_avx2
from native_avx import vex, regs256, fp_choices
from native_cases import constants
from native_ext import record3, meta3
from native_int import selected

M64 = (1 << 64) - 1


def lane(rng, bits, payloads):
    """A random operand of one lane: a class, then a value of it."""
    c = constants(bits)
    f = 23 if bits == 32 else 52
    e = 8 if bits == 32 else 11
    bias = (1 << (e - 1)) - 1
    sign = rng.getrandbits(1) << (bits - 1)
    k = rng.randrange(12)
    if k == 0: return sign
    if k == 1: return sign | rng.randrange(1, 1 << f)                                   # denormal
    if k == 2: return sign | c['infinity']
    if k == 3:                                                                          # NaN with a distinct payload
        payloads[0] += 1
        q = rng.getrandbits(1) << (f - 1)
        return sign | c['infinity'] | q | (payloads[0] & ((1 << (f - 1)) - 1)) or 1
    if k == 4: return sign | ((2 * bias - rng.randrange(3)) << f) | rng.getrandbits(f)  # near overflow
    if k == 5: return sign | ((1 + rng.randrange(3)) << f) | rng.getrandbits(f)        # near underflow
    if k == 6: return sign | (bias << f) | rng.getrandbits(4)                           # near 1
    return sign | (rng.randrange(bias - 40, bias + 40) << f) | rng.getrandbits(f)


def as_float(v, bits):
    return struct.unpack('<f' if bits == 32 else '<d', v.to_bytes(bits // 8, 'little'))[0]


def from_float(x, bits):
    try:
        return int.from_bytes(struct.pack('<f' if bits == 32 else '<d', x), 'little')
    except OverflowError:
        return 0


def vec(rng, bits, n, payloads):
    return [lane(rng, bits, payloads) for _ in range(n)]


def pack(lanes, bits):
    return sum((v & ((1 << bits) - 1)) << (bits * k) for k, v in enumerate(lanes))


def mxcsr_of(rng, unmasked=False):
    masks = 0x3F if not unmasked else rng.choice([0x3E, 0x3D, 0x3B, 0x37, 0x2F, 0x1F, 0, 0x3F ^ (1 << rng.randrange(6))])
    return masks << 7 | rng.randrange(4) << 13 | rng.choice((0, 0x40, 0x8000, 0x8040))


FMA_OPS = list(range(0x96, 0xA0)) + list(range(0xA6, 0xB0)) + list(range(0xB6, 0xC0))
FMA_NAMES = {0x6: 'fmaddsub', 0x7: 'fmsubadd', 0x8: 'fmadd_p', 0x9: 'fmadd_s', 0xA: 'fmsub_p', 0xB: 'fmsub_s',
             0xC: 'fnmadd_p', 0xD: 'fnmadd_s', 0xE: 'fnmsub_p', 0xF: 'fnmsub_s'}


def fma_random(rng, count):
    n = max(200, count * 2)
    for i in range(n):
        op = rng.choice(FMA_OPS)
        W = rng.getrandbits(1)
        bits = 64 if W else 32
        scalar = op & 1 and op & 0xF >= 9
        L = rng.getrandbits(1)
        lanes = 256 // bits
        p = [rng.getrandbits(20)]
        x, y, z = vec(rng, bits, lanes, p), vec(rng, bits, lanes, p), vec(rng, bits, lanes, p)
        if rng.random() < 0.25:   # (near) cancellation: z = -(x*y), rounded in the element format
            for k in range(lanes):
                prod = as_float(x[k], bits) * as_float(y[k], bits)
                z[k] = from_float(-prod, bits) ^ (rng.getrandbits(1) if rng.random() < 0.5 else 0)
        mem = rng.random() < 0.3
        unm = rng.random() < 1 / 6
        # dest/op1 = YMM0 (x), op2 = vvvv = YMM1 (y), op3 = r/m = YMM2 or [EBX] (z)
        code = vex(2, 1, L, W, 1) + bytes([op, 0x03 if mem else 0xC2])
        xmm, ymmh = regs256([pack(x, bits), pack(y, bits), pack(z, bits), 0])
        memb = pack(z, bits).to_bytes(32, 'little') + bytes(rng.getrandbits(8) for _ in range(32))
        yield record3(code, xmm=xmm, ymmh=ymmh, mem=memb, mxcsr=mxcsr_of(rng, unm)), \
            meta3('fma_random', f'{op:02x}.w{W}', code, L=L, unmasked=unm)


def f16c_exhaustive(rng, count):
    total = 65536 if count >= 10000 else 1024
    vals = list(range(total))
    for k in range(0, total, 8):
        hv = pack(vals[k:k + 8], 16)
        xmm, ymmh = regs256([0, 0, hv, 0])
        code = vex(2, 1, 1, 0, 0) + bytes([0x13, 0xC2])   # VCVTPH2PS ymm0, xmm2
        yield record3(code, xmm=xmm, ymmh=ymmh, mxcsr=0x1F80), meta3('f16c_exhaustive', 'vcvtph2ps_all', code, first=k)
    for k in range(0, total, 32):   # memory operand, random MXCSR (DAZ ignored by the conversion; IE/DE unmasked)
        hv = pack([rng.randrange(65536) for _ in range(4)], 16)
        code = vex(2, 1, 0, 0, 0) + bytes([0x13, 0x03])
        yield record3(code, mem=hv.to_bytes(8, 'little'), mxcsr=mxcsr_of(rng, rng.random() < 0.5)), \
            meta3('f16c_exhaustive', 'vcvtph2ps_mem', code)
    singles = [0, 0x80000000, 0x3F800000, 0x477FE000, 0x477FEFFF, 0x477FF000, 0x477FF001, 0x47800000, 0x7F7FFFFF,
               0x7F800000, 0xFF800000, 0x7FC00001, 0x7FA00001, 0xFFBFFFFF, 0x38800000, 0x387FFFFF, 0x387FC000,
               0x38000000, 0x33800000, 0x33800001, 0x337FFFFF, 0x33000000, 0x00000001, 0x00800000, 0x3EAAAAAB,
               0xBF7FFFFF, 0x3F801000, 0x3F802000, 0x3F803000]
    reps = 2 if count >= 10000 else 1
    for imm in range(8):
        for rc in range(4):
            for L in (0, 1):
                for dest in ('reg', 'mem'):
                    for r in range(reps * 8):
                        lanes = [rng.choice(singles) if rng.random() < 0.6 else rng.getrandbits(32) for _ in range(8)]
                        xmm, ymmh = regs256([pack(lanes, 32), 0, 0, 0])
                        modrm = 0x03 if dest == 'mem' else 0xC2
                        code = vex(3, 1, L, 0, 0) + bytes([0x1D, modrm, imm | (rng.getrandbits(5) << 3 if r % 4 == 3 else 0)])
                        mx = mxcsr_of(rng, r % 3 == 2) & ~0x6000 | rc << 13
                        yield record3(code, xmm=xmm, ymmh=ymmh, mxcsr=mx, mem=bytes(rng.getrandbits(8) for _ in range(64))), \
                            meta3('f16c_exhaustive', f'vcvtps2ph_{dest}', code, imm=imm, rc=rc, L=L)


# AVX/AVX2/FMA floating-point forms for the unmasked-exception family: (name, map, pp, op, vvvv used,
# element bits, imm8 or None, packed)
AVX_FP = [('vaddps', 1, 0, 0x58, 1, 32, None, 1), ('vaddpd', 1, 1, 0x58, 1, 64, None, 1), ('vaddss', 1, 2, 0x58, 1, 32, None, 0),
          ('vaddsd', 1, 3, 0x58, 1, 64, None, 0), ('vmulps', 1, 0, 0x59, 1, 32, None, 1), ('vmulsd', 1, 3, 0x59, 1, 64, None, 0),
          ('vsubpd', 1, 1, 0x5C, 1, 64, None, 1), ('vdivps', 1, 0, 0x5E, 1, 32, None, 1), ('vdivsd', 1, 3, 0x5E, 1, 64, None, 0),
          ('vsqrtps', 1, 0, 0x51, 0, 32, None, 1), ('vsqrtsd', 1, 3, 0x51, 1, 64, None, 0), ('vminps', 1, 0, 0x5D, 1, 32, None, 1),
          ('vmaxpd', 1, 1, 0x5F, 1, 64, None, 1), ('vcmpps', 1, 0, 0xC2, 1, 32, 0x11, 1), ('vcmpsd', 1, 3, 0xC2, 1, 64, 0x04, 0),
          ('vcvtps2pd', 1, 0, 0x5A, 0, 32, None, 1), ('vcvtpd2ps', 1, 1, 0x5A, 0, 64, None, 1), ('vcvtdq2ps', 1, 0, 0x5B, 0, 32, None, 1),
          ('vcvtps2dq', 1, 1, 0x5B, 0, 32, None, 1), ('vcvttpd2dq', 1, 1, 0xE6, 0, 64, None, 1), ('vcvtsd2ss', 1, 3, 0x5A, 1, 64, None, 0),
          ('vhaddps', 1, 3, 0x7C, 1, 32, None, 1), ('vaddsubpd', 1, 1, 0xD0, 1, 64, None, 1), ('vroundps', 3, 1, 0x08, 0, 32, 0x04, 1),
          ('vroundsd', 3, 1, 0x0B, 1, 64, 0x00, 0), ('vdpps', 3, 1, 0x40, 1, 32, 0xF1, 1), ('vfmadd231ps', 2, 1, 0xB8, 1, 32, None, 1),
          ('vfmadd132sd', 2, 1, 0x99, 1, 64, None, 0), ('vfnmsub213pd', 2, 1, 0xAE, 1, 64, None, 1), ('vfmaddsub231ps', 2, 1, 0xB6, 1, 32, None, 1),
          ('vcomiss', 1, 0, 0x2F, 0, 32, None, 0), ('vucomisd', 1, 1, 0x2E, 0, 64, None, 0)]
SSE_FP = [('addsubps', b'\xf2\x0f\xd0', 32, None), ('addsubpd', b'\x66\x0f\xd0', 64, None), ('haddps', b'\xf2\x0f\x7c', 32, None),
          ('haddpd', b'\x66\x0f\x7c', 64, None), ('hsubps', b'\xf2\x0f\x7d', 32, None), ('hsubpd', b'\x66\x0f\x7d', 64, None),
          ('roundps', b'\x66\x0f\x3a\x08', 32, 0x00), ('roundpd', b'\x66\x0f\x3a\x09', 64, 0x04), ('roundss', b'\x66\x0f\x3a\x0a', 32, 0x01),
          ('roundsd', b'\x66\x0f\x3a\x0b', 64, 0x0C), ('dpps', b'\x66\x0f\x3a\x40', 32, 0xFF), ('dppd', b'\x66\x0f\x3a\x41', 64, 0x31)]


def exception_lanes(rng, bits, n, kind):
    """Operands a, b (lists) that raise exception `kind` (IE, DE, ZE, OE, UE, PE) in one random lane."""
    c = constants(bits)
    f = 23 if bits == 32 else 52
    a = [c['one'] + rng.getrandbits(4) for _ in range(n)]
    b = [c['one'] for _ in range(n)]
    k = rng.randrange(n)
    if kind == 'IE': a[k], b[k] = c['snan'], c['one']
    elif kind == 'DE': a[k] = rng.randrange(1, 1 << f)
    elif kind == 'ZE': b[k] = 0
    elif kind == 'OE': a[k], b[k] = c['largest'], c['largest']
    elif kind == 'UE': a[k], b[k] = c['normal'] | 1, c['half']
    else: a[k], b[k] = c['one'] | 1, c['three']
    if rng.random() < 0.3:   # a second exception kind in another lane: the priority
        j = rng.randrange(n); a[j] = c['snan'] if rng.random() < 0.5 else rng.randrange(1, 1 << f)
    return a, b, k


def avx_unmasked(rng, count):
    per = max(4, count // 60)
    for name, mp, pp, op, uses_v, bits, imm, packed in AVX_FP:
        for kind in ('IE', 'DE', 'ZE', 'OE', 'UE', 'PE'):
            for j in range(per):
                L = j % 2 if packed else 0
                n = (256 if L else 128) // bits
                a, b, k = exception_lanes(rng, bits, n, kind)
                mem = j % 3 == 2
                W = 1 if mp == 2 and bits == 64 else 0
                code = vex(mp, pp, L, W, 1 if uses_v else 0) + bytes([op, 0x03 if mem else 0xC2])
                if imm is not None: code += bytes([imm])
                bit = 'IDZOUP'.index(kind[0])
                masks = rng.choice([0x3F ^ (1 << bit), 0, 0x3F ^ (1 << bit) ^ (1 << rng.randrange(6))])
                mx = masks << 7 | rng.randrange(4) << 13 | rng.choice((0, 0x40, 0x8000))
                xmm, ymmh = regs256([pack(a, bits), pack(a, bits), pack(b, bits), 0])
                yield record3(code, xmm=xmm, ymmh=ymmh, mem=pack(b, bits).to_bytes(32, 'little') + bytes(32), mxcsr=mx), \
                    meta3('avx_unmasked', f'{name}_{kind}', code, lane=k, L=L)
    # a store whose data raises the exception: VCVTPD2PS/VCVTPS2PH to memory must leave the memory unchanged
    for imm in (0, 4):
        for kind in ('OE', 'PE', 'IE', 'UE'):
            for j in range(per):
                a, b, k = exception_lanes(rng, 32, 8, kind)
                code = vex(3, 1, 1, 0, 0) + bytes([0x1D, 0x03, imm])
                xmm, ymmh = regs256([pack(a, 32), 0, 0, 0])
                yield record3(code, xmm=xmm, ymmh=ymmh, mem=bytes(range(64)), mxcsr=0x3F << 7 & ~(1 << (7 + 'IDZOUP'.index(kind[0])))), \
                    meta3('avx_unmasked', f'vcvtps2ph_mem_{kind}', code)


def sse_unmasked_ext(rng, count):
    per = max(4, count // 40)
    for name, enc, bits, imm in SSE_FP:
        for kind in ('IE', 'DE', 'ZE', 'OE', 'UE', 'PE'):
            for j in range(per):
                n = 128 // bits
                a, b, k = exception_lanes(rng, bits, n, kind)
                mem = j % 3 == 2
                code = enc + bytes([0x03 if mem else 0xC1]) + (bytes([imm]) if imm is not None else b'')
                bit = 'IDZOUP'.index(kind[0])
                mx = rng.choice([0x3F ^ (1 << bit), 0]) << 7 | rng.randrange(4) << 13 | rng.choice((0, 0x40, 0x8000))
                xmm = [0x0123456789abcdef ^ (q * 0x101010101010101) for q in range(32)]
                xmm[0], xmm[1] = pack(a, bits) & M64, pack(a, bits) >> 64
                xmm[2], xmm[3] = pack(b, bits) & M64, pack(b, bits) >> 64
                yield record3(code, xmm=xmm, mem=pack(b, bits).to_bytes(16, 'little'), mxcsr=mx), \
                    meta3('sse_unmasked_ext', f'{name}_{kind}', code, lane=k)


def avx_random(rng, count):
    specs = [(k, f, 'avx') for k, f in sorted(gen_avx.SPECS.items())] + [(k, f, 'avx2') for k, f in sorted(gen_avx2.SPECS.items())]
    n = max(300, count * 3 + 500)
    for i in range(n):
        (mp, pp, op), flags, src = specs[rng.randrange(len(specs))]
        fl = flags.split()
        if 'x' in fl and src == 'avx' and (mp, pp, op) in ((1, 0, 0x77), (1, 0, 0xAE)): continue
        gather = 'G' in fl
        L = 0 if ('L0' in fl or 'G0' in fl) else 1 if 'L1' in fl else rng.getrandbits(1)
        W = 0 if 'W0' in fl else 1 if 'W1' in fl else rng.getrandbits(1)
        mem = gather or ('M' in fl) or ('R' not in fl and rng.random() < 0.6)
        regs = (gen_avx2.REGS if src == 'avx2' else gen_avx.REGS).get((mp, pp, op), (0,))
        reg = regs[rng.randrange(len(regs))]
        uses_v = 'V' in fl or ('Vr' in fl and not mem) or gather
        code = vex(mp, pp, L, W, (1 if not gather else 2) if uses_v else 0, two=bool(rng.getrandbits(1)))
        page2 = rng.choice([(0x67, 0x67), (0x67, 0x67), (0x67, 0x65), (0x67, 0)])
        ebx = 0x10000 + rng.choice([0, 0x40, 0x100, 0x200]) if rng.random() < 0.5 else 0x11000 - rng.choice([1, 4, 8, 12, 16, 24, 31, 32])
        regs_in = {3: ebx}
        if gather:
            code += bytes([op, 0x04 | (reg & 7) << 3 if reg == 0 else 0x04, (rng.randrange(4) << 6) | (1 << 3) | 3])
        else:
            code += bytes([op, (0x03 if mem else 0xC2) | (reg & 7) << 3])
        if mp == 3 or 'I' in fl:
            imm = rng.getrandbits(8)
            if mp == 3 and op in (0x4A, 0x4B, 0x4C): imm = (imm & 0x0F) | 0x30
            code += bytes([imm])
        bits = 64 if W or pp in (1, 3) else 32
        vals = [sum(rng.choice(fp_choices(bits)) << (bits * k) if rng.random() < 0.6 else rng.getrandbits(bits) << (bits * k)
                    for k in range(256 // bits)) for _ in range(4)]
        if gather:   # indices up to the second page: some elements fault (#PF midway), masks random
            vals[1] = sum((rng.randrange(-16, 0x1100) & 0xFFFFFFFF) << (32 * k) for k in range(8))
            vals[2] = sum(((rng.getrandbits(1) << 31) | rng.getrandbits(31)) << (32 * k) for k in range(8))
            regs_in[3] = 0x10800
        xmm, ymmh = regs256(vals)
        memb = bytes(rng.getrandbits(8) for _ in range(64))
        kw = {}   # (VRCPPS/VRSQRTPS, 'Q': strict since the model computes the EPYC 7742's table, X86/Zen2Rcp.lean)
        yield record3(code, regs=regs_in, xmm=xmm, ymmh=ymmh, mxcsr=mxcsr_of(rng, rng.random() < 0.1), mem=memb, permissions=page2,
                      seed=rng.getrandbits(32) | 1), meta3('avx_random', '%d.%d.%02x' % (mp, pp, op), code, L=L, src=src, **kw)


def fam(name, gen):
    return lambda rng, count: iter(selected(name, count, gen, rng))


FAMILIES = [(fam('fma_random', fma_random), ('fma', 'avx', 'osxsave')),
            (fam('f16c_exhaustive', f16c_exhaustive), ('f16c', 'avx', 'osxsave')),
            (fam('avx_unmasked', avx_unmasked), ('avx', 'avx2', 'fma', 'f16c', 'osxsave')),
            (fam('sse_unmasked_ext', sse_unmasked_ext), ('sse3', 'sse41')),
            (fam('avx_random', avx_random), ('avx', 'avx2', 'fma', 'f16c', 'osxsave'))]
