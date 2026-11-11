"""Native hardware campaign families for the AVX2 workstream (x86_32/X86/Ext/Avx2.lean), registered
in fp_cases.FAMILIES with the CPUID features they need ('avx2', 'fma', 'f16c', 'osxsave'). Inputs
only: no model answer is used by generation.

* avx2_ops: every AVX2/FMA3/F16C form of gen_avx2.SPECS except the gathers, VEX.128/256, register
  and [EBX] memory operands, floating-point operand classes, random MXCSR (rounding, DAZ, FTZ,
  unmasked exceptions);
* fma_special: the FMA cases the manuals leave open or that are easy to get wrong: 0 * inf + QNaN
  (Intel: no IE; AMD's manuals are silent: 'observe'), the NaN operand order of x * y + z for the
  three forms (AMD silent: 'observe'), signed zeros, exact cancellation in every rounding mode, the
  underflow boundary with FTZ/DAZ;
* f16c: VCVTPH2PS/VCVTPS2PH for binary16 denormals with DAZ/FTZ (AMD: DAZ ignored by VCVTPH2PS, FTZ
  by VCVTPS2PH), every imm8 rounding mode, NaN payloads, overflow;
* avx2_gather: gathers of every form with in-range indices and random masks, an element on a
  not-present page (the partial state after the #PF; the SDM's mask normalization: 'observe'),
  register overlap and VSIB #UD forms;
* avx2_maskmov: VPMASKMOVD/Q next to a not-present / read-only page (masked-out elements: AMD
  'implementation dependent', 'observe');
* avx2_encoding: VEX.W/VEX.L/VEX.vvvv #UD forms, FMA4 opcodes (#UD on Zen 2), VEX.L = 1 of the
  scalar FMA forms (LIG);
* avx2_alignment: #AC with EFLAGS.AC for VPMASKMOV (AMD's table: 16/32 bytes; the model: 16,
  'observe') and gather elements."""
import fp_cases
import gen_avx2
from native_avx import vex, regs256, value256, mxcsr_random, nans

M64 = (1 << 64) - 1


def avx2_ops(rng, count):
    per = max(count // 200, 6)
    for (map_, pp, op), flags in sorted(gen_avx2.SPECS.items()):
        fl = flags.split()
        if 'G' in fl:
            continue
        key = (map_, pp, op)
        for j in range(per):
            L = 0 if ('L0' in fl or 'G0' in fl) else 1 if 'L1' in fl else j % 2
            W = 0 if 'W0' in fl else 1 if 'W1' in fl else (j // 2) % 2
            mem = True if 'M' in fl else False if 'R' in fl else bool(j % 3 == 0)
            regs = gen_avx2.REGS.get(key, (0,))
            reg = regs[j % len(regs)]
            code = vex(map_, pp, L, W, 1 if 'V' in fl else 0, two=bool(j % 2))
            code += bytes([op, (0x03 if mem else 0xC2) | reg << 3])
            if map_ == 3 or 'I' in fl:
                imm = rng.getrandbits(8)
                if key == (3, 1, 0x4C):
                    imm = (imm & 0x0F) | 0x30          # is4 = YMM3
                code += bytes([imm])
            fma = map_ == 2 and op >= 0x96
            bits = 64 if fma and W else 32
            vals = [value256(rng, bits) for _ in range(4)]
            if map_ == 2 and op in (0x45, 0x46, 0x47):   # variable shifts: small counts mostly
                vals[2] = sum((rng.randrange(70) if rng.randrange(4) else rng.getrandbits(32)) << (32 * k) for k in range(8))
            if map_ == 2 and op in (0x8C, 0x8E):
                vals[1] = sum(((rng.getrandbits(1) << 31) | rng.getrandbits(31)) << (32 * k) for k in range(8))
            mem_bytes = vals[2].to_bytes(32, 'little') + bytes(rng.getrandbits(8) for _ in range(32))
            xmm, ymmh = regs256(vals)
            kw = {}
            if fma and sum(nans(bits, v, 256 // bits) for v in vals[:3]) >= 2:
                kw = dict(policy='observe', reason='several NaN operands: the SDM picks x, y, z of x*y+z in order; AMD is silent')
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mxcsr_random(rng), mem=mem_bytes),
                   fp_cases.meta('avx2_ops', '%d.%d.%02x' % key, code, L=L, W=W, **kw))


def _f32(x):
    import struct
    return struct.unpack('<I', struct.pack('<f', x))[0]


def fma_special(rng, count):
    one, inf, q1, q2, q3, s1 = 0x3F800000, 0x7F800000, 0x7FC00001, 0x7FC00002, 0x7FC00003, 0x7FA00004
    rows = [
        ('zero_inf_one', 0, inf, one, {}),
        ('zero_inf_qnan', 0, inf, q3, dict(policy='observe', reason='0*inf+QNaN: IE is implementation defined '
                                            '(IEEE 754-2008 7.2); Intel: no IE; AMD silent')),
        ('inf_zero_snan', inf, 0, s1, {}),
        ('nan_order_xyz', q1, q2, q3, dict(policy='observe', reason='NaN operand order: SDM table 14-17; AMD silent')),
        ('nan_order_yz', one, q2, s1, dict(policy='observe', reason='NaN operand order: SDM table 14-17; AMD silent')),
        ('cancel', one, one, 0xBF800000, {}), ('neg_zero', 0x80000000, one, 0x80000000, {}),
        ('single_round', 0x3F800001, 0x3F7FFFFE, 0xBF800000, {}), ('no_overflow', 0x7F7FFFFF, 0x40000000, 0xFF7FFFFF, {}),
        ('tiny', 0x3F7FFFFF, 0x00800000, 0, {}), ('denormal', 0x00400000, 0x40000000, 0, {}),
    ]
    for name, x, y, z, kw in rows:
        for opname, op in (('vfmadd132ss', 0x99), ('vfmsub213ss', 0xAB), ('vfnmadd231ss', 0xBD), ('vfmadd132ps', 0x98)):
            # op1 = xmm0 = x, op2 = xmm1, op3 = xmm2: 132 computes xmm0 * xmm2 + xmm1
            code = vex(2, 1, 0, 0, 1) + bytes([op, 0xC2])
            vals = [x * 0x0000000100000001 * ((1 << 64) + 1), z * 0x0000000100000001 * ((1 << 64) + 1),
                    y * 0x0000000100000001 * ((1 << 64) + 1), 0]
            xmm, ymmh = regs256(vals)
            for mx in (0x1F80, 0x3F80, 0x5F80, 0x7F80, 0x9F80, 0x1FC0):
                yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mx),
                       fp_cases.meta('fma_special', '%s_%s' % (opname, name), code, **kw))


def f16c(rng, count):
    halves = [0x0001, 0x03FF, 0x8200, 0x0400, 0x7BFF, 0x7C00, 0xFC00, 0x7E01, 0x7D02, 0x3C00, 0x3555, 0x8000]
    singles = [_f32(2.0 ** -25), _f32(2.0 ** -24 * 1.5), 0x387FC000, 0x00000001, _f32(65520.0), _f32(65504.0),
               _f32(1.0 / 3), 0x7FA00001, 0xFFC12345, _f32(-2.0 ** -15), 0x477FF000, 0x33000001]
    for L in (0, 1):
        hv = sum(halves[k % len(halves)] << (16 * k) for k in range(16))
        xmm, ymmh = regs256([0, 0, hv, 0])
        code = vex(2, 1, L, 0, 0) + bytes([0x13, 0xC2])
        for mx in (0x1F80, 0x1FC0, 0x9F80, 0x1F00):
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mx),
                   fp_cases.meta('f16c', 'vcvtph2ps_l%d' % L, code, mxcsr=mx))
        sv = sum(singles[k % len(singles)] << (32 * k) for k in range(8))
        xmm, ymmh = regs256([sv, 0, 0, 0])
        for imm in (0, 1, 2, 3, 4, 0xF8):
            code = vex(3, 1, L, 0, 0) + bytes([0x1D, 0xC2, imm])
            for mx in (0x1F80, 0x9FC0, 0x3F80, 0x1D80):
                yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mx),
                       fp_cases.meta('f16c', 'vcvtps2ph_l%d_imm%x' % (L, imm), code, mxcsr=mx))
            code = vex(3, 1, L, 0, 0) + bytes([0x1D, 0x03, imm])     # memory destination [EBX]
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=0x1F80, mem=bytes(range(64))),
                   fp_cases.meta('f16c', 'vcvtps2ph_mem_l%d_imm%x' % (L, imm), code))


def avx2_gather(rng, count):
    """dest YMM0, mask YMM2, index YMM1, base EBX (the data page, 64 known bytes)."""
    for op in (0x90, 0x91, 0x92, 0x93):
        for L in (0, 1):
            for W in (0, 1):
                for j in range(max(count // 400, 4)):
                    scale = rng.randrange(4)
                    db, ib = 64 if W else 32, 64 if op & 1 else 32
                    n = (256 if L else 128) // max(db, ib)
                    idx = [rng.randrange((64 - db // 8) // (1 << scale) + 1) for _ in range(8)]
                    xv = sum((v & ((1 << ib) - 1)) << (ib * k) for k, v in enumerate(idx[:256 // ib]))
                    mv = sum(((rng.getrandbits(1) << (db - 1)) | rng.getrandbits(db - 1)) << (db * k) for k in range(256 // db))
                    xmm, ymmh = regs256([value256(rng, 32), xv, mv, 0])
                    code = vex(2, 1, L, W, 2) + bytes([op, 0x04, (scale << 6) | (1 << 3) | 3])   # [ebx + ymm1*s]
                    yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mem=bytes(rng.getrandbits(8) for _ in range(64))),
                           fp_cases.meta('avx2_gather', '%02x_l%d_w%d' % (op, L, W), code, scale=scale))
    # an element on the not-present second page: the partial state after #PF
    for op, W in ((0x90, 0), (0x92, 1), (0x91, 0)):
        idx = [0, 4, 8, 0x1000 // 4, 12, 16, 20, 24]
        xv = sum(v << (32 * k) for k, v in enumerate(idx)) if not op & 1 else sum((v * 4) << (64 * k) for k, v in enumerate(idx[:4]))
        for mask in ('all', 'mixed'):
            mv = sum((0x80000000 | rng.getrandbits(31) if mask == 'all' or k % 2 == 0 else rng.getrandbits(31)) << (32 * k)
                     for k in range(8))
            xmm, ymmh = regs256([value256(rng, 32), xv, mv, 0])
            code = vex(2, 1, 1, W, 2) + bytes([op, 0x04, (2 << 6 if not op & 1 else 0) | (1 << 3) | 3])
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, address=0x10000, permissions=(0x67, 0), mem=bytes(range(64))),
                   fp_cases.meta('avx2_gather', 'pf_%02x_%s' % (op, mask), code, policy='observe',
                                 reason='mask elements not yet processed: SDM normalizes them, AMD/model leave them'))
    # #UD forms
    for name, code in (('mod3', 'c4e26d90c1'), ('no_vsib', 'c4e26d9003'), ('dest_mask', 'c4e27d90040b'),
                       ('dest_index', 'c4e26d900403'), ('mask_index', 'c4e26d900413'), ('a16', '67c4e26d900400')):
        yield (fp_cases.record(code), fp_cases.meta('avx2_gather', 'ud_' + name, code))


def avx2_maskmov(rng, count):
    vals = [value256(rng, 32) for _ in range(4)]
    for name, op, W in (('d_ld', 0x8C, 0), ('q_ld', 0x8C, 1), ('d_st', 0x8E, 0), ('q_st', 0x8E, 1)):
        for L in (0, 1):
            for mask in ('none', 'low', 'high', 'all'):
                bits = 64 if W else 32
                n = (256 if L else 128) // bits
                sel = {'none': [], 'low': [0], 'high': [n - 1], 'all': list(range(n))}[mask]
                m = sum((1 << (bits * k + bits - 1)) for k in sel)
                xmm, ymmh = regs256([vals[0], m, vals[2], vals[3]])
                code = vex(2, 1, L, W, 1) + bytes([op, 0x03])
                for off in (8, 16, 0):
                    kw = dict(policy='observe', reason='AMD APM vol. 4 VPMASKMOVD: exceptions of masked-out '
                              'elements are implementation dependent') if mask != 'all' else {}
                    yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, address=0x11000 - off, permissions=(0x67, 0)),
                           fp_cases.meta('avx2_maskmov', '%s_l%d_%s' % (name, L, mask), code, offset=off, **kw))
                yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, address=0x11000, permissions=(0x67, 0x65)),
                       fp_cases.meta('avx2_maskmov', '%s_l%d_%s_ro' % (name, L, mask), code))


def avx2_encoding(rng, count):
    vals = [value256(rng, 32) for _ in range(4)]
    xmm, ymmh = regs256(vals)
    cases = ['c4e37d00c11b', 'c4e3f900c11b', 'c4e2f536c2', 'c4e27136c2', 'c4e27d5ac1', 'c4e2795a03', 'c4e27919c1',
             'c4e2fd78c1', 'c4e3f502c255', 'c4e2f546c2', 'c4e37138c201', 'c4e37539c101', 'c4e3f546c221',
             'c4e3f54cc230', 'c4e27d2ac1', 'c5fdd703', 'c4e2758cc2', 'c4e2f913c1', 'c4e3751dc100',
             'c4e37168c230', 'c4e3715cc230', 'c4e37178c230', 'c4e3716ac230', 'c4e3f17fc230',   # FMA4: #UD on Zen 2
             'c4e27599c2', 'c4e2f5b9c2', 'c4e2759bc2',                                          # scalar FMA, VEX.L = 1
             'c4e33d1dc100', 'c4e2b913c1']                                                      # inverted vvvv[3] = 0
    for code in cases:
        yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mem=bytes(range(64))), fp_cases.meta('avx2_encoding', code, code))


def avx2_alignment(rng, count):
    m = (1 << 255) | (1 << 127) | (1 << 31)
    xmm, ymmh = regs256([0, 0, m, 0])
    ops = [('vpmaskmovd256', 'c4e26d8c03'), ('vpmaskmovd128', 'c4e2698c03'), ('vpmaskmovq_st', 'c4e2ed8e03'),
           ('vpgatherdd', 'c4e26d90040b'), ('vpgatherdq', 'c4e2ed90040b')]
    for name, code in ops:
        for off in (0, 1, 2, 4, 8, 16):
            for flags in (0x40202, 0x202):
                yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, flags=flags, address=0x10000 + off),
                       fp_cases.meta('avx2_alignment', name, code, offset=off, ac=flags >> 18 & 1,
                                     policy='observe', reason='AMD tables: 16/32-byte #AC for VPMASKMOV; the model: 16'))
