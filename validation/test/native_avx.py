"""Native hardware campaign families for the AVX workstream (x86_32/X86/Ext/Avx.lean, Vex.lean),
registered in fp_cases.FAMILIES with the CPUID features they need ('avx', 'osxsave'). Inputs only:
no model answer is used by generation.

* avx_ops: every AVX form of gen_avx.SPECS, VEX.128 and VEX.256, register and [EBX] memory operands,
  floating-point operand classes, random MXCSR (rounding, DAZ, FTZ, unmasked exceptions);
* avx_encoding: encodings whose treatment the model chose from the manuals: VEX.W ignored outside
  64-bit mode (VMOVD, VPEXTRD, VPINSRD, VCVTSI2SS), VEX.L ignored by the scalar forms (LIG), is4
  imm8[7] ignored, the inverted VEX.vvvv[3] of the C4 form ignored, VZEROALL with VEX.W = 1 (AMD APM
  vol. 4 lists it as #UD, its encoding table and Intel as WIG: 'observe');
* avx_maskmov: VMASKMOVPS/PD next to a not-present page (masked-out elements there: AMD calls their
  exception behaviour implementation dependent, 'observe');
* avx_alignment: the aligned moves (#GP) and #AC with EFLAGS.AC (AMD APM vol. 2 table 8-7: 256-bit
  media 16).

Cases whose result is implementation specific or undefined carry policy 'observe': VRCPPS/VRSQRTPS
and their scalar forms (approximations), two NaN operands of one operation."""
import struct

import fp_cases
import gen_avx
from native_cases import constants

M64 = (1 << 64) - 1


def fp_choices(bits):
    c = constants(bits)
    return list(c.values()) + [0, 1, c['one'] + 1, c['normal'] - 1, c['sign'] | c['one'], c['sign'] | c['infinity']]


def value256(rng, bits):
    choices = fp_choices(bits)
    return sum((rng.choice(choices) if rng.randrange(4) else rng.getrandbits(bits)) << (bits * k)
               for k in range(256 // bits))


def regs256(vals):
    """xmm (XMM0..15 quadword list) and ymmh (YMM0..7 bits 255:128) from up to eight 256-bit values."""
    xmm = [0x0123456789abcdef ^ (k * 0x101010101010101) for k in range(32)]
    ymmh = [0xfedcba9876543210 ^ (k * 0x1010101010101) for k in range(16)]
    for r, v in enumerate(vals):
        xmm[2 * r], xmm[2 * r + 1] = v & M64, (v >> 64) & M64
        ymmh[2 * r], ymmh[2 * r + 1] = (v >> 128) & M64, (v >> 192) & M64
    return xmm, ymmh


def vex(map_, pp, L, W, vvvv, two=True):
    vb = (~vvvv & 0xF) << 3 | (L << 2) | pp
    if two and map_ == 1 and W == 0:
        return bytes([0xC5, 0x80 | vb])
    return bytes([0xC4, 0xE0 | map_, (W << 7) | vb])


def nans(bits, v, n):
    e = 8 if bits == 32 else 11
    f = 23 if bits == 32 else 52
    ls = [(v >> (bits * k)) & ((1 << bits) - 1) for k in range(n)]
    return sum(1 for x in ls if (x >> f) & ((1 << e) - 1) == (1 << e) - 1 and x & ((1 << f) - 1))


def mxcsr_random(rng):
    return (rng.choice((63, 63, 63, 62, 61, 59, 55, 47, 31, 0)) << 7) | (rng.randrange(4) << 13) | \
        rng.choice((0, 0x40, 0x8000, 0x8040))


def avx_ops(rng, count):
    per = max(count // 200, 6)
    for (map_, pp, op), flags in sorted(gen_avx.SPECS.items()):
        fl = flags.split()
        key = (map_, pp, op)
        for j in range(per):
            L = 0 if ('L0' in fl or 'G0' in fl) else 1 if 'L1' in fl else j % 2
            mem = True if 'M' in fl else False if 'R' in fl else bool(j % 3 == 0)
            reg = gen_avx.REGS.get(key, (0,))[j % len(gen_avx.REGS.get(key, (0,)))]
            uses_v = 'V' in fl or ('Vr' in fl and not mem)
            code = vex(map_, pp, L, 0, 1 if uses_v else 0, two=bool(j % 2))
            code += bytes([op])
            if key != (1, 0, 0x77):
                if 'gd' in fl or 'gw' in fl:
                    code += bytes([0x03 | reg << 3]) if mem else bytes([0xC2 | reg << 3])
                else:
                    code += bytes([0x03 | reg << 3]) if mem else bytes([0xC2 | reg << 3])
            if map_ == 3 or 'I' in fl:
                imm = rng.getrandbits(8)
                if map_ == 3 and op in (0x4A, 0x4B, 0x4C):
                    imm = (imm & 0x0F) | 0x30          # is4 = YMM3
                code += bytes([imm])
            bits = 64 if ('nd' in fl or pp in (1, 3) and op not in (0x2A,)) else 32
            vals = [value256(rng, bits) for _ in range(4)]
            mem_bytes = (vals[2] & ((1 << 256) - 1)).to_bytes(32, 'little') + bytes(rng.getrandbits(8) for _ in range(32))
            if key == (1, 0, 0xAE):
                mem_bytes = struct.pack('<16I', *([0x1f80 | rng.getrandbits(6)] * 16))
            if map_ == 2 and op in (0x2C, 0x2D, 0x2E, 0x2F):   # masks: a mix of selected elements
                vals[1] = sum(((rng.getrandbits(1) << 31) | rng.getrandbits(31)) << (32 * k) for k in range(8))
            xmm, ymmh = regs256(vals)
            kw = {}
            if 'Q' in fl:
                kw = dict(policy='observe', reason='VRCPPS/VRSQRTPS approximations are implementation specific')
            elif ('nf' in fl or 'nd' in fl or 'n0' in fl) and \
                    nans(bits, vals[1], 256 // bits) + nans(bits, vals[2] if not mem else vals[2], 256 // bits) >= (1 if 'n0' in fl else 2):
                kw = dict(policy='observe', reason='two NaN operands of one operation (first-operand rule; TCG differs)')
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mxcsr_random(rng), mem=mem_bytes),
                   fp_cases.meta('avx_ops', '%d.%d.%02x' % key, code, L=L, **kw))


def avx_encoding(rng, count):
    vals = [value256(rng, 32) for _ in range(4)]
    xmm, ymmh = regs256(vals)
    cases = [
        ('vmovd_w1', 'c4e1f96ec0', {}), ('vmovd_st_w1', 'c4e1f97ec0', {}),
        ('vpextrd_w1', 'c4e3f916c002', {}), ('vpinsrd_w1', 'c4e3f122c003', {}),
        ('vcvtsi2ss_w1', 'c4e1f22ac0', {}), ('vcvtss2si_w1', 'c4e1fa2dc1', {}),
        ('vaddss_l1', 'c5f658c2', {}), ('vsqrtsd_l1', 'c5f751c2', {}), ('vmovss_l1', 'c5f610c2', {}),
        ('vmovss_ld_l1', 'c5fe1003', {}), ('vmovss_ld_vvvv', 'c5e21003', {}), ('vmovsd_ld_vvvv', 'c4e1631003', {}),
        ('vmovss_st_vvvv', 'c5e21103', {}), ('vcmpss_l1', 'c5f6c2c21d', {}), ('vcvtss2sd_l1', 'c5f65ac2', {}),
        ('vcvtsi2sd_l1', 'c5f72ac0', {}), ('vroundss_l1', 'c4e3750ac201', {}), ('vcomiss_l1', 'c5fc2fc1', {}),
        ('vblendvps_is4_bit7', 'c4e3754ac2b0', {}), ('vblendvps_is4', 'c4e3754ac230', {}),
        ('vmovaps_vvvv8', 'c4e13828c1', {}), ('vaddps_vvvv9', 'c4e13458c2', {}),
        ('vzeroall_w1', 'c4e1fc77', dict(policy='observe',
                                         reason='AMD APM vol. 4 VZEROALL: exception table "VEX.W = 1", encoding "X" (WIG)')),
        ('vzeroupper_w1', 'c4e1f877', {}),
        ('vpermilps_w1', 'c4e2f50cc2', {}), ('vbroadcastss_w1', 'c4e2fd1803', {}),
        ('vmovd_l1', 'c5fd7ec0', {}), ('vmovlps_l1', 'c5fc1303', {}), ('vmovntdq_reg', 'c5fde7c1', {}),
        ('vpaddb_mmx', 'c5f0fcc2', {}), ('vzeroupper_66', 'c5f977', {}), ('vpblendvb_legacy', 'c4e27910c1', {}),
    ]
    for name, code, kw in cases:
        for mx in (0x1f80, 0x9fc0):
            yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, mxcsr=mx, mem=bytes(range(64))),
                   fp_cases.meta('avx_encoding', name, code, **kw))


def avx_maskmov(rng, count):
    vals = [value256(rng, 32) for _ in range(4)]
    for name, op in (('ps_ld', 0x2C), ('pd_ld', 0x2D), ('ps_st', 0x2E), ('pd_st', 0x2F)):
        for L in (0, 1):
            for mask in ('none', 'low', 'high', 'all'):
                n = 8 if op in (0x2C, 0x2E) else 4
                bits = 32 if n == 8 else 64
                sel = {'none': [], 'low': [0], 'high': [n - 1], 'all': list(range(n))}[mask]
                m = sum((1 << (bits * k + bits - 1)) for k in sel)
                xmm, ymmh = regs256([vals[0], m, vals[2], vals[3]])
                code = vex(2, 1, L, 0, 1) + bytes([op, 0x03])
                for off in (8, 16, 0):
                    kw = dict(policy='observe', reason='AMD APM vol. 4 VMASKMOVPS: exceptions of masked-out '
                              'elements are implementation dependent') if mask != 'all' else {}
                    yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, address=0x11000 - off,
                                           permissions=(0x67, 0)),
                           fp_cases.meta('avx_maskmov', '%s_l%d_%s' % (name, L, mask), code, offset=off, **kw))
                # read-only page (stores): masked-out elements must not fault
                yield (fp_cases.record(code, xmm=xmm, ymmh=ymmh, address=0x11000, permissions=(0x67, 0x65)),
                       fp_cases.meta('avx_maskmov', '%s_l%d_%s_ro' % (name, L, mask), code))


def avx_alignment(rng, count):
    ops = [('vmovaps128', 'c5f82803'), ('vmovaps256', 'c5fc2803'), ('vmovdqa256', 'c5fd6f03'),
           ('vmovntps256', 'c5fc2b03'), ('vmovntdqa', 'c4e2792a03'), ('vmovups256', 'c5fc1003'),
           ('vaddps256', 'c5fc5803'), ('vaddss', 'c5f25803'), ('vmovsd', 'c5fb1003'), ('vmovd', 'c5f96e03'),
           ('vbroadcastss', 'c4e2791803'), ('vbroadcastf128', 'c4e27d1a03'), ('vpextrw', 'c4e379150300'),
           ('vmaskmovps', 'c4e2712c03'), ('vldmxcsr', 'c5f8ae13'), ('vstmxcsr', 'c5f8ae1b')]
    mem = struct.pack('<16I', *([0x1f80] * 16))
    for name, code in ops:
        for off in (0, 1, 2, 4, 8, 16):
            for flags in (0x40202, 0x202):
                yield (fp_cases.record(code, flags=flags, address=0x10000 + off, mem=mem),
                       fp_cases.meta('avx_alignment', name, code, offset=off, ac=flags >> 18 & 1))
