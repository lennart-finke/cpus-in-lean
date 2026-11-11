"""Native hardware campaign families for the Sse workstream (x86_32/X86/Ext/Sse.lean): SSE3 (including
FISTTP), SSSE3, SSE4.1, SSE4.2, SSE4a and MisalignSse. Registered in fp_cases.FAMILIES with the CPUID
features they need. Inputs only: no model answer is used by generation.

Cases whose result the manuals leave undefined or describe inconsistently carry policy 'observe'
(recorded, not failed): EXTRQ/INSERTQ bits 127:64 and index + length > 64 (AMD APM vol. 4),
HADDPx/HSUBPx/ADDSUBPx and DPPS with two NaN operands of one operation, and the PCMPxSTRx
equal-ordered edge cases where APM vol. 4 1.5.3 and the SDM differ (empty prototype, partial match
at the end of a full-length string)."""
import struct

import fp_cases
from native_cases import constants

M64 = (1 << 64) - 1


def record(*args, **kw):
    return fp_cases.record(*args, **kw)


def meta(*args, **kw):
    return fp_cases.meta(*args, **kw)


def xmm_of(*vs):
    """XMM0.. from 128-bit values, the rest distinctive."""
    out = []
    for v in vs:
        out += [v & M64, v >> 64]
    return out + [0x0123456789abcdef ^ (k * 0x101010101010101) for k in range(len(out), 32)]


def lanes_of(rng, bits, n, choices):
    return sum((rng.choice(choices) if rng.randrange(4) else rng.getrandbits(bits)) << (bits * k) for k in range(n))


def fp_choices(bits):
    c = constants(bits)
    return list(c.values()) + [0, 1, c['one'] + 1, c['normal'] - 1, c['sign'] | c['one'], c['sign'] | c['infinity']]


def mxcsr_random(rng):
    return (rng.choice((63, 62, 61, 59, 55, 47, 31, 0)) << 7) | (rng.randrange(4) << 13) | rng.choice((0, 0x40, 0x8000, 0x8040))


def has_two_nans(bits, a, b):
    nan = lambda x: (x >> (bits - 1 - (8 if bits == 32 else 11)) & ((1 << (8 if bits == 32 else 11)) - 1)) == \
        (1 << (8 if bits == 32 else 11)) - 1 and x & ((1 << (23 if bits == 32 else 52)) - 1)
    ls = [(v >> (bits * k)) & ((1 << bits) - 1) for v in (a, b) for k in range(128 // bits)]
    return sum(1 for x in ls if nan(x)) >= 2


def fp_case(rng, family, name, code, bits, imm_choices=None, nan_observe=True):
    choices = fp_choices(bits)
    a, b = lanes_of(rng, bits, 128 // bits, choices), lanes_of(rng, bits, 128 // bits, choices)
    mem = bool(rng.randrange(2))
    c = bytes.fromhex(code) + bytes([3 if mem else 0xc1])
    if imm_choices is not None:
        c += bytes([rng.choice(imm_choices)])
    kw = {}
    if nan_observe and has_two_nans(bits, a, b):
        kw = dict(policy='observe', reason='two NaN operands of one operation (first-operand rule; TCG differs)')
    return record(c, xmm=xmm_of(a, b), mxcsr=mxcsr_random(rng), mem=b.to_bytes(16, 'little')), meta(family, name, c, **kw)


def int_case(rng, family, name, code, imm=None, mmx=False, mem_bytes=16):
    pats = (0, M64, 0x8000800080008000, 0x7fff7fff7fff7fff, 0x8080808080808080, 0x7f7f7f7f7f7f7f7f,
            0x0102030405060708, 0xff00ff00ff00ff00, 0x80000000ffffffff)
    pick = lambda: rng.choice(pats) if rng.randrange(3) else rng.getrandbits(64)
    a = pick() | pick() << 64
    b = pick() | pick() << 64
    mem = bool(rng.randrange(2))
    c = bytes.fromhex(code) + bytes([3 if mem else 0xc1]) + (bytes([imm]) if imm is not None else b'')
    if mmx:
        return record(c, a=(a & M64, 0xffff), b=(b & M64, 0xffff), mem=(b & M64).to_bytes(8, 'little')), meta(family, name, c)
    return record(c, xmm=xmm_of(a, b), mem=b.to_bytes(16, 'little')[:mem_bytes]), meta(family, name, c)


def sse3_cases(rng, count):
    for name, code, bits in (('haddps', 'f20f7c', 32), ('hsubps', 'f20f7d', 32), ('addsubps', 'f20fd0', 32),
                             ('haddpd', '660f7c', 64), ('hsubpd', '660f7d', 64), ('addsubpd', '660fd0', 64)):
        for _ in range(max(count // 20, 50)):
            yield fp_case(rng, 'sse3_arith', name, code, bits)
    for name, code in (('movsldup', 'f30f12'), ('movshdup', 'f30f16'), ('movddup', 'f20f12'), ('lddqu', 'f20ff0')):
        for offset in (0, 1, 4, 8, 15):
            c = bytes.fromhex(code) + b'\x03'
            yield record(c, address=0x10000 + offset, mem=bytes(range(64))), meta('sse3_move', name, c, offset=offset)
        c = bytes.fromhex(code) + b'\xc1'
        if name != 'lddqu':
            yield record(c), meta('sse3_move', name, c)
        else:
            yield record(c), meta('sse3_move', 'lddqu_reg_ud', c)
    # FISTTP m16/m32/m64 [ebx]: every operand class, all rounding modes (ignored), masked and unmasked IE
    for name, code in (('fisttp16', 'df0b'), ('fisttp32', 'db0b'), ('fisttp64', 'dd0b')):
        for rc in range(4):
            for j, a in enumerate(fp_cases.VALUES):
                for mask in (0x3f, 0x3e):
                    yield record(code, a=a, cw=0x340 | rc << 10 | mask), meta('sse3_fisttp', name, code, rc=rc, operand_class=j)
        for tags in (255, 0):                          # empty ST(0): stack underflow
            yield record(code, tags=tags), meta('sse3_fisttp', name + '_tags', code, tags=tags)


SSSE3 = [('pshufb', 0x00), ('phaddw', 0x01), ('phaddd', 0x02), ('phaddsw', 0x03), ('pmaddubsw', 0x04),
         ('phsubw', 0x05), ('phsubd', 0x06), ('phsubsw', 0x07), ('psignb', 0x08), ('psignw', 0x09),
         ('psignd', 0x0a), ('pmulhrsw', 0x0b), ('pabsb', 0x1c), ('pabsw', 0x1d), ('pabsd', 0x1e)]


def ssse3_cases(rng, count):
    for name, op in SSSE3:
        for _ in range(max(count // 100, 20)):
            yield int_case(rng, 'ssse3', name + '_mmx', '0f38%02x' % op, mmx=True)
            yield int_case(rng, 'ssse3', name, '660f38%02x' % op)
    for imm in list(range(34)) + [0x7f, 0x80, 0xff]:
        yield int_case(rng, 'ssse3', 'palignr_mmx', '0f3a0f', imm=imm, mmx=True)
        yield int_case(rng, 'ssse3', 'palignr', '660f3a0f', imm=imm)


SSE41_INT = [('pblendvb', '660f3810'), ('blendvps', '660f3814'), ('blendvpd', '660f3815'), ('ptest', '660f3817'),
             ('pmuldq', '660f3828'), ('pcmpeqq', '660f3829'), ('packusdw', '660f382b')] + \
    [('pmovsx%02x' % k, '660f38%02x' % (0x20 + k)) for k in range(6)] + \
    [('pmovzx%02x' % k, '660f38%02x' % (0x30 + k)) for k in range(6)] + \
    [('pminmax%02x' % op, '660f38%02x' % op) for op in range(0x38, 0x40)] + [('pmulld', '660f3840'), ('phminposuw', '660f3841')]


def sse41_cases(rng, count):
    for name, code in SSE41_INT:
        for _ in range(max(count // 200, 20)):
            yield int_case(rng, 'sse41_int', name, code)
    for name, code, imms in (('blendps', '660f3a0c', range(16)), ('blendpd', '660f3a0d', range(4)),
                             ('pblendw', '660f3a0e', range(256)), ('mpsadbw', '660f3a42', range(8)),
                             ('pextrb', '660f3a14', range(16)), ('pextrw', '660f3a15', range(8)),
                             ('pextrd', '660f3a16', range(4)), ('extractps', '660f3a17', range(4)),
                             ('pinsrb', '660f3a20', range(16)), ('pinsrd', '660f3a22', range(4)),
                             ('insertps', '660f3a21', range(256))):
        for imm in imms:
            yield int_case(rng, 'sse41_imm', name, code, imm=imm, mem_bytes=16)
    for name, code, bits in (('roundps', '660f3a08', 32), ('roundpd', '660f3a09', 64),
                             ('roundss', '660f3a0a', 32), ('roundsd', '660f3a0b', 64)):
        for _ in range(max(count // 20, 64)):
            yield fp_case(rng, 'sse41_round', name, code, bits, imm_choices=range(16), nan_observe=False)
    for name, code, bits in (('dpps', '660f3a40', 32), ('dppd', '660f3a41', 64)):
        for _ in range(max(count // 20, 64)):
            yield fp_case(rng, 'sse41_dp', name, code, bits, imm_choices=range(256))
    for offset in (0, 4, 8):
        c = bytes.fromhex('660f382a03')
        yield record(c, address=0x10000 + offset, mem=bytes(range(64))), meta('sse41_movntdqa', 'movntdqa', c, offset=offset)


def strings(rng):
    """(prototype, string under test) pairs as 128-bit values, including the edge cases."""
    alpha = b'abcz\x00\x7f\x80\xff'
    def s(n, extra=b''):
        v = bytes(rng.choice(alpha[:4]) for _ in range(n)) + extra
        return int.from_bytes(v.ljust(16, b'\0')[:16], 'little')
    def raw():
        return int.from_bytes(bytes(rng.choice(alpha) for _ in range(16)), 'little')
    yield 0, s(10)                                                    # empty prototype
    yield s(3), int.from_bytes(b'xxxxxxxxxxxxxabc', 'little') | 0     # partial match at the end
    yield int.from_bytes(b'abcd', 'little'), int.from_bytes(b'zzzzzzzzzzzzzzab', 'little')
    yield s(16, b''), s(16)
    for _ in range(6):
        yield s(rng.randrange(17)), s(rng.randrange(17))
        yield raw(), raw()


def sse42_cases(rng, count):
    for op, name in ((0x60, 'pcmpestrm'), (0x61, 'pcmpestri'), (0x62, 'pcmpistrm'), (0x63, 'pcmpistri')):
        for a, b in strings(rng):
            for imm in range(0, 256, 1 if count >= 10000 else 3):
                mem = bool(imm & 0x80)
                c = bytes([0x66, 0x0f, 0x3a, op, 3 if mem else 0xc1, imm])
                r = bytearray(record(c, xmm=xmm_of(a, b), mem=b.to_bytes(16, 'little')))
                if op in (0x60, 0x61):     # EAX, EDX: explicit lengths
                    struct.pack_into('<Q', r, 16, rng.choice([0, 3, 5, 8, 16, 17, 0xfffffffd, 0x80000000]))
                    struct.pack_into('<Q', r, 32, rng.choice([0, 3, 7, 15, 16, 0xffffffff]))
                kw = {}
                if imm & 0x0c == 0x0c:
                    kw = dict(policy='observe', reason='equal-ordered edge cases: APM vol. 4 1.5.3 and the SDM differ')
                yield bytes(r), meta('sse42_strings', name, c, imm=imm, **kw)
    for _ in range(64):
        yield int_case(rng, 'sse42_int', 'pcmpgtq', '660f3837')


def sse4a_cases(rng, count):
    undefined = dict(policy='observe', reason='EXTRQ/INSERTQ: bits 127:64 undefined, index + length > 64 undefined (APM vol. 4)')
    for length in (0, 1, 7, 8, 16, 31, 32, 33, 63):
        for index in (0, 1, 8, 31, 32, 33, 56, 63):
            for name, code in (('extrq_imm', '660f78c0'), ('insertq_imm', 'f20f78c1')):
                c = bytes.fromhex(code) + bytes([length | (rng.getrandbits(2) << 6), index])
                v = rng.getrandbits(128) | rng.getrandbits(128) << 128
                yield record(c, xmm=xmm_of(v & ((1 << 128) - 1), v >> 128)), meta('sse4a', name, c, length=length, index=index, **undefined)
            for name, code in (('extrq', '660f79c1'), ('insertq', 'f20f79c1')):
                c = bytes.fromhex(code)
                ctl = length | index << 8
                src = (rng.getrandbits(64) | ctl << 64) if name == 'insertq' else (ctl | rng.getrandbits(48) << 16)
                yield record(c, xmm=xmm_of(rng.getrandbits(128), src)), meta('sse4a', name, c, **undefined)
    for name, code in (('movntss', 'f30f2b03'), ('movntsd', 'f20f2b03')):
        for offset in (0, 1, 3, 60):
            yield record(code, address=0x10000 + offset), meta('sse4a', name, code, offset=offset)
    for code in ('660f7806', 'f20f7906', '660f78c8'):   # memory forms, EXTRQ /1: #UD
        c = bytes.fromhex(code) + (b'\x04\x08' if code[4:6] == '78' else b'')
        yield record(c), meta('sse4a', 'ud', c)


def misalign_cases(rng, count):
    """MXCSR.MM = 1: misaligned load/execute operands are accepted, MOVAPS/MOVDQA/MOVNTPS/MOVNTDQ/
    MOVNTDQA still #GP (APM vol. 1, 4.3.2); LDMXCSR of bit 17."""
    for name, code in (('addps', '0f5803'), ('haddps', 'f20f7c03'), ('pshufb', '660f380003'), ('ptest', '660f381703'),
                       ('paddd', '660ffe03'), ('movaps', '0f2803'), ('movaps_st', '0f2903'), ('movdqa', '660f6f03'),
                       ('movntps', '0f2b03'), ('movntdq', '660fe703'), ('movntdqa', '660f382a03'), ('roundps', '660f3a080300')):
        for offset in (0, 4, 8, 15):
            for mm in (0, 1):
                yield record(code, address=0x10000 + offset, mxcsr=0x1f80 | mm << 17, mem=bytes(range(64))), \
                    meta('misalign_sse', name, code, offset=offset, mm=mm)
    for mx in (0x21f80, 0x41f80, 0x31f80):
        yield record('0fae13', mem=struct.pack('<I', mx)), meta('misalign_sse', 'ldmxcsr', '0fae13', value=mx)
