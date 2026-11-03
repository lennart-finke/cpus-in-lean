"""Deterministic SSE hardware probes; constructs inputs, never expected results.

The matrix covers every MXCSR mask/rounding/DAZ/FTZ combination for twelve
operand scenarios, plus sticky-status, range-boundary and NaN-payload probes.
All arithmetic values below are IEEE bit encodings, not host float calculations.
"""
import json
import struct
from pathlib import Path

FORMATS = [('ps', b'', 32), ('pd', b'\x66', 64),
           ('ss', b'\xf3', 32), ('sd', b'\xf2', 64)]
CONTROL_MASKS = (0, 0x3f, 0x3d, 0x2f, 0x37)


def constants(bits):
    fraction, bias = (23, 127) if bits == 32 else (52, 1023)
    one = bias << fraction
    normal = 1 << fraction
    infinity = ((1 << (bits - fraction - 1)) - 1) << fraction
    return dict(one=one, two=one + normal, half=one - normal,
                three=one + normal + (normal >> 1), normal=normal,
                largest=infinity - 1, power=infinity - normal,
                sign=1 << (bits - 1), infinity=infinity,
                quiet=infinity | (normal >> 1), snan=infinity | 0x123)


def record(code, bits, left, right, dst=0, src=1, flags=0x202, mxcsr=0x1f80):
    """Build the common 440-byte record, keeping inactive registers distinctive."""
    regs = [0x1234567800000000 + i for i in range(16)]
    regs[4] = 0x8800
    xmm = [0x0123456789abcdef ^ (i * 0x101010101010101) for i in range(32)]
    for reg, lanes in ((dst, left), (src, right)):
        packed = sum(lanes[i % len(lanes)] << (i * bits) for i in range(128 // bits))
        xmm[2*reg:2*reg+2] = [packed & ((1 << 64) - 1), packed >> 64]
    return struct.pack('<16s16QQII2Q32QII', bytes([len(code)]) + code.ljust(15, b'\xcc'),
                       *regs, flags, 1, 1, 0x67, 0x67, *xmm, mxcsr, 0)


def focused_sse():
    serial = 0

    def emit(fmt, mandatory, bits, group, scenario, op, left, right,
             mask, rounding=0, controls=0, sticky=0):
        nonlocal serial
        dst, src = (14, 15) if serial & 1 else (0, 1)
        rex = b'\x45' if dst == 14 else b''
        code = mandatory + rex + bytes([0x0f, op, 0xc0 | ((dst & 7) << 3) | (src & 7)])
        mxcsr = (mask << 7) | (rounding << 13) | (0x40 if controls & 1 else 0) | (0x8000 if controls & 2 else 0) | sticky
        # Scalar instructions must preserve the upper destination lanes.
        if fmt in ('ss', 'sd'):
            c = constants(bits)
            left = [left[0]] + [c['one'] + i for i in range(1, 128 // bits)]
            right = [right[0]] + [c['two'] + i for i in range(1, 128 // bits)]
        flags = 0x202 | (0x100 if serial & 2 else 0)
        serial += 1
        return record(code, bits, left, right, dst, src, flags, mxcsr), dict(
            family='hardware_sse_' + group, scenario=scenario, format=fmt,
            code=code.hex(), mask=0xdd5, mxcsr=mxcsr,
            exception_masks=mask, rounding=rounding, daz=bool(controls & 1),
            ftz=bool(controls & 2), sticky=sticky)

    for fmt, mandatory, bits in FORMATS:
        c = constants(bits)
        one, normal, largest = c['one'], c['normal'], c['largest']
        scenarios = [
            ('invalid', 0x5e, [0], [0]),
            ('denormal', 0x58, [1], [one]),
            ('divide_zero', 0x5e, [one], [0]),
            ('overflow_exact', 0x59, [c['power']], [c['two']]),
            ('overflow_inexact', 0x59, [largest], [largest]),
            ('underflow_exact', 0x59, [normal], [normal]),
            ('underflow_inexact', 0x5e, [normal], [c['three']]),
            ('subnormal_exact', 0x59, [normal], [c['half']]),
            ('precision', 0x5e, [one], [c['three']]),
            ('mixed_invalid_underflow', 0x5e, [0, normal], [0, c['three']]),
            ('mixed_denormal_overflow', 0x59, [1, largest], [one, largest]),
            ('mixed_underflow_precision', 0x59, [normal, one+1], [normal, one+1]),
        ]
        for rounding in range(4):
            for controls in range(4):
                for mask in range(64):
                    for name, op, left, right in scenarios:
                        yield emit(fmt, mandatory, bits, 'matrix', name, op, left, right, mask, rounding, controls)
                for mask in CONTROL_MASKS:
                    for sticky in (0x20, 0x3f):
                        for name, op, left, right in scenarios:
                            yield emit(fmt, mandatory, bits, 'sticky', name, op, left, right, mask, rounding, controls, sticky)

        # Neighbours of the normal/subnormal boundary, half-ULP ties, both signs,
        # and packed lane permutations with conflicting exception conditions.
        boundaries = [
            ('min_subnormal', 0x59, 1, c['half']),
            ('max_subnormal', 0x59, normal-1, one+1),
            ('below_min_normal', 0x59, normal, one-1),
            ('above_min_normal', 0x59, normal+1, one-1),
            ('half_min_normal', 0x59, normal, c['half']),
            ('below_overflow', 0x59, largest, one-1),
            ('above_overflow', 0x59, largest, one+1),
            ('round_tie', 0x58, one, (one - (24 if bits == 32 else 53) * normal)),
        ]
        for name, op, a, b in boundaries:
            for sign in (0, c['sign']):
                for rounding in range(4):
                    for controls in range(4):
                        for mask in CONTROL_MASKS:
                            yield emit(fmt, mandatory, bits, 'boundary', name, op, [a | sign],
                                       [b | sign if op == 0x58 else b], mask, rounding, controls)
        if fmt in ('ps', 'pd'):
            for name, op, left, right in scenarios[-3:]:
                for lane in range(128 // bits):
                    a = [left[1]] * (128 // bits); b = [right[1]] * (128 // bits)
                    a[lane], b[lane] = left[0], right[0]
                    for mask in range(64):
                        yield emit(fmt, mandatory, bits, 'lane_priority', name, op, a, b, mask)

        q1, q2, s1, s2 = c['quiet'] | 0x123, c['quiet'] | 0x185edf, c['snan'], c['infinity'] | 0x456
        pairs = [(q1,q2), (q2,q1), (s1,q2), (q2,s1), (s1,s2), (s2,s1),
                 (q1 | c['sign'],q2), (q2,q1 | c['sign'])]
        for op in (0x58, 0x59, 0x5c, 0x5d, 0x5e, 0x5f):
            for pair, (a,b) in enumerate(pairs):
                for mask in (0x3f, 0x3e):
                    for rounding in range(4):
                        yield emit(fmt, mandatory, bits, 'nan_payload', f'pair_{pair}', op, [a], [b], mask, rounding)


def saved_nan_case():
    fixture = json.loads((Path(__file__).parent / 'fixtures/native_nan_payload.json').read_text())
    return bytes.fromhex(fixture['record_hex']), dict(
        family='hardware_sse_saved_nan', scenario='qemu_20261022_3557',
        code=fixture['code'], mask=0xdd5, original_seed=fixture['seed'],
        original_index=fixture['index'], original_record_sha256=fixture['record_sha256'])
