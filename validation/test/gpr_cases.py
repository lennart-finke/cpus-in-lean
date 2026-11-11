"""Native hardware campaign families for the general-purpose Zen 2 extensions (x86_32/X86/Ext/Gpr.lean).

Registered in fp_cases.FAMILIES with the CPUID features they need. Each case is one user-mode
instruction in the native oracle's record format (fp_cases.record) with its GPR inputs patched in;
the model and the hardware are compared on the vector, EFLAGS (defined flags only: `flags_mask`),
the GPRs and the memory hash. Values the hardware does not determine are not generated as
comparisons: RDRAND/RDSEED/RDTSCP results, RDPID (Linux puts the CPU number into TSC_AUX), RDPRU
for MPERF/APERF, RDPMC (CR4.PCE depends on perf). What they do test that QEMU cannot:
  * the documented-undefined flags are masked, but the raw native rows keep them (results archive);
  * RORX with VEX.vvvv != 1111b (the APM lists no #UD, the SDM does; the model executes it);
  * RDPRU with an unsupported ECX (the model: EDX:EAX = 0, CF = 0 -- CF is inferred);
  * CLZERO, MONITORX/MWAITX at CPL 3, MCOMMIT with EFER.MCOMMIT = 0 (Linux leaves it clear),
    CLFLUSH/CLFLUSHOPT/CLWB page faults, prefetches of unmapped memory, BZHI with a large index.
"""
import struct

from fp_cases import record, meta

CF, PF, AF, ZF, SF, OF = 1, 4, 0x10, 0x40, 0x80, 0x800
ARITH = 0x8D5
ADDR = 0x10000          # EBX, EBP, ESI, EDI point here (fp_cases.record); ModRM 03 = [EBX]
REGS = ('eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi')


def gpr_record(code, regs=None, flags=0x202, **kw):
    """fp_cases.record with GPRs replaced: `regs` maps register numbers (ESP excluded) to values."""
    r = bytearray(record(code, flags=flags, **kw))
    for k, v in (regs or {}).items():
        assert k != 4
        struct.pack_into('<Q', r, 16 + 8 * k, v & 0xFFFFFFFF)
    return bytes(r)


def gmeta(family, name, code, flags_mask=ARITH, **kw):
    m = meta(family, name, code if isinstance(code, str) else code.hex(), **kw)
    m['flags_mask'] = flags_mask
    return m


def values(rng):
    return [0, 1, 2, 0x80000000, 0xFFFFFFFF, 0x7FFFFFFF, 0x8000, 0xFFFF, 0x10000, 0x12345678,
            0xF0F0F0F0] + [rng.getrandbits(32) for _ in range(5)]


def vex3(map_, pp, vvvv, L=0, W=0):
    return bytes([0xC4, 0xE0 | map_, (W << 7) | ((~vvvv & 15) << 3) | (L << 2) | pp])


def flags_in(rng):
    return 0x202 | (rng.getrandbits(12) & ARITH)


def bitcount_cases(rng, count):
    # POPCNT (all flags defined), LZCNT/TZCNT (CF, ZF defined), 16 and 32 bits, register and memory
    for name, op, mask in (('popcnt', 0xB8, ARITH), ('lzcnt', 0xBD, CF | ZF), ('tzcnt', 0xBC, CF | ZF)):
        for p66 in (b'', b'\x66'):
            for mod in (0xC1, 0x03):
                for v in values(rng):
                    code = p66 + bytes([0xF3, 0x0F, op, mod])
                    yield gpr_record(code, {1: v, 0: 0x55555555}, flags=flags_in(rng),
                                     mem=struct.pack('<I', v)), gmeta('gpr_bitcount', name, code, mask)


def bmi_cases(rng, count):
    # (name, map, pp, opcode, ModRM.reg or None, defined flags)
    forms = [('andn', 2, 0, 0xF2, None, SF | ZF | CF | OF), ('blsr', 2, 0, 0xF3, 1, SF | ZF | CF | OF),
             ('blsmsk', 2, 0, 0xF3, 2, SF | ZF | CF | OF), ('blsi', 2, 0, 0xF3, 3, SF | ZF | CF | OF),
             ('bzhi', 2, 0, 0xF5, None, SF | ZF | CF | OF), ('pext', 2, 2, 0xF5, None, ARITH),
             ('pdep', 2, 3, 0xF5, None, ARITH), ('mulx', 2, 3, 0xF6, None, ARITH),
             ('bextr', 2, 0, 0xF7, None, ZF | CF | OF), ('shlx', 2, 1, 0xF7, None, ARITH),
             ('sarx', 2, 2, 0xF7, None, ARITH), ('shrx', 2, 3, 0xF7, None, ARITH),
             ('rorx', 3, 3, 0xF0, None, ARITH)]
    for name, map_, pp, op, reg, mask in forms:
        for i in range(max(24, count // 200)):
            L = 1 if i % 12 == 11 else 0                       # VEX.L = 1: #UD
            W = i & 1                                          # VEX.W ignored outside 64-bit mode
            vvvv = 2                                           # EDX (MULX: low half to EDX too)
            if name == 'rorx':
                vvvv = 15 if i % 3 else rng.choice([0, 1, 2])  # vvvv != 1111b: APM silent, SDM #UD
            dst = 0 if reg is None else 0
            mod = rng.choice([0xC0 | (dst << 3) | 1, (dst << 3) | 3]) if reg is None else \
                rng.choice([0xC1 | (reg << 3), 0x03 | (reg << 3)])
            code = vex3(map_, pp, vvvv, L, W) + bytes([op, mod])
            if map_ == 3:
                code += bytes([rng.choice([0, 1, 7, 31, 32, 33, rng.randrange(256)])])
            src = rng.choice(values(rng))
            ctl = rng.choice([rng.randrange(40) | rng.randrange(40) << 8, rng.randrange(70), rng.getrandbits(32),
                              0x2020, 0xFF00, 0x0820])
            regs = {0: 0x55555555, 1: src, 2: ctl}
            yield gpr_record(code, regs, flags=flags_in(rng), mem=struct.pack('<I', src)), \
                gmeta('gpr_bmi', name, code, mask, vvvv=vvvv, L=L, W=W)
    # undefined forms: VEX.0F38 F3 /0 and /4../7, F2/F6 with other pp, F4
    for code in ('c4e278f3c1', 'c4e278f3e1', 'c4e279f2c1', 'c4e278f6c1', 'c4e279f6c1', 'c4e278f4c1',
                 'c4e379f0c105', 'c4e279f5c1'):
        yield gpr_record(code), gmeta('gpr_bmi', 'undefined', code)


def adx_movbe_crc_cases(rng, count):
    for name, pfx in (('adcx', b'\x66'), ('adox', b'\xf3')):
        for mod in (0xC1, 0x03):
            for v in values(rng):
                code = pfx + bytes([0x0F, 0x38, 0xF6, mod])
                f = flags_in(rng)
                yield gpr_record(code, {0: rng.choice(values(rng)), 1: v}, flags=f, mem=struct.pack('<I', v)), \
                    gmeta('gpr_adx', name, code)
    for code in ('0f38f603', 'f20f38f603'):    # no / F2 prefix: #UD
        yield gpr_record(code), gmeta('gpr_adx', 'undefined', code)


def movbe_cases(rng, count):
    for p66 in (b'', b'\x66'):
        for op, mod in ((0xF0, 0x03), (0xF1, 0x03), (0xF0, 0x43), (0xF1, 0x4B), (0xF0, 0xC1)):
            for v in values(rng)[:8]:
                code = p66 + bytes([0x0F, 0x38, op, mod]) + (bytes([rng.randrange(32)]) if mod & 0x40 else b'')
                yield gpr_record(code, {0: 0xA1B2C3D4, 1: v}, mem=bytes(rng.getrandbits(8) for _ in range(64))), \
                    gmeta('gpr_movbe', 'movbe', code)
    yield gpr_record('f30f38f003'), gmeta('gpr_movbe', 'undefined', 'f30f38f003')


def crc32_cases(rng, count):
    for pfx, op in ((b'\xf2', 0xF0), (b'\x66\xf2', 0xF1), (b'\xf2', 0xF1), (b'\x66\xf2', 0xF0)):
        for mod in (0xC1, 0x03, 0xC4):
            for v in values(rng)[:10]:
                code = pfx + bytes([0x0F, 0x38, op, mod])
                yield gpr_record(code, {0: rng.getrandbits(32), 1: v, 2: rng.getrandbits(32)},
                                 mem=struct.pack('<I', v)), gmeta('gpr_crc32', 'crc32', code)


def cache_cases(rng, count):
    # CLFLUSH, CLFLUSHOPT, CLWB on writable, read-only and not-present pages; prefetches never fault
    forms = [('clflush', '0fae3b', 'clfsh'), ('clflushopt', '660fae3b', 'clflushopt'),
             ('clwb', '660fae33', 'clwb'), ('prefetch', '0f0d03', 'prefetchw'),
             ('prefetchw', '0f0d0b', 'prefetchw'), ('prefetch_r5', '0f0d2b', 'prefetchw'),
             ('prefetchnta', '0f1803', None), ('prefetch_reg', '0f0dc1', 'prefetchw')]
    for name, code, _ in forms:
        for perms in ((0x67, 0x67), (0x65, 0x67), (0, 0x67), (0x45, 0x67)):
            for offset in (0, 63, 4095):
                yield gpr_record(code, address=ADDR + offset, permissions=perms), \
                    gmeta('gpr_cache', name, code, permissions=perms, offset=offset)


def clzero_cases(rng, count):
    for perms in ((0x67, 0x67), (0x65, 0x67), (0, 0x67)):
        for offset in (0, 1, 63, 64, 100, 4095):
            yield gpr_record('0f01fc', {0: ADDR + offset}, permissions=perms, mem=bytes(range(64))), \
                gmeta('gpr_clzero', 'clzero', '0f01fc', permissions=perms, offset=offset)


def monitorx_cases(rng, count):
    # MONITORX at CPL 3 (ECX must be 0), MWAITX (ECX[31:2] #GP; with ECX[1] and a short timer)
    for ecx in (0, 1, 0x80000000):
        yield gpr_record('0f01fa', {0: ADDR, 1: ecx}), gmeta('gpr_monitorx', 'monitorx', '0f01fa', ecx=ecx)
    for ecx, ebx in ((0, 0), (2, 1000), (3, 1000), (4, 0), (2, 0)):
        yield gpr_record('0f01fb', {0: 0, 1: ecx, 3: ebx}), gmeta('gpr_monitorx', 'mwaitx', '0f01fb', ecx=ecx)


def system_cases(rng, count):
    # CPL 3: MONITOR/MWAIT #UD (HWCR.MonMwaitUserEn = 0 under Linux), WBNOINVD #GP, MCOMMIT #UD
    # (EFER.MCOMMIT = 0), RDRAND/RDSEED/RDPID #UD forms
    for name, code in (('monitor', '0f01c8'), ('mwait', '0f01c9'), ('wbnoinvd', 'f30f09'),
                       ('mcommit', 'f30f01fa'), ('rdrand_mem', '0fc733'), ('rdrand_f3', 'f30fc7f0'),
                       ('rdseed_f2', 'f20fc7f8'), ('rdpid_mem', 'f30fc73b'), ('rdpid_f2', 'f20fc7f8'),
                       ('rdrand_lock', 'f00fc7f0')):
        yield gpr_record(code, {0: ADDR, 1: 0}), gmeta('gpr_system', name, code)


def rdpru_cases(rng, count):
    # unsupported register numbers: EDX:EAX = 0; CF (the model: 0) and OF/SF/ZF/AF/PF = 0
    for ecx in (2, 3, 0x10, 0xFFFFFFFF):
        yield gpr_record('0f01fd', {0: 0x11111111, 1: ecx, 2: 0x22222222}, flags=0x202 | ARITH), \
            gmeta('gpr_rdpru', 'rdpru', '0f01fd', ecx=ecx)


FAMILIES = [
    (bitcount_cases, ('popcnt', 'abm', 'bmi1')),
    (bmi_cases, ('bmi1', 'bmi2')),
    (adx_movbe_crc_cases, ('adx',)),
    (movbe_cases, ('movbe',)),
    (crc32_cases, ('sse42',)),
    (cache_cases, ('clfsh', 'clflushopt', 'clwb', 'prefetchw')),
    (clzero_cases, ('clzero',)),
    (monitorx_cases, ('mwaitx',)),
    (system_cases, ('monitor', 'wbnoinvd', 'mcommit', 'rdrand', 'rdseed', 'rdpid')),
    (rdpru_cases, ('rdpru',)),
]
