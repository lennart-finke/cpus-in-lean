"""Native families of the integer instruction set against the current model (bundle format v3; the
earlier integer campaigns, test/native.py, native_memory.py, native_hunt.py, predate the decoder and
dispatch rebuild and their results were not kept).

* `int_core`: the random integer generator of the QEMU differential tests (gen.py `gen_one`: ALU, shifts
  and rotates, MUL/DIV, BCD, bit tests and scans, CMPXCHG/XADD/XCHG with and without LOCK, string
  instructions with small REP counts and both DF values, stack instructions, MOVZX/MOVSX/BSWAP/SETcc/
  CMOVcc, near transfers into the code page, LEA, flag instructions, 16-bit operand and address size,
  segment overrides, ...), its memory operands moved to the oracle's arena, with the defined flags of
  each vector (`flags_mask`; the undefined ones are observations, `flags_observe`), and page-permission
  variants (read-only and unmapped data pages) for a quarter of the cases;
* `int_directed`: exhaustive and boundary matrices: BCD (all AL values), shifts and rotates (all counts
  0..33 and 255 at 8/16/32 bits), MUL/IMUL/DIV/IDIV with #DE, LOCK on every one-byte and 0F opcode
  (memory and register forms: the LOCK #UD rules), CMPXCHG/CMPXCHG8B/XADD/XCHG, string instructions
  (REP counts 0..5, DF 0/1, page crossings), stack instructions at page boundaries (PUSH/POP/PUSHA/
  POPA/ENTER/LEAVE/CALL/RET), Jcc/SETcc/CMOVcc for every condition and flag pattern, LOOP/LOOPcc/JCXZ,
  LEA with every 32-bit ModRM/SIB form and every 16-bit form, BT*/BSF/BSR, BOUND, read-modify-write
  instructions on read-only and unmapped pages and across page boundaries, and ARPL/VERR/VERW/LAR/LSL/
  SGDT/SIDT/SLDT/STR/SMSW at CPL 3 (OS-specific results: every field 'observe'; Linux emulates
  SGDT/SIDT/SMSW, and newer kernels SLDT/STR, under UMIP, the model raises #GP);
* `shift16_rules`: 16-bit SHLD/SHRD with every count 0..31 and nonzero sources and destinations, r16 and
  m16, imm8 and CL (open question G8), and the 8- and 16-bit shifts and rotates (RCL/RCR: modulo 9/17)
  with every count 0..31; all flags recorded (the undefined ones as observations).

All of them go through native_ext.select (the oracle's validation, the model's observability, accesses
inside the low 256 KiB), like the encoding fuzz.
"""
import collections
import random
import struct

from native_ext import record3, meta3, layout, select, cached, STATS, ARITH
from native_flags import undefined_flags

DF = 0x400


def case(family, name, code, *, regs=None, flags=0x202, perms=(0x67, 0x67), mem=b'', patches=(), mask=None, **kw):
    code = bytes.fromhex(code) if isinstance(code, str) else bytes(code)
    regs = dict(regs or {})
    for k, v in ((0, 0x12345678), (1, 3), (2, 0x76543210), (3, 0x10000), (4, 0x11800), (5, 0x10000), (6, 0x10000),
                 (7, 0x10000)):
        regs.setdefault(k, v)
    raw = record3(code, regs=regs, flags=flags, permissions=perms, mem=mem, patches=patches)
    m = meta3(family, name, code, **kw)
    und = undefined_flags(code, regs)
    m['flags_mask'] = (ARITH | DF) & ~und if mask is None else mask
    if und: m['flags_observe'] = und
    return raw, m


# ---------------------------------------------------------------------------------------------------
# int_core: gen.py's random integer vectors

def int_core_candidates(rng, count):
    import gen as G
    G.random = rng                      # gen_one draws from the module's `random`
    G.DATA = 0x10000                    # its data area becomes the oracle's arena (8 KiB, page boundary at +0x1000)
    for _ in range(count):
        try:
            insn, g = G.gen_one()
        except struct.error:   # a 16-bit absolute address of the arena (above 64 KiB): not encodable
            continue
        patches = [(o, v & 0xFFFFFFFF) for o, v in g.patches]
        mem = bytearray(64)   # the arena is random (its seed); the patch only carries gen.py's patches
        ext = []
        for o, v in patches:
            if 0 <= o <= 60: struct.pack_into('<I', mem, o, v)
            elif 0 <= o <= 8188: ext.append((o, v))
        if len(ext) > 8: continue
        perms = (0x67, 0x67)
        if rng.random() < 0.25:
            perms = rng.choice([(0x65, 0x67), (0x67, 0x65), (0, 0x67), (0x67, 0), (0x65, 0x65)])
        regs = {k: g.regs[k] for k in range(8)}
        flags = 0x202 | (g.eflags & 0x40DD5)
        raw = record3(insn, regs=regs, flags=flags, permissions=perms, mem=bytes(mem), patches=ext,
                      seed=rng.getrandbits(32) | 1)
        m = meta3('int_core', f'{layout(insn)[1]:03x}', insn)
        und = ARITH & ~g.fmask
        m['flags_mask'] = (ARITH | DF) & g.fmask
        if und: m['flags_observe'] = und
        if perms != (0x67, 0x67): m['permissions'] = perms
        yield raw, m


# ---------------------------------------------------------------------------------------------------
# int_directed

VALS32 = [0, 1, 2, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x12345678, 0xFEDCBA98]
CONDS = range(16)
FLAGSETS = [0, 1, 4, 0x40, 0x80, 0x800, 0x41, 0x880, 0x80 | 0x40, 0x801, 0xC5, 0x8D5, 0x10, 0x81, 0x840, 0x804]


def bcd(rng):
    for op in (0x27, 0x2F, 0x37, 0x3F):
        for al in range(256):
            for fl in (0, 1, 0x10, 0x11):
                yield case('int_directed', f'bcd_{op:02x}', bytes([op]), regs={0: 0xFF00 | al}, flags=0x202 | fl)
    for op in (0xD4, 0xD5):
        for base in range(256):
            for ax in (0, 0x7F, 0x80, 0xFF, 0x100, 0xFF00, 0xFFFF):
                yield case('int_directed', f'bcd_{op:02x}', bytes([op, base]), regs={0: ax})


def shifts(rng):
    for size, pfx, op_i, op_1, op_cl in ((8, b'', 0xC0, 0xD0, 0xD2), (16, b'\x66', 0xC1, 0xD1, 0xD3), (32, b'', 0xC1, 0xD1, 0xD3)):
        for reg in range(8):
            for cnt in list(range(34)) + [63, 255]:
                for v in (0x81, 0x8001, 0x80000001, 0x12345678, 0xFFFFFFFF):
                    for fl in (0x202, 0x203):
                        code = pfx + bytes([op_i, 0xC0 | reg << 3, cnt])
                        yield case('int_directed', f'shift{size}_{reg}', code, regs={0: v}, flags=fl)
                        code = pfx + bytes([op_cl, 0xC0 | reg << 3])
                        yield case('int_directed', f'shift{size}_{reg}_cl', code, regs={0: v, 1: 0xFFFFFF00 | cnt}, flags=fl)
            code = pfx + bytes([op_1, 0xC0 | reg << 3])
            yield case('int_directed', f'shift{size}_{reg}_1', code, regs={0: 0x80000081})


def muldiv(rng):
    pairs = [(a, b) for a in VALS32 for b in (0, 1, 2, 0xFF, 0xFFFF, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF, 3, 0x10)]
    for size, pfx, op in ((8, b'', 0xF6), (16, b'\x66', 0xF7), (32, b'', 0xF7)):
        for reg in (4, 5, 6, 7):
            for a, b in pairs:
                for d in (0, 1, 0xFFFFFFFF, 0x7FFFFFFF):
                    if rng.random() < 0.5: continue
                    yield case('int_directed', f'muldiv{size}_{reg}', pfx + bytes([op, 0xC3 | reg << 3]), regs={0: a, 2: d, 3: b})
            for mem_b in (0, 1, 7):
                yield case('int_directed', f'muldiv{size}_{reg}_mem', pfx + bytes([op, 0x03 | reg << 3]),
                           regs={0: 0x12345678, 2: 0}, mem=struct.pack('<I', mem_b))
    for a, b in pairs[::3]:
        for code in ('0fafc3', '660fafc3', '69c378563412', '6bc3f0', '666bc37f'):
            yield case('int_directed', f'imul_{code[:4]}', code, regs={0: a, 3: b})


def lock_matrix(rng):
    for esc in (b'', b'\x0f'):
        for op in range(256):
            for mod in (0x03, 0xC3):
                for reg in (0, 1, 6) if op in (0x80, 0x81, 0x83, 0xF6, 0xF7, 0xFE, 0xFF, 0xBA, 0xC7) else (0,):
                    code = b'\xf0' + esc + bytes([op, mod | reg << 3]) + b'\x01\x00\x00\x00'
                    n = layout(code)[0]
                    if n > 15: continue
                    yield case('int_directed', f'lock_{esc.hex()}{op:02x}_{"m" if mod == 3 else "r"}', code[:n],
                               regs={1: 3}, mem=struct.pack('<II', 0x12345678, 0x9ABCDEF0))


def atomics(rng):
    for perms in ((0x67, 0x67), (0x65, 0x67), (0, 0x67)):
        for lock in (b'', b'\xf0'):
            for code, eax in (('0fb10b', 0x12345678), ('0fb10b', 0), ('0fb00b', 0x78), ('660fb10b', 0x5678),
                              ('0fc10b', 0), ('0fc00b', 0), ('660fc10b', 0), ('870b', 0), ('860b', 0), ('66870b', 0)):
                yield case('int_directed', f'atomic_{code}', lock + bytes.fromhex(code), regs={0: eax, 1: 0xCAFEBABE},
                           perms=perms, mem=struct.pack('<II', 0x12345678, 0x9ABCDEF0))
            for edx, eax in ((0x9ABCDEF0, 0x12345678), (0, 0)):
                yield case('int_directed', 'cmpxchg8b', lock + b'\x0f\xc7\x0b', regs={0: eax, 2: edx, 1: 1, 3: 0x10000},
                           perms=perms, mem=struct.pack('<II', 0x12345678, 0x9ABCDEF0))
        yield case('int_directed', 'cmpxchg8b_reg', 'f00fc7c8')
        yield case('int_directed', 'xchg_reg_lock', 'f087c3')


def strings(rng):
    for op in (0xA4, 0xA5, 0xA6, 0xA7, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF):
        for pfx in (b'', b'\x66'):
            if op in (0xA4, 0xA6, 0xAA, 0xAC, 0xAE) and pfx: continue
            for rep in (b'', b'\xf3', b'\xf2'):
                for ecx in (0, 1, 2, 5):
                    for df in (0, DF):
                        for si, di in ((0x10100, 0x10800), (0x10FFE, 0x11FFC), (0x11FFE, 0x10002), (0x10FF0, 0x10FF8)):
                            perms = rng.choice([(0x67, 0x67), (0x67, 0x67), (0x67, 0x65), (0x67, 0)])
                            yield case('int_directed', f'string_{op:02x}', rep + pfx + bytes([op]),
                                       regs={1: ecx, 6: si, 7: di, 0: 0x41424344}, flags=0x202 | df | 0x40, perms=perms)
        # 16-bit addressing (SI/DI below the arena: a #PF) and XLAT
    for code in ('67a4', '67f3a5', 'd7', '67d7', '26d7', '64d7', '65a5'):
        yield case('int_directed', 'string_misc', code, regs={1: 2, 6: 0x10100, 7: 0x10200, 3: 0x10040, 0: 0x37})


def stack(rng):
    for esp in (0x10000, 0x10002, 0x10004, 0x10020, 0x11000, 0x11002, 0x11004, 0x10FFE, 0x11FFC, 0x12000, 0x11FE0):
        for perms in ((0x67, 0x67), (0x67, 0x65), (0x65, 0x67), (0, 0x67), (0x67, 0)):
            for code in ('50', '6650', '58', '6658', '6a80', '68efbeadde', '6668efbe', 'ff33', '8f03', '60', '6660',
                         '61', '6661', '9c', '669c', 'c8100000', 'c8040001', 'c8080003', '66c80400', 'c9', '66c9',
                         'e800000000', 'c3', 'c20800', '0fa0', '0fa8', '06', '16'):
                yield case('int_directed', f'stack_{code[:4]}', code, regs={4: esp, 5: esp + 0x40, 3: 0x10100},
                           perms=perms, patches=[(o, 0x20180) for o in ((esp - 0x10000) & ~3, (esp - 0x10000 + 4) & ~3)
                                                 if 0 <= o <= 8188][:2])


def branches(rng):
    for cc in CONDS:
        for fl in FLAGSETS:
            yield case('int_directed', f'jcc8_{cc:x}', bytes([0x70 | cc, 0x10]), flags=0x202 | fl)
            yield case('int_directed', f'jcc32_{cc:x}', bytes([0x0F, 0x80 | cc, 0x20, 0, 0, 0]), flags=0x202 | fl)
            yield case('int_directed', f'setcc_{cc:x}', bytes([0x0F, 0x90 | cc, 0xC0 | (fl & 7)]), flags=0x202 | fl)
            yield case('int_directed', f'cmovcc_{cc:x}', bytes([0x0F, 0x40 | cc, 0xC3]), flags=0x202 | fl, regs={3: 0xDEADBEEF})
            yield case('int_directed', f'cmovcc_m_{cc:x}', bytes([0x0F, 0x40 | cc, 0x03]), flags=0x202 | fl,
                       perms=rng.choice([(0x67, 0x67), (0, 0x67)]))
    for op in (0xE0, 0xE1, 0xE2, 0xE3):
        for ecx in (0, 1, 2, 0x10000, 0xFFFFFFFF):
            for zf in (0, 0x40):
                for a16 in (b'', b'\x67'):
                    yield case('int_directed', f'loop_{op:02x}', a16 + bytes([op, 0x08]), regs={1: ecx}, flags=0x202 | zf)
    for code in ('eb10', 'e910000000', 'e800010000', 'ebf0', 'ffd0', 'ffe0', '66ffd0', 'ff13', 'ff23'):
        yield case('int_directed', 'jmp_call', code, regs={0: 0x20180, 3: 0x10000}, patches=[(0, 0x201A0)])


def lea(rng):
    for mod in (0, 1, 2):
        for rm in range(8):
            sibs = range(256) if rm == 4 else (None,)
            for sib in sibs:
                code = bytes([0x8D, mod << 6 | rm]) + (bytes([sib]) if sib is not None else b'')
                if mod == 1: code += bytes([rng.getrandbits(8)])
                elif mod == 2 or (mod == 0 and (rm == 5 or (sib is not None and sib & 7 == 5))):
                    code += struct.pack('<I', rng.getrandbits(32))
                regs = {k: rng.getrandbits(32) for k in (0, 1, 2, 3, 5, 6, 7)}
                yield case('int_directed', 'lea32', code, regs=regs)
                if sib is None or sib % 8 == 0:   # the same form as a load (a sample of the SIBs)
                    mregs = {k: 0x10000 + rng.randrange(0x40) for k in (0, 1, 2, 3, 5, 6, 7)}
                    mcode = bytes([0x8B]) + code[1:]
                    if mod == 2 or (mod == 0 and (rm == 5 or (sib is not None and sib & 7 == 5))):
                        mcode = mcode[:-4] + struct.pack('<I', 0x10000 + rng.randrange(0x100)) if (mod == 0) else mcode[:-4] + struct.pack('<I', rng.randrange(0x100))
                    yield case('int_directed', 'mov32_forms', mcode, regs=mregs, perms=rng.choice([(0x67, 0x67), (0x67, 0)]))
    for mod in (0, 1, 2):
        for rm in range(8):
            code = b'\x67\x8d' + bytes([mod << 6 | rm])
            if mod == 1: code += bytes([rng.getrandbits(8)])
            elif mod == 2 or (mod == 0 and rm == 6): code += struct.pack('<H', rng.getrandbits(16))
            for pfx in (b'', b'\x66'):
                yield case('int_directed', 'lea16', pfx + code, regs={k: rng.getrandbits(32) for k in (0, 1, 2, 3, 5, 6, 7)})


def misc(rng):
    for code in ('0fb6c3', '0fb7c3', '0fbec3', '0fbfc3', '660fb6c3', '660fbec3', '0fb603', '0fbf03', '0fc8', '0fcb', '660fc8',
                 '98', '6698', '99', '6699', 'f8', 'f9', 'f5', 'fc', 'fd', '9e', '9f', '9c', '9d', 'd6', '90', 'f390',
                 '86c3', '87c3', '6687c3', '0fa3c3', '0fabc3', '0fb3c3', '0fbbc3', '0fbae304', '0fbaeb1f', '0fbaf321', '0fbafb00',
                 '0fa303', '0fab03', '0fb303', '0fbb03', '0fbcc3', '0fbdc3', '660fbcc3', '0fbc03', '0fbd03'):
        for v in (0, 1, 0x80000000, 0x12345678, 0xFFFFFFFF):
            for fl in (0x202, 0x2D7 & ~0x100 | 0x202):
                yield case('int_directed', f'misc_{code}', code, regs={0: rng.choice((0, 5, 31, 32, 0x7FF)), 3: v}, flags=fl,
                           perms=rng.choice([(0x67, 0x67), (0x65, 0x67)]))
    # BOUND (in and out of range), ARPL, and the system instructions at CPL 3 (OS-specific: observe)
    for lo, hi, v in ((0, 10, 5), (0, 10, 11), (5, 10, 4), (0x80000000, 0x7FFFFFFF, 0)):
        yield case('int_directed', 'bound32', '6203', regs={0: v}, mem=struct.pack('<ii', lo - (1 << 32) * (lo >> 31), hi))
        yield case('int_directed', 'bound16', '666203', regs={0: v}, mem=struct.pack('<hh', lo & 0x7FFF, hi & 0x7FFF))
    for code in ('63d8', '6303', '0f00e3', '0f00eb', '0f00e0', '0f00e8', '0f02c3', '0f03c3', '0f0203', '0f0303',
                 '0f0103', '0f010b', '0f00c0', '0f00c8', '0f0003', '0f000b', '0f01e0', '0f0123', '660f01e0'):
        for sel in (0x23, 0x2B, 0x33, 0, 0x10):
            r, m = case('int_directed', f'system_{code}', code, regs={0: sel, 3: 0x10100})
            m['observe_fields'] = ['*']; m['reason'] = 'OS-specific at CPL 3 (descriptor tables, UMIP emulation)'
            yield r, m


def rmw(rng):
    ops = ['0103', '0903', '1103', '1903', '2103', '2903', '3103', '8303' + '05', '800380', 'ff03', 'ff0b', 'f713', 'f71b',
           'd123', 'd12b', 'c10304', 'd303', '8703', '0fb103', '0fc103', '0fab03', '0fbb03', '0fba2b03', '0f9003', '8903',
           '6601 03'.replace(' ', ''), '6683 03 7f'.replace(' ', ''), '0fa403 04'.replace(' ', ''), '0fad03', 'fe03', 'f603 55'.replace(' ', '')]
    for code in ops:
        for ebx, perms in ((0x10100, (0x65, 0x67)), (0x10100, (0, 0x67)), (0x10FFE, (0x67, 0x65)), (0x10FFE, (0x67, 0)),
                           (0x10FFD, (0x67, 0x67)), (0x11FFE, (0x67, 0x67)), (0x10FFF, (0x65, 0x67)), (0x10100, (0x67, 0x67))):
            for lock in ((b'',) if code.startswith(('89', '0f90', 'd1', 'c1', 'd3', 'f6', '0fa4', '0fad')) else (b'', b'\xf0')):
                yield case('int_directed', f'rmw_{code}', lock + bytes.fromhex(code), regs={3: ebx, 0: 0x87654321, 1: 5},
                           perms=perms)
    for code in ('8b03', '668b03', '8a03', 'ff33', 'f7 03 01000000'.replace(' ', '')):
        for ebx in (0x10FFD, 0x10FFE, 0x10FFF, 0x11FFD, 0x11FFF, 0x0FFFE):
            for perms in ((0x67, 0x67), (0x67, 0), (0, 0x67), (0x67, 0x65)):
                yield case('int_directed', f'cross_{code[:4]}', code, regs={3: ebx}, perms=perms)


def directed(rng):
    for g in (bcd, shifts, muldiv, lock_matrix, atomics, strings, stack, branches, lea, misc, rmw):
        yield from g(rng)


# ---------------------------------------------------------------------------------------------------
# shift16_rules (open question G8 and the 8/16-bit rotate counts)

def shift16(rng):
    pairs = [(0x1234, 0xABCD), (0x8001, 0x7FFE), (0xFFFF, 0x0001), (0x0001, 0x8000), (0x5A5A, 0xA5A5), (0xC3C3, 0x1F1F)]
    for op, name in ((0xA4, 'shld'), (0xAC, 'shrd')):
        for cnt in range(32):
            for dst, src in pairs:
                hi = rng.getrandbits(16) << 16
                for fl in (0x202, 0x203):
                    yield case('shift16_rules', f'{name}_r16_imm', bytes([0x66, 0x0F, op, 0xD8, cnt]), regs={0: hi | dst, 3: src | hi}, flags=fl)
                    yield case('shift16_rules', f'{name}_r16_cl', bytes([0x66, 0x0F, op + 1, 0xD8]), regs={0: hi | dst, 3: src, 1: cnt}, flags=fl)
                    yield case('shift16_rules', f'{name}_m16_imm', bytes([0x66, 0x0F, op, 0x1E, cnt]), regs={3: src, 6: 0x10100}, flags=fl,
                               patches=[(0x100, dst | 0xEEEE0000)])
                    yield case('shift16_rules', f'{name}_m16_cl', bytes([0x66, 0x0F, op + 1, 0x1E]), regs={3: src, 6: 0x10100, 1: cnt},
                               flags=fl, patches=[(0x100, dst | 0xEEEE0000)])
    for size, pfx, op in ((8, b'', 0xC0), (16, b'\x66', 0xC1)):
        for reg in range(8):
            for cnt in range(32):
                for v in (0x81, 0x8001, 0x5A, 0xC3C3, 0x7FFF):
                    for fl in (0x202, 0x203, 0xA03):
                        yield case('shift16_rules', f'shift{size}_{reg}_r', pfx + bytes([op, 0xC0 | reg << 3, cnt]), regs={0: 0xDEAD0000 | v}, flags=fl)
                    yield case('shift16_rules', f'shift{size}_{reg}_m', pfx + bytes([op, 0x06 | reg << 3, cnt]), regs={6: 0x10100},
                               flags=0x203, patches=[(0x100, 0xEEEE0000 | v)])


def selected(family, count, make, rng):
    """The cases of `make(rng, count)` that native_ext.select keeps, cached; the family's own generator is
    seeded with a tag drawn from the bundle's (deterministic for seed, count and model)."""
    tag = rng.getrandbits(64)
    def produce():
        rng = random.Random(f'{family}:{count}:{tag}')
        stats = collections.Counter(); out = []; batch = []
        for c in make(rng, count):
            batch.append(c)
            if len(batch) == 20000:
                out += select(batch, stats); batch = []
        out += select(batch, stats)
        return out, stats
    cases, stats = cached(family, [count, tag], produce)
    STATS[family] = stats
    return cases


def int_core(rng, count):
    yield from selected('int_core', count, lambda rng, n: int_core_candidates(rng, max(300, n * 28)), rng)


def int_directed(rng, count):
    yield from selected('int_directed', count, lambda rng, n: directed(rng) if n >= 10000 else
                        (c for k, c in enumerate(directed(rng)) if k % 50 == 0), rng)


def shift16_rules(rng, count):
    yield from selected('shift16_rules', count, lambda rng, n: shift16(rng) if n >= 10000 else
                        (c for k, c in enumerate(shift16(rng)) if k % 50 == 0), rng)


FAMILIES = [(int_core, ()), (int_directed, ()), (shift16_rules, ())]


# ---------------------------------------------------------------------------------------------------
# code16: a 16-bit code segment (the oracle's LDT: CS 07h based at the code page, IP 0100h; DS = ES 0Fh
# based at the arena, limit 1FFFh; SS, FS, GS flat 32-bit). Linux allows it to user processes through
# modify_ldt (CONFIG_MODIFY_LDT_SYSCALL, CONFIG_X86_16BIT; the oracle stops with an error, recorded as
# a failed campaign, where it is not available).

CODE16 = ['0107', '0300', '83471005', '810634127856', '660107', '670103', '2907', '3107', '8507', 'f617',
          'd1e0', 'c1e005', 'd3e0', 'd127', 'c02f03', 'd3c8', '660fa4d805', '0fa5d8', '0fa307', '0fbb07', '0fbc07',
          'f7e3', 'f7f3', 'f6f3', '66f7f3', 'f7fb', '0faf07', '6b070f', '69c33412',
          'a4', 'a5', 'f3a4', 'f3a5', '66a5', 'f366a5', 'aa', 'ab', 'f3ab', 'ac', 'ad', 'a6', 'a7', 'f3a6', 'ae', 'af',
          'f2ae', '67a4', '26a5', '36a4', '64ac', 'd7', '26d7',
          '50', '58', '60', '61', '6660', '6661', '9c', '9d', 'c8080000', 'c8040001', 'c9', '6a05', '683412', 'ff37',
          '8f07', '06', '0e', '16', '1e', '0fa0', '0fa8',
          '7405', '7505', '0f840500', 'e305', '67e305', 'e205', 'eb05', 'e90500', 'e80500', 'c3', 'c20400', 'ffd0',
          'ffe0', 'ff17', 'ff27', '66e805000000', '66c3',
          '0fb607', '0fbe07', '660fb707', '0fbf07', '98', '99', '6698', '6699', '0fc8', '660fc8', '86c4', '87d8', '9e', '9f',
          'f5', 'fd', 'fc', '6207', '666207', '63d8', '0fb507',
          'd907', 'dd1f', 'df07', 'db2f', 'd937', '66d937', 'dd37', '66dd37', 'd927', 'dd27', 'd93f', 'dd3f', '0fae07',
          '0fae17', '0fae1f', '0f1007', '0f1107', '660f6f07', '660f7f07', 'f30f7e07', '0f2807', '660f5807', 'c5f85807',
          'c5fc1007', 'c4e27d1807', '0f0d0f', '0f1807', '0fae3f']


def code16_cases(rng, count):
    reps = 16 if count >= 10000 else 2
    for code in CODE16:
        for k in range(reps):
            regs = {r: (rng.getrandbits(16) << 16) | rng.randrange(0x1F00) for r in (0, 2, 3, 5, 6, 7)}
            regs[1] = rng.choice((0, 1, 2, 5)) | (rng.getrandbits(16) << 16 if k % 2 else 0)
            regs[4] = 0x11800 - 4 * rng.randrange(16)
            if k % 4 == 0: regs[0] = 0x180 + 4 * rng.randrange(0x100)       # CALL/JMP AX: an IP in the INT3 filling
            sp_off = regs[4] - 0x10000
            flags = 0x202 | (rng.getrandbits(12) & 0x8D5) | (DF if k % 5 == 4 else 0)
            perms = rng.choice([(0x67, 0x67)] * 5 + [(0x67, 0x65), (0x65, 0x67), (0, 0x67)])
            patches = [(sp_off, 0x0180 | (0x0190 << 16)), ((regs[3] & 0xFFFF) & ~3, 0x01A0 | (0x01B0 << 16))]
            yield case('code16', f'c16_{code}', code, regs=regs, flags=flags, perms=perms, patches=patches)
    # random encodings in the 16-bit segment, single-stepped as in enc_fuzz (no fix-ups: refusals are counted)
    import native_fuzz
    from native_ext import windows_safe
    for _ in range(max(100, count // 2)):
        code, kind = native_fuzz.random_encoding(rng)
        code = code[:15]
        if not windows_safe(code): continue
        c = native_fuzz.inputs(rng)
        raw = record3(code, regs=c['regs'], xmm=c['xmm'], ymmh=c['ymmh'], mem=c['mem'], flags=c['flags'], mxcsr=c['mxcsr'],
                      permissions=c['permissions'], stack=c['stack'], cw=c['cw'], sw=c['sw'], tags=c['tags'], seed=c['seed'])
        m = meta3('code16', 'random_' + kind, code)
        und = undefined_flags(code, c['regs'])   # (decoded as 32-bit code: an approximation of the undefined flags)
        m['flags_mask'] = ARITH & ~und
        if und: m['flags_observe'] = und
        yield raw, m


def code16_mode(rng, count):
    """code16_cases with every record in mode 1 and marked (`code16`)."""
    for raw, m in code16_cases(rng, count):
        r = bytearray(raw)
        r[776 + 28] = 1
        yield bytes(r), dict(m, code16=True)


def code16(rng, count):
    yield from selected('code16', count, code16_mode, rng)


FAMILIES += [(code16, ())]
