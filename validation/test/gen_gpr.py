#!/usr/bin/env python3
"""'ext' family of gen.py for the general-purpose Zen 2 extensions (x86_32/X86/Ext/Gpr.lean).

`gen(g)` returns one instruction (bytes) for the ring-3 differential harness and sets g.fmask and
g.desc, or returns None. Forms (isa_forms.IMPLEMENTED, owner Gpr):
  POPCNT / LZCNT / TZCNT, MOVBE, CRC32, ADCX / ADOX, the VEX BMI1/BMI2 instructions (including
  VEX.L = 1, VEX.W = 1, every pp and ModRM.reg value of their opcodes), PREFETCH/PREFETCHW (memory and
  #UD register forms), RDPID, and the #UD/#GP forms of RDRAND/RDSEED (memory form, F2/F3), RDPMC
  (CPL 3, CR4.PCE = 0), MONITOR/MWAIT (CPL 3) and MCOMMIT (EFER.MCOMMIT = 0).
Not generated (QEMU cannot be compared; covered by test/sys/t_gpr.c and test/gpr_ref.py):
  RDRAND/RDSEED/RDTSCP/RDPRU results (random or time values), CLZERO, MONITORX, MWAITX, RDPRU (not in
  TCG), WBNOINVD (TCG does not check CPL, like WBINVD), RDPID with a 66 prefix (TCG writes 16 bits;
  APM RDPID: operand-size prefixes do not apply), CLFLUSH/CLFLUSHOPT/CLWB (TCG makes no memory access,
  so neither segment, page-fault checks nor the accessed bit; APM CLFLUSH).
"""
import random
import struct

CF, PF, AF, ZF, SF, OF = 1, 4, 0x10, 0x40, 0x80, 0x800
ALL = 0xFFFFFFFF & ~0x10000

SEGS = [0x26, 0x36, 0x3E, 0x64, 0x65]


def r32():
    return random.getrandbits(32)


def value():
    """An interesting 32-bit operand value."""
    return random.choice([0, 1, 2, 3, 0x80000000, 0xFFFFFFFF, 0x7FFFFFFF, 0x8000, 0xFFFF, 0x10000,
                          1 << random.randint(0, 31), (1 << random.randint(0, 32)) - 1,
                          r32(), r32(), r32() & r32(), r32() | r32(), r32() & 0xFF, r32() & 0xFFFF])


def vex3(map_, pp, L, W, vvvv):
    """A three-byte VEX prefix for 32-bit mode (inverted R and X must be 1; inverted B random;
    vvvv[3] (inverted) random as well: it is ignored outside 64-bit mode)."""
    v = (~vvvv & 7) | (random.getrandbits(1) << 3 if random.random() < 0.2 else 8)
    return bytes([0xC4, 0xC0 | (random.getrandbits(1) << 5) | map_, (W << 7) | (v << 3) | (L << 2) | pp])


def regval(g, r, v):
    if r != 4 and r not in g.addr_regs:
        g.regs[r] = v


def legacy_prefixes(opsz_ok=True, rep=None):
    """Random 66/67/segment prefixes (and the mandatory prefix `rep`)."""
    p = []
    p66 = opsz_ok and random.random() < 0.3
    if p66:
        p.append(0x66)
    if random.random() < 0.1:
        p.append(0x67)
    if random.random() < 0.15:
        p.append(random.choice(SEGS))
    if random.random() < 0.03:
        p.append(0xF0)
    random.shuffle(p)
    if rep is not None:
        p.append(rep)          # the mandatory prefix closest to the opcode
    return bytes(p), p66, 0x67 in p


def modrm(g, a16, reg=None, mem=None):
    if mem is None:
        mem = random.random() < 0.5
    b, rm, _ = g.modrm(a16, reg, force_mem=mem, force_reg=not mem)
    return b, rm, (b[0] >> 6) != 3


def gen(g):
    kind = random.choice(['cnt', 'cnt', 'movbe', 'crc32', 'adx', 'bmi', 'bmi', 'bmi', 'bmi', 'misc'])
    fm = ALL
    if kind == 'cnt':
        op = random.choice([0xB8, 0xBC, 0xBD])
        pre, p66, a16 = legacy_prefixes(rep=0xF3)
        mr, rm, mem = modrm(g, a16)
        if not mem and random.random() < 0.5:
            regval(g, rm, random.choice([0, 0, 1, 0x8000, 0x80000000, 0x10000, value()]))
        insn = pre + bytes([0x0F, op]) + mr
        if op != 0xB8:
            fm &= ~(OF | SF | AF | PF)
    elif kind == 'movbe':
        op = random.choice([0xF0, 0xF1])
        pre, p66, a16 = legacy_prefixes()
        if random.random() < 0.05:
            pre += b'\xF3'        # #UD
        mr, rm, mem = modrm(g, a16, mem=random.random() < 0.9)
        insn = pre + bytes([0x0F, 0x38, op]) + mr
    elif kind == 'crc32':
        op = random.choice([0xF0, 0xF1])
        pre, p66, a16 = legacy_prefixes(rep=0xF2)
        mr, rm, mem = modrm(g, a16)
        insn = pre + bytes([0x0F, 0x38, op]) + mr
    elif kind == 'adx':
        mp = random.choice([0x66, 0xF3, 0x66, 0xF3, None, 0xF2])
        pre, _, a16 = legacy_prefixes(opsz_ok=mp != 0x66, rep=mp)
        if mp == 0x66 and random.random() < 0.2:
            pre = b'\x66' + pre
        mr, rm, mem = modrm(g, a16)
        insn = pre + bytes([0x0F, 0x38, 0xF6]) + mr
    elif kind == 'bmi':
        insn, fm = gen_bmi(g)
    else:
        insn, fm = gen_misc(g)
    if insn is None or len(insn) > 15:
        return None
    g.fmask = fm
    g.desc = 'ext-gpr:%s' % insn.hex()
    return insn


# (map, opcode, pp) of the BMI instructions; undefined pp/reg combinations are generated as well
BMI = [(2, 0xF2, 0), (2, 0xF3, 0), (2, 0xF5, 0), (2, 0xF5, 2), (2, 0xF5, 3), (2, 0xF6, 3),
       (2, 0xF7, 0), (2, 0xF7, 1), (2, 0xF7, 2), (2, 0xF7, 3), (3, 0xF0, 3)]


def gen_bmi(g):
    if random.random() < 0.1:
        # an undefined form of these opcodes (other pp; VEX.0F38 F4 is unassigned)
        map_, op = random.choice([(2, 0xF2), (2, 0xF3), (2, 0xF5), (2, 0xF6), (3, 0xF0), (2, 0xF4)])
        pp = random.randint(0, 3)
        if (map_, op, pp) in BMI:
            return None, ALL
    else:
        map_, op, pp = random.choice(BMI)
    L = 1 if random.random() < 0.05 else 0
    W = random.getrandbits(1)
    vvvv = random.randint(0, 7)
    a16 = random.random() < 0.1
    pre = (b'\x67' if a16 else b'') + (bytes([random.choice(SEGS)]) if random.random() < 0.15 else b'')
    reg = None
    if (map_, op) == (2, 0xF3) and random.random() < 0.9:
        reg = random.randint(1, 3)
    mr, rm, mem = modrm(g, a16, reg=reg)
    reg = (mr[0] >> 3) & 7
    insn = pre + vex3(map_, pp, L, W, vvvv) + bytes([op]) + mr
    if map_ == 3:
        insn += bytes([random.choice([0, 1, 31, 32, 33, random.getrandbits(8)])])
    # interesting control operands in vvvv (BEXTR, BZHI, shift counts) and EDX (MULX)
    if op in (0xF7, 0xF5) and pp == 0:
        regval(g, vvvv, random.choice([value(), random.randint(0, 40) | (random.randint(0, 40) << 8),
                                       r32() & 0xFFFF, random.randint(0, 0x30)]))
    elif op == 0xF7:
        regval(g, vvvv, random.choice([value(), random.randint(0, 70)]))
    elif op == 0xF5:
        regval(g, vvvv, value())
    fm = ALL
    if op in (0xF2, 0xF3, 0xF5) and pp == 0:
        fm &= ~(AF | PF)        # ANDN, BLSx, BZHI
    if op == 0xF7 and pp == 0:
        fm &= ~(SF | AF | PF)   # BEXTR
    return insn, fm


def gen_misc(g):
    k = random.choice(['prefetch', 'prefetch', 'rdrand_ud', 'rdpid', 'rdpmc', 'monitor', 'mcommit', 'clflush'])
    a16 = random.random() < 0.1
    if k == 'prefetch':
        pre, _, a16 = legacy_prefixes()
        if random.random() < 0.1:
            pre += bytes([random.choice([0xF2, 0xF3])])
        mr, _, _ = modrm(g, a16, mem=random.random() < 0.85)
        return pre + b'\x0f\x0d' + mr, ALL
    if k == 'rdrand_ud':
        # memory forms, F2/F3 for RDRAND, F2 for RDSEED, LOCK: #UD
        reg = random.choice([6, 7])
        mem = random.random() < 0.5
        mp = None if mem else (random.choice([0xF2, 0xF3]) if reg == 6 else 0xF2)
        pre, _, a16 = legacy_prefixes(rep=mp)
        if mp is None and not mem:
            pre = b'\xF0' + pre
        mr, _, _ = modrm(g, a16, reg=reg, mem=mem)
        return pre + b'\x0f\xc7' + mr, ALL
    if k == 'rdpid':
        pre, _, a16 = legacy_prefixes(opsz_ok=False, rep=0xF3)
        mr, _, _ = modrm(g, a16, reg=7, mem=random.random() < 0.1)
        return pre + b'\x0f\xc7' + mr, ALL
    if k == 'rdpmc':
        regval(g, 1, random.choice([0, 1, 3, 4, 6, r32()]))
        pre, _, _ = legacy_prefixes()
        return pre + b'\x0f\x33', ALL
    if k == 'monitor':
        pre, _, _ = legacy_prefixes()
        regval(g, 1, random.choice([0, 0, 1, 2]))
        return pre + bytes([0x0F, 0x01, random.choice([0xC8, 0xC9])]), ALL
    if k == 'clflush':
        # CLFLUSH (/7), 66: CLFLUSHOPT (/7), CLWB (/6); TCG makes no memory access, so only with
        # paging off (no #PF, no accessed bit)
        g.no_paging = True
        reg, mp = random.choice([(7, None), (7, 0x66), (6, 0x66)])
        pre, _, a16 = legacy_prefixes(opsz_ok=False, rep=mp)
        mr, _, _ = modrm(g, a16, reg=reg, mem=True)
        return pre + b'\x0f\xae' + mr, ALL
    # MCOMMIT: F3 0F 01 FA, #UD while EFER.MCOMMIT = 0
    pre, _, _ = legacy_prefixes(rep=0xF3)
    return pre + b'\x0f\x01\xfa', ALL
