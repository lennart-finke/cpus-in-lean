#!/usr/bin/env python3
"""'ext' family generator for the Sse forms of isa_forms.IMPLEMENTED (x86_32/X86/Ext/Sse.lean):
SSE3, SSSE3 (MMX and XMM forms), SSE4.1, SSE4.2 and SSE4a, legacy encodings.

`ext(g, form)` returns the instruction bytes of a random instance of `form` (a Form row) and sets up
`g` (gen.Gen): registers for implicit operands (PCMPESTRx lengths in EAX/EDX), a description, and,
for floating-point instructions whose result depends on which of two NaN operands is returned (HADDPx,
HSUBPx, ADDSUBPx, DPPS, DPPD), `g.seed`: a data seed whose XMM pattern and memory operand have at
most one NaN input (none for DPPS/DPPD, whose additions combine all products). Hardware returns the
first operand of two NaNs (SDM vol. 1, table 4-7; AMD APM vol. 4 DPPS), TCG the one with the larger
significand, as the existing SSE tests already exclude (sys/t_simd.c, denan).

Memory operands use an absolute disp32 address in the data area (16-byte aligned three times in
four, sometimes next to the page boundary at 0x9000) or, for non-FP forms, gen.Gen.modrm's random
addressing; register-only and memory-only forms are sometimes generated with the other kind of
operand to check their #UD.
"""
import random

DATA, DATA_SIZE = 0x8000, 8192
PP_BYTE = {0: b'', 1: b'\x66', 2: b'\xf3', 3: b'\xf2'}

# (map, opcode) of forms whose NaN choice matters (see above): value = max NaN inputs
NAN_SENSITIVE = {(1, 0x7C): 1, (1, 0x7D): 1, (1, 0xD0): 1, (3, 0x40): 0, (3, 0x41): 0}
# memory-only and register-only forms (map, pp, opcode)
MEM_ONLY = {(1, 3, 0xF0), (1, 2, 0x2B), (1, 3, 0x2B), (2, 1, 0x2A)}
REG_ONLY = {(1, 1, 0x78), (1, 3, 0x78), (1, 1, 0x79), (1, 3, 0x79)}
# ModRM.rm names a general register (PEXTRB/W/D, EXTRACTPS to r32; PINSRB/D from r32)
GPR_RM = {(3, 1, 0x14), (3, 1, 0x15), (3, 1, 0x16), (3, 1, 0x17), (3, 1, 0x20), (3, 1, 0x22)}
# size in bytes of the memory operand of each FP-sensitive form
MEM_SIZE = {(1, 1, 0x7C): 16, (1, 3, 0x7C): 16, (1, 1, 0x7D): 16, (1, 3, 0x7D): 16, (1, 1, 0xD0): 16,
            (1, 3, 0xD0): 16, (3, 1, 0x40): 16, (3, 1, 0x41): 16}


def xorshift(x):
    x ^= (x << 13) & 0xFFFFFFFF; x ^= x >> 17; x ^= (x << 5) & 0xFFFFFFFF
    return x


def words(seed, n):
    """The first n 32-bit words of xorshift32 from seed (harness.c: data area, vec_pattern)."""
    out, s = [], seed
    for _ in range(n):
        s = xorshift(s)
        out.append(s)
    return out


def nan32(w):
    return (w >> 23) & 0xFF == 0xFF and w & 0x7FFFFF != 0


def nan64(lo, hi):
    return (hi >> 20) & 0x7FF == 0x7FF and ((hi & 0xFFFFF) or lo)


def count_nans(ws, double):
    if double:
        return sum(1 for k in range(0, len(ws), 2) if nan64(ws[k], ws[k + 1]))
    return sum(1 for w in ws if nan32(w))


def pick_seed(reg, rm, addr, double, max_nans):
    """A data seed whose XMM`reg` and XMM`rm` (or the 16 bytes at `addr`) hold at most max_nans
    NaN lanes in total."""
    while True:
        seed = random.getrandbits(32) | 1
        pat = words(seed ^ 0xA5A5A5A5, 32)
        a = pat[4 * reg:4 * reg + 4]
        if addr is None:
            b = pat[4 * rm:4 * rm + 4]
        else:
            off = addr - DATA
            if off % 4:
                return None   # unaligned: the generator only uses dword-aligned absolute addresses here
            data = words(seed, off // 4 + 4)
            b = data[off // 4:off // 4 + 4]
        if count_nans(a, double) + count_nans(b, double) <= max_nans:
            return seed


def abs_addr(size):
    """A data-area address: 16-byte aligned 3/4 of the time, near the 0x9000 page boundary 1/10."""
    if random.random() < 0.1:
        return DATA + 0x1000 - random.choice([16, 12, 8, 4, 0])
    a = DATA + random.randint(0x100, DATA_SIZE - 0x100)
    return a & ~15 if random.random() < 0.75 else a & ~3


def interesting_len():
    return random.choice([0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFF0,
                          random.randint(0, 40), -random.randint(1, 40) & 0xFFFFFFFF, random.getrandbits(32)])


def ext(g, form):
    """Instruction bytes of a random instance of `form` (owner 'Sse'), or None."""
    map_, pp, op = form.map, form.pp, random.choice(form.ops)
    key = (map_, pp, op)
    esc = {1: b'\x0f', 2: b'\x0f\x38', 3: b'\x0f\x3a'}[map_]
    pre = PP_BYTE[pp]
    if pp in (2, 3) and random.random() < 0.15:
        pre = random.choice([b'\x66' + pre, pre + b'\x66'])   # F2/F3 take precedence over 66
    seg = b''
    if random.random() < 0.1:
        # (no CS override: TCG does not check the writability of CS for stores, as gen.py's integer
        # generator also avoids)
        seg = bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])])
    mem = random.random() < 0.4
    if key in MEM_ONLY:
        mem = random.random() < 0.95
    if key in REG_ONLY:
        mem = random.random() < 0.05
    reg = random.randint(0, 7)
    rm = random.randint(0, 7)
    if key in GPR_RM and rm == 4:
        rm = 0                                 # keep ESP
    if key == (1, 1, 0x78) and random.random() < 0.9:
        reg = 0                                # EXTRQ xmm, imm8, imm8 is 66 0F 78 /0
    addr = None
    sensitive = (map_, op) in NAN_SENSITIVE
    if mem:
        # absolute addresses for FP forms (NaN check) and PCMPxSTRx (EAX/EDX are lengths)
        if sensitive or (map_ == 3 and op in (0x60, 0x61, 0x62, 0x63)) or random.random() < 0.6:
            addr = abs_addr(MEM_SIZE.get(key, 16))
            modrm = bytes([(reg << 3) | 5]) + addr.to_bytes(4, 'little')
        else:
            modrm, _, _ = g.modrm(False, reg, force_mem=True)
    else:
        modrm = bytes([0xC0 | (reg << 3) | rm])
    if map_ == 3:
        imm = bytes([random.getrandbits(8)])
    elif key in ((1, 1, 0x78), (1, 3, 0x78)):
        imm = bytes([random.choice([random.randint(0, 64), random.getrandbits(8)]),
                     random.choice([random.randint(0, 64), random.getrandbits(8)])])
    else:
        imm = b''
    if map_ == 3 and op in (0x60, 0x61, 0x62, 0x63):
        g.regs[0] = interesting_len()
        g.regs[2] = interesting_len()
    if sensitive:
        double = pp == 1 and op != 0x40
        seed = pick_seed(reg, rm, addr, double, NAN_SENSITIVE[(map_, op)])
        if seed is None:
            return None
        g.seed = seed
    insn = seg + pre + esc + bytes([op]) + modrm + imm
    if len(insn) > 15:
        return None
    g.desc = 'ext-%s:%s' % (form.feature, insn.hex())
    return insn
