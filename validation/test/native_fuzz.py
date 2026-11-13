"""Native family `enc_fuzz`: random ENCODING fuzz over the whole opcode space (bundle format v3; the
safety design is in FP-HARDWARE.md, "The extended bundle").

Systematic part: every (map, mandatory prefix, opcode, ModRM.mod in {memory, register}, ModRM.reg) of
the one-byte, 0F, 0F 38 and 0F 3A maps once (32,768), and every (VEX map 1..3, VEX.pp, VEX.L, VEX.W,
opcode, mod, VEX.vvvv in {1111b, another}) once (49,152); random rest: legacy prefix sequences (66 67 F2
F3 F0 and the six segment overrides, repeated, redundant, in any order, up to fourteen), every map,
2- and 3-byte VEX with every mmmmm/pp/L/W/vvvv/B, EVEX (62) and XOP (8F) forms, 3DNow! (0F 0F),
ModRM/SIB/displacement variety with 32- and 16-bit addressing, and encodings padded to 15 and 16 bytes.
Every byte after the opcode that the model does not consume stays in the record (the processor may).

Safety of the inputs (whatever the processor decodes):
* EFLAGS.TF = 1 in every case: the processor stops after one instruction (#DB), whatever its length,
  so no further bytes run (the oracle's validation refuses trailing bytes without TF);
* every GPR is below 0x12000 (an arena pointer or a small value), so base + 8 x index < 0xA2000, and no
  four bytes of the instruction (and its 0xCC filling) form a dword in [0x50000, 0x1200000): no
  displacement or immediate any decoding could use reaches the oracle's image at 1 MiB; every XMM/YMM
  dword is in [-0x4000, 0x4000), so no gather index reaches it either;
* ECX (a REP count) is at most 63; with TF a REP instruction runs one iteration anyway;
* candidates the oracle's validation refuses (software interrupts, SYSCALL, far transfers, segment
  loads, near transfers out of the code page's INT3 filling) or whose model result is not observable
  or accesses memory outside the low 256 KiB are dropped by native_ext.select, counted by reason.
"""
import collections
import random
import struct

import fp_cases
from native_ext import record3, meta3, layout, windows_safe, select, cached, STATS, ARITH
from native_flags import undefined_flags

FAMILY = 'enc_fuzz'
SEG = [0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65]
LEGACY = SEG + [0x66, 0x67, 0xF0, 0xF2, 0xF3]
PP = [b'', b'\x66', b'\xf3', b'\xf2']
ESC = [b'', b'\x0f', b'\x0f\x38', b'\x0f\x3a']
REL8 = set(range(0x70, 0x80)) | {0xE0, 0xE1, 0xE2, 0xE3, 0xEB}
RELZ = {0xE8, 0xE9} | set(range(0x180, 0x190))


def small_dword(rng):
    return rng.randrange(-0x4000, 0x4000) & 0xFFFFFFFF


def inputs(rng):
    """Register, vector, x87, MXCSR and memory inputs within the safety bounds above."""
    regs = {}
    for k in range(8):
        if k == 4:   # ESP: in the 64-byte patch (its dwords 4..11 are code-page pointers for RET) or the arena
            regs[k] = 0x10010 + 4 * rng.randrange(8) if rng.random() < 0.3 else 0x10100 + 4 * rng.randrange(0x7a0)
        elif k == 1:
            regs[k] = rng.choice([0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 33, 63, rng.randrange(64)])
        elif rng.random() < 0.65:
            regs[k] = (0x10000 + rng.randrange(0x2000)) & ~rng.choice([0, 1, 3, 7, 15, 63])
        else:
            regs[k] = rng.randrange(0x100)
    xmm = [small_dword(rng) | small_dword(rng) << 32 for _ in range(32)]
    ymmh = [small_dword(rng) | small_dword(rng) << 32 for _ in range(16)]
    mem = bytearray(rng.getrandbits(8) for _ in range(64))
    for k in range(4, 12):   # code-page pointers into the INT3 filling, after the instruction
        struct.pack_into('<I', mem, 4 * k, 0x20180 + 4 * rng.randrange(0x200))
    flags = 0x302 | (rng.getrandbits(12) & 0x4D5) | (0x40000 if rng.random() < 0.15 else 0)
    mxcsr = (rng.getrandbits(6) << 7) | (rng.randrange(4) << 13) | rng.choice((0, 0x40, 0x8000, 0x8040)) | rng.getrandbits(6) * (rng.random() < 0.2)
    perms = rng.choice([(0x67, 0x67)] * 6 + [(0x67, 0x65), (0x67, 0), (0x65, 0x67), (0, 0x67)])
    stack = [(rng.getrandbits(64), rng.randrange(65536)) if rng.random() < 0.5 else rng.choice(fp_cases.VALUES)
             for _ in range(8)]
    return dict(regs=regs, xmm=xmm, ymmh=ymmh, mem=bytes(mem), flags=flags, mxcsr=mxcsr, permissions=perms,
                stack=stack, cw=0x40 | rng.getrandbits(6) | rng.randrange(4) << 8 | rng.randrange(4) << 10,
                sw=rng.randrange(8) << 11, tags=rng.choice((255, 0, rng.randrange(256))), seed=rng.getrandbits(32) | 1)


def modrm_bytes(rng, mod, reg, a16=False):
    """ModRM (+ SIB + displacement) with the given mod (3 = register) and reg."""
    rm = rng.randrange(8)
    out = bytes([mod << 6 | reg << 3 | rm])
    if mod == 3: return out
    if a16:
        if mod == 0 and rm == 6: return out + struct.pack('<H', rng.randrange(0x10000))
        return out + (bytes([rng.getrandbits(8)]) if mod == 1 else struct.pack('<H', rng.getrandbits(16)) if mod == 2 else b'')
    if rm == 4: out += bytes([rng.getrandbits(8)])
    if mod == 1: out += bytes([rng.getrandbits(8)])
    elif mod == 2 or (mod == 0 and (rm == 5 or (rm == 4 and out[1] & 7 == 5))): out += struct.pack('<I', disp32(rng))
    return out


def disp32(rng):
    return rng.choice([rng.randrange(-0x800, 0x800) & 0xFFFFFFFF, 0x10000 + rng.randrange(0x2000),
                       rng.randrange(0x40000), rng.getrandbits(32)])


def fix(code, rng, case):
    """Make the instruction safe and runnable where a byte pattern is not: relative transfers get a
    target in the code page's INT3 filling, RET a stack pointer at the code pointers of the patch, an
    indirect JMP/CALL r/m such a pointer (register: the register holds a code-page pointer; memory: [reg]
    at the patch), and no dword window reaches the oracle's image (bytes re-drawn)."""
    code = bytearray(code)
    for _ in range(20):
        n, op, pfx, at, disp, imm = layout(code)
        if n <= 15 and op in REL8 | RELZ and imm is not None and imm[0] < len(code):
            nxt = 0x20100 + n
            t = 0x20100 + n + rng.randrange(0x40) if rng.random() < 0.7 else 0x20000 + rng.randrange(0x100)
            rel = t - nxt
            o, size = imm
            for k in range(size):
                if o + k < len(code): code[o + k] = (rel >> (8 * k)) & 0xFF
        if n <= 15 and op in (0xC2, 0xC3):
            case['regs'][4] = 0x10010 + 4 * rng.randrange(8)
        if n <= 15 and op == 0xFF and at is not None and at < len(code) and (code[at] >> 3 & 7) in (2, 4):
            if code[at] >> 6 == 3:
                case['regs'][code[at] & 7] = 0x20180 + 4 * rng.randrange(0x200)
            elif at < len(code):
                # [EBX] (or [BX] with 16-bit addressing: below the arena, a certain #PF), without SIB/disp
                a16 = 0x67 in code[:pfx]
                end = disp[0] + disp[1] if disp else at + 1 + (0 if a16 or code[at] & 7 != 4 else 1)
                code[at:end] = bytes([(code[at] & 0x38) | (7 if a16 else 3)])
                case['regs'][3] = 0x10010 + 4 * rng.randrange(8)
        if windows_safe(code): return bytes(code[:15])
        # re-draw the bytes of a window that could be taken as an address of the oracle image
        b = bytes(code) + b'\xcc' * 3
        for i in range(len(b) - 3):
            if 0x50000 <= int.from_bytes(b[i:i + 4], 'little') < 0x1200000:
                j = min(i + 3, len(code) - 1)
                code[j] = rng.getrandbits(8)
                break
    return None


def build(rng, code, name, **extra):
    case = inputs(rng)
    code = fix(code, rng, case)
    if code is None or not code: return None
    raw = record3(code, regs=case['regs'], xmm=case['xmm'], ymmh=case['ymmh'], mem=case['mem'],
                  flags=case['flags'], mxcsr=case['mxcsr'], permissions=case['permissions'], stack=case['stack'],
                  cw=case['cw'], sw=case['sw'], tags=case['tags'], seed=case['seed'])
    m = meta3(FAMILY, name, code, **extra)
    n, op, pfx, at, disp, imm = layout(code)
    und = undefined_flags(code, case['regs'])
    m['flags_mask'] = ARITH & ~und
    if und: m['flags_observe'] = und
    return raw, m


def systematic(rng, stride=1):
    k = 0
    for mp in range(4):
        for pp in range(4):
            for op in range(256):
                for mem in (True, False):
                    for reg in range(8):
                        k += 1
                        if k % stride: continue
                        body = PP[pp] + ESC[mp] + bytes([op]) + modrm_bytes(rng, rng.randrange(3) if mem else 3, reg)
                        body += bytes(rng.getrandbits(8) for _ in range(4))
                        c = build(rng, body[:15], f'map{mp}', pp=pp, op=op, mem=mem, reg=reg)
                        if c: yield c
    for mp in (1, 2, 3):
        for pp in range(4):
            for L in (0, 1):
                for W in (0, 1):
                    for op in range(256):
                        for mem in (True, False):
                            for other in (False, True):
                                k += 1
                                if k % stride: continue
                                vvvv = 15 if not other else rng.randrange(15)   # the encoded (inverted) field
                                b1 = 0xE0 | mp if rng.random() < 0.5 else 0xC0 | mp   # R = X = 1; B either
                                body = bytes([0xC4, b1, W << 7 | vvvv << 3 | L << 2 | pp, op])
                                body += modrm_bytes(rng, rng.randrange(3) if mem else 3, rng.randrange(8))
                                body += bytes(rng.getrandbits(8) for _ in range(2))
                                c = build(rng, body[:15], f'vex{mp}', pp=pp, L=L, W=W, op=op, mem=mem,
                                          vvvv='1111' if not other else 'other')
                                if c: yield c


def random_encoding(rng):
    """(bytes, kind) of one random encoding."""
    npfx = rng.choice([0, 0, 0, 1, 1, 2, 3, rng.randrange(15)])
    pfx = bytes(rng.choice(LEGACY) for _ in range(npfx))
    a16 = 0x67 in pfx
    kind = rng.choice(['one', 'one', '0f', '0f', '0f38', '0f3a', 'vex2', 'vex3', 'vex3', 'evex', 'xop', '3dnow', 'pad'])
    mod = rng.choice([0, 1, 2, 3, 3])
    mrm = lambda: modrm_bytes(rng, mod, rng.randrange(8), a16)
    tail = bytes(rng.getrandbits(8) for _ in range(rng.randrange(6)))
    if kind == 'one': body = bytes([rng.getrandbits(8)]) + mrm()
    elif kind == '0f': body = bytes([0x0F, rng.getrandbits(8)]) + mrm()
    elif kind == '0f38': body = bytes([0x0F, 0x38, rng.getrandbits(8)]) + mrm()
    elif kind == '0f3a': body = bytes([0x0F, 0x3A, rng.getrandbits(8)]) + mrm()
    elif kind == 'vex2': body = bytes([0xC5, 0x80 | rng.getrandbits(7), rng.getrandbits(8)]) + mrm()
    elif kind == 'vex3':
        body = bytes([0xC4, 0xC0 | rng.getrandbits(6), rng.getrandbits(8), rng.getrandbits(8)]) + mrm()
    elif kind == 'evex':   # 62 P0 P1 P2: P0 bits 7:6 = 11 (the BOUND register form on Zen 2)
        body = bytes([0x62, 0xC0 | rng.getrandbits(6), rng.getrandbits(8), rng.getrandbits(8), rng.getrandbits(8)]) + mrm()
    elif kind == 'xop':
        body = bytes([0x8F, (rng.getrandbits(3) << 5) | rng.choice([8, 9, 10, rng.randrange(32)]), rng.getrandbits(8),
                      rng.getrandbits(8)]) + mrm()
    elif kind == '3dnow': body = bytes([0x0F, 0x0F]) + mrm() + bytes([rng.getrandbits(8)])
    else:   # padded with prefixes to a decoded length of 15 or 16 (the length limit)
        inner = rng.choice([bytes([0x0F, 0x38, rng.getrandbits(8)]), bytes([0x0F, 0x3A, rng.getrandbits(8)]),
                            bytes([rng.getrandbits(8)]), bytes([0x0F, rng.getrandbits(8)])]) + mrm() + tail
        n = layout(inner)[0]
        want = rng.choice([14, 15, 16, 17])
        pad = max(0, want - n)
        return bytes(rng.choice(LEGACY) for _ in range(pad)) + inner, f'pad{want}'
    return pfx + body + tail, kind


def candidates(rng, count):
    stride = 1 if count >= 10000 else max(1, 10000 // max(count, 1) * 4)
    yield from systematic(rng, stride)
    for _ in range(max(100, count * 11)):
        code, kind = random_encoding(rng)
        c = build(rng, code[:15], 'random_' + kind, prefixes=sum(1 for b in code[:15] if b in LEGACY))
        if c: yield c


def enc_fuzz(rng_unused, count):
    """The selected cases (native_ext.select), deterministic for (count, model)."""
    def produce():
        rng = random.Random(f'enc_fuzz:{count}')
        stats = collections.Counter(); out = []; batch = []
        for c in candidates(rng, count):
            batch.append(c)
            if len(batch) == 20000:
                out += select(batch, stats); batch = []
        out += select(batch, stats)
        stats['candidates'] = sum(v for k, v in stats.items() if k != 'candidates')
        return out, stats
    cases, stats = cached(FAMILY, count, produce)
    STATS[FAMILY] = stats
    yield from cases


FAMILIES = [(enc_fuzz, ())]
