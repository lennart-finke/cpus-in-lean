#!/usr/bin/env python3
"""Generate random single-instruction test vectors for differential testing against QEMU.

Each vector: instruction bytes, initial GPRs/EFLAGS/data-segment selectors, a seed for the
4 KiB data area (xorshift32) and up to two 32-bit patches into it. Alongside vectors.bin a
meta file records, per vector, the EFLAGS bits that are architecturally defined after the
instruction (undefined flags are masked in the comparison) and a short description.

Layout shared with the harness and the Lean runner:
  DATA = 0x8000 (4 KiB), CODE = 0x20000 (512 B, instruction at +256, rest filled with INT3)
"""
import random, struct, sys

DATA, DATA_SIZE = 0x8000, 8192
CODE, INSN_OFF, CODE_SIZE = 0x20000, 256, 512
CF, PF, AF, ZF, SF, OF = 1, 4, 0x10, 0x40, 0x80, 0x800
ARITH = CF | PF | AF | ZF | SF | OF
ALL = 0xFFFFFFFF & ~0x10000  # RF is never compared

SELECTORS = [0, 0x1B, 0x23, 0x2B, 0x33, 0x3B, 0x4B, 0x53, 0x5B, 0x63, 0x6B, 0x40, 0x08, 0x10,
             0x23 | 4, 0x70, 0xFFFF]

# (imm kind, has modrm) for the one-byte map; None = not generated
def info1(b):
    if b < 0x40:
        lo = b & 7
        if lo < 4: return ('', True)
        if lo == 4: return ('ib', False)
        if lo == 5: return ('iz', False)
        return ('', False)
    if 0x40 <= b < 0x60: return ('', False)
    if 0x70 <= b <= 0x7F: return ('rel8', False)
    if 0x84 <= b <= 0x8F: return ('', True)
    if 0xB0 <= b <= 0xB7: return ('ib', False)
    if 0xB8 <= b <= 0xBF: return ('iz', False)
    if 0xD0 <= b <= 0xD3: return ('', True)
    if 0xE0 <= b <= 0xE3: return ('rel8', False)
    if 0xE4 <= b <= 0xE7: return ('ib', False)
    t = {0x60: ('', False), 0x61: ('', False), 0x62: ('', True), 0x63: ('', True),
         0x68: ('iz', False), 0x69: ('iz', True), 0x6A: ('ib', False), 0x6B: ('ib', True),
         0x6C: ('', False), 0x6D: ('', False), 0x6E: ('', False), 0x6F: ('', False),
         0x80: ('ib', True), 0x81: ('iz', True), 0x82: ('ib', True), 0x83: ('ib', True),
         0x90: ('', False), 0x91: ('', False), 0x92: ('', False), 0x93: ('', False), 0x94: ('', False),
         0x95: ('', False), 0x96: ('', False), 0x97: ('', False), 0x98: ('', False), 0x99: ('', False),
         0x9C: ('', False), 0x9D: ('', False), 0x9E: ('', False), 0x9F: ('', False),
         0xA0: ('moffs', False), 0xA1: ('moffs', False), 0xA2: ('moffs', False), 0xA3: ('moffs', False),
         0xA4: ('', False), 0xA5: ('', False), 0xA6: ('', False), 0xA7: ('', False),
         0xA8: ('ib', False), 0xA9: ('iz', False), 0xAA: ('', False), 0xAB: ('', False),
         0xAC: ('', False), 0xAD: ('', False), 0xAE: ('', False), 0xAF: ('', False),
         0xC0: ('ib', True), 0xC1: ('ib', True), 0xC2: ('iw', False), 0xC3: ('', False),
         0xC4: ('', True), 0xC5: ('', True), 0xC6: ('ib', True), 0xC7: ('iz', True),
         0xC8: ('enter', False), 0xC9: ('', False), 0xD4: ('ib', False), 0xD5: ('ib', False),
         0xD6: ('', False), 0xD7: ('', False), 0xE8: ('rel', False), 0xE9: ('rel', False),
         0xEB: ('rel8', False), 0xEC: ('', False), 0xED: ('', False), 0xEE: ('', False), 0xEF: ('', False),
         0xF4: ('', False), 0xF5: ('', False), 0xF6: ('grp3', True), 0xF7: ('grp3', True),
         0xF8: ('', False), 0xF9: ('', False), 0xFA: ('', False), 0xFB: ('', False), 0xFC: ('', False),
         0xFD: ('', False), 0xFE: ('', True), 0xFF: ('', True)}
    return t.get(b)

def info2(b):
    if b in (0x00, 0x01, 0x02, 0x03) or 0x18 <= b <= 0x1F or 0x20 <= b <= 0x23 or 0x40 <= b <= 0x4F \
       or 0x90 <= b <= 0x9F:
        return ('', True)
    if 0x80 <= b <= 0x8F: return ('rel', False)
    if 0xC8 <= b <= 0xCF: return ('', False)
    # 0F 08 INVD / 0F 09 WBINVD omitted: QEMU executes them at CPL 3 instead of raising #GP
    t = {0x06: ('', False), 0x0B: ('', False),
         0x30: ('', False), 0x32: ('', False),
         0xA0: ('', False), 0xA1: ('', False), 0xA8: ('', False), 0xA9: ('', False),
         0xA3: ('', True), 0xA4: ('ib', True), 0xA5: ('', True), 0xAB: ('', True), 0xAC: ('ib', True),
         0xAD: ('', True), 0xAF: ('', True), 0xB0: ('', True), 0xB1: ('', True), 0xB2: ('', True),
         0xB3: ('', True), 0xB4: ('', True), 0xB5: ('', True), 0xB6: ('', True), 0xB7: ('', True),
         0xB9: ('', True), 0xBA: ('ib', True), 0xBB: ('', True), 0xBC: ('', True), 0xBD: ('', True),
         0xBE: ('', True), 0xBF: ('', True), 0xC0: ('', True), 0xC1: ('', True), 0xC7: ('', True),
         0xFF: ('', True)}
    return t.get(b)

OPS1 = [b for b in range(256) if info1(b) is not None and b not in (0x0F, 0x26, 0x2E, 0x36, 0x3E)]
OPS2 = [b for b in range(256) if info2(b) is not None]
CONTROL = {0x70 + i for i in range(16)} | {0xE0, 0xE1, 0xE2, 0xE3, 0xE8, 0xE9, 0xEB, 0xC2, 0xC3}
STRING = set(range(0xA4, 0xB0)) - {0xA8, 0xA9} | {0x6C, 0x6D, 0x6E, 0x6F}

def r32(): return random.getrandbits(32)

def interesting32():
    return random.choice([0, 1, 2, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF, 0x10000,
                          0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, r32(), r32() & 0xFF,
                          r32() & 0xFFFF, -random.randint(1, 300) & 0xFFFFFFFF])

def ptr():
    if random.random() < 0.1:   # near the page boundary at 0x9000
        return DATA + 0x1000 + random.randint(-12, 4)
    return DATA + random.randint(0x300, 0xD00)

def code_target(length):
    """A code buffer offset outside the instruction itself."""
    while True:
        t = random.randint(32, CODE_SIZE - 32)
        if not (INSN_OFF <= t < INSN_OFF + length + 1):
            return t

class Gen:
    def __init__(self):
        self.regs = [interesting32() for _ in range(8)]
        self.regs[4] = (DATA + random.randint(0x600, 0xA00)) & ~3   # ESP
        self.eflags = 0x2 | (r32() & (ARITH | 0x400)) | (0x200 if random.random() < 0.5 else 0) \
            | (0x40000 if random.random() < 0.2 else 0) | (0x100 if random.random() < 0.1 else 0)
        self.sel = [0x23, 0x23, 0x23, 0x23]
        self.patches = []
        self.fmask = ALL
        self.desc = ''
        self.addr_regs = set()

    def modrm(self, a16, reg=None, force_mem=None, force_reg=False):
        """Return modrm/sib/disp bytes, choosing register values that keep memory operands in DATA."""
        mod = 3 if force_reg else random.choice([0, 1, 2, 3] if force_mem is None else ([0, 1, 2] if force_mem else [3]))
        if reg is None: reg = random.randint(0, 7)
        rm = random.randint(0, 7)
        out = []
        if mod == 3:
            return bytes([0xC0 | (reg << 3) | rm]), rm, None
        if a16:
            if mod == 0 and rm == 6:
                disp = DATA + random.randint(0, DATA_SIZE - 8)
                return bytes([(reg << 3) | 6]) + struct.pack('<H', disp), rm, disp
            bases = {0: (3, 6), 1: (3, 7), 2: (5, 6), 3: (5, 7), 4: (6,), 5: (7,), 6: (5,), 7: (3,)}[rm]
            b = bases[0]
            self.regs[b] = (self.regs[b] & 0xFFFF0000) | ptr()
            self.addr_regs.update(bases)
            if len(bases) > 1:
                self.regs[bases[1]] = (self.regs[bases[1]] & 0xFFFF0000) | random.randint(0, 0x40)
            if mod == 1: dbytes = struct.pack('<b', random.randint(-128, 127))
            elif mod == 2: dbytes = struct.pack('<h', random.randint(-0x100, 0x100))
            else: dbytes = b''
            return bytes([(mod << 6) | (reg << 3) | rm]) + dbytes, rm, None
        if rm == 5 and mod == 0:
            disp = DATA + random.randint(0, DATA_SIZE - 8)
            return bytes([(reg << 3) | 5]) + struct.pack('<I', disp), rm, disp
        sib = b''
        if rm == 4:
            scale, index, base = random.randint(0, 3), random.randint(0, 7), random.randint(0, 7)
            if base == 5 and mod == 0:
                sib = bytes([(scale << 6) | (index << 3) | 5]) + struct.pack('<I', DATA + random.randint(0, DATA_SIZE - 0x210))
                if index != 4:
                    self.regs[index] = random.randint(0, 0x40); self.addr_regs.add(index)
            else:
                sib = bytes([(scale << 6) | (index << 3) | base])
                if index == 4:
                    self.regs[base] = ptr()
                elif index == base:
                    self.regs[base] = (DATA + random.randint(0x300, 0xD00)) // (1 + (1 << scale))
                else:
                    self.regs[base] = ptr()
                    self.regs[index] = random.randint(0, 0x40)
                    self.addr_regs.add(index)
                self.addr_regs.add(base)
        else:
            self.regs[rm] = ptr()
            self.addr_regs.add(rm)
        if mod == 1: dbytes = struct.pack('<b', random.randint(-128, 127))
        elif mod == 2: dbytes = struct.pack('<i', random.randint(-0x200, 0x200))
        else: dbytes = b''
        return bytes([(mod << 6) | (reg << 3) | rm]) + sib + dbytes, rm, None

def gen_one():
    g = Gen()
    while True:
        two = random.random() < 0.3
        op = random.choice(OPS2 if two else OPS1)
        info = info2(op) if two else info1(op)
        if info is not None: break
    kind, has_modrm = info
    prefixes = []
    p66 = random.random() < 0.25
    p67 = random.random() < 0.1
    control = (not two and op in CONTROL) or (two and 0x80 <= op <= 0x8F) or (not two and op == 0xFF)
    if control or (two and 0xC8 <= op <= 0xCF) or (two and op == 0xC7) or (not two and op in (0x62, 0xC8, 0xC9, 0x60, 0x61)):
        p66 = False
    if not two and op in (0xE0, 0xE1, 0xE2, 0xE3) and p67:
        p67 = False
    if p66: prefixes.append(0x66)
    if p67: prefixes.append(0x67)
    seg_ovr = random.random() < 0.15
    if seg_ovr: prefixes.append(random.choice([0x26, 0x36, 0x3E, 0x64, 0x65]))
    rep = None
    if not two and op in STRING and random.random() < 0.6:
        rep = random.choice([0xF2, 0xF3])
        prefixes.append(rep)
    if random.random() < 0.05:
        prefixes.append(0xF0)
    random.shuffle(prefixes)
    opsz = 2 if p66 else 4
    a16 = p67
    body = bytes([0x0F, op]) if two else bytes([op])
    reg = None
    force_mem = None
    force_reg = False
    mrm = b''
    rmreg = None
    absaddr = None
    # opcode specific constraints
    if two and op in (0x00,):
        reg = random.choice([0, 1, 2, 3, 4, 5])
    if two and op == 0x01:
        reg = random.choice([0, 1, 2, 3, 4, 6, 7])
        if reg in (0, 1, 2, 3, 7): force_mem = True
    if two and op in (0x20, 0x22):
        reg = random.choice([0, 2, 3, 4]); force_reg = True
    if two and op in (0x21, 0x23):
        reg = random.choice([0, 1, 2, 3, 6, 7]); force_reg = True
    if two and op == 0xC7:
        reg = random.choice([1, 1, 1, 0, 2]); force_mem = None if reg != 1 else random.random() < 0.9
    if two and op in (0xB2, 0xB4, 0xB5) or (not two and op in (0xC4, 0xC5, 0x62)):
        force_mem = random.random() < 0.95
    if not two and op == 0xFF:
        reg = random.choice([0, 1, 2, 4, 6, 7])
    if not two and op == 0xFE:
        reg = random.choice([0, 1, 0, 1, 2])
    if not two and op in (0x8C, 0x8E):
        reg = random.choice([0, 1, 2, 3, 4, 5, 0, 2, 3, 4, 5, 6])
    if not two and op in (0xC6, 0xC7):
        reg = 0 if random.random() < 0.95 else random.randint(1, 7)
    if not two and op == 0x8F:
        reg = 0 if random.random() < 0.95 else random.randint(1, 7)
    if two and op == 0xBA:
        reg = random.choice([4, 5, 6, 7, 4, 5, 6, 7, 0])
    if has_modrm:
        mrm, rmreg, absaddr = g.modrm(a16, reg, force_mem, force_reg)
        reg = (mrm[0] >> 3) & 7
    modreg = has_modrm and (mrm[0] >> 6) == 3
    # immediates
    imm = b''
    if kind == 'ib':
        v = random.choice([random.getrandbits(8), random.randint(0, 40)])
        if not two and op in (0xD4, 0xD5): v &= 0x7F   # QEMU sign-extends the AAM/AAD base
        if two and op in (0xA4, 0xAC) and opsz == 2: v = random.randint(0, 16)
        imm = bytes([v])
    elif kind == 'iw':
        imm = struct.pack('<H', random.choice([0, 4, 8, random.randint(0, 64)]))
    elif kind == 'iz':
        imm = struct.pack('<H' if opsz == 2 else '<I', interesting32() & (0xFFFF if opsz == 2 else 0xFFFFFFFF))
    elif kind == 'moffs':
        a = DATA + random.randint(0, DATA_SIZE - 8)
        imm = struct.pack('<H' if a16 else '<I', a)
    elif kind == 'enter':
        imm = struct.pack('<HB', random.randint(0, 64), random.choice([0, 0, 1, 2, 3]))
    elif kind == 'grp3':
        if reg < 2:
            imm = struct.pack('<B', random.getrandbits(8)) if op == 0xF6 else \
                struct.pack('<H' if opsz == 2 else '<I', interesting32() & (0xFFFF if opsz == 2 else 0xFFFFFFFF))
    pre = bytes(prefixes)
    length_wo = len(pre) + len(body) + len(mrm)
    if kind in ('rel8', 'rel'):
        size = 1 if kind == 'rel8' else 4
        length = length_wo + size
        while True:
            rel = random.randint(-128, 127)
            t = INSN_OFF + length + rel
            if 8 <= t < CODE_SIZE - 8 and not (INSN_OFF <= t <= INSN_OFF + length):
                break
        imm = struct.pack('<b', rel) if size == 1 else struct.pack('<i', rel)
    insn = pre + body + mrm + imm
    if len(insn) > 15:
        return gen_one()
    L = len(insn)
    # register / memory set-up for implicit operands
    if not two and op in STRING or (not two and op in (0x6C, 0x6D, 0x6E, 0x6F)):
        g.regs[6] = ptr() if not a16 else (g.regs[6] & 0xFFFF0000) | ptr()
        g.regs[7] = ptr() if not a16 else (g.regs[7] & 0xFFFF0000) | ptr()
        if rep: g.regs[1] = random.choice([0, 1, 2, 3, 5, 8]) | (0 if not a16 else (r32() & 0xFFFF0000))
        # REP INS/OUTS with a zero count: QEMU checks I/O permission before the count (the SDM
        # REP pseudocode executes no iteration); not generated
        if rep and op in (0x6C, 0x6D, 0x6E, 0x6F) and g.regs[1] & (0xFFFF if a16 else 0xFFFFFFFF) == 0:
            g.regs[1] |= 1
    if not two and op == 0xD7:
        g.regs[3] = (g.regs[3] & 0xFFFF0000 if a16 else 0) | ptr()
    if not two and op in (0xE0, 0xE1, 0xE2, 0xE3):
        g.regs[1] = random.choice([0, 1, 2, 5, r32()])
    if not two and op in (0x8E,) or (two and op in (0x00,) and reg in (2, 3, 4, 5)) or (two and op in (0x02, 0x03)):
        if modreg:
            g.regs[rmreg] = (g.regs[rmreg] & 0xFFFF0000) | random.choice(SELECTORS)
        elif absaddr is not None or True:
            pass
    if not two and op in (0x07, 0x17, 0x1F) or (two and op in (0xA1, 0xA9)):
        if random.random() < 0.7:
            g.patches.append((g.regs[4] - DATA, random.choice(SELECTORS)))
    if not two and op in (0xC2, 0xC3):
        g.patches.append((g.regs[4] - DATA, CODE + code_target(L)))
    if not two and op == 0xFF and reg in (2, 4):
        if modreg:
            g.regs[rmreg] = CODE + code_target(L)
        else:
            # replace operand by an absolute memory operand we can patch
            a = DATA + random.randint(0, DATA_SIZE - 8) & ~3
            insn = pre.replace(b'\x67', b'') + body + bytes([(reg << 3) | 5]) + struct.pack('<I', a)
            g.patches.append((a - DATA, CODE + code_target(len(insn))))
    if (two and op in (0xB2, 0xB4, 0xB5)) or (not two and op in (0xC4, 0xC5)):
        if absaddr is not None and random.random() < 0.7:
            g.patches.append((absaddr - DATA + opsz, random.choice(SELECTORS)))
    if two and op in (0xA3, 0xAB, 0xB3, 0xBB) and not modreg:
        if reg in g.addr_regs:
            return gen_one()
        g.regs[reg] = random.randint(-200, 200) & 0xFFFFFFFF
    if not two and op in (0xD2, 0xD3) or (two and op in (0xA5, 0xAD)):
        g.regs[1] = (g.regs[1] & ~0xFF) | random.choice([0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33,
                                                         random.randint(0, 255)])
        if two and opsz == 2: g.regs[1] = (g.regs[1] & ~0xFF) | random.randint(0, 16)
    if not two and op == 0x61 or (not two and op == 0xC9):
        g.regs[5] = (DATA + random.randint(0x600, 0xA00)) & ~3 if op == 0xC9 else g.regs[5]
    if not two and op == 0xC8:
        g.regs[5] = (DATA + random.randint(0x600, 0xA00)) & ~3
    if not two and op in (0x62,) and modreg is False:
        pass
    if two and op == 0xC7 and reg == 1 and random.random() < 0.5 and absaddr is not None:
        g.patches.append((absaddr - DATA, g.regs[0]))
        g.patches.append((absaddr - DATA + 4, g.regs[2]))
    # flags that are defined after the instruction
    fm = ALL
    logic = {0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x30, 0x31, 0x32,
             0x33, 0x34, 0x35, 0x84, 0x85, 0xA8, 0xA9}
    if not two:
        if op in logic or (op in (0x80, 0x81, 0x82, 0x83) and reg in (1, 4, 6)) or \
           (op in (0xF6, 0xF7) and reg in (0, 1)):
            fm &= ~AF
        if op in (0xC0, 0xC1, 0xD0, 0xD1, 0xD2, 0xD3):
            bits = 8 if op in (0xC0, 0xD0, 0xD2) else opsz * 8
            cnt = (imm[0] if op in (0xC0, 0xC1) else 1 if op in (0xD0, 0xD1) else g.regs[1] & 0xFF) & 0x1F
            if cnt != 0:
                if reg >= 4:
                    fm &= ~AF
                    if cnt >= bits: fm &= ~CF
                if cnt != 1: fm &= ~OF
        if op in (0xF6, 0xF7) and reg in (4, 5) or op in (0x69, 0x6B):
            fm &= ~(SF | ZF | AF | PF)
        if op in (0xF6, 0xF7) and reg in (6, 7):
            fm &= ~ARITH
        if op in (0x37, 0x3F): fm &= ~(OF | SF | ZF | PF)
        if op in (0x27, 0x2F): fm &= ~OF
        if op in (0xD4, 0xD5): fm &= ~(OF | AF | CF)
    else:
        if op in (0xA4, 0xA5, 0xAC, 0xAD):
            cnt = (imm[0] if op in (0xA4, 0xAC) else g.regs[1] & 0xFF) & 0x1F
            if cnt != 0:
                fm &= ~AF
                if cnt != 1: fm &= ~OF
                if opsz == 2 and cnt > 16: fm &= ~ARITH
        if op == 0xAF: fm &= ~(SF | ZF | AF | PF)
        if op in (0xA3, 0xAB, 0xB3, 0xBB, 0xBA): fm &= ~(OF | SF | AF | PF)
        if op in (0xBC, 0xBD): fm &= ~(CF | OF | SF | AF | PF)
    g.fmask = fm
    g.desc = insn.hex()
    return insn, g

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    out = sys.argv[3] if len(sys.argv) > 3 else 'vectors'
    random.seed(seed)
    with open(out + '.bin', 'wb') as vb, open(out + '.meta', 'w') as mf:
        for k in range(n):
            insn, g = gen_one()
            patches = (g.patches + [(0xFFFF, 0), (0xFFFF, 0)])[:2]
            poff = [p[0] if p[0] == 0xFFFF or 0 <= p[0] <= DATA_SIZE - 4 else 0xFFFF for p in patches]
            paging = random.random() < 0.5
            mode = (1 if paging else 0) | (2 if random.random() < 0.5 else 0)
            # REP + single-step: QEMU traps with EIP on the instruction even after the last
            # iteration (the SDM REP loop completes the instruction); not generated
            if insn and any(b in (0xF2, 0xF3) for b in insn[:4]) and g.eflags & 0x100:
                g.eflags &= ~0x100
            def pte():
                if random.random() < 0.4: return 0x67        # fully accessible, A and D set
                return random.choice([0, 1]) | (random.getrandbits(2) << 1) | (random.getrandbits(2) << 5)
            vb.write(struct.pack('<B15s8III4H2H2I3I', len(insn), insn.ljust(15, b'\0'),
                                 *[r & 0xFFFFFFFF for r in g.regs], g.eflags, random.getrandbits(32) | 1,
                                 *g.sel, *poff, *[p[1] & 0xFFFFFFFF for p in patches],
                                 mode, pte() | 1 if random.random() < 0.7 else pte(), pte()))
            mf.write('%08x %s\n' % (g.fmask, g.desc))

if __name__ == '__main__':
    main()
