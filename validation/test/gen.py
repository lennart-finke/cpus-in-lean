#!/usr/bin/env python3
"""Generate random single-instruction test vectors for differential testing against QEMU.

Each vector: instruction bytes, initial GPRs/EFLAGS/data-segment selectors, a seed for the
4 KiB data area (xorshift32) and up to two 32-bit patches into it. Alongside vectors.bin a
meta file records, per vector, the EFLAGS bits that are architecturally defined after the
instruction (undefined flags are masked in the comparison) and a short description.

Layout shared with the harness and the Lean runner:
  DATA = 0x8000 (4 KiB), CODE = 0x20000 (512 B, instruction at +256, rest filled with INT3)

Record formats (shared with test/harness/harness.c and TestMain.lean):
  v1  (default; also used by native.py): 88-byte records, no header, integer state only.
  v2  (--v2, used by run.sh): a 16-byte header (V2_MAGIC, record size 96, 0) and 96-byte records:
      the v1 fields, then MXCSR (u32) and vector flags (u32; bit 0: enable CR4.OSXSAVE and
      XCR0 = 7). The harness then also enables CR4.OSFXSR/OSXMMEXCPT, loads XMM0-7 (and, with
      OSXSAVE, YMM0-7 bits 255:128) from a pattern derived from the data seed (`vec_pattern`) and
      reports MXCSR, XMM0-7 and the YMM upper halves after the instruction.
  v2 adds instruction families beyond the integer generator: 'ud' (encodings that are #UD on
  Zen 2: unused 0F 38 / 0F 3A / VEX opcodes, VEX after 66/F2/F3/LOCK, unknown VEX maps, EVEX and
  XOP register forms, ...), 'len' (such encodings padded with prefixes to 15 bytes (#UD) or 16
  bytes (#GP(0)); for 16 bytes QEMU reports #UD, see TestMain.lean) and 'ext' (forms in
  isa_forms.IMPLEMENTED: gen_gpr.py for the general-purpose extensions, xsave_gen.py for the XSAVE
  forms, gen_crypto.py, gen_sse.py (via ext_form) for SSE3..SSE4a, gen_avx.py, gen_avx2.py,
  gen_sys.py, gen_svm.py). With --v2, main prints how many distinct undefined encodings per map the
  'ud' family emitted (ud_stats) to stderr; run.sh shows it.
"""
import os, random, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import isa_forms
import gen_sys
import xsave_gen
import gen_gpr   # 'ext' family: general-purpose extensions (x86_32/X86/Ext/Gpr.lean)

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
        prefixes.append(0xF0)   # (LOCK MOV CR0 is MOV CR8 with AltMovCr8, which the model implements)
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

V2 = False   # set by main() for --v2
VFLAGS = 0   # vector flags of the run (main)
V2_MAGIC = b'X86VEC\x00\x02'
V2_SIZE = 96

def xorshift(x):
    x ^= (x << 13) & 0xFFFFFFFF; x ^= x >> 17; x ^= (x << 5) & 0xFFFFFFFF
    return x

def vec_pattern(seed):
    """Initial XMM0-7 and YMM0-7[255:128] of a v2 vector: 64 words from xorshift32, starting at
    seed ^ 0xA5A5A5A5 (XMM0 word 0 first; the same in harness.c and TestMain.lean)."""
    s, out = seed ^ 0xA5A5A5A5, []
    for _ in range(64):
        s = xorshift(s)
        out.append(s)
    return out

PP_BYTE = {0: b'', 1: b'\x66', 2: b'\xf3', 3: b'\xf2'}

def vex_bytes(map_, pp, L, W, vvvv, two_byte):
    """A VEX prefix in 32-bit mode: inverted R and X are 1 (required), inverted B random."""
    vb = (~vvvv & 0xF) << 3 | (L << 2) | pp
    if two_byte:
        return bytes([0xC5, 0x80 | vb])
    return bytes([0xC4, 0xC0 | (random.getrandbits(1) << 5) | map_, (W << 7) | vb])

def vex_layout(map_, op, pp):
    """(ModRM, immediate bytes) of a VEX opcode: the layout of the legacy map with the same opcode
    (x86_32/X86/Decode.lean); None for map 1 opcodes whose layout is not a ModRM/imm8 one."""
    if map_ == 2: return (True, 0)
    if map_ == 3: return (True, 1)
    if 0x80 <= op <= 0x8F or op in (0x78,) and pp in (1, 3): return None
    if op in (0x77, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0B, 0x0E, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x37,
              0xA0, 0xA1, 0xA2, 0xA8, 0xA9, 0xAA) or 0xC8 <= op <= 0xCF:
        return (False, 0)
    if 0x70 <= op <= 0x73 or op in (0xC2, 0xC4, 0xC5, 0xC6, 0xA4, 0xAC, 0xBA):
        return (True, 1)
    if op in (0x04, 0x0A, 0x0C, 0x0F, 0x24, 0x25, 0x26, 0x27, 0x36, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D,
              0x3E, 0x3F, 0x7A, 0x7B, 0xA6, 0xA7):
        return (False, 0)
    return (True, 0)

# 0F-map opcodes without an instruction on Zen 2 for some prefixes (isa_forms decides which)
UD_0F = [0x04, 0x0A, 0x0C, 0x0E, 0x0F, 0x24, 0x25, 0x26, 0x27, 0x36, 0x39, 0x3B, 0x3C, 0x3D, 0x3E,
         0x3F, 0x78, 0x79, 0x7A, 0x7B, 0xA6, 0xA7, 0xB8]
MODRM_0F = {0x78, 0x79, 0xB8}

# 'vexnb' kind of the 'ud' family: the undefined neighbours of the implemented VEX forms (isa_forms
# `vex_neighbours`: an opcode byte with a VEX row, under a mandatory prefix and VEX.L for which no row
# exists), emitted in turn so that a run covers them independently of chance. The pinned ones come
# first in every run: forms where a model dispatch on the opcode byte fell into a default arm for an
# undefined prefix (VEX.256.NP.0F 70 executed as VPSHUFLW, review finding); every eighth 'vexnb'
# vector is a pinned one (with VEX.vvvv = 1111b).
VEXNB_PINNED = [(1, 0, 0x70, 1), (1, 0, 0x70, 0)]
_vexnb = {'list': None, 'next': 0, 'n': 0}

def vexnb_next():
    """The next neighbour and whether it is a pinned one."""
    if _vexnb['list'] is None:
        rest = [t for t in isa_forms.vex_neighbours() if t not in VEXNB_PINNED and t != (1, 0, 0xC4, 0)
                and t != (1, 0, 0xC4, 1)]
        random.shuffle(rest)
        _vexnb['list'] = rest
    n = _vexnb['n']
    _vexnb['n'] += 1
    if n % 8 == 0:
        return VEXNB_PINNED[(n // 8) % len(VEXNB_PINNED)], True
    lst = _vexnb['list']
    t = lst[_vexnb['next'] % len(lst)]
    _vexnb['next'] += 1
    return t, False

def ud_form(g, a16, force=None):
    """An encoding that is #UD on Zen 2 and in the model, as (bytes, kind); the bytes include the
    mandatory or legacy prefix the form needs. With `force`, the ModRM byte (and an imm8) is that
    value (a register form): used by the length tests, whose last byte is the INT3 filler."""
    kinds = ['map2', 'map3', 'vex', 'vex', 'vexpfx', 'vexmap', 'evex', 'xop', '0f', 'vexnb', 'vexnb']
    if force is not None:
        kinds = ['map2', 'map3', 'vex', '0f']
    kind = random.choice(kinds)
    def modrm(reg=None):
        return bytes([force]) if force is not None else g.modrm(a16, reg)[0]
    if kind in ('map2', 'map3'):
        m = 2 if kind == 'map2' else 3
        while True:
            pp, op = random.randint(0, 3), random.getrandbits(8)
            if not isa_forms.defined('legacy', m, pp, op):
                break
        body = PP_BYTE[pp] + bytes([0x0F, 0x38 if m == 2 else 0x3A, op])
        if m == 3:
            mr = g.modrm(a16)[0] if force is None else bytes([0xC0 | random.getrandbits(6)])
            return body + mr + bytes([force if force is not None else random.getrandbits(8)]), kind
        return body + modrm(), kind
    if kind == '0f':
        while True:
            op, pp = random.choice(UD_0F), random.randint(0, 3)
            if not isa_forms.defined('legacy', 1, pp, op):
                break
        body = PP_BYTE[pp] + bytes([0x0F, op])
        if op in MODRM_0F:
            return body + modrm(), kind
        return (None if force is not None else body), kind
    if kind in ('vex', 'vexpfx', 'vexmap', 'vexnb'):
        nb, pinned = vexnb_next() if kind == 'vexnb' else (None, False)
        while True:
            m = random.choice([1, 2, 3]) if kind != 'vexmap' else random.choice([0] + list(range(4, 32)))
            pp, op = random.randint(0, 3), random.getrandbits(8)
            L, W, vvvv = random.getrandbits(1), random.getrandbits(1), random.getrandbits(4)
            if nb is not None:
                # mostly VEX.vvvv = 1111b (register 0), so that the undefined prefix/L is the only
                # reason for the #UD of a form that takes no VEX.vvvv operand
                m, pp, op, L = nb
                if pinned or random.random() < 0.75:
                    vvvv = 0
            # (Avx) the ModRM kind and reg field are chosen first, so that forms defined only for some
            # VEX.L/VEX.W/mod/reg (isa_forms rows) have their undefined neighbours tested as #UD
            lay = vex_layout(m, op, pp) if kind != 'vexmap' else None
            mem = force is None and random.random() < 0.5
            mreg = (force >> 3) & 7 if force is not None else random.randint(0, 7)
            mod = (0 if mem else 3) if lay is not None and lay[0] else None
            # (Avx) QEMU 11.1.2 aborts on VEX.NP.0F C4 (assert(vec_len == 16) in gen_pinsr): not
            # generated; the model raises #UD (no such VEX form)
            if kind != 'vexmap' and m == 1 and pp == 0 and op == 0xC4:
                continue
            # after a 66/F2/F3/LOCK prefix every VEX form is #UD; an unknown map too
            if kind not in ('vex', 'vexnb') or not isa_forms.defined('vex', m, pp, op, mod,
                                                                    mreg if mod is not None else None, L=L, W=W):
                break
            assert nb is None, nb   # a neighbour is undefined for every W, mod and reg
        # C5: bit 6 of its byte is inverted vvvv[3], which must be 1 (vvvv < 8) in 32-bit mode
        two = m == 1 and W == 0 and vvvv < 8 and random.random() < 0.5
        pre = bytes([random.choice([0x66, 0xF2, 0xF3, 0xF0])]) if kind == 'vexpfx' else b''
        body = pre + vex_bytes(m, pp, L, W, vvvv, two) + bytes([op])
        if kind == 'vexmap':
            return body, kind
        if lay is None or (force is not None and not lay[0]):
            return None, kind
        if lay[0]:
            body += bytes([force]) if force is not None else \
                g.modrm(a16, mreg, force_mem=mem, force_reg=not mem)[0]
        if lay[1]:
            body += bytes([force if force is not None else random.getrandbits(8)])
        return body, kind
    if kind == 'evex':
        # 62 with ModRM.mod = 11: EVEX on AVX-512 CPUs, the #UD register form of BOUND on Zen 2
        return bytes([0x62, 0xC0 | random.getrandbits(6)]) + bytes(random.getrandbits(8) for _ in range(4)), kind
    # 8F with ModRM.reg != 0: XOP on CPUs with XOP, #UD on Zen 2 (POP r/m needs reg = 0)
    return bytes([0x8F]) + modrm(random.randint(1, 7)), kind

# Coverage of the 'ud' family: the distinct undefined encodings emitted in a run, per map. A distinct
# encoding is a combination of the fields that isa_forms.defined() and the model's decoder tell
# apart: (map, mandatory prefix pp, opcode byte, ModRM.mod class (register / memory / no ModRM),
# ModRM.reg, VEX.L, VEX.W); for 'vexpfx' also the legacy prefix before the VEX; for the one-byte
# opcodes 62 (EVEX) and 8F (XOP) (opcode, ModRM.mod class, ModRM.reg). Not told apart: ModRM.rm,
# SIB, displacement, VEX.vvvv/R/X/B, the immediate, and the 67/segment prefixes of gen_v2_family.
# 'vexnb' vectors are counted on their own, and also as the isa_forms.vex_neighbours() entries
# (map, pp, opcode, VEX.L) they cover.
UD_BUCKETS = ['62/8F', '0F', '0F38', '0F3A', 'VEX.0F', 'VEX.0F38', 'VEX.0F3A', 'VEX map 0/4-31',
              'pfx+VEX', 'vexnb']
_ud_seen = {'n': 0, 'keys': {b: set() for b in UD_BUCKETS}, 'nb': set()}

def ud_key(kind, body):
    """(bucket, distinct-encoding key) of the bytes `body` of ud_form's kind `kind`."""
    def mrm(j):
        return ('reg' if body[j] >> 6 == 3 else 'mem', body[j] >> 3 & 7) if j < len(body) else (None, None)
    if kind in ('evex', 'xop'):
        return '62/8F', (body[0],) + mrm(1)
    if kind in ('map2', 'map3', '0f'):
        pp = {0x66: 1, 0xF3: 2, 0xF2: 3}.get(body[0], 0)
        m = {'0f': 1, 'map2': 2, 'map3': 3}[kind]
        i = (1 if pp else 0) + (1 if m == 1 else 2)   # the opcode byte
        has_modrm = m != 1 or body[i] in MODRM_0F
        return ['0F', '0F38', '0F3A'][m - 1], (pp, body[i]) + (mrm(i + 1) if has_modrm else (None, None))
    pre = body[0] if kind == 'vexpfx' else None
    i = 1 if kind == 'vexpfx' else 0
    if body[i] == 0xC5:
        m, W, L, pp, i = 1, 0, body[i + 1] >> 2 & 1, body[i + 1] & 3, i + 2
    else:
        m, W, L, pp, i = body[i + 1] & 0x1F, body[i + 2] >> 7, body[i + 2] >> 2 & 1, body[i + 2] & 3, i + 3
    op = body[i]
    if kind == 'vexmap':
        return 'VEX map 0/4-31', (m, pp, op, L, W)
    lay = vex_layout(m, op, pp)
    key = (m, pp, op, L, W) + (mrm(i + 1) if lay[0] else (None, None))
    if kind == 'vexpfx':
        return 'pfx+VEX', (pre,) + key
    if kind == 'vexnb':
        return 'vexnb', key
    return ['VEX.0F', 'VEX.0F38', 'VEX.0F3A'][m - 1], key

def ud_record(kind, body):
    bucket, key = ud_key(kind, body)
    _ud_seen['n'] += 1
    _ud_seen['keys'][bucket].add(key)
    if kind == 'vexnb':
        _ud_seen['nb'].add(key[:4])

def ud_stats():
    """One line: the 'ud' vectors of the run and their distinct encodings per map (ud_key)."""
    k = _ud_seen['keys']
    nbs = [t for t in isa_forms.vex_neighbours() if t[:3] != (1, 0, 0xC4)]   # (as vexnb_next)
    return 'ud family: %d vectors; distinct encodings: %s (covering %d of %d VEX neighbours)' % (
        _ud_seen['n'], ', '.join('%s %d' % (b, len(k[b])) for b in UD_BUCKETS), len(_ud_seen['nb']), len(nbs))

def gen_v2_family(g):
    """A vector of a v2-only family ('ud', 'len'), or None to use the integer generator."""
    r = random.random()
    if r < 0.15:
        a16 = random.random() < 0.1
        body, kind = ud_form(g, a16)
        if body is None:
            return None
        pre = (b'\x67' if a16 else b'') + \
            (bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])]) if random.random() < 0.15 else b'')
        insn = pre + body
        if len(insn) > 15:
            return None
        g.desc = 'ud-%s:%s' % (kind, insn.hex())
        ud_record(kind, body)
        return insn
    if r < 0.22:
        # length limit: a #UD form whose last byte (ModRM or imm8) is 0xCC, the code buffer's
        # filler, padded with DS prefixes to 15 bytes (#UD) or 16 bytes (#GP(0)); 15 bytes stored
        body, kind = ud_form(g, False, force=0xCC)
        if body is None:
            return None
        total = random.choice([15, 16])
        if len(body) >= total:
            return None
        insn = b'\x3e' * (total - len(body)) + body
        g.desc = 'len%d-%s:%s' % (total, kind, insn.hex())
        return insn[:15]
    if r < 0.26:   # 'ext': the XSAVE forms (isa_forms.IMPLEMENTED, owner Xsave) and their neighbours
        return xsave_gen.gen(g, VFLAGS)
    if r < 0.28:
        # 'ext' forms of system workstream A (test/gen_sys.py)
        insn, g.desc = gen_sys.sys_form()
        return insn
    if r < 0.44:
        return gen_gpr.gen(g)   # 'ext' family of the Gpr forms (gen_gpr.py)
    # 'ext' family, Crypto workstream: AES-NI, PCLMULQDQ, SHA (gen_crypto.py)
    if r < 0.55:
        import gen_crypto
        return gen_crypto.gen(g)
    if r < 0.72:
        return ext_form(g)      # 'ext' family of the Sse forms (gen_sse.py)
    if r < 0.84:
        import gen_avx          # 'ext' family of the AVX forms (gen_avx.py)
        return gen_avx.gen(g)
    if r < 0.93:
        import gen_avx2         # 'ext' family of the AVX2/FMA3/F16C forms (gen_avx2.py)
        return gen_avx2.gen(g)
    if r < 0.95:
        import gen_svm          # 'ext' family of the SVM forms (gen_svm.py)
        insn, g.desc = gen_svm.svm_form()
        return insn
    return None

# 'ext' family: a random isa_forms.IMPLEMENTED row, generated by its owner's module (gen_<owner>.py,
# `ext(g, form)` -> instruction bytes or None; it may set g.seed, the vector's data seed).
import gen_sse
EXT_GENERATORS = {
    'Sse': gen_sse.ext,
}

def ext_form(g):
    rows = [f for f in isa_forms.IMPLEMENTED if f.owner in EXT_GENERATORS]
    if not rows:
        return None
    f = random.choice(rows)
    return EXT_GENERATORS[f.owner](g, f)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    v2 = '--v2' in sys.argv
    global V2
    V2 = v2
    n = int(args[0]) if len(args) > 0 else 10000
    seed = int(args[1]) if len(args) > 1 else 1
    out = args[2] if len(args) > 2 else 'vectors'
    random.seed(seed)
    # bit 0: CR4.OSXSAVE and XCR0 = 7 (x87, SSE and AVX state), as Zen 2 has XSAVE
    global VFLAGS
    vflags = 1 if isa_forms.model_has('xsave') else 0
    VFLAGS = vflags
    with open(out + '.bin', 'wb') as vb, open(out + '.meta', 'w') as mf:
        if v2:
            vb.write(V2_MAGIC + struct.pack('<II', V2_SIZE, 0))
        for k in range(n):
            insn = None
            if v2:
                g = Gen()
                insn = gen_v2_family(g)
            if insn is None:
                insn, g = gen_one()
            patches = (g.patches + [(0xFFFF, 0), (0xFFFF, 0)])[:2]
            poff = [p[0] if p[0] == 0xFFFF or 0 <= p[0] <= DATA_SIZE - 4 else 0xFFFF for p in patches]
            paging = random.random() < 0.5
            if getattr(g, 'no_paging', False):
                paging = False   # e.g. CLFLUSH: TCG makes no access (gen_gpr.py)
            mode = (1 if paging else 0) | (2 if random.random() < 0.5 else 0)
            # REP + single-step: QEMU traps with EIP on the instruction even after the last
            # iteration (the SDM REP loop completes the instruction); not generated
            if insn and any(b in (0xF2, 0xF3) for b in insn[:4]) and g.eflags & 0x100:
                g.eflags &= ~0x100
            def pte():
                if random.random() < 0.4: return 0x67        # fully accessible, A and D set
                return random.choice([0, 1]) | (random.getrandbits(2) << 1) | (random.getrandbits(2) << 5)
            vb.write(struct.pack('<B15s8III4H2H2I3I', len(insn), insn.ljust(15, b'\0'),
                                 *[r & 0xFFFFFFFF for r in g.regs], g.eflags,
                                 getattr(g, 'seed', None) or random.getrandbits(32) | 1,
                                 *g.sel, *poff, *[p[1] & 0xFFFFFFFF for p in patches],
                                 mode, pte() | 1 if random.random() < 0.7 else pte(), pte()))
            if v2:
                # all exceptions masked; random rounding control, FTZ, DAZ and sticky flags
                mxcsr = 0x1F80 | (random.getrandbits(2) << 13) | (0x8000 if random.random() < 0.3 else 0) \
                    | (0x40 if random.random() < 0.3 else 0) | (random.getrandbits(6) if random.random() < 0.3 else 0)
                mxcsr &= getattr(g, 'mxcsr_and', 0xFFFFFFFF)   # (a generator may clear bits, gen_avx.py)
                vb.write(struct.pack('<II', mxcsr, vflags))
            mf.write('%08x %s\n' % (g.fmask, g.desc))
    if v2:
        print(ud_stats(), file=sys.stderr)

if __name__ == '__main__':
    main()
