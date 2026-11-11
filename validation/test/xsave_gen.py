"""Random single-instruction vectors for the XSAVE forms of isa_forms.IMPLEMENTED (gen.py's 'ext'
family) and their undefined neighbours (#UD against QEMU, as the 'ud' family does for other maps).

The harness runs them in ring 3. With vector flag bit 0 (CR4.OSXSAVE, XCR0 = 7; gen.py sets it once
the model implements XSAVE) the forms execute; without it they are #UD. Forms whose result depends
on a choice the manuals leave to the processor, or that TCG lacks, are not generated (they are
covered by test/sys/t_xsave.c):
  * XGETBV with ECX = 1 (XINUSE: the harness's x87 state is in its initial configuration, which the
    model tracks and TCG does not),
  * XSAVE/XSAVEOPT with EDX:EAX bit 0 (the same XINUSE[0], and TCG does not write FOP) or with bit 2
    but not bit 1 (TCG skips MXCSR),
  * XSETBV without OSXSAVE (TCG checks the CPL before CR4.OSXSAVE, see sys/qemu-deviations.txt),
  * XSAVEC, XSAVES, XRSTORS with OSXSAVE (TCG has none of them; #UD is generated without OSXSAVE).
"""
import random
import struct

DATA = 0x8000
AREA_MAX = 0x340          # standard-format size with the AVX state


def mem_operand(g, a16):
    """ModRM/SIB/disp bytes for a memory operand at an address near a 64-byte boundary in DATA, the
    register(s) set in `g`. Returns (bytes without the reg field filled in: a function of reg)."""
    off = random.choice([random.randrange(0, 8192 - AREA_MAX) & ~63,           # aligned
                         0x1000 - random.choice([0x40, 0x200, 0x240, 0x300]),  # crossing page 9
                         random.randrange(0, 8192 - AREA_MAX)])                # anything (#GP)
    addr = DATA + off
    if a16:
        g.regs[3] = (g.regs[3] & 0xFFFF0000) | addr          # [bx]
        return lambda reg: bytes([(reg << 3) | 7])
    kind = random.randrange(3)
    if kind == 0:
        r = random.choice([1, 3, 6, 7])   # not EAX/EDX (the mask), not ESP/EBP
        g.regs[r] = addr
        return lambda reg: bytes([(reg << 3) | r])
    if kind == 1:
        d = random.randint(-128, 127)
        g.regs[3] = (addr - d) & 0xFFFFFFFF
        return lambda reg: bytes([0x40 | (reg << 3) | 3]) + struct.pack('<b', d)
    return lambda reg: bytes([(reg << 3) | 5]) + struct.pack('<I', addr)


def gen(g, vflags):
    """One vector (instruction bytes) of the XSAVE forms; sets g.desc."""
    on = vflags & 1
    a16 = random.random() < 0.08
    pre = b'\x67' if a16 else b''
    if random.random() < 0.1:
        pre += bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])])
    kind = random.choice(['xgetbv', 'xgetbv', 'xsetbv', 'save', 'save', 'save', 'xrstor', 'comp',
                          'prefix', 'neighbour'])
    if kind == 'xsetbv' and not on:
        kind = 'xgetbv'
    if kind == 'comp' and on:
        kind = 'save'
    # EDX:EAX
    mask = random.choice([2, 4, 6, 6, 7, 3, 0]) | (random.getrandbits(64) & ~7 if random.random() < 0.3 else 0)
    if kind == 'save' and on:
        mask &= ~1
        if mask & 6 == 4:
            mask |= 2
    g.regs[0] = mask & 0xFFFFFFFF
    g.regs[2] = mask >> 32
    if kind in ('xgetbv', 'xsetbv'):
        g.regs[1] = random.choice([0, 0, 0, 2, 3, 0x80000000, 0xFFFFFFFF]) if kind == 'xgetbv' or random.random() < 0.3 \
            else 0
        if kind == 'xgetbv' and not on and random.random() < 0.3:
            g.regs[1] = 1
        body = b'\x0f\x01' + (b'\xd0' if kind == 'xgetbv' else b'\xd1')
        g.desc = '%s:ecx=%x' % (kind, g.regs[1])
        return pre + body
    if kind == 'neighbour':
        # undefined encodings next to the XSAVE forms: 0F 01 D2..D7, register forms of 0F AE /4 and
        # 0F C7 /3../5, 0F C7 /0 and /2 with memory
        c = random.randrange(4)
        if c == 0:
            body = bytes([0x0F, 0x01, 0xD0 + random.randint(2, 7)])
        elif c == 1:
            body = bytes([0x0F, 0xAE, 0xE0 | random.randrange(8)])
        elif c == 2:
            body = bytes([0x0F, 0xC7, 0xC0 | (random.choice([3, 4, 5]) << 3) | random.randrange(8)])
        else:
            body = bytes([0x0F, 0xC7]) + mem_operand(g, a16)(random.choice([0, 2]))
        g.desc = 'xsave-ud:%s' % body.hex()
        return pre + body
    if kind == 'prefix':
        # a 66, F2 or F3 prefix on an NP form: #UD (66 0F AE /6 is CLWB, not generated)
        p = random.choice([0x66, 0xF2, 0xF3])
        c = random.randrange(3)
        if c == 0:
            body = bytes([p, 0x0F, 0x01, random.choice([0xD0, 0xD1])])
        elif c == 1:
            reg = random.choice([4, 5] + ([6] if p != 0x66 else []))
            body = bytes([p, 0x0F, 0xAE]) + mem_operand(g, a16)(reg)
        else:
            body = bytes([p, 0x0F, 0xC7]) + mem_operand(g, a16)(random.choice([3, 4, 5]))
        g.desc = 'xsave-pfx:%s' % body.hex()
        return pre + body
    op = {'save': random.choice([(0xAE, 4), (0xAE, 6)]), 'xrstor': (0xAE, 5),
          'comp': random.choice([(0xC7, 3), (0xC7, 4), (0xC7, 5)])}[kind]
    body = bytes([0x0F, op[0]]) + mem_operand(g, a16)(op[1])
    g.desc = '%s:%s m=%x' % (kind, body.hex(), mask)
    return pre + body
