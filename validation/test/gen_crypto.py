"""'ext' family of gen.py for the crypto workstream: AES-NI, PCLMULQDQ and SHA (legacy encodings).

`gen(g)` returns the bytes of one random instruction of isa_forms.IMPLEMENTED's crypto rows, with
register or memory source operand (several addressing forms, mostly 16-byte aligned so that most
cases execute; misaligned AES/PCLMULQDQ operands raise #GP(0), SHA ones are not generated, see
`gen`), random destination/source registers, every imm8 (PCLMULQDQ: all four quadword selectors
and the ignored bits), and occasionally a segment override or LOCK prefix (#UD). XMM0..7 come from
the vector's seed (gen.vec_pattern), memory from the data area. The description 'crypto-<name>:<reg>:<x<rm>|m<address>>:<hex>:<imm decimal>' lets
`cryptoref.py vectors` recompute the expected destination from the vector with the independent
reference and check QEMU's result (test/run.sh); x86test compares the model with QEMU.
"""
import random
import struct

import cryptoref
import isa_forms

DATA = 0x8000
FORMS = sorted(cryptoref.FORMS.items())


def _check_forms():
    for (map_, pfx, op), _ in FORMS:
        pp = {0: 0, 0x66: 1}[pfx]
        assert any(isa_forms._matches(f, 'legacy', map_, pp, op, None, None) for f in isa_forms.IMPLEMENTED), \
            'crypto form %d/%x/%x is not in isa_forms.IMPLEMENTED' % (map_, pfx, op)


_check_forms()


def _memory(g, reg, misalign):
    """ModRM (+SIB, displacement) for a memory operand at a chosen address; sets the registers."""
    ea = DATA + 16 * random.randint(0x10, 0x1F0)
    if misalign and random.random() < 0.15:
        ea += random.randint(1, 15)          # misaligned: #GP(0)
    kind = random.choice(['base', 'disp8', 'disp32', 'sib', 'abs'])
    if kind == 'abs':
        return bytes([(reg << 3) | 5]) + struct.pack('<I', ea), ea
    base = random.choice([0, 1, 2, 3, 5, 6, 7])
    if kind == 'base':
        if base == 5:
            kind = 'disp8'
        else:
            g.regs[base] = ea
            return bytes([(reg << 3) | base]), ea
    if kind == 'disp8':
        d = random.randint(-128, 127)
        g.regs[base] = (ea - d) & 0xFFFFFFFF
        return bytes([0x40 | (reg << 3) | base]) + struct.pack('<b', d), ea
    if kind == 'disp32':
        d = random.randint(-0x2000, 0x2000)
        g.regs[base] = (ea - d) & 0xFFFFFFFF
        return bytes([0x80 | (reg << 3) | base]) + struct.pack('<i', d), ea
    # [base + index * 2^scale], mod = 00 (base != EBP)
    base = random.choice([0, 1, 2, 3, 6, 7])
    index = random.choice([r for r in (0, 1, 2, 3, 5, 6, 7) if r != base])
    scale = random.randint(0, 3)
    iv = random.randint(0, 0x40)
    g.regs[index] = iv
    g.regs[base] = (ea - (iv << scale)) & 0xFFFFFFFF
    return bytes([(reg << 3) | 4, (scale << 6) | (index << 3) | base]), ea


def gen(g):
    (map_, pfx, op), name = random.choice(FORMS)
    reg = random.randint(0, 7)
    pre = b''
    if random.random() < 0.1:
        pre += bytes([random.choice([0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65])])
    if random.random() < 0.03:
        pre += b'\xf0'                      # LOCK: #UD
    if pfx:
        pre += bytes([pfx])
    body = pre + bytes([0x0F, 0x38 if map_ == 2 else 0x3A, op])
    if random.random() < 0.6:
        rm = random.randint(0, 7)
        body += bytes([0xC0 | (reg << 3) | rm])
        src = 'x%d' % rm
    else:
        # TCG does not check the alignment of the SHA instructions' memory operands (its decoder
        # entries lack the SSE exception class), where the SDM's exception class 4 raises #GP(0):
        # misaligned SHA operands are tested by the system tests (crypto.exc lines) instead
        mrm, ea = _memory(g, reg, misalign=not name.startswith('sha'))
        body += mrm
        src = 'm%x' % ea
    imm = 0
    if map_ == 3:
        imm = random.getrandbits(8)
        if name == 'pclmulqdq' and random.random() < 0.5:
            imm = random.choice([0x00, 0x01, 0x10, 0x11])
        body += bytes([imm])
    # (decimal imm last: x86test treats descriptions ending in a6/a7 as CMPS)
    g.desc = 'crypto-%s:%d:%s:%s:%d' % (name, reg, src, body.hex(), imm)
    return body
