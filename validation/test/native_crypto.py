"""Native hardware campaign families for AES-NI, PCLMULQDQ and SHA (fp_cases.FAMILIES).

Inputs only (no model or reference answer is used by generation). Each case runs one instruction
with XMM0 (destination) and XMM1 or [EBX] (source); the record compares XMM0..7, flags and faults.
Besides random and edge operands, the families probe what is not settled from the manuals:
misaligned memory operands (SDM exception class 4: #GP(0) without MisalignSse) and, for the "NP" SHA
instructions, a 66/F2/F3 prefix, which the model treats as #UD (as Bochs; the SDM says such a prefix
is #UD or another instruction; QEMU's TCG executes them). These carry policy 'observe' so that a
difference is reported for review instead of failing the campaign.
"""
M64 = (1 << 64) - 1
AES = [('aesimc', 'db'), ('aesenc', 'dc'), ('aesenclast', 'dd'), ('aesdec', 'de'), ('aesdeclast', 'df')]
SHA = [('sha1nexte', 'c8'), ('sha1msg1', 'c9'), ('sha1msg2', 'ca'), ('sha256rnds2', 'cb'),
       ('sha256msg1', 'cc'), ('sha256msg2', 'cd')]
def record(*a, **k):
    import fp_cases   # imported lazily: fp_cases imports this module for FAMILIES
    return fp_cases.record(*a, **k)


def meta(*a, **k):
    import fp_cases
    return fp_cases.meta(*a, **k)


EDGE = [0, M64, 0x8000000000000000, 1, 0x0123456789ABCDEF, 0x6363636363636363, 0x5252525252525252]


def _xmm(rng, edge):
    """XMM0..7 (and the x86-64 registers the record carries) as 32 quadwords."""
    q = [rng.choice(EDGE) if edge and rng.randrange(3) == 0 else rng.getrandbits(64) for _ in range(32)]
    return q


def _cases(rng, count, family, forms):
    """forms: (name, code prefix bytes as hex, has imm8)."""
    n = max(count // 10, 64)
    for name, code, imm8 in forms:
        for i in range(n):
            mem = i % 3 == 2
            xmm = _xmm(rng, i % 2 == 0)
            c = code + ('03' if mem else 'c1')
            if imm8:
                c += '%02x' % (i % 256 if name == 'pclmulqdq' and i < 256 else rng.getrandbits(8))
            src = rng.getrandbits(128)
            yield record(c, xmm=xmm, mem=src.to_bytes(16, 'little')), meta(family, name, c, memory=mem)
        # misaligned memory operand (#GP(0) by the SDM's exception class 4)
        for offset in (1, 4, 8, 15):
            c = code + '03' + ('00' if imm8 else '')
            yield record(c, xmm=_xmm(rng, False), address=0x10000 + offset, mem=bytes(range(16))), meta(
                family, name, c, offset=offset)
        # page permissions on the source (#PF)
        for perms in ((0x65, 0x67), (0, 0x67)):
            c = code + '03' + ('00' if imm8 else '')
            yield record(c, xmm=_xmm(rng, False), permissions=perms, mem=bytes(range(16))), meta(
                family, name, c, permissions=perms)


def aes_cases(rng, count):
    forms = [(n, '660f38' + op, False) for n, op in AES] + [('aeskeygenassist', '660f3adf', True)]
    yield from _cases(rng, count, 'aes', forms)
    # every RCON value of AESKEYGENASSIST
    for imm in range(256):
        c = '660f3adfc1%02x' % imm
        yield record(c, xmm=_xmm(rng, False)), meta('aes', 'aeskeygenassist', c, imm=imm)
    # without the 66 prefix, or with F2/F3: #UD
    for n, op in AES:
        for pfx in ('', 'f3', 'f2', '66f3'):
            c = pfx + '0f38' + op + 'c1'
            yield record(c, xmm=_xmm(rng, False)), meta('aes_prefix', n, c)


def pclmul_cases(rng, count):
    yield from _cases(rng, count, 'pclmulqdq', [('pclmulqdq', '660f3a44', True)])
    # every imm8 (quadword selectors in bits 0 and 4, the others ignored), register form
    for imm in range(256):
        c = '660f3a44c1%02x' % imm
        yield record(c, xmm=_xmm(rng, imm % 2 == 0)), meta('pclmulqdq', 'pclmulqdq', c, imm=imm)
    for pfx in ('', 'f3', 'f2'):
        c = pfx + '0f3a44c100'
        yield record(c, xmm=_xmm(rng, False)), meta('pclmulqdq_prefix', 'pclmulqdq', c)


def sha_cases(rng, count):
    forms = [(n, '0f38' + op, False) for n, op in SHA] + [('sha1rnds4', '0f3acc', True)]
    for raw, m in _cases(rng, count, 'sha', forms):
        if 'offset' in m:
            m = dict(m, policy='observe',
                     reason='misaligned SHA operand: #GP(0) by the SDM exception class 4; QEMU TCG runs it')
        yield raw, m
    for imm in range(256):
        c = '0f3accc1%02x' % imm
        yield record(c, xmm=_xmm(rng, False)), meta('sha', 'sha1rnds4', c, imm=imm)
    for n, op in SHA + [('sha1rnds4', 'cc')]:
        for pfx in ('66', 'f3', 'f2'):
            c = pfx + ('0f3a' if n == 'sha1rnds4' else '0f38') + op + 'c1' + ('00' if n == 'sha1rnds4' else '')
            yield record(c, xmm=_xmm(rng, False)), meta(
                'sha_prefix', n, c, policy='observe',
                reason='"NP" SHA instruction with a 66/F2/F3 prefix: #UD in the model (Bochs, SDM NP); unconfirmed on Zen 2')
