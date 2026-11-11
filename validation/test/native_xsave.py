"""Native hardware families for the XSAVE feature set (fp_cases.FAMILIES; x86_32/X86/Ext/Xsave.lean).

User mode on the target (Linux, IA-32 compatibility mode, CR4.OSXSAVE = 1). Assumed host state: XCR0
= 7 (x87, SSE, AVX: a Zen 2 Linux host; the 7742 has no PKU, so Linux does not enable PKRU), and
every component in use (XINUSE = 7): Linux loads the instruction's state from the signal frame with
XRSTOR and XSTATE_BV bits 0..2 set, and the inputs are outside the initial configurations (non-zero
registers). Under these conditions everything the cases observe is defined by the manuals, except:
  * bytes 5, 14..15, 22..23 (reserved), 28..31 (MXCSR_MASK, an implementation value), bytes 10..15
    of each x87 register slot and 288..463 (XMM8..15/reserved in compatibility mode) of the legacy
    region, which memory kind 4 leaves out of the hashes (FpMain.lean, signal_oracle.c);
  * which AMD revision the XSaveErPtr rule describes: the pointers in the frame are 0 anyway.
Masks stay within XCR0 = 7, so a host with more XCR0 bits (AVX-512, PKRU) gives the same images;
only XGETBV with ECX = 0 reports the host's XCR0.

Cases: XSAVE, XSAVEOPT, XSAVEC with every RFBM and high EDX:EAX bits, x87 stacks with and without a
pending exception (FSW.ES: the error pointers); XSAVES/XRSTORS at CPL 3 (#GP(0)); XRSTOR from an
area whose header is zero (seed 0: every requested component initialized, MXCSR loaded for RFBM[1]
or RFBM[2]) with valid and reserved MXCSR values, from random memory (#GP header checks), and
misaligned (#GP(0)); XGETBV with ECX = 0, 1, 2; XSETBV at CPL 3 (#GP(0))."""
import struct

from fp_cases import record, meta, VALUES

KIND = 4   # memory kind: XSAVE image (masked as above)


def _with_regs(raw, **regs):
    """Patch GPR inputs of a record (eax, ecx, edx, ebx: 64-bit slots at 16 + 8k)."""
    r = bytearray(raw)
    for name, v in regs.items():
        k = {'eax': 0, 'ecx': 1, 'edx': 2, 'ebx': 3}[name]
        struct.pack_into('<Q', r, 16 + 8 * k, v & 0xFFFFFFFF)
    return bytes(r)


def _mask(m):
    return dict(eax=m & 0xFFFFFFFF, edx=m >> 32)


MASKS = list(range(8)) + [0xFFFFFFFFFFFFFFFF, 0x7FFFFFFF00000007, 0x0000020000000206, 0x80000005]


def xsave_family(rng, count):
    saves = [('xsave', '0fae23'), ('xsaveopt', '0fae33')]
    for name, code in saves:
        for m in MASKS:
            for j, (cw, sw) in enumerate(((0x37f, 0x2800), (0x37e, 0x3881), (0x27f, 0x0020))):
                a, b = VALUES[(j * 5 + m) % len(VALUES)], VALUES[(j * 3 + 2 + m) % len(VALUES)]
                raw = record(code, a=a, b=b, cw=cw, sw=sw, mxcsr=0x1f80 | (j << 13), memory_kind=KIND,
                             seed=rng.getrandbits(32) | 1)
                yield _with_regs(raw, **_mask(m)), meta('xsave_save', name, code, mask=m, pending=sw >> 7 & 1)
    # XRSTOR: zero header (seed 0), the 64-byte patch holds the x87 environment and MXCSR
    for m in MASKS:
        for mx in (0x1f80, 0x3fc0, 0xffff, 0x11f80):
            mem = bytearray(64)
            struct.pack_into('<HHB', mem, 0, 0x27f, 0x3800, 0xff)
            struct.pack_into('<I', mem, 24, mx)
            raw = record('0fae2b', seed=0, mem=bytes(mem), memory_kind=KIND)
            yield _with_regs(raw, **_mask(m)), meta('xsave_restore', 'xrstor_init', '0fae2b', mask=m, mxcsr=mx)
        raw = record('0fae2b', seed=rng.getrandbits(32) | 1, memory_kind=KIND)
        yield _with_regs(raw, **_mask(m)), meta('xsave_restore', 'xrstor_random', '0fae2b', mask=m)
    for name, code in saves + [('xrstor', '0fae2b')]:
        for off in (8, 16, 32, 48):
            raw = record(code, address=0x10000 + off, memory_kind=KIND, seed=0)
            yield _with_regs(raw, **_mask(7)), meta('xsave_fault', name + '_misaligned', code, offset=off)
    for ecx in (0, 1, 2, 0x80000000):
        raw = record('0f01d0')
        yield _with_regs(raw, ecx=ecx), meta('xsave_xcr', 'xgetbv', '0f01d0', ecx=ecx,
                                            reason='XCR0 of a Zen 2 Linux host (7)' if ecx == 0 else '')
    raw = record('0f01d1')
    yield _with_regs(raw, ecx=0, eax=7, edx=0), meta('xsave_xcr', 'xsetbv', '0f01d1')


def xsavec_family(rng, count):
    for m in MASKS:
        for j, (cw, sw) in enumerate(((0x37f, 0x2800), (0x37e, 0x3881))):
            raw = record('0fc723', cw=cw, sw=sw, a=VALUES[(m + j) % len(VALUES)], memory_kind=KIND,
                         mxcsr=0x1f80 if j == 0 else 0x9fc0, seed=rng.getrandbits(32) | 1)
            yield _with_regs(raw, **_mask(m)), meta('xsave_compacted', 'xsavec', '0fc723', mask=m)


def xsaves_family(rng, count):
    # XSAVES and XRSTORS are privileged: #GP(0) at CPL 3
    for name, code in (('xsaves', '0fc72b'), ('xrstors', '0fc71b')):
        raw = record(code, memory_kind=KIND)
        yield _with_regs(raw, **_mask(7)), meta('xsave_privileged', name, code)
