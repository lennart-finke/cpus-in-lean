#!/usr/bin/env python3
"""Independent reference for the XSAVE family (model-only part of t_xsave.c).

Written from the manuals, not from the Lean model: Intel SDM vol. 1, chapter 13 (13.4 XSAVE area,
13.6 XINUSE/XMODIFIED, 13.7-13.12) and the vol. 2 pseudocode of XSAVE, XSAVEOPT, XSAVEC, XSAVES,
XRSTOR and XRSTORS; AMD APM vol. 2, 11.5 (table 11-3 initial values) and vol. 4; AMD APM vol. 3,
appendix E, CPUID Fn8000_0008_EBX[2] XSaveErPtr: "FXSAVE, XSAVE, FXSAVEOPT, XSAVEC, XSAVES always save
error pointers and FXRSTOR, XRSTOR, XRSTORS always restore error pointers" -- but the EPYC 7742 itself
saves them only when FSW.ES = 1 (zeros otherwise) and restores them always, and writes the padding bytes
10..15 of the x87 register slots as zeros (native campaign families fpu_pointers, xsave_padding;
validation/README.md, "The EPYC 7742 runs"), which this reference follows. The other points where the
manuals leave the processor latitude are fixed the way x86_32/X86/Ext/Xsave.lean documents them:
  * XINUSE[i] = (bit i set by the last XRSTOR*/cleared by its init) OR (component i not in its
    initial configuration); the generated cases reset that bit with an XRSTOR before every case,
  * no modified optimization applies (the case instruction never follows an XRSTOR directly),

    xsaveref.py table N SEED > xsave_cases.h   (the case table t_xsave.c checks; default 400, 1)
    xsaveref.py selftest                        (layout and pseudocode spot checks)

Case inputs are derived from per-case seeds with xorshift32 exactly as t_xsave.c does (`gen_state`,
`gen_memory`); each table row holds those seeds, the instruction, XCR0, EDX:EAX, the header patches
and the expected vector, FNV-1a hashes of the 1024-byte area and of the observed state afterwards,
and XGETBV(1).
"""
import random
import struct
import sys

M64 = (1 << 64) - 1
# State components of the model (CPUID 0xD): x87, SSE, AVX (YMM_Hi128: 256 bytes at offset 576,
# not 64-byte aligned when compacted); IA32_XSS supports nothing (EPYC 7742).
XCR0_SUPPORTED = 0x7
EXT = {2: (256, 576, False)}          # component: (size, standard offset, 64-byte aligned when compacted)
MXCSR_MASK = 0x2FFFF   # MXCSR.MM (bit 17) with MisalignSse (AMD APM vol. 1, 4.2.2)
OPS = ['xsave', 'xsaveopt', 'xsavec', 'xsaves', 'xrstor', 'xrstors']
NOVEC = 0xFFFF


def xs(s):
    s ^= (s << 13) & 0xFFFFFFFF
    s ^= s >> 17
    s ^= (s << 5) & 0xFFFFFFFF
    return s


class Rng:
    def __init__(self, seed):
        self.s = seed or 1

    def next(self):
        self.s = xs(self.s)
        return self.s


def fnv(data):
    h = 2166136261
    for b in data:
        h = ((h ^ b) * 16777619) & 0xFFFFFFFF
    return h


class State:
    """x87 (FXSAVE-image view: ST(k) in stack order), XMM0-7, YMM0-7[255:128], MXCSR, tracking."""
    def __init__(self):
        self.init_x87()
        self.xmm = [0] * 8
        self.ymm = [0] * 8
        self.mxcsr = 0x1F80
        self.inuse = 0       # XINUSE bits set/cleared by XRSTOR*

    def init_x87(self):
        # AMD APM vol. 2, table 11-3; SDM 13.6
        self.fcw, self.fsw, self.ftw, self.fop = 0x37F, 0, 0, 0
        self.fip, self.fcs, self.fdp, self.fds = 0, 0, 0, 0
        self.st = [(0, 0)] * 8

    def x87_initial(self):
        return (self.fcw == 0x37F and self.fsw == 0 and self.ftw == 0 and self.fop == 0 and self.fip == 0 and
                self.fcs == 0 and self.fdp == 0 and self.fds == 0 and all(r == (0, 0) for r in self.st))

    def xinuse(self):
        v = self.inuse
        if not self.x87_initial(): v |= 1
        if any(self.xmm): v |= 2
        if any(self.ymm): v |= 4
        return v

    def copy(self):
        n = State()
        n.__dict__.update({k: (list(v) if isinstance(v, list) else v) for k, v in self.__dict__.items()})
        return n


def gen_state(seed, init):
    """The state t_xsave.c loads before a case (same draw order as gen_state there)."""
    r = Rng(seed)
    s = State()
    s.fcw = (r.next() & 0x0F3F) | 0x0040
    fsw = r.next() & 0x3F7F
    if fsw & ~s.fcw & 0x3F:
        fsw |= 0x8080             # ES and B consistent with the unmasked flags
    s.fsw = fsw
    s.ftw = r.next() & 0xFF
    s.fop = r.next() & 0x7FF
    s.fip = r.next()
    s.fcs = r.next() & 0xFFFF
    s.fdp = r.next()
    s.fds = r.next() & 0xFFFF
    st = []
    for _ in range(8):
        lo, hi, se = r.next(), r.next(), r.next() & 0xFFFF
        st.append((lo | hi << 32, se))
    s.st = st
    m = r.next()
    s.mxcsr = 0x1F80 if m & 7 == 0 else (m >> 16) & 0xFFFF
    s.xmm = [sum(r.next() << (32 * w) for w in range(4)) for _ in range(8)]
    s.ymm = [sum(r.next() << (32 * w) for w in range(4)) for _ in range(8)]
    if init & 1: s.init_x87()
    if init & 2: s.xmm = [0] * 8
    if init & 4: s.ymm = [0] * 8
    # loaded by XRSTOR with RFBM = 7 and XSTATE_BV = NOT init
    s.inuse = ~init & 7
    return s


def gen_memory(seed):
    r = Rng(seed ^ 0x5A5A5A5A)
    return bytearray(b''.join(struct.pack('<I', r.next()) for _ in range(256)))


def u64(mem, off): return struct.unpack_from('<Q', mem, off)[0]
def put(mem, off, fmt, v): struct.pack_into(fmt, mem, off, v)


# ---- layout (SDM 13.4) ----
def std_offset(i): return EXT[i][1]


def compact_offset(fmt, i):
    off = 576
    for j in range(2, i):
        if fmt >> j & 1 and j in EXT:
            off += EXT[j][0]
    if EXT[i][2]:
        off = (off + 63) & ~63
    return off


# ---- component save/load ----
def pointers(s):
    """(FOP, FIP, FCS, FDP, FDS) as FXSAVE and XSAVE store them: only with FSW.ES = 1 (EPYC 7742)."""
    return (s.fop, s.fip, s.fcs, s.fdp, s.fds) if s.fsw & 0x80 else (0, 0, 0, 0, 0)


def save_x87(s, mem):
    # the error pointers (FOP 11 bits; FCS and FDS zero-extended to 32 bits: the 32-bit FXSAVE image layout
    # of the legacy region) only with FSW.ES = 1; the register slots' padding as zeros (EPYC 7742)
    fop, fip, fcs, fdp, fds = pointers(s)
    struct.pack_into('<HHBBH', mem, 0, s.fcw, s.fsw, s.ftw, 0, fop)
    struct.pack_into('<IIII', mem, 8, fip, fcs, fdp, fds)
    for k, (sig, se) in enumerate(s.st):
        struct.pack_into('<QH6x', mem, 32 + 16 * k, sig, se)


def save_mxcsr(s, mem):
    struct.pack_into('<II', mem, 24, s.mxcsr, MXCSR_MASK)


def save_xmm(s, mem):
    for k, v in enumerate(s.xmm):
        mem[160 + 16 * k:176 + 16 * k] = v.to_bytes(16, 'little')


def save_ymm(s, mem, off):
    for k, v in enumerate(s.ymm):
        mem[off + 16 * k:off + 16 * k + 16] = v.to_bytes(16, 'little')


def load_x87(s, mem):
    fcw, fsw, ftw, _, fop = struct.unpack_from('<HHBBH', mem, 0)
    fip, fcs, fdp, fds = struct.unpack_from('<IHxxIH', mem, 8)
    # AMD APM vol. 5 FXRSTOR: ES (and B) recomputed from the flags and masks
    es = fsw & ~fcw & 0x3F != 0
    fsw = (fsw & 0x7F7F) | (0x8080 if es else 0)
    # the control word's reserved bits 7 and 13..15 read as 0 and bit 6 as 1 (observed on the EPYC 7742
    # for FRSTOR, native campaign family alignment_check; Bochs masks every FCW load the same way)
    s.fcw, s.fsw, s.ftw, s.fop = (fcw & 0x1F3F) | 0x40, fsw, ftw, fop & 0x7FF
    s.fip, s.fcs, s.fdp, s.fds = fip, fcs, fdp, fds          # XSaveErPtr: always loaded
    s.st = [struct.unpack_from('<QH', mem, 32 + 16 * k) for k in range(8)]


def load_xmm(mem):
    return [int.from_bytes(mem[160 + 16 * k:176 + 16 * k], 'little') for k in range(8)]


def load_ymm(mem, off):
    return [int.from_bytes(mem[off + 16 * k:off + 16 * k + 16], 'little') for k in range(8)]


class Fault(Exception):
    pass


# ---- instructions (SDM vol. 2 pseudocode) ----
def xsave(s, mem, xcr0, mask, opt):
    rfbm = xcr0 & mask
    old_bv = u64(mem, 512)
    inuse = s.xinuse()
    to_save = rfbm & inuse if opt else rfbm
    if to_save & 1: save_x87(s, mem)
    if to_save & 2: save_xmm(s, mem)
    if rfbm & 6: save_mxcsr(s, mem)
    if to_save & 4: save_ymm(s, mem, std_offset(2))
    put(mem, 512, '<Q', (old_bv & ~rfbm) | (inuse & rfbm))


def xsavec(s, mem, xcr0, xss, mask, supervisor):
    rfbm = ((xcr0 | xss) if supervisor else xcr0) & mask
    inuse = s.xinuse()
    to_save = rfbm & inuse
    if s.mxcsr != 0x1F80 and rfbm & 2:
        to_save |= 2
    if to_save & 1: save_x87(s, mem)
    if to_save & 2:
        save_mxcsr(s, mem)
        save_xmm(s, mem)
    for i in sorted(EXT):
        if rfbm >> i & 1 and to_save >> i & 1:
            save_ymm(s, mem, compact_offset(rfbm, i))
    put(mem, 512, '<Q', to_save)
    put(mem, 520, '<Q', rfbm | 1 << 63)


def xrstor(s, mem, xcr0, xss, mask, supervisor):
    enabled = (xcr0 | xss) if supervisor else xcr0
    rfbm = enabled & mask
    bv, comp = u64(mem, 512), u64(mem, 520)
    if comp >> 63 == 0:
        if supervisor: raise Fault(13)
        if bv & ~xcr0 & M64 or comp != 0 or u64(mem, 528) != 0: raise Fault(13)
        fmt = None
    else:
        if any(u64(mem, 528 + 8 * k) for k in range(6)): raise Fault(13)
        fmt = comp & ~(1 << 63)
        if fmt & ~enabled & M64 or bv & ~comp & M64: raise Fault(13)
    n = s.copy()
    if fmt is None:
        restore = rfbm & bv
        initialize = rfbm & ~bv
        if restore & 1: load_x87(n, mem)
        elif initialize & 1: n.init_x87()
        if rfbm & 6:
            n.mxcsr = u32(mem, 24)
        if restore & 2: n.xmm = load_xmm(mem)
        elif initialize & 2: n.xmm = [0] * 8
        if restore & 4: n.ymm = load_ymm(mem, std_offset(2))
        elif initialize & 4: n.ymm = [0] * 8
    else:
        restore = fmt & rfbm & bv
        initialize = (rfbm & ~bv) | (rfbm & ~fmt)
        if restore & 1: load_x87(n, mem)
        elif initialize & 1: n.init_x87()
        if restore & 2:
            n.xmm = load_xmm(mem)
            n.mxcsr = u32(mem, 24)
        elif initialize & 2:
            n.xmm = [0] * 8
            n.mxcsr = 0x1F80
        if restore & 4: n.ymm = load_ymm(mem, compact_offset(fmt, 2))
        elif initialize & 4: n.ymm = [0] * 8
    if n.mxcsr & ~MXCSR_MASK: raise Fault(13)
    n.inuse = (s.inuse & ~rfbm) | restore
    return n


def u32(mem, off): return struct.unpack_from('<I', mem, off)[0]


def observe(s):
    """What t_xsave.c reads back: an FXSAVE image (into zeros) and YMM0-7[255:128]."""
    img = bytearray(512)
    fop, fip, fcs, fdp, fds = pointers(s)   # (FXSAVE: the error pointers only with FSW.ES = 1)
    struct.pack_into('<HHBBH', img, 0, s.fcw, s.fsw, s.ftw, 0, fop)
    struct.pack_into('<IIIIII', img, 8, fip, fcs, fdp, fds, s.mxcsr, 0)   # (mask not observed)
    for k, (sig, se) in enumerate(s.st):
        struct.pack_into('<QH', img, 32 + 16 * k, sig, se)
    save_xmm(s, img)
    return bytes(img) + b''.join(v.to_bytes(16, 'little') for v in s.ymm)


def run_case(op, xcr0, mask, init, seed, patch):
    s = gen_state(seed, init)
    mem = gen_memory(seed)
    apply_patch(mem, patch)
    vec = NOVEC
    try:
        if op in ('xsave', 'xsaveopt'):
            xsave(s, mem, xcr0, mask, op == 'xsaveopt')
        elif op in ('xsavec', 'xsaves'):
            xsavec(s, mem, xcr0, 0, mask, op == 'xsaves')
        else:
            s = xrstor(s, mem, xcr0, 0, mask, op == 'xrstors')
    except Fault as f:
        vec = f.args[0]
        mem = gen_memory(seed)
        apply_patch(mem, patch)
        s = gen_state(seed, init)
    xinuse1 = xcr0 & (s.xinuse() | (2 if s.mxcsr != 0x1F80 else 0))
    return vec, fnv(mem), fnv(observe(s)), xinuse1


def apply_patch(mem, p):
    """Header patches of a restore case (t_xsave.c `patch`): XSTATE_BV, XCOMP_BV, header bytes
    16..63 zeroed and one 8-byte word of them set, MXCSR, FSW."""
    if p is None:
        return
    bv, comp, ridx, rval, mx, fsw = p
    put(mem, 512, '<Q', bv)
    put(mem, 520, '<Q', comp)
    for k in range(6):
        put(mem, 528 + 8 * k, '<Q', 0)
    if ridx < 6:
        put(mem, 528 + 8 * ridx, '<Q', rval)
    if mx != 0xFFFFFFFF:
        put(mem, 24, '<I', mx)
    put(mem, 2, '<H', fsw)


def subset(rng, m):
    return sum(1 << i for i in range(64) if m >> i & 1 and rng.random() < 0.6)


def gen_case(rng):
    op = rng.choice(OPS)
    xcr0 = rng.choice([1, 3, 7, 7])
    mask = rng.getrandbits(3) | (rng.getrandbits(64) & ~7 if rng.random() < 0.3 else 0)
    if rng.random() < 0.15: mask = M64
    init = rng.getrandbits(3) if rng.random() < 0.5 else 0
    seed = rng.getrandbits(32) | 1
    patch = None
    if op in ('xrstor', 'xrstors'):
        mem = gen_memory(seed)
        compacted = op == 'xrstors' or rng.random() < 0.5
        if compacted:
            comp = 1 << 63 | subset(rng, 7 if rng.random() < 0.9 else xcr0)
            if rng.random() < 0.1: comp &= ~(1 << 63) if op == 'xrstors' else M64
            if rng.random() < 0.05: comp |= 1 << rng.choice([3, 9, 40, 62])
        else:
            comp = 0 if rng.random() < 0.92 else (rng.getrandbits(63) or 1)
        bv = subset(rng, comp & 7 if compacted and rng.random() < 0.8 else 7)
        if rng.random() < 0.05: bv |= 1 << rng.choice([3, 9, 63])
        ridx = 6 if rng.random() < 0.85 else rng.randrange(6)
        rval = rng.getrandbits(64) or 1
        mx = rng.choice([0xFFFFFFFF, 0x1F80, 0x21F80, rng.getrandbits(16), rng.getrandbits(16)])
        if rng.random() < 0.05: mx = rng.getrandbits(32) | 0x10000
        fcw = struct.unpack_from('<H', mem, 0)[0]
        fsw = rng.getrandbits(16) & 0x3F7F
        if fsw & ~fcw & 0x3F: fsw |= 0x8080
        patch = (bv, comp, ridx, rval, mx, fsw)
    return op, xcr0, mask, init, seed, patch


def table(n, seed):
    rng = random.Random(seed)
    rows = []
    for _ in range(n):
        op, xcr0, mask, init, s, patch = gen_case(rng)
        vec, mh, sh, x1 = run_case(op, xcr0, mask, init, s, patch)
        bv, comp, ridx, rval, mx, fsw = patch or (0, 0, 6, 0, 0xFFFFFFFF, 0)
        rows.append('{%d, %d, %d, 0x%xull, 0x%x, 0x%xull, 0x%xull, %d, 0x%xull, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x},'
                    % (OPS.index(op), xcr0, init, mask, s, bv, comp, ridx, rval, mx, fsw, vec, mh, sh, x1))
    print('/* Generated by xsaveref.py table %d %d: XSAVE-family cases with expected results (see t_xsave.c). */' % (n, seed))
    print('struct xcase { u8 op, xcr0, init; u64 mask; u32 seed; u64 bv, comp; u8 ridx; u64 rval; u32 mx, fsw, vec, memh, sth, xinuse1; };')
    print('static const struct xcase xcases[] = {')
    for r in rows: print(r)
    print('};')


def selftest():
    assert compact_offset(7, 2) == 576 and compact_offset(4, 2) == 576
    s = gen_state(12345, 0)
    mem = bytearray(1024)
    xsavec(s, mem, 7, 0, M64, False)
    assert u64(mem, 520) == 1 << 63 | 7 and u64(mem, 512) == 7
    n = xrstor(State(), mem, 7, 0, M64, False)
    assert observe(n) == observe(s), 'compacted round trip'
    mem2 = bytearray(1024)
    xsave(s, mem2, 7, M64, False)
    n2 = xrstor(State(), mem2, 7, 0, M64, False)
    assert observe(n2) == observe(s), 'standard round trip'
    # XSAVEC of an initial state writes nothing but the header (MXCSR = 1F80H)
    mem3 = bytearray(b'\xAA' * 1024)
    xsavec(State(), mem3, 7, 0, 7, False)
    assert u64(mem3, 512) == 0 and mem3[:512] == b'\xAA' * 512
    print('xsaveref selftest ok')


if __name__ == '__main__':
    a = sys.argv[1:]
    if a and a[0] == 'table':
        table(int(a[1]) if len(a) > 1 else 400, int(a[2]) if len(a) > 2 else 1)
    elif a and a[0] == 'selftest':
        selftest()
    else:
        print(__doc__)
        sys.exit(2)
