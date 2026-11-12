#!/usr/bin/env python3
"""'ext' family generator for the AVX forms of isa_forms.IMPLEMENTED (owner 'Avx',
x86_32/X86/Ext/Avx.lean): VEX-encoded SSE..SSE4.2, AES, PCLMULQDQ and the AVX-only instructions,
128- and 256-bit, in 32-bit mode.

`gen(g)` returns the bytes of one random instance of a form of SPECS and sets up `g` (gen.Gen):
VEX prefix (two- or three-byte), VEX.L, VEX.W, VEX.vvvv, ModRM (register or memory: absolute,
or gen.Gen.modrm's addressing; 16-bit addressing and segment overrides sometimes), imm8/is4, and
the implicit operands (PCMPESTRx lengths in EAX/EDX, VMASKMOVDQU's DS:EDI, a valid MXCSR image for
VLDMXCSR). A tenth of the cases break one encoding rule (VEX.L, VEX.W, VEX.vvvv, ModRM.mod or reg)
to test the #UD conditions (or, e.g. with VEX.L = 1, the AVX2 form, which the model implements too).
The vector state (XMM0-7, YMM0-7 bits 255:128), MXCSR, EFLAGS and memory are
compared by x86test.

TCG behaviours that are not generated (the system tests check them, with deviation rules or in their
model-only part):
* VRCPPS/VRSQRTPS/VRCPSS/VRSQRTSS (Q): their results are implementation specific; TCG computes them
  in MXCSR.RC and returns tiny results unflushed, the model as `X86/Simd.lean` documents (the system
  tests use round-to-nearest and no denormal inputs, as for the legacy forms);
* VCVTSI2SS/SD and VMOVSS/SD with VEX.L = 1 (LIG, SDM/APM): TCG leaves bits 255:128 of the
  destination nonzero instead of zeroing them (generated with VEX.L = 0);
* VROUNDSS/SD with VEX.L = 1: QEMU aborts (assert(!s->vex_l) in gen_VROUNDSx);
* is4 with imm8[7] = 1 (VBLENDVPS/PD, VPBLENDVB): imm8[7] is ignored outside 64-bit mode (SDM
  BLENDVPS: "In 32-bit mode, imm8[7] is ignored"; AMD APM vol. 4, VPERMIL2PD: "In non-64-bit mode,
  bit 7 is ignored"); TCG uses imm8[7:4] as the register number;
* two NaN operands of one floating-point operation: hardware returns the first source (SDM vol. 1,
  table 4-7), TCG the one with the larger significand; for the forms in NAN2 the seed is chosen so
  that the two sources have at most one NaN (none for VDPPS/VDPPD) (as gen_sse.py);
* VMINPx/VMAXPx/VMINSx/VMAXSx with MXCSR.DAZ: the result is the DAZ-flushed source (the
  comparison's operand), TCG returns the unflushed denormal (as t_simd.c's NODAZ rows for the legacy
  forms); generated with DAZ clear;
* VMASKMOVPS/PD loads with paging: TCG loads the whole operand, so masked-out elements on a
  non-present page fault; the model (SDM: "Faults occur only due to mask-bit required memory
  accesses") does not. These vectors run without paging (g.no_paging).
"""
import random
import struct

import isa_forms

DATA, DATA_SIZE = 0x8000, 8192

# (map, pp, op) -> flags (see `gen`):
#   V   VEX.vvvv is a source (otherwise it must be 1111b); Vr: only in the register form (VMOVSS/SD;
#       their loads ignore it, their stores need 1111b)
#   L0, L1 the required VEX.L (else any; G = VEX.L ignored, G0: ignored but generated as 0); W0 VEX.W
#   must be 0
#   M / R  memory / register operand only; A aligned (class 1); I imm8; S store to memory
#   sN memory operand size N; sv 16/32 by VEX.L; sh 8/16 by VEX.L; sd 8/32 by VEX.L (VMOVDDUP)
#   gr r/m is a GPR source; gw r/m is a GPR destination; gd ModRM.reg is a GPR destination
#   nf/nd: two FP sources of single/double elements (NaN choice, see the module documentation)
#   n0: no NaN source at all (VDPPS/VDPPD); x: special set-up (by opcode); Q: not generated (below)
SPECS = {}

def _add(map_, pp, ops, flags):
    for op in ops:
        SPECS[(map_, pp, op)] = flags

R = lambda a, b: list(range(a, b + 1))
# VEX.0F, no prefix
_add(1, 0, [0x10], 'sv')
_add(1, 0, [0x11], 'sv S')
_add(1, 0, [0x14, 0x15, 0x54, 0x55, 0x56, 0x57, 0x5D, 0x5F], 'V sv')
_add(1, 0, [0x28], 'A sv')
_add(1, 0, [0x29], 'A sv S')
_add(1, 0, [0x2B], 'M A sv S')
_add(1, 0, [0x2E, 0x2F], 'G s4')
_add(1, 0, [0x50], 'R gd')
_add(1, 0, [0x51, 0x5B], 'sv')
_add(1, 0, [0x52, 0x53], 'sv Q')
_add(1, 0, [0x58, 0x59, 0x5C, 0x5E], 'V sv nf')
_add(1, 0, [0x5A], 'sh')
_add(1, 0, [0xC2, 0xC6], 'V I sv')
_add(1, 0, [0x12, 0x16], 'V L0 s8')
_add(1, 0, [0x13, 0x17], 'M L0 s8 S')
_add(1, 0, [0x77], 'x')
_add(1, 0, [0xAE], 'M L0 s4 x')
# VEX.66.0F
_add(1, 1, [0x10, 0x5A, 0x5B, 0xE6], 'sv')
_add(1, 1, [0x11], 'sv S')
_add(1, 1, [0x14, 0x15, 0x54, 0x55, 0x56, 0x57, 0x5D, 0x5F], 'V sv')
_add(1, 1, [0x28, 0x6F], 'A sv')
_add(1, 1, [0x29, 0x7F], 'A sv S')
_add(1, 1, [0x2B, 0xE7], 'M A sv S')
_add(1, 1, [0x2E, 0x2F], 'G s8')
_add(1, 1, [0x50], 'R gd')
_add(1, 1, [0x51], 'sv')
_add(1, 1, [0x58, 0x59, 0x5C, 0x5E, 0x7C, 0x7D, 0xD0], 'V sv nd')
_add(1, 1, [0xC2, 0xC6], 'V I sv')
_add(1, 1, [0x12, 0x16], 'V M L0 s8')
_add(1, 1, [0x13, 0x17], 'M L0 s8 S')
_add(1, 1, R(0x60, 0x6D) + [0x74, 0x75, 0x76] + R(0xD1, 0xD5) + R(0xD8, 0xDF) + R(0xE0, 0xE5) +
     R(0xE8, 0xEF) + R(0xF1, 0xF6) + R(0xF8, 0xFE), 'V L0 sv')
_add(1, 1, [0x6E], 'L0 s4 gr')
_add(1, 1, [0x7E], 'L0 s4 S gw')
_add(1, 1, [0x70], 'L0 I sv')
_add(1, 1, [0x71, 0x72, 0x73], 'V R L0 I x')
_add(1, 1, [0xC4], 'V L0 I s2 gr')
_add(1, 1, [0xC5], 'R L0 I gd')
_add(1, 1, [0xD6], 'L0 s8 S')
_add(1, 1, [0xD7], 'R L0 gd')
_add(1, 1, [0xF7], 'R L0 x')
# VEX.F3.0F
_add(1, 2, [0x10], 'Vr G0 s4')
_add(1, 2, [0x11], 'Vr G0 s4 S')
_add(1, 2, [0x12, 0x16, 0x5B], 'sv')
_add(1, 2, [0x2A], 'V G0 s4 gr')
_add(1, 2, [0x2C, 0x2D], 'G s4 gd')
_add(1, 2, [0x51, 0x5A, 0x5D, 0x5F], 'V G s4')
_add(1, 2, [0x52, 0x53], 'V G s4 Q')
_add(1, 2, [0x58, 0x59, 0x5C, 0x5E], 'V G s4 nf')
_add(1, 2, [0xC2], 'V G I s4')
_add(1, 2, [0x6F], 'sv')
_add(1, 2, [0x7F], 'sv S')
_add(1, 2, [0xE6], 'sh')
_add(1, 2, [0x70], 'L0 I sv')
_add(1, 2, [0x7E], 'L0 s8')
# VEX.F2.0F
_add(1, 3, [0x10], 'Vr G0 s8')
_add(1, 3, [0x11], 'Vr G0 s8 S')
_add(1, 3, [0x12], 'sd')
_add(1, 3, [0x2A], 'V G0 s4 gr')
_add(1, 3, [0x2C, 0x2D], 'G s8 gd')
_add(1, 3, [0x51, 0x5A, 0x5D, 0x5F], 'V G s8')
_add(1, 3, [0x58, 0x59, 0x5C, 0x5E], 'V G s8 nd')
_add(1, 3, [0xC2], 'V G I s8')
_add(1, 3, [0x7C, 0x7D, 0xD0], 'V sv nf')
_add(1, 3, [0xE6], 'sv')
_add(1, 3, [0xF0], 'M sv')
_add(1, 3, [0x70], 'L0 I sv')
# VEX.66.0F38
_add(2, 1, R(0x00, 0x0B) + [0x28, 0x29, 0x2B] + R(0x37, 0x40) + R(0xDC, 0xDF), 'V L0 sv')
_add(2, 1, [0x1C, 0x1D, 0x1E, 0x41, 0xDB], 'L0 sv')
for op, n in zip([0x20, 0x21, 0x22, 0x23, 0x24, 0x25], [8, 4, 2, 8, 4, 8]):
    _add(2, 1, [op, op + 0x10], 'L0 s%d' % n)
_add(2, 1, [0x2A], 'M A L0 s16')
_add(2, 1, [0x0C, 0x0D], 'V W0 sv')
_add(2, 1, [0x0E, 0x0F], 'W0 sv')
_add(2, 1, [0x17], 'sv')
_add(2, 1, [0x18], 'M W0 s4')
_add(2, 1, [0x19], 'M W0 L1 s8')
_add(2, 1, [0x1A], 'M W0 L1 s16')
_add(2, 1, [0x2C, 0x2D], 'V M W0 sv x')
_add(2, 1, [0x2E, 0x2F], 'V M W0 sv S')
# VEX.66.0F3A (all with imm8)
_add(3, 1, [0x04, 0x05], 'W0 I sv')
_add(3, 1, [0x06], 'V W0 L1 I s32')
_add(3, 1, [0x08, 0x09], 'I sv')
# VROUNDSS/SD ignore VEX.L, but QEMU 11.1.2 aborts on VEX.L = 1 (assert(!s->vex_l) in gen_VROUNDSx);
# generated with VEX.L = 0 only, VEX.L = 1 is checked in the model-only system tests
_add(3, 1, [0x0A], 'V G0 I s4')
_add(3, 1, [0x0B], 'V G0 I s8')
_add(3, 1, [0x0C, 0x0D], 'V I sv')
_add(3, 1, [0x0E, 0x0F, 0x42, 0x44], 'V L0 I sv')
_add(3, 1, [0x14], 'L0 I s1 S gw')
_add(3, 1, [0x15], 'L0 I s2 S gw')
_add(3, 1, [0x16, 0x17], 'L0 I s4 S gw')
_add(3, 1, [0x18], 'V W0 L1 I s16')
_add(3, 1, [0x19], 'W0 L1 I s16 S')
_add(3, 1, [0x20], 'V L0 I s1 gr')
_add(3, 1, [0x21], 'V L0 I s4')
_add(3, 1, [0x22], 'V L0 I s4 gr')
_add(3, 1, [0x40], 'V I sv n0')
_add(3, 1, [0x41], 'V L0 I sv n0')
_add(3, 1, [0x4A, 0x4B], 'V W0 I sv')
_add(3, 1, [0x4C], 'V W0 L0 I sv')
_add(3, 1, [0x60, 0x61, 0x62, 0x63], 'L0 I sv x')
_add(3, 1, [0xDF], 'L0 I sv')

# allowed ModRM.reg values of the group forms
REGS = {(1, 1, 0x71): (2, 4, 6), (1, 1, 0x72): (2, 4, 6), (1, 1, 0x73): (2, 3, 6, 7), (1, 0, 0xAE): (2, 3)}


def _check_specs():
    """Every spec is an implemented Avx form and every implemented Avx form has a spec."""
    for (m, pp, op), fl in SPECS.items():
        L = 1 if 'L1' in fl.split() else 0
        mod = 3 if 'R' in fl.split() else 0
        reg = REGS.get((m, pp, op), (None,))[0]
        assert any(isa_forms._matches(f, 'vex', m, pp, op, mod, reg, None, L, 0)
                   for f in isa_forms.IMPLEMENTED if f.owner == 'Avx'), 'not in IMPLEMENTED: %r' % ((m, pp, op),)
    for f in isa_forms.IMPLEMENTED:
        if f.owner == 'Avx':
            for op in f.ops:
                assert (f.map, f.pp, op) in SPECS, 'no spec for %r' % ((f.map, f.pp, op),)


_check_specs()


def xorshift(x):
    x ^= (x << 13) & 0xFFFFFFFF; x ^= x >> 17; x ^= (x << 5) & 0xFFFFFFFF
    return x


def words(seed, n):
    out, s = [], seed
    for _ in range(n):
        s = xorshift(s)
        out.append(s)
    return out


def _nans(ws, double):
    if double:
        return sum(1 for k in range(0, len(ws), 2)
                   if (ws[k + 1] >> 20) & 0x7FF == 0x7FF and ((ws[k + 1] & 0xFFFFF) or ws[k]))
    return sum(1 for w in ws if (w >> 23) & 0xFF == 0xFF and w & 0x7FFFFF)


def _ymm(pat, r):
    """The 8 words of YMMr (low word first) from a vec_pattern list."""
    return pat[4 * r:4 * r + 4] + pat[32 + 4 * r:32 + 4 * r + 4]


def pick_seed(a, b, addr, nbytes, double, max_nans):
    """A data seed with at most `max_nans` NaN elements in YMMa and YMMb (or the `nbytes` at `addr`)."""
    for _ in range(2000):
        seed = random.getrandbits(32) | 1
        pat = words(seed ^ 0xA5A5A5A5, 64)
        x = _ymm(pat, a)
        if addr is None:
            y = _ymm(pat, b)
        else:
            off = addr - DATA
            if off % 4:
                return None
            y = words(seed, off // 4 + nbytes // 4)[off // 4:]
        if _nans(x, double) + _nans(y, double) <= max_nans:
            return seed
    return None


def vex_bytes(map_, pp, L, W, vvvv, two):
    vb = (~vvvv & 0xF) << 3 | (L << 2) | pp
    if two:
        return bytes([0xC5, 0x80 | vb])
    return bytes([0xC4, 0xC0 | (random.getrandbits(1) << 5) | map_, (W << 7) | vb])


def interesting_len():
    return random.choice([0, 1, 2, 7, 8, 9, 15, 16, 17, 0x80000000, 0xFFFFFFFF, random.randint(0, 40),
                          -random.randint(1, 40) & 0xFFFFFFFF, random.getrandbits(32)])


def _size(fl, L):
    for f in fl:
        if f.startswith('s') and f[1:].isdigit():
            return int(f[1:])
    if 'sh' in fl:
        return 16 if L else 8
    if 'sd' in fl:
        return 32 if L else 8
    return 32 if L else 16


def _addr(size, aligned):
    """An absolute data-area address: aligned to the operand (or 16) mostly, next to the 0x9000 page
    boundary a tenth of the time."""
    if random.random() < 0.1:
        return DATA + 0x1000 - random.choice([32, 24, 16, 12, 8, 4, 0, size])
    a = DATA + random.randint(0x100, DATA_SIZE - 0x100)
    al = max(size, 4) if aligned else random.choice([size, 16, 4, 1])
    return a & ~(al - 1) if random.random() < (0.9 if aligned else 0.6) else a


def gen(g):
    (map_, pp, op), flags = random.choice(sorted(SPECS.items()))
    fl = flags.split()
    if 'Q' in fl:
        return None
    key = (map_, pp, op)
    broken = random.random() < 0.1      # break one encoding rule
    # VEX.L
    if 'L0' in fl or 'G0' in fl:
        L = 0
    elif 'L1' in fl:
        L = 1
    else:
        L = random.getrandbits(1)
    W = 0 if 'W0' in fl else random.getrandbits(1)
    # operand kind
    if 'M' in fl:
        mem = True
    elif 'R' in fl:
        mem = False
    else:
        mem = random.random() < 0.45
    regs = REGS.get(key)
    reg = random.choice(regs) if regs else random.randint(0, 7)
    # (VMOVSS/SD: VEX.vvvv is a source of the register form and ignored by the load, Avx.lean)
    uses_v = 'V' in fl or ('Vr' in fl and not mem) or (key in ((1, 2, 0x10), (1, 3, 0x10)) and mem)
    vvvv = random.randint(0, 7) if uses_v else (0 if random.random() < 0.9 else 8)
    if uses_v and random.random() < 0.1:
        vvvv += 8                         # inverted VEX.vvvv[3] = 0: ignored outside 64-bit mode
    what = None
    if broken:
        what = random.choice(['L', 'W', 'mod', 'reg', 'vvvv'])
        if what == 'L' and ('L0' in fl or 'L1' in fl):
            L ^= 1
        elif what == 'W' and 'W0' in fl:
            W = 1
        elif what == 'mod' and ('M' in fl or 'R' in fl):
            mem = not mem
        elif what == 'reg' and regs:
            reg = random.choice([r for r in range(8) if r not in regs])
        elif what == 'vvvv' and not uses_v:
            vvvv = random.randint(1, 15)
            if vvvv == 8:
                vvvv = 9
        else:
            what = None
    if key == (1, 0, 0x77):
        mem = None
    two = map_ == 1 and W == 0 and vvvv < 8 and random.random() < 0.5
    pre = b''
    if random.random() < 0.08:
        pre += bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])])
    a16 = mem and random.random() < 0.08 and key not in ((1, 1, 0xF7), (1, 0, 0xAE))
    if a16:
        pre += b'\x67'
    body = pre + vex_bytes(map_, pp, L, W, vvvv, two) + bytes([op])
    addr = None
    size = _size(fl, L)
    if mem is None:
        modrm = b''
    elif mem:
        if not a16 and (random.random() < 0.6 or 'x' in fl or 'nf' in fl or 'nd' in fl or 'n0' in fl):
            addr = _addr(size, 'A' in fl)
            modrm = bytes([(reg << 3) | 5]) + struct.pack('<I', addr)
        else:
            modrm, _, _ = g.modrm(a16, reg, force_mem=True)
    else:
        rm = random.randint(0, 7)
        if 'gw' in fl and rm == 4:
            rm = 0                        # keep ESP
        modrm = bytes([0xC0 | (reg << 3) | rm])
    if 'gd' in fl and reg == 4 and mem is not None:
        modrm = bytes([modrm[0] & ~0x38]) + modrm[1:]   # keep ESP: ModRM.reg = EAX
        reg = 0
    imm = b''
    if map_ == 3 or 'I' in fl:
        v = random.getrandbits(8)
        if key[2] in (0x71, 0x72, 0x73) and map_ == 1 and random.random() < 0.5:
            v = random.randint(0, 70)
        if map_ == 3 and op in (0x4A, 0x4B, 0x4C):
            v &= 0x7F                     # is4: imm8[7] (see the module documentation)
        imm = bytes([v])
    insn = body + modrm + imm
    if len(insn) > 15:
        return None
    # implicit operands and special set-up
    if map_ == 3 and op in (0x60, 0x61):
        g.regs[0] = interesting_len()
        g.regs[2] = interesting_len()
    if key == (1, 1, 0xF7):              # VMASKMOVDQU: DS:EDI
        g.regs[7] = DATA + random.randint(0x100, DATA_SIZE - 0x100) if random.random() < 0.9 else \
            DATA + 0x1000 - random.randint(0, 16)
    if key == (1, 0, 0xAE) and addr is not None and reg == 2:
        # a valid MXCSR image (TCG loads reserved bits instead of raising #GP(0); the system tests
        # check that rule, simd.ldmxcsr)
        g.patches.append((addr - DATA, 0x1F80 | random.getrandbits(16) & 0xE07F))   # VLDMXCSR
    if map_ == 1 and op in (0x5D, 0x5F):
        g.mxcsr_and = ~0x40              # VMIN/VMAX: no DAZ (see the module documentation)
    if map_ == 2 and op in (0x2C, 0x2D):
        g.no_paging = True               # VMASKMOVPS/PD load: see the module documentation
    nan = 'nf' in fl or 'nd' in fl or 'n0' in fl
    if nan and mem is not None:
        double = 'nd' in fl or (map_ == 3 and op == 0x41)
        b = modrm[0] & 7 if not mem else None
        if mem and addr is None:
            return None
        seed = pick_seed(vvvv & 7, b, addr, size, double, 0 if 'n0' in fl else 1)
        if seed is None:
            return None
        g.seed = seed
    g.desc = 'avx-%d%d%02x%s:%s:v' % (map_, pp, op, '-' + what if what else '', insn.hex())
    return insn
