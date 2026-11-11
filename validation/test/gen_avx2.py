#!/usr/bin/env python3
"""'ext' family generator for the AVX2, FMA3 and F16C forms of isa_forms.IMPLEMENTED (owner 'Avx2',
x86_32/X86/Ext/Avx2.lean), in 32-bit mode.

`gen(g)` returns the bytes of one random instance of a form of SPECS and sets up `g` (gen.Gen), like
gen_avx.py: two- or three-byte VEX prefix, VEX.L, VEX.W, VEX.vvvv, ModRM (register or memory:
absolute, or gen.Gen.modrm's addressing; 16-bit addressing and segment overrides sometimes), imm8
and is4. A tenth of the cases break one encoding rule (VEX.L, VEX.W, VEX.vvvv, ModRM.mod or reg).
The vector state (XMM0-7, YMM0-7 bits 255:128), MXCSR, EFLAGS and memory are compared by x86test.

Gathers (VEX.66.0F38 90..93) have their own generator (`gather`): VSIB with every scale, with and
without a base register, dword and qword indices, VEX.128/256, VEX.W, and the #UD forms (dest, mask
and index not distinct, ModRM.mod = 11b, no VSIB byte (ModRM.rm != 100b), 16-bit addressing). The
index and mask registers come from the vector pattern of the data seed (gen.vec_pattern), so the seed
is chosen such that every selected element (mask sign bit) addresses the data area: with random
32-bit indices that leaves at most one selected element (the system test t_avx2.c gathers many,
across faults). With paging, a selected element on a not-present or user-inaccessible data page
faults: the model and QEMU then agree on the partial state (no element before it is selected).

TCG behaviours that are not generated (the system tests check them):
* VPMASKMOVD/Q loads with paging: TCG loads the whole operand, so masked-out elements on a
  not-present page fault (as VMASKMOVPS/PD, gen_avx.py); these vectors run without paging;
* is4 with imm8[7] = 1 (VPBLENDVB ymm): TCG uses imm8[7:4] as the register number (gen_avx.py);
* binary16 denormal inputs of VCVTPH2PS: TCG applies MXCSR.DAZ to them and reports DE (AMD APM vol. 4
  VCVTPH2PS: "MXCSR.DAZ is ignored and no MXCSR denormal exception is reported"); the data seed is
  chosen without them;
* VCVTPS2PH with MXCSR.FTZ = 1: TCG flushes tiny results to zero (AMD APM vol. 4 VCVTPS2PH:
  "MXCSR[FTZ] has no effect on this instruction"); generated with FTZ = 0 (g.mxcsr_clear);
* VEX.L = 1 of the scalar FMA forms (VFMADD132SS .. VFNMSUB231SD, "VEX.LIG"): TCG keeps bits 255:128
  of the destination instead of zeroing them (SDM VFMADD132SS: "DEST[MAXVL-1:128] <- 0"); generated
  with VEX.L = 0 (G0), the system test checks VEX.L = 1 in its model-only part (avx2m.lig).
"""
import random
import struct

import isa_forms
from gen_avx import DATA, DATA_SIZE, vex_bytes, words, _addr

SPECS = {}


def _add(map_, pp, ops, flags):
    for op in ops:
        SPECS[(map_, pp, op)] = flags


R = lambda a, b: list(range(a, b + 1))
# flags: as gen_avx.py (V VEX.vvvv source, L0/L1 required VEX.L, W0/W1 required VEX.W, M/R memory /
# register only, A aligned, I imm8, S store, sN size N, sv 16/32 by VEX.L, sh 8/16 by VEX.L, gd/gr GPR
# operand, G0 VEX.L ignored but generated as 0), plus: fs FMA scalar (4/8 bytes by VEX.W), x special (by opcode), G gather.
SHIFTS = [0xD1, 0xD2, 0xD3, 0xE1, 0xE2, 0xF1, 0xF2, 0xF3]
_add(1, 1, [op for op in R(0x60, 0x6D) + [0x74, 0x75, 0x76] + R(0xD1, 0xD5) + R(0xD8, 0xDF) + R(0xE0, 0xE5) +
            R(0xE8, 0xEF) + R(0xF1, 0xF6) + R(0xF8, 0xFE) if op not in SHIFTS], 'V L1 sv')
_add(1, 1, SHIFTS, 'V L1 s16')
_add(1, 1, [0x70], 'L1 I sv')
_add(1, 1, [0x71, 0x72, 0x73], 'V R L1 I x')
_add(1, 1, [0xD7], 'R L1 gd')
_add(1, 2, [0x70], 'L1 I sv')
_add(1, 3, [0x70], 'L1 I sv')
_add(2, 1, R(0x00, 0x0B) + [0x28, 0x29, 0x2B] + R(0x37, 0x40), 'V L1 sv')
_add(2, 1, [0x1C, 0x1D, 0x1E], 'L1 sv')
for op, n in zip([0x20, 0x21, 0x22, 0x23, 0x24, 0x25], [16, 8, 4, 16, 8, 16]):
    _add(2, 1, [op, op + 0x10], 'L1 s%d' % n)
_add(2, 1, [0x2A], 'M A L1 s32')
_add(2, 1, [0x13], 'W0 sh')
_add(2, 1, [0x16, 0x36], 'V W0 L1 s32')
_add(2, 1, [0x18], 'R W0')
_add(2, 1, [0x19], 'R W0 L1')
_add(2, 1, [0x45, 0x47], 'V sv')
_add(2, 1, [0x46], 'V W0 sv')
_add(2, 1, [0x58], 'W0 s4')
_add(2, 1, [0x59], 'W0 s8')
_add(2, 1, [0x78], 'W0 s1')
_add(2, 1, [0x79], 'W0 s2')
_add(2, 1, [0x5A], 'M W0 L1 s16')
_add(2, 1, [0x8C], 'V M sv x')
_add(2, 1, [0x8E], 'V M sv S')
_add(2, 1, R(0x90, 0x93), 'G')
for hi in (0x90, 0xA0, 0xB0):
    _add(2, 1, [hi + 6, hi + 7, hi + 8, hi + 10, hi + 12, hi + 14], 'V sv')
    _add(2, 1, [hi + 9, hi + 11, hi + 13, hi + 15], 'V G0 fs')
_add(3, 1, [0x1D], 'W0 I sh S')
_add(3, 1, [0x00, 0x01], 'W1 L1 I s32')
_add(3, 1, [0x02], 'V W0 I sv')
_add(3, 1, [0x0E, 0x0F, 0x42], 'V L1 I sv')
_add(3, 1, [0x4C], 'V W0 L1 I sv')
_add(3, 1, [0x38], 'V W0 L1 I s16')
_add(3, 1, [0x39], 'W0 L1 I s16 S')
_add(3, 1, [0x46], 'V W0 L1 I s32')

REGS = {(1, 1, 0x71): (2, 4, 6), (1, 1, 0x72): (2, 4, 6), (1, 1, 0x73): (2, 3, 6, 7)}


def _check_specs():
    """Every spec is an implemented Avx2 form and every implemented Avx2 form has a spec."""
    for (m, pp, op), fl in SPECS.items():
        fl = fl.split()
        L = 0 if 'L0' in fl else 1
        W = 1 if 'W1' in fl else 0
        mod = 3 if 'R' in fl else 0
        reg = REGS.get((m, pp, op), (None,))[0]
        rm = 4 if 'G' in fl else None
        assert any(isa_forms._matches(f, 'vex', m, pp, op, mod, reg, rm, L, W)
                   for f in isa_forms.IMPLEMENTED if f.owner == 'Avx2'), 'not in IMPLEMENTED: %r' % ((m, pp, op),)
    for f in isa_forms.IMPLEMENTED:
        if f.owner == 'Avx2':
            for op in f.ops:
                assert (f.map, f.pp, op) in SPECS, 'no spec for %r' % ((f.map, f.pp, op),)


_check_specs()


def _size(fl, L, W):
    for f in fl:
        if f.startswith('s') and f[1:].isdigit():
            return int(f[1:])
    if 'sh' in fl:
        return 16 if L else 8
    if 'fs' in fl:
        return 8 if W else 4
    return 32 if L else 16


def _ymm_words(pat, r):
    """The 8 words of YMMr (low word first) from a vec_pattern list."""
    return pat[4 * r:4 * r + 4] + pat[32 + 4 * r:32 + 4 * r + 4]


def gather(g):
    """A gather (VSIB) vector; see the module documentation."""
    op = random.choice([0x90, 0x91, 0x92, 0x93])
    L, W = random.getrandbits(1), random.getrandbits(1)
    dest, mask, index = random.sample(range(8), 3)
    broken = None
    mod = random.choice([0, 0, 1, 2])
    a16 = False
    if random.random() < 0.12:
        broken = random.choice(['dm', 'di', 'mi', 'mod', 'rm', 'a16'])
        if broken == 'dm':
            mask = dest
        elif broken == 'di':
            index = dest
        elif broken == 'mi':
            index = mask
        elif broken == 'a16':
            a16 = True
    scale = random.randint(0, 3)
    nobase = mod == 0 and random.random() < 0.3
    # ESP keeps the harness stack; with mod = 00, base 101b means no base (disp32)
    base = 5 if nobase else random.choice([0, 1, 2, 3, 6, 7] + ([5] if mod else []))
    if broken == 'mod':
        modrm = bytes([0xC0 | (dest << 3) | random.randint(0, 7)])
    elif broken == 'rm':
        g.regs[1] = DATA + 0x100
        modrm = bytes([(dest << 3) | 1])                             # [ECX], no VSIB byte
    else:
        sib = bytes([(scale << 6) | (index << 3) | base])
        disp = random.choice([0, random.randint(-128, 127), random.getrandbits(32)])
        if mod == 1:
            disp = random.randint(-128, 127)
            dbytes = struct.pack('<b', disp)
        elif mod == 2 or nobase:
            dbytes = struct.pack('<I', disp & 0xFFFFFFFF)
        else:
            disp, dbytes = 0, b''
        modrm = bytes([(mod << 6) | (dest << 3) | 4]) + sib + dbytes
        # a seed whose selected elements address the data area, then the base register
        db = 64 if W else 32
        ib = 64 if op & 1 else 32
        n = (256 if L else 128) // max(db, ib)
        esz = db // 8
        for _ in range(3000):
            seed = random.getrandbits(32) | 1
            pat = words(seed ^ 0xA5A5A5A5, 64)
            m = _ymm_words(pat, mask)
            x = _ymm_words(pat, index)
            sel = [k for k in range(n) if (m[k] if db == 32 else m[2 * k + 1]) >> 31]
            raws = [((x[k] if ib == 32 else x[2 * k]) << scale) & 0xFFFFFFFF for k in sel]
            if len(raws) > 1 and max(raws) - min(raws) > 64:
                continue
            lo = min(raws) if raws else 0
            span = (max(raws) - lo) if raws else 0
            target = DATA + random.randint(0, (DATA_SIZE - esz - span) // esz) * esz
            if random.random() < 0.1:
                target = DATA + 0x1000 - esz * random.randint(0, 2) - span   # next to the 0x9000 page
            if random.random() < 0.15:
                target += random.randint(1, esz - 1)                   # misaligned element
            need = (target - lo - disp) & 0xFFFFFFFF
            if nobase:
                modrm = bytes([(dest << 3) | 4]) + sib + struct.pack('<I', (target - lo) & 0xFFFFFFFF)
            else:
                g.regs[base] = need
            g.seed = seed
            break
        else:
            return None
    vvvv = mask
    pre = b''
    if a16:
        pre += b'\x67'
    if random.random() < 0.08:
        pre += bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])])
    insn = pre + vex_bytes(2, 1, L, W, vvvv, False) + bytes([op]) + modrm
    if len(insn) > 15:
        return None
    g.desc = 'avx2-gather%02x%s:%s:v' % (op, '-' + broken if broken else '', insn.hex())
    return insn


def gen(g):
    (map_, pp, op), flags = random.choice(sorted(SPECS.items()))
    fl = flags.split()
    if 'G' in fl or random.random() < 0.12:
        return gather(g)
    key = (map_, pp, op)
    broken = random.random() < 0.1
    L = 0 if 'L0' in fl or 'G0' in fl else 1 if 'L1' in fl else random.getrandbits(1)
    W = 0 if 'W0' in fl else 1 if 'W1' in fl else random.getrandbits(1)
    mem = True if 'M' in fl else False if 'R' in fl else random.random() < 0.45
    regs = REGS.get(key)
    reg = random.choice(regs) if regs else random.randint(0, 7)
    uses_v = 'V' in fl
    vvvv = random.randint(0, 7) if uses_v else (0 if random.random() < 0.9 else 8)
    if uses_v and random.random() < 0.1:
        vvvv += 8                         # inverted VEX.vvvv[3] = 0: ignored outside 64-bit mode
    what = None
    if broken:
        what = random.choice(['L', 'W', 'mod', 'reg', 'vvvv'])
        if what == 'L' and ('L0' in fl or 'L1' in fl):
            L ^= 1
        elif what == 'W' and ('W0' in fl or 'W1' in fl):
            W ^= 1
        elif what == 'mod' and ('M' in fl or 'R' in fl):
            mem = not mem
        elif what == 'reg' and regs:
            reg = random.choice([r for r in range(8) if r not in regs])
        elif what == 'vvvv' and not uses_v:
            vvvv = random.choice([v for v in range(1, 16) if v != 8])
        else:
            what = None
    two = map_ == 1 and W == 0 and vvvv < 8 and random.random() < 0.5
    pre = b''
    if random.random() < 0.08:
        pre += bytes([random.choice([0x26, 0x36, 0x3E, 0x64, 0x65])])
    a16 = mem and random.random() < 0.08
    if a16:
        pre += b'\x67'
    body = pre + vex_bytes(map_, pp, L, W, vvvv, two) + bytes([op])
    size = _size(fl, L, W)
    addr = None
    if mem:
        if not a16 and (random.random() < 0.6 or key == (2, 1, 0x13)):
            addr = _addr(size, 'A' in fl)
            modrm = bytes([(reg << 3) | 5]) + struct.pack('<I', addr)
        else:
            modrm, _, _ = g.modrm(a16, reg, force_mem=True)
    else:
        rm = random.randint(0, 7)
        modrm = bytes([0xC0 | (reg << 3) | rm])
    if 'gd' in fl and reg == 4:
        modrm = bytes([modrm[0] & ~0x38]) + modrm[1:]   # keep ESP: ModRM.reg = EAX
    imm = b''
    if map_ == 3 or 'I' in fl:
        v = random.getrandbits(8)
        if key[2] in (0x71, 0x72, 0x73) and map_ == 1 and random.random() < 0.5:
            v = random.randint(0, 70)
        if key == (3, 1, 0x4C):
            v &= 0x7F                     # is4: imm8[7] (gen_avx.py)
        imm = bytes([v])
    insn = body + modrm + imm
    if len(insn) > 15:
        return None
    if key == (2, 1, 0x8C):
        g.no_paging = True               # VPMASKMOV load: see the module documentation
    if key == (3, 1, 0x1D):
        g.mxcsr_clear = 0x8000           # VCVTPS2PH: TCG applies MXCSR.FTZ (module documentation)
    if key == (2, 1, 0x13) and mem is not None:
        # VCVTPH2PS: no binary16 denormal among the converted elements (module documentation)
        rm = None if mem else modrm[0] & 7
        for _ in range(2000):
            seed = random.getrandbits(32) | 1
            if mem:
                if addr is None or addr % 4:
                    return None
                ws = words(seed, (addr - DATA) // 4 + size // 4)[(addr - DATA) // 4:]
            else:
                pat = words(seed ^ 0xA5A5A5A5, 64)
                ws = pat[4 * rm:4 * rm + size // 4]
            if not any((w >> s) & 0x7C00 == 0 and (w >> s) & 0x3FF for w in ws for s in (0, 16)):
                g.seed = seed
                break
        else:
            return None
    if map_ == 1 and op in SHIFTS and addr is not None and addr % 4 == 0 and random.random() < 0.7:
        # a small shift count in the low quadword of the m128 operand
        g.patches.append((addr - DATA, random.randint(0, 70)))
        g.patches.append((addr + 4 - DATA, 0))
    g.desc = 'avx2-%d%d%02x%s:%s:v' % (map_, pp, op, '-' + what if what else '', insn.hex())
    return insn
