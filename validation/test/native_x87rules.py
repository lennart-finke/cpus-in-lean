"""Native families for rules the model still infers (bundle format v3; FP-HARDWARE.md, "The extended
bundle"; validation/README.md, "Open questions for the EPYC"). One instruction per case; outcomes the
manuals leave open are 'observe' fields, recorded exactly (raw dumps of 64 arena bytes where an image
matters) but not failed.

* `x87_control_load`: FLDCW, FLDENV and FRSTOR (32- and 16-bit formats), FXRSTOR and XRSTOR (x87
  component) loading a control word from every class of reserved/defined bit patterns (bits 6, 7, 13,
  14, 15 in all 32 combinations; PC including the reserved 01b; RC; masks): the loaded FCW is the
  outcome (compared in full, reserved bits included: the 7742 reads bits 7, 13..15 as 0 and bit 6 as
  1, `fcwLoad`); and the stores FNSTCW/FNSTENV/FXSAVE of a frame FCW with reserved bits set, with an
  exact dump of what they write;
* `fxsave_align`: FXSAVE/FXRSTOR/XSAVE/XSAVEOPT/XRSTOR with EFLAGS.AC = 0/1 and operands misaligned
  modulo 4, 16 and 64 (#AC or #GP first), also on an unmapped page (#AC, #GP or #PF);
* `xsave_padding`: exact 64-byte dumps of FXSAVE/XSAVE/XSAVEOPT images over the x87 register slots
  (bytes 10..15 of each slot), the reserved bytes, the header and the AVX area, over two different
  arena fills (written and untouched bytes are told apart);
* `x87_trans_special`: FYL2XP1, FYL2X, FPATAN, F2XM1, FSCALE, FXTRACT, FPREM, FPREM1 with +-0, +-inf,
  QNaN, SNaN, denormals, pseudo-denormals, unnormals, pseudo-NaN/infinity and ordinary values in every
  operand position, exceptions masked and unmasked (results of the transcendental ones are
  approximations: their register differences are observations, flags and stack are strict);
* `fenv16`: the 16-bit (66-prefixed) FNSTENV/FNSAVE/FLDENV/FRSTOR formats (14/94-byte images) with
  exact dumps, and their 32-bit counterparts;
* `fpu_pointers`: non-zero input FIP/FDP/FOP (installed in the 64-bit layout of the signal frame) with
  FSW.ES = 0 and 1, under x87 non-control instructions (with and without memory operands and unmasked
  exceptions), control instructions, non-x87 instructions and the image stores FXSAVE/XSAVE/FNSTENV:
  which instructions update FIP/FDP/FOP, whether FOP follows AMD's "FOP compatibility" rule, and what
  the stores write with ES = 0 and 1 (XSaveErPtr). The pointer fields and the dumps are compared
  (`compare_pointers`) and reported as observations.
"""
import struct

from fp_cases import VALUES, ONE
from native_ext import record3, meta3
from native_int import selected

EBX = 0x10200   # the image operand (arena offset 0x200; the 64-byte patch at 0x10000 stays free)
OFF = EBX - 0x10000
FULL_FCW = 0xFFFF


def fcw_patterns():
    for r in range(32):   # reserved bits 6, 7, 13, 14, 15
        reserved = (r & 1) << 6 | (r >> 1 & 1) << 7 | (r >> 2 & 7) << 13
        for pc in range(4):
            for rc in (0, 3):
                yield reserved | pc << 8 | rc << 10 | (0x3F if (r + pc) % 3 else 0x15)


def x87_control_load(rng, count):
    pats = list(fcw_patterns())
    if count < 10000: pats = pats[::16]
    for cw in pats:
        sw = 0x3800 | rng.choice((0, 0x81, 0x20))
        kw = dict(cw=0x37F, sw=0, regs={3: EBX, 0: 7, 2: 0}, seed=rng.getrandbits(32) | 1)
        # FLDCW m16
        yield record3('d92b', patches=[(OFF, cw | 0xAAAA0000)], **kw), meta3('x87_control_load', 'fldcw', 'd92b', fcw=cw, fcw_full=True)
        # FLDENV / FRSTOR, 32-bit (CW, SW, TW dwords) and 16-bit (words) formats
        for name, code, words in (('fldenv32', 'd923', 0), ('frstor32', 'dd23', 0), ('fldenv16', '66d923', 1), ('frstor16', '66dd23', 1)):
            env = [(OFF, (cw | 0xFFFF0000) if not words else cw | sw << 16), (OFF + 4, (sw | 0xFFFF0000) if not words else 0xFFFF),
                   (OFF + 8, 0xFFFFFFFF if not words else 0)]
            yield record3(code, patches=env, **kw), meta3('x87_control_load', name, code, fcw=cw, fcw_full=True)
        # FXRSTOR: legacy region with a valid MXCSR; XRSTOR: XSTATE_BV = x87 only, zero header
        fx = [(OFF, cw | sw << 16), (OFF + 4, 0xFF), (OFF + 24, 0x1F80), (OFF + 28, 0xFFFF)]
        yield record3('0fae0b', patches=fx, **kw), meta3('x87_control_load', 'fxrstor', '0fae0b', fcw=cw, fcw_full=True)
        xr = [(OFF + 512, 0, 16), (OFF + 512, 1)] + fx
        yield record3('0fae2b', patches=xr, **dict(kw, regs={3: EBX, 0: 1, 2: 0})), \
            meta3('x87_control_load', 'xrstor', '0fae2b', fcw=cw, fcw_full=True, requires_xsave=True)
    # stores of a frame FCW with reserved bits: what FNSTCW/FNSTENV/FXSAVE write (exact dump)
    for cw in pats[::2]:
        for name, code in (('fnstcw', 'd93b'), ('fnstenv32', 'd933'), ('fnstenv16', '66d933'), ('fxsave', '0fae03')):
            yield record3(code, cw=cw, regs={3: EBX}, dump=OFF), \
                meta3('x87_control_load', name + '_store', code, fcw=cw, fcw_full=True)


def fxsave_align(rng, count):
    ops = [('fxsave', '0fae03'), ('fxrstor', '0fae0b'), ('xsave', '0fae23'), ('xsaveopt', '0fae33'), ('xrstor', '0fae2b')]
    for name, code in ops:
        for off in (0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 60, 63):
            for ac in (0, 0x40000):
                for perms in ((0x67, 0x67), (0x67, 0)):
                    base = 0x10400 + off if perms == (0x67, 0x67) else 0x10F00 + off   # the image crosses into page 1
                    o = base - 0x10000
                    patches = [(o & ~3, 0x0000037F), ((o & ~3) + 24, 0x1F80), ((o & ~3) + 28, 0x1F80)]
                    if name == 'xrstor': patches += [((o & ~3) + 512, 0, 16), ((o & ~3) + 512, 1)]
                    yield record3(code, regs={3: base, 0: 7, 2: 0}, flags=0x202 | ac, permissions=perms,
                                  patches=patches if base + 600 < 0x12000 else patches[:3]), \
                        meta3('fxsave_align', name, code, offset=off, ac=ac >> 18, page=perms[1])


def xsave_padding(rng, count):
    for name, code, eax in (('fxsave', '0fae03', 0), ('xsave', '0fae23', 7), ('xsave_x87', '0fae23', 1),
                            ('xsave_sse', '0fae23', 2), ('xsaveopt', '0fae33', 7)):
        for window in (0, 64, 128, 192, 256, 448, 512, 576, 640, 704, 768):
            if name == 'fxsave' and window >= 512: continue
            for seed in (0x13579BDF, 0x2468ACE1):
                for j, (cw, sw) in enumerate(((0x37F, 0x3800), (0x37E, 0x3881))):
                    a, b = VALUES[(j * 5 + window) % len(VALUES)], VALUES[(j * 3 + 2) % len(VALUES)]
                    yield record3(code, a=a, b=b, cw=cw, sw=sw, regs={3: EBX, 0: eax, 2: 0}, seed=seed, dump=OFF + window), \
                        meta3('xsave_padding', name, code, window=window, seed=seed, compare_pointers=True,
                              observe_fields=['fip64', 'fdp64'],   # (dumps, FOP/FIP/FDP: strict since the EPYC 7742 run)
                              reason='image bytes the manuals leave reserved (exact dump)')


SPECIAL = [(0, 0), (0, 0x8000), (ONE[0], 0x7FFF), (ONE[0], 0xFFFF), (0xC000000000000000, 0x7FFF),
           (0xA000000000000000, 0x7FFF), (0x4000000000000000, 0x7FFF), (0x0000000000000001, 0), (0x8000000000000001, 0),
           (0x8000000000000000, 0), (0x4000000000000000, 0x3FFF), (ONE[0], 0x3FFF), (ONE[0], 0xBFFF),
           (0xC90FDAA22168C235, 0x4000), (0x8000000000000000, 0x3FFE), (0xB504F333F9DE6484, 0x3FFE),
           (ONE[0], 0x4040), (ONE[0], 0x3F00), (0xFFFFFFFFFFFFFFFF, 0x7FFE), (0x8000000000000000, 0xBFFE)]
TRANS = [('fyl2xp1', 'd9f9', 1), ('fyl2x', 'd9f1', 1), ('fpatan', 'd9f3', 1), ('f2xm1', 'd9f0', 0), ('fscale', 'd9fd', 0),
         ('fxtract', 'd9f4', 0), ('fprem', 'd9f8', 0), ('fprem1', 'd9f5', 0)]


def x87_trans_special(rng, count):
    approx = {'fyl2xp1', 'fyl2x', 'fpatan', 'f2xm1'}
    for name, code, _ in TRANS:
        for i, a in enumerate(SPECIAL):
            for j, b in enumerate(SPECIAL):
                if count < 10000 and (i + j) % 7: continue
                for mask in (0x3F, 0x00):
                    kw = dict(policy='observe', reason='transcendental approximation') if name in approx else {}
                    m = meta3('x87_trans_special', name, code, a=i, b=j, unmasked=mask == 0, **kw)
                    if name in ('fprem', 'fprem1'): m['sw_mask'] |= 0x4700
                    yield record3(code, a=a, b=b, cw=0x340 | mask | rng.randrange(4) << 10, tags=0xFF), m


def fenv16(rng, count):
    forms = [('fnstenv16', '66d933', 1), ('fnsave16', '66dd33', 3), ('fnstenv32', 'd933', 1), ('fnsave32', 'dd33', 3),
             ('fldenv16', '66d923', 0), ('frstor16', '66dd23', 0)]
    for name, code, store in forms:
        for top in range(8):
            for es in (0, 1):
                for window in ((0, 64) if name.startswith('fnsave') else (0,)):
                    sw = top << 11 | (0x81 if es else 0) | rng.choice((0, 0x4500))
                    cw = 0x37F if not es else 0x37E
                    tags = rng.choice((0xFF, 0x0F, 0xA5, 0))
                    patches = [(OFF, 0x027F | (top << 11 | 0x4100) << 16), (OFF + 4, 0x5555)] if not store else []
                    yield record3(code, a=VALUES[top], b=VALUES[top + 3], cw=cw, sw=sw, tags=tags, regs={3: EBX}, dump=OFF + window,
                                  ext_flags=1, fop=0x5A5, fip=0x20123, fdp=0x10345, patches=patches), \
                        meta3('fenv16', name, code, top=top, es=es, window=window, compare_pointers=True,
                              observe_fields=['fip64', 'fdp64'],   # (dumps, FOP/FIP/FDP: strict since the EPYC 7742 run)
                              reason='x87 environment image layout and pointer fields (exact dump)')


def fpu_pointers(rng, count):
    instrs = [('nop', '90'), ('mov', '8b03'), ('addps', '0f58c1'), ('fnop', 'd9d0'), ('fld1', 'd9e8'), ('fadd_st1', 'd8c1'),
              ('fld_m32', 'd903'), ('fst_m64', 'dd13'), ('fxch', 'd9c9'), ('fincstp', 'd9f7'), ('fdiv_st1', 'd8f1'),
              ('fnstcw', 'd93b'), ('fnstsw', 'dd3b'), ('fnclex', 'dbe2'), ('fldcw', 'd92b'), ('fwait', '9b'), ('fninit', 'dbe3'),
              ('emms', '0f77'), ('fxsave', '0fae03'), ('xsave', '0fae23'), ('fnstenv', 'd933'), ('fnsave', 'dd33'),
              ('fxrstor', '0fae0b')]
    for name, code in instrs:
        for es in (0, 1):
            for unmasked in (0, 1):
                for fip, fdp in ((0x20123, 0x10345), (0x123456789A, 0xFEDCBA98765)):
                    sw = 0x3800 | (0x84 if es else 0)                    # ES with a pending ZE when es = 1
                    cw = 0x37F & ~(4 if unmasked else 0) & ~(1 if es else 0) if not es else 0x37B
                    if unmasked: cw &= ~0x04
                    patches = [(OFF, 0x37F), (OFF + 24, 0x1F80)]
                    yield record3(code, a=(0, 0), b=ONE, cw=cw, sw=sw, regs={3: EBX, 0: 7, 2: 0}, ext_flags=1, fop=0x1A5,
                                  fip=fip, fdp=fdp, dump=OFF, patches=patches, mem=struct.pack('<f', 2.0) * 16), \
                        meta3('fpu_pointers', name, code, es=es, unmasked=unmasked, wide=fip > 0xFFFFFFFF, compare_pointers=True,
                              observe_fields=['fip64', 'fdp64'],   # (dumps, FOP/FIP/FDP: strict since the EPYC 7742 run)
                              reason='FIP/FDP/FOP update and save policy (open question F5, X6)')


def fam(name, gen):
    return lambda rng, count: iter(selected(name, count, gen, rng))


FAMILIES = [(fam('x87_control_load', x87_control_load), ('xsave', 'osxsave', 'avx')),
            (fam('fxsave_align', fxsave_align), ('xsave', 'osxsave', 'avx', 'xsaveopt')),
            (fam('xsave_padding', xsave_padding), ('xsave', 'osxsave', 'avx', 'xsaveopt')),
            (fam('x87_trans_special', x87_trans_special), ()),
            (fam('fenv16', fenv16), ()),
            (fam('fpu_pointers', fpu_pointers), ('xsave', 'osxsave', 'avx'))]
