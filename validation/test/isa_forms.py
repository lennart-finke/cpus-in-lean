#!/usr/bin/env python3
"""Instruction forms of the Zen 2 ISA beyond the core model, for test generation.

QEMU runs the tests with an EPYC-Rome CPU (test/run.sh, test/sys/run.sh), so it executes
instructions (SSE3, POPCNT, AVX, ...) that the model still raises #UD for. Every such form is listed
in NOT_YET_IMPLEMENTED below, and the generators (gen.py, sys/t_simd.c tables) never emit a
form that matches it: no mismatch is accepted silently, the forms are simply not tested yet.

THIS LIST MUST SHRINK TO EMPTY. A workstream that implements a feature removes its rows here
(one row per line, grouped by owner, so parallel edits merge cleanly) and adds generator rows for
the forms in IMPLEMENTED (gen.py's 'ext' family) and/or sys/t_simd.c.

A form is (encoding, map, pp, opcode byte) plus an optional ModRM constraint:
  encoding  'legacy', 'vex', or 'legacy-lock' (the legacy form with a LOCK prefix)
  map       1 = 0F, 2 = 0F 38, 3 = 0F 3A
  pp        mandatory prefix: 0 none, 1 = 66, 2 = F3, 3 = F2 (as Inst.pp); None = any
  ops       opcode bytes
  modrm     None, or (mod, reg) with mod in {'mem', 'reg', None} and reg 0..7 or None, optionally
            (mod, reg, rm) for a single register form (rm 0..7; a query without rm matches it)
Rows may be broader than the exact set of Zen 2 forms (e.g. a whole VEX opcode range); they must
not be narrower, or the '#UD' family would generate a form that QEMU executes.
"""
from collections import namedtuple

Form = namedtuple('Form', 'feature owner encoding map pp ops modrm')

def F(feature, owner, encoding, map_, pp, ops, modrm=None):
    return Form(feature, owner, encoding, map_, pp, tuple(ops), modrm)

def rng(a, b):
    return list(range(a, b + 1))

# Zen 2 forms the model does not implement yet (owner = module in x86_32/X86/Ext/).
NOT_YET_IMPLEMENTED = [
    # --- Gpr ---
    F('popcnt', 'Gpr', 'legacy', 1, 2, [0xB8]),
    F('bmi1', 'Gpr', 'legacy', 1, 2, [0xBC]),
    F('abm', 'Gpr', 'legacy', 1, 2, [0xBD]),
    F('movbe', 'Gpr', 'legacy', 2, None, [0xF0, 0xF1]),
    F('adx', 'Gpr', 'legacy', 2, None, [0xF6]),
    F('bmi', 'Gpr', 'vex', 2, None, [0xF2, 0xF3, 0xF5, 0xF6, 0xF7]),
    F('bmi2', 'Gpr', 'vex', 3, None, [0xF0]),
    F('rdrand', 'Gpr', 'legacy', 1, None, [0xC7], ('reg', 6)),
    F('rdseed', 'Gpr', 'legacy', 1, None, [0xC7], ('reg', 7)),
    F('monitor', 'Gpr', 'legacy', 1, None, [0x01], ('reg', 1)),
    F('rdtscp', 'Gpr', 'legacy', 1, None, [0x01], ('reg', 7)),
    F('clflush', 'Gpr', 'legacy', 1, 0, [0xAE], ('mem', 7)),
    F('clflushopt', 'Gpr', 'legacy', 1, 1, [0xAE], ('mem', 7)),
    F('clwb', 'Gpr', 'legacy', 1, 1, [0xAE], ('mem', 6)),
    F('rdpid', 'Gpr', 'legacy', 1, 2, [0xC7], ('reg', 7)),
    F('wbnoinvd', 'Gpr', 'legacy', 1, 2, [0x09]),
    F('prefetchw', 'Gpr', 'legacy', 1, None, [0x0D]),
    F('rdpmc', 'Gpr', 'legacy', 1, None, [0x33]),
    # --- Sse ---
    F('sse3', 'Sse', 'legacy', 1, 2, [0x12, 0x16]),
    F('sse3', 'Sse', 'legacy', 1, 3, [0x12, 0xF0]),
    F('sse3', 'Sse', 'legacy', 1, None, [0x7C, 0x7D, 0xD0]),
    F('sse4a', 'Sse', 'legacy', 1, 1, [0x78, 0x79]),
    F('sse4a', 'Sse', 'legacy', 1, 3, [0x78, 0x79]),
    F('sse4a', 'Sse', 'legacy', 1, 2, [0x2B]),
    F('sse4a', 'Sse', 'legacy', 1, 3, [0x2B]),
    F('ssse3', 'Sse', 'legacy', 2, None, rng(0x00, 0x0B) + [0x1C, 0x1D, 0x1E]),
    F('sse41', 'Sse', 'legacy', 2, None, [0x10, 0x14, 0x15, 0x17] + rng(0x20, 0x25) + rng(0x28, 0x2B) +
      rng(0x30, 0x35) + rng(0x37, 0x41)),
    F('ssse3', 'Sse', 'legacy', 3, None, [0x0F]),
    F('sse41', 'Sse', 'legacy', 3, None, rng(0x08, 0x0E) + rng(0x14, 0x17) + rng(0x20, 0x22) + rng(0x40, 0x42)),
    F('sse42', 'Sse', 'legacy', 3, None, rng(0x60, 0x63)),
    # --- Crypto ---
    F('aes', 'Crypto', 'legacy', 2, None, rng(0xDB, 0xDF)),
    F('sha', 'Crypto', 'legacy', 2, None, rng(0xC8, 0xCD)),
    F('pclmulqdq', 'Crypto', 'legacy', 3, None, [0x44]),
    F('aes', 'Crypto', 'legacy', 3, None, [0xDF]),
    F('sha', 'Crypto', 'legacy', 3, None, [0xCC]),
    # --- Xsave ---
    F('xsave', 'Xsave', 'legacy', 1, None, [0x01], ('reg', 2)),
    F('xsave', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 4)),
    F('xsave', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 5)),
    F('xsaveopt', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 6)),
    F('xsaves', 'Xsave', 'legacy', 1, None, [0xC7], ('mem', 3)),
    F('xsavec', 'Xsave', 'legacy', 1, None, [0xC7], ('mem', 4)),
    F('xsaves', 'Xsave', 'legacy', 1, None, [0xC7], ('mem', 5)),
    # --- Avx / Avx2 (VEX opcode ranges of Zen 2's AVX, AVX2, FMA3, F16C, VAES-128) ---
    F('avx', 'Avx', 'vex', 1, None, rng(0x10, 0x17) + rng(0x28, 0x2F) + rng(0x50, 0x7F) + [0xAE, 0xC2] +
      rng(0xC4, 0xC6) + rng(0xD0, 0xFE)),
    F('avx', 'Avx', 'vex', 2, None, rng(0x00, 0x4F) + rng(0x58, 0x5A) + [0x78, 0x79, 0x8C, 0x8E] +
      rng(0x90, 0x9F) + rng(0xA6, 0xAF) + rng(0xB6, 0xBF) + rng(0xDB, 0xDF)),
    F('avx', 'Avx', 'vex', 3, None, rng(0x00, 0x22) + [0x38, 0x39] + rng(0x40, 0x4C) + rng(0x60, 0x63) + [0xDF]),
    # --- Svm ---
    F('svm', 'Svm', 'legacy', 1, None, [0x01], ('reg', 3)),
]

# Forms the model implements and gen.py's 'ext' family generates. A row is a Form plus generator
# hints; see gen.py (ext_form). Empty until a workstream adds its forms.
IMPLEMENTED = [
    # --- Sys (generator: test/gen_sys.py) ---
    F('syscall', 'Sys', 'legacy', 1, None, [0x05, 0x07]),
    F('sep', 'Sys', 'legacy', 1, None, [0x34, 0x35]),
    F('smap', 'Sys', 'legacy', 1, None, [0x01], ('reg', 1, 2)),    # 0F 01 CA CLAC
    F('smap', 'Sys', 'legacy', 1, None, [0x01], ('reg', 1, 3)),    # 0F 01 CB STAC
    F('altMovCr8', 'Sys', 'legacy-lock', 1, None, [0x20, 0x22], (None, 0)),
]


def _matches(f, encoding, map_, pp, op, mod, reg, rm=None):
    if f.encoding != encoding or f.map != map_ or op not in f.ops:
        return False
    if f.pp is not None and f.pp != pp:
        return False
    if f.modrm is not None:
        m, r = f.modrm[:2]
        if m == 'mem' and mod == 3 or m == 'reg' and mod != 3:
            return False
        if r is not None and reg != r:
            return False
        if len(f.modrm) > 2 and rm is not None and rm != f.modrm[2]:
            return False
    return True


def not_yet_implemented(encoding, map_, pp, op, mod=None, reg=None, rm=None):
    """The form (with ModRM mod/reg/rm if known) is a Zen 2 form the model does not implement yet."""
    return any(_matches(f, encoding, map_, pp, op, mod, reg, rm) for f in NOT_YET_IMPLEMENTED)


def defined(encoding, map_, pp, op, mod=None, reg=None, rm=None):
    """The form may be defined on Zen 2 (listed as implemented or not yet implemented)."""
    return not_yet_implemented(encoding, map_, pp, op, mod, reg, rm) or \
        any(_matches(f, encoding, map_, pp, op, mod, reg, rm) for f in IMPLEMENTED)


def model_has(feature):
    """The model implements `feature` (no NOT_YET_IMPLEMENTED row carries it)."""
    return all(f.feature != feature for f in NOT_YET_IMPLEMENTED)


if __name__ == '__main__':
    by = {}
    for f in NOT_YET_IMPLEMENTED:
        by.setdefault(f.owner, []).append(f.feature)
    for owner, feats in by.items():
        print('%-8s %s' % (owner, ' '.join(sorted(set(feats)))))
    print('%d not-yet-implemented rows' % len(NOT_YET_IMPLEMENTED))
