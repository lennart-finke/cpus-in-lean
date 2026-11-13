#!/usr/bin/env python3
"""The EPYC 7742's RCPPS/RCPSS/RSQRTPS/RSQRTSS function (legacy and VEX), reconstructed from its native
results (validation/README.md, "The EPYC 7742 runs"; open question S5).

  zen2_rcp.py tables BUNDLE RESULTS   rebuild x86_32/X86/Zen2Rcp.lean from the hardware rows of the
                                       `sse_rcp_sweep` campaigns (every 12-bit entry at four points)
  zen2_rcp.py bound                   the relative error of the table function against exact 1/x and
                                       1/sqrt(x) over every input of every entry (exact rational arithmetic)

The function (also `rcp32`, `rsqrt32` below, with the tables read from Zen2Rcp.lean): for
x = (-1)^s * 2^(E-127) * 1.f with t = fraction bits 22..11 (bits 10..0 never matter):
* RCP, normal x: sign s, biased exponent 253 - E, fraction RCP[t] << 11; +-0 when 253 - E <= 0.
* RSQRT, positive normal x: E odd: exponent (379 - E)/2, fraction RSQRT_ODD[t] << 11; E even: (380 - E)/2,
  RSQRT_EVEN[t] << 11.
* NaN: quieted (also a negative NaN for RSQRT); +-0 and denormals (DAZ or not): +-inf; RCP(+-inf) = +-0;
  RSQRT(+inf) = +0; RSQRT of another negative operand: the default NaN FFC00000h. MXCSR has no effect and
  is never changed.
Every RCP/RSQRT lane of the extended EPYC run (52,794, every family, legacy and VEX, PS and SS) is
reproduced: `native_fp.py recompare` compares them strictly against the model, which computes this.
"""
import json
import math
import struct
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[1] / 'x86_32' / 'X86' / 'Zen2Rcp.lean'
NAMES = ('rcpTable', 'rsqrtOddTable', 'rsqrtEvenTable')


def read_tables(path=LEAN):
    """The three tables of Zen2Rcp.lean (lists of 4096 naturals)."""
    lines = path.read_text().splitlines()
    out = {}
    for k, line in enumerate(lines):
        for name in NAMES:
            if line.startswith(f'def {name} : Array Nat := unpack'):
                s = lines[k + 1].strip().strip('"')
                out[name] = [int(s[3 * i:3 * i + 3], 16) for i in range(len(s) // 3)]
    assert all(len(out[n]) == 4096 for n in NAMES), 'malformed Zen2Rcp.lean'
    return out[NAMES[0]], out[NAMES[1]], out[NAMES[2]]


_T = None


def _tables():
    global _T
    if _T is None: _T = read_tables()
    return _T


def _special(x, rsqrt):
    s = x >> 31; e = x >> 23 & 0xFF; f = x & 0x7FFFFF
    if e == 0xFF and f: return x | 0x400000
    if e == 0: return (s << 31) | 0x7F800000
    if rsqrt and s: return 0xFFC00000
    if e == 0xFF: return s << 31
    return None


def rcp32(x):
    r = _special(x, False)
    if r is not None: return r
    s = x >> 31; e = x >> 23 & 0xFF; t = (x & 0x7FFFFF) >> 11
    return s << 31 if 253 - e <= 0 else (s << 31) | ((253 - e) << 23) | (_tables()[0][t] << 11)


def rsqrt32(x):
    r = _special(x, True)
    if r is not None: return r
    e = x >> 23 & 0xFF; t = (x & 0x7FFFFF) >> 11
    if e & 1: return ((379 - e) // 2) << 23 | (_tables()[1][t] << 11)
    return ((380 - e) // 2) << 23 | (_tables()[2][t] << 11)


def bound():
    """max |rel. error| in units of 2^-12 over every input of every entry: the extremes lie at the interval
    ends (the product r*x and r^2*x are monotone in x within an entry), the upper end open."""
    rcp, odd, even = _tables()
    worst = {}
    for name, tab, sq, scale in (('rcp', rcp, False, 1), ('rsqrt_odd', odd, True, 1), ('rsqrt_even', even, True, 2)):
        m = Fraction(0)
        for t, r in enumerate(tab):
            y = Fraction(4096 + r, 8192)   # the result mantissa for an operand mantissa in [1, 2) (x scale)
            for tt in (t, t + 1):
                x = Fraction(4096 + tt, 4096) * scale
                b = Fraction(3, 2 ** 13)   # 1.5 * 2^-12
                if not sq:
                    err = abs(y * x - 1)
                    assert err <= b, (name, t, tt)
                    m = max(m, err)
                else:   # |y*sqrt(x) - 1| <= b  <=>  (1-b)^2 <= y^2*x <= (1+b)^2 (checked exactly)
                    v = y * y * x
                    assert (1 - b) ** 2 <= v <= (1 + b) ** 2, (name, t, tt)
                    m = max(m, Fraction(abs(math.sqrt(v) - 1)))
        worst[name] = float(m * 4096)
    return worst


def tables_from_results(bundle, results):
    """The tables from the hardware rows of the sse_rcp_sweep campaigns (each entry: four operands with
    fraction bits 22..11 = t and different bits 10..0, which must all give the same result)."""
    sys.path.insert(0, str(HERE))
    import native_fp
    src = native_fp.load_source(bundle, results)
    tabs = {('rcpps', 127): [None] * 4096, ('rsqrtps', 127): [None] * 4096, ('rsqrtps', 128): [None] * 4096}
    for spec in src['manifest']['campaigns']:
        meta = json.loads((src['bundle'] / (spec['name'] + '.json')).read_text())
        if not meta or meta[0]['family'] != 'sse_rcp_sweep': continue
        cols = native_fp.cols_of(src['manifest']['kind'], spec)
        status, rows, _ = native_fp.hardware_state(src['result'], spec, src['host']['results'].get(spec['name']), cols['native'])
        data = (src['bundle'] / (spec['name'] + '.bin')).read_bytes()
        for h in rows:
            m = meta[h[0]]
            if m.get('table') is None: continue
            rec = data[8 + h[0] * cols['size']:8 + (h[0] + 1) * cols['size']]
            x = struct.unpack_from('<2Q', rec, 176 + 16)   # XMM1 (the source of 0F 52/53 C1)
            ins = [x[0] & 0xFFFFFFFF, x[0] >> 32, x[1] & 0xFFFFFFFF, x[1] >> 32]
            r = native_fp.normalize(h)
            outs = [r[13] & 0xFFFFFFFF, r[13] >> 32, r[14] & 0xFFFFFFFF, r[14] >> 32]   # XMM0
            tab = tabs[(m['instruction'], m['exponent'])]
            for a, b in zip(ins, outs):
                assert (a & 0x7FFFFF) >> 11 == m['table'] and b >> 23 == 126 and b & 0x7FF == 0, (spec['name'], h[0])
                v = (b & 0x7FFFFF) >> 11
                assert tab[m['table']] in (None, v), ('entry not determined by bits 22..11', spec['name'], h[0])
                tab[m['table']] = v
    assert all(None not in t for t in tabs.values()), 'sweep incomplete'
    return tabs[('rcpps', 127)], tabs[('rsqrtps', 127)], tabs[('rsqrtps', 128)]


LEAN_HEAD = '''/-!
# Zen 2 RCP/RSQRT tables (generated by `validation/test/zen2_rcp.py tables`; do not edit)

The AMD EPYC 7742's RCPPS/RCPSS/RSQRTPS/RSQRTSS (legacy and VEX.128/VEX.256) on one binary32 lane,
reconstructed from hardware observations: EPYC 7742 microcode 0x830107c, native campaign `sse_rcp_sweep`
(campaigns 066-068 of the bundle ia32-epyc-ext: every 12-bit table entry at four points of its interval,
fraction bits 10..0 = 0, 7FFh and two random values, all four giving the same result), and checked against
every RCP/RSQRT lane of that run (52,794 lanes of sse_rcp_sweep, sse_random, avx_ops, avx_random and
enc_fuzz, all reproduced; `native_fp.py recompare`). The function itself is `FP.rcp`/`FP.rsqrt`
(`X86/Simd.lean`): x = (-1)^s * 2^(E-127) * 1.f, t = f >> 11 (fraction bits 22..11);
* RCP, normal x: biased result exponent 253 - E, fraction rcpTable[t] << 11, sign s; ±0 for E ≥ 253
  whatever MXCSR.FTZ;
* RSQRT, positive normal x: E odd: exponent (379 - E) / 2, fraction rsqrtOddTable[t] << 11 (x in
  [1,2)·4^k); E even: exponent (380 - E) / 2, fraction rsqrtEvenTable[t] << 11 (x in [2,4)·4^k).
Entry 0 of RCP and RSQRT_ODD is not 1.0: RCP(1.0) = 0.99975586 (3F7FF000h), RSQRT(1.0) = 0.99987793.
The tables are stored as hexadecimal strings (three digits per entry, entry 0 first; a 4096-element
array literal exceeds the elaborator's recursion depth) and unpacked once.
-/

namespace X86.Zen2Rcp

private def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87

/-- Three hexadecimal digits per entry. -/
def unpack (s : String) : Array Nat := Id.run do
  let cs := s.toList.toArray
  let mut a : Array Nat := Array.mkEmpty (cs.size / 3)
  for i in [0:cs.size / 3] do
    a := a.push (hexDigit cs[3*i]! * 256 + hexDigit cs[3*i+1]! * 16 + hexDigit cs[3*i+2]!)
  return a
'''

DOCS = {'rcpTable': 'RCPPS/RCPSS: result fraction bits 22..11 for an operand with fraction bits 22..11 = index\n'
                    '(result exponent 253 - E).',
        'rsqrtOddTable': 'RSQRTPS/RSQRTSS, odd biased exponent E (operand in [1, 2)·4^k): result exponent (379 - E) / 2.',
        'rsqrtEvenTable': 'RSQRTPS/RSQRTSS, even biased exponent E (operand in [2, 4)·4^k): result exponent (380 - E) / 2.'}


def lean(tabs):
    rcp, odd, even = tabs
    s = LEAN_HEAD
    for name, t in zip(NAMES, tabs):
        s += f'\n/-- {DOCS[name]} -/\ndef {name} : Array Nat := unpack\n  "' + ''.join(f'{v:03x}' for v in t) + '"\n'
    s += f'''
#guard rcpTable.size == 4096 && rsqrtOddTable.size == 4096 && rsqrtEvenTable.size == 4096
#guard rcpTable[0]! == {rcp[0]} && rcpTable[4095]! == {rcp[4095]}
#guard rsqrtOddTable[0]! == {odd[0]} && rsqrtEvenTable[4095]! == {even[4095]}
#guard rcpTable.foldl (· + ·) 0 == {sum(rcp)} && rsqrtOddTable.foldl (· + ·) 0 == {sum(odd)} &&
  rsqrtEvenTable.foldl (· + ·) 0 == {sum(even)}

end X86.Zen2Rcp
'''
    return s


def main():
    if len(sys.argv) == 4 and sys.argv[1] == 'tables':
        tabs = tables_from_results(sys.argv[2], sys.argv[3])
        LEAN.write_text(lean(tabs))
        print(f'{LEAN}: 3 tables of 4096 entries from the sweep')
    elif len(sys.argv) == 2 and sys.argv[1] == 'bound':
        for k, v in bound().items(): print(f'max relative error {k}: {v:.4f} * 2^-12 (<= 1.5)')
    else:
        print(__doc__); return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
