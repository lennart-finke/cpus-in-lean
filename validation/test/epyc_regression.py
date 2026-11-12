"""Replay saved AMD EPYC 7742 observations of the IA-32 native campaign against the current model.

`fixtures/native_epyc_fixes.json` holds a sample (up to 12 per root cause) of the cases of the first hardware
run of the native bundle (`ia32-epyc-linux`, campaigns 000-034) whose model results differed from the
hardware: FCOM/FCOMI results with unmasked exceptions, FLD ST(i) stack-fault precedence, FXTRACT, FSCALE
massive overflow, FPREM underflow, FST of denormals, F2XM1/FYL2X/FYL2XP1 domain and precision flags,
the x87 control word and environment images, FXSAVE padding and #AC, MASKMOVDQU #AC, misaligned SHA
operands, RORX with VEX.vvvv != 1111b, and the undefined flags of LZCNT/TZCNT/BEXTR. Each case is the
776-byte input record (bundle format v2) and the hardware's raw output row; the expected state is the hardware's, never
the model's.

The comparison is stricter than the campaign's (`native_fp.differences`): every column except FIP, FDP
and FOP is compared unmasked (all FSW bits, including the condition codes, all EFLAGS bits except RF,
which Linux's signal frame sets for faults), and empty x87 register payloads only when both sides mark
the register empty.

Build with `lake build x86fp`, then run `python3 test/epyc_regression.py` (also a unit test).
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import native_fp  # noqa: E402

X86FP = Path(os.environ.get('X86FP', HERE.parent / '.lake/build/bin/x86fp'))


def raw_differences(h, m):
    out = []
    for k, (a, b) in enumerate(zip(h, m)):
        if k in (33, 34, 35) or a is None:
            continue
        if 36 <= k < 52:
            ht = (h[31] >> 11) & 7
            mt = (m[31] >> 11) & 7
            if not (h[32] >> (ht + (k - 36) // 2) % 8) & 1 and not (m[32] >> (mt + (k - 36) // 2) % 8) & 1:
                continue
        if k == 4:
            a &= ~0x10000
            b &= ~0x10000
        if a != b:
            out.append(dict(field=native_fp.LABELS[k], hardware=f'{a:x}', model=f'{b:x}'))
    return out


def main():
    fixture = json.loads((HERE / 'fixtures/native_epyc_fixes.json').read_text())
    cases = fixture['cases']
    cols = native_fp.KINDS['ia32-fp-v2']
    records = []
    for case in cases:
        record = bytes.fromhex(case['record_hex'])
        assert len(record) == cols['size'] and record[1:1 + record[0]].hex() == case['code']
        assert len(case['native_row'].split()) == cols['native']
        records.append(record)
    with tempfile.TemporaryDirectory() as tmp:
        inp = Path(tmp) / 'cases.bin'
        out = Path(tmp) / 'model.out'
        inp.write_bytes((len(records) | 1 << 63).to_bytes(8, 'little') + b''.join(records))
        with out.open('w') as log:
            subprocess.run([str(X86FP), '--compat', str(inp)], check=True, stdout=log, timeout=600)
        model = list(native_fp.rows(out, len(cases), cols['model']))
    failures = []
    for case, m in zip(cases, model):
        h = [int(x, 16) for x in case['native_row'].split()]
        h[0] = m[0]   # the row index of the original campaign
        diff = raw_differences(native_fp.normalize(h), m)
        if diff:
            failures.append(dict(cluster=case['cluster'], campaign=case['campaign'], index=case['index'],
                                 instruction=case['instruction'], code=case['code'], differences=diff))
    for failure in failures:
        print(json.dumps(failure))
    print(f'{len(cases)} saved EPYC 7742 cases in {len(fixture["clusters"])} root causes, {len(failures)} mismatches')
    return int(bool(failures))


if __name__ == '__main__':
    raise SystemExit(main())
