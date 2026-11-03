"""Replay saved physical-CPU stack fault observations against the current IA-32 model.

Build with `lake build x86test`, then run `python3 test/stack_regression.py`.
No server, QEMU, or expected-result generation is required.
"""
import json
import subprocess
import tempfile
from pathlib import Path

from hardware import ROOT, validate_output
from native import differences


def main():
    fixture=json.loads((Path(__file__).parent/'fixtures/native_stack_faults.json').read_text())
    cases=fixture['cases']
    records=[]
    for case in cases:
        record=bytes.fromhex(case['model_record_hex'])
        assert len(record)==88 and record[1:1+record[0]].hex()==case['meta']['code']
        assert len(case['native_row'].split())==61
        records.append(record)
    with tempfile.TemporaryDirectory() as tmp:
        inp=Path(tmp)/'vectors.bin';out=Path(tmp)/'model.out'
        inp.write_bytes(b''.join(records))
        with out.open('w') as log:
            subprocess.run([ROOT/'.lake/build/bin/x86test','--native-memory',inp],
                           check=True,stdout=log,timeout=60)
        validate_output(out,len(cases),'i386',4)
        rows=out.read_text().splitlines()[1:-1]
    failures=[]
    for case,row in zip(cases,rows):
        native=[int(x,16) for x in case['native_row'].split()]
        model=[int(x,16) for x in row.split()]
        diff=differences('i386',case['meta'],native,model)
        if diff:failures.append(dict(index=case['meta']['index'],scenario=case['meta']['scenario'],differences=diff))
    for failure in failures:print(json.dumps(failure))
    print(f'{len(cases)} saved hardware stack cases, {len(failures)} mismatches')
    return int(bool(failures))


if __name__=='__main__':raise SystemExit(main())
