#!/usr/bin/env python3
"""Fail closed on missing records, unsupported model instructions, or mismatches."""
import json
import sys
from pathlib import Path

def read(path, n):
    lines=Path(path).read_text().splitlines()
    if not lines or lines[-1]!='END' or not lines[0].startswith('BEGIN '):
        raise ValueError(f'{path}: incomplete run')
    if int(lines[0].split()[1],16)!=n or len(lines)!=n+2:
        raise ValueError(f'{path}: wrong record count')
    out=[]
    for k,line in enumerate(lines[1:-1]):
        row=[int(x,16) for x in line.split()]
        if len(row)!=58 or row[0]!=k: raise ValueError(f'{path}: malformed record {k}')
        out.append(row)
    return out

def compare(meta, reference, model):
    meta=json.loads(Path(meta).read_text());q=read(reference,len(meta));m=read(model,len(meta))
    labels=['index','vector','error','rip']+[f'r{k}' for k in range(16)]+['rflags','cr2','memory_hash','pte0','pte1']+[f'xmm{k//2}.{"lo" if k%2==0 else "hi"}' for k in range(32)]+['mxcsr']
    errors=0
    for spec,a,b in zip(meta,q,m):
        # Only undefined arithmetic flags are masked; all registers and memory effects compare.
        mask=spec['mask'] if a[1] in (1,3) else 0xDD5
        a[20]&=mask;b[20]&=mask
        differences=[f'{labels[k]}: qemu={x:016x}, lean={y:016x}' for k,(x,y) in enumerate(zip(a,b)) if x!=y]
        if differences:
            errors+=1
            if errors<=20:
                print(f"vector {spec['index']} ({spec['family']}, {spec['code']}): "+'; '.join(differences))
    print(f'{len(meta)} vectors, {errors} mismatches')
    return bool(errors)

if __name__=='__main__': sys.exit(compare(*sys.argv[1:]))
