#!/usr/bin/env python3
"""Fail closed on missing records, unsupported model instructions, or mismatches."""
import json
import sys
from pathlib import Path

PREFIXES={0x26,0x2e,0x36,0x3e,0x64,0x65,0x66,0x67,0xf0,0xf2,0xf3}

def rmw_destination(code):
    """Read-modify-write with a memory destination (the lockable instructions, shifts, SHLD/SHRD).
    The model, like the CPU of the hardware campaigns, translates it with write intent on the first
    access; QEMU's TCG reads it first and writes afterwards."""
    b=bytes.fromhex(code);k=0
    while k<len(b) and (b[k] in PREFIXES or 0x40<=b[k]<=0x4f): k+=1
    if k+1>=len(b): return False
    op=b[k];k+=1
    if op==0x0f: op=0x100|b[k];k+=1
    if k>=len(b) or b[k]>>6==3: return False
    reg=(b[k]>>3)&7
    return ((op<0x40 and op&7 in (0,1) and op>>3!=7) or (op in (0x80,0x81,0x83) and reg!=7)
            or op in (0xc0,0xc1,0xd0,0xd1,0xd2,0xd3,0x86,0x87) or (op in (0xf6,0xf7) and reg in (2,3))
            or (op in (0xfe,0xff) and reg in (0,1)) or op in (0x1a4,0x1a5,0x1ac,0x1ad,0x1ab,0x1b3,0x1bb)
            or (op==0x1ba and reg>=5) or op in (0x1b0,0x1b1,0x1c0,0x1c1) or (op==0x1c7 and reg==1))

def qemu_as_hardware(code, q, m):
    """Rewrite exactly the fields of QEMU's row that show TCG's read-first RMW signature (as in
    ../validation/TestMain.lean): a #PF without the W bit, possibly on the next page of a crossing
    operand whose first page is read-only, and A where the write-intent walk sets A and D or faults
    before setting A. Every other field is still compared."""
    if q[1]!=14 or m[1]!=14 or not rmw_destination(code): return q
    q=list(q)
    if not q[2]&2 and m[2]&2 and m[21]<q[21] and q[21]&0xfff==0 and q[21]-m[21]<16: q[2],q[21]=m[2],m[21]
    if not q[2]&2 and m[2]==q[2]|2: q[2]=m[2]
    for k in (23,24):
        if (q[k]&0x20 and m[k]==q[k]&~0x20) or m[k] in (q[k]|0x40,q[k]|0x60): q[k]=m[k]
    return q

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
    errors=tcg=0
    for spec,a,b in zip(meta,q,m):
        # Only undefined arithmetic flags are masked; all registers and memory effects compare.
        mask=spec['mask'] if a[1] in (1,3) else 0xDD5
        a[20]&=mask;b[20]&=mask
        h=qemu_as_hardware(spec['code'],a,b)
        if h!=a and h==b: tcg+=1
        a=h
        differences=[f'{labels[k]}: qemu={x:016x}, lean={y:016x}' for k,(x,y) in enumerate(zip(a,b)) if x!=y]
        if differences:
            errors+=1
            if errors<=20:
                print(f"vector {spec['index']} ({spec['family']}, {spec['code']}): "+'; '.join(differences))
    print(f'{len(meta)} vectors, {errors} mismatches ({tcg} known QEMU deviations accepted)')
    return bool(errors)

if __name__=='__main__': sys.exit(compare(*sys.argv[1:]))
