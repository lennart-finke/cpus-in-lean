#!/usr/bin/env python3
"""Exercise native oracle plumbing inside the existing Linux/TCG guest.

This checks the runner, not physical hardware. Known SSE TCG deviations are
recorded separately; the ordinary register vectors must match both models.
"""
import argparse
import importlib.util
import json
import os
import random
import select
import struct
import subprocess
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'test'))
from native import differences, read_native, native_columns


def member(name,payload,mode=0o100644):
    name=name.encode()+b'\0'
    fields=[1,mode,0,0,1,0,len(payload),0,0,0,0,len(name),0]
    raw=b'070701'+b''.join(f'{x:08x}'.encode() for x in fields)+name
    raw+=b'\0'*(-len(raw)%4);raw+=payload;raw+=b'\0'*(-len(payload)%4)
    return raw


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('prepared',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--count',type=int,default=100)
    p.add_argument('--cpu',default='qemu64')
    args=p.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    root=args.prepared.resolve();indexes={}
    kind=json.loads((root/'manifest.json').read_text())['kind']
    columns=native_columns(kind)
    archive=member('native-oracle',(root/'oracle').read_bytes(),0o100755)
    for arch in ('i386','x86_64'):
        data=(root/arch/'native.bin').read_bytes();count=struct.unpack_from('<Q',data)[0]
        indexes[arch]=list(range(min(args.count,count-(112 if arch=='x86_64' else 0))))
        if kind=='native-memory':
            # Uniform strides alias periodic permission/TF matrices; use a
            # reproducible sample and retain both ends of the record stream.
            indexes[arch]=sorted(set(random.Random(20261022).sample(range(count),min(args.count,count)))|{0,count-1})
        elif arch=='x86_64':
            indexes[arch]+=list(range(count-112,count))
        payload=struct.pack('<Q',len(indexes[arch]))+b''.join(data[8+i*440:8+(i+1)*440] for i in indexes[arch])
        archive+=member(arch+'.bin',payload)
    (out/'indexes.json').write_text(json.dumps(indexes,indent=2)+'\n')
    archive+=member('TRAILER!!!',b'',0)
    base=(ROOT.parent/'x86_64/guest/initramfs.cpio').read_bytes()
    initrd=out/'initramfs.cpio';initrd.write_bytes(base+b'\0'*(-len(base)%512)+archive)
    command=['qemu-system-x86_64','-accel','tcg','-cpu',args.cpu,'-m','128','-kernel',str(ROOT.parent/'x86_64/guest/bzImage'),
             '-initrd',str(initrd),'-append','console=ttyS0 nokaslr noapic nolapic','-display','none','-serial','stdio','-monitor','none','-no-reboot']
    proc=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    result=bytearray();sent=False;deadline=time.monotonic()+180
    try:
        while time.monotonic()<deadline:
            if select.select([proc.stdout],[],[],0.2)[0]:
                chunk=os.read(proc.stdout.fileno(),65536)
                if not chunk:
                    break
                result.extend(chunk)
                if not sent and b'~ # ' in result:
                    proc.stdin.write(b'dmesg -n 1; echo NATIVE32_BEGIN; /native-oracle i386 < /i386.bin 2>/err32; echo NATIVE32_STATUS:$?; echo NATIVE64_BEGIN; /native-oracle x86_64 < /x86_64.bin 2>/err64; echo NATIVE64_STATUS:$?; cat /err32 /err64; echo NATIVE_DONE\n')
                    proc.stdin.flush();sent=True
                if b'\nNATIVE_DONE\r\n' in result:
                    break
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill();proc.wait()
    text=result.decode(errors='replace').replace('\r','');(out/'qemu.log').write_text(text)
    lines=text.splitlines()
    if 'NATIVE_DONE' not in lines:
        raise RuntimeError('Linux guest smoke test did not finish')
    failed=False
    for arch,num in [('i386','32'),('x86_64','64')]:
        first=lines.index('NATIVE'+num+'_BEGIN')+1
        last=lines.index('NATIVE'+num+'_STATUS:0')
        path=out/(arch+'.out');path.write_text('\n'.join(lines[first:last])+'\n')
        hardware=read_native(path,len(indexes[arch]),columns)
        metadata=json.loads((root/arch/'vectors.json').read_text())
        model=[[int(x,16) for x in line.split()] for line in (root/arch/'model.out').read_text().splitlines()[1:-1]]
        bad=[]
        for h,i in zip(hardware,indexes[arch]):
            diff=differences(arch,metadata[i],h,model[i])
            if diff:
                item=dict(index=i,code=metadata[i]['code'],family=metadata[i]['family'],differences=diff)
                # TCG reports the REP start after the final single-stepped
                # iteration. Keep the counterexample; do not relax native comparison.
                if (kind=='native-memory' and item['family'].startswith('memory_rep_')
                    and h[55]==model[i][1]==1 and h[7]==model[i][5]==0
                    and h[3]==0x20100 and model[i][3]==0x20100+len(bytes.fromhex(item['code']))
                    and len(diff)==1 and diff[0].startswith('IP:')):
                    item['tcg_deviation']='REP final-iteration single-step IP; pending hardware confirmation'
                bad.append(item)
        (out/(arch+'-mismatches.json')).write_text(json.dumps(bad,indent=2)+'\n')
        ordinary=[b for b in bad if 'tcg_deviation' not in b and b['family'] not in ('hardware_daz_minmax','hardware_invalid','hardware_denormal',
                                                      'hardware_divide_zero','hardware_overflow','hardware_underflow','hardware_precision')]
        print(arch,len(indexes[arch]),'TCG smoke vectors;',len(ordinary),'ordinary mismatches;',len(bad)-len(ordinary),'TCG deviation cases')
        failed |= bool(ordinary)
    return int(failed)


if __name__=='__main__':
    sys.exit(main())
