#!/usr/bin/env python3
"""Exercise the FP oracle in the existing Linux/TCG guest. NOT hardware evidence.

TCG disagrees with x87 C1, unmasked SSE and other intentional probes. This checks
signal-frame plumbing, complete output and calibration; all differences are saved.
"""
import argparse
import importlib.util
import json
import subprocess
import time
from pathlib import Path

from native_fp import rows, normalize, differences, write_json
spec=importlib.util.spec_from_file_location('native_smoke',Path(__file__).parent/'native/smoke.py')
smoke=importlib.util.module_from_spec(spec);spec.loader.exec_module(smoke)
member=smoke.member


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('bundle',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--timeout',type=int,default=120)
    args=p.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    repo=Path(__file__).resolve().parents[2]
    manifest=json.loads((args.bundle/'manifest.json').read_text())
    if len(manifest['campaigns'])!=1:raise ValueError('use a --smoke bundle')
    spec=manifest['campaigns'][0];name=spec['name']
    archive=member('fp-oracle',(args.bundle/'oracle').read_bytes(),0o100755)
    archive+=member('fp.bin',(args.bundle/(name+'.bin')).read_bytes())
    archive+=member('init',b'#!/bin/sh\nexport PATH=/bin:/sbin\necho FP_BEGIN\n/fp-oracle i386 < /fp.bin\necho FP_STATUS:$?\n/bin/busybox poweroff -f\n',0o100755)
    archive+=member('TRAILER!!!',b'',0)
    base=(repo/'x86_64/guest/initramfs.cpio').read_bytes()
    initrd=args.output/'initramfs.cpio';initrd.write_bytes(base+b'\0'*(-len(base)%512)+archive)
    cmd=['qemu-system-x86_64','-accel','tcg','-cpu','max','-m','128','-kernel',str(repo/'x86_64/guest/bzImage'),
         '-initrd',str(initrd),'-append','console=ttyS0 nokaslr noapic nolapic loglevel=1','-display','none',
         '-serial','stdio','-monitor','none','-no-reboot']
    with (args.output/'guest.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT)
        try:
            deadline=time.monotonic()+args.timeout
            while proc.poll() is None and time.monotonic()<deadline:
                if 'FP_STATUS:' in (args.output/'guest.log').read_text():break
                time.sleep(0.2)
        finally:
            if proc.poll() is None:proc.terminate()
            try:proc.wait(timeout=5)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()
    lines=[line.strip() for line in (args.output/'guest.log').read_text().splitlines()]
    if 'FP_STATUS:0' not in lines:raise RuntimeError('oracle failed; inspect guest.log')
    start=lines.index(f'BEGIN {spec["count"]:016x}');end=lines.index('END',start)
    path=args.output/'native.out';path.write_text('\n'.join(lines[start:end+1])+'\n')
    native=list(rows(path,spec['count'],83));model=list(rows(args.bundle/(name+'.model'),spec['count'],55))
    metadata=json.loads((args.bundle/(name+'.json')).read_text());bad=[]
    for meta,h,m in zip(metadata,native,model):
        diff=differences(meta,normalize(h),m)
        if diff:bad.append(dict(meta,differences=diff))
    write_json(args.output/'tcg-differences.json',bad)
    calibration=[b for b in bad if b['family']=='calibration']
    if calibration:raise RuntimeError(f'calibration mismatch: {calibration}')
    print(f'{spec["count"]} complete TCG observations; {len(bad)} differences retained; calibration passed. NOT hardware validation.')


if __name__=='__main__':main()
