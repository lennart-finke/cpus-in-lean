#!/usr/bin/env python3
"""Boot and run the same shell/workload on Lean and QEMU; require both to finish.
The QEMU baseline is produced from the same amd64 images, never the i386 baseline.
"""
import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
CMDLINE='console=ttyS0 earlyprintk=serial,ttyS0 nokaslr noapic nolapic'

def workload(data):
    text=data.decode(errors='replace').replace('\r','')
    lines=text.splitlines()
    # Match marker lines exactly, never the echoed command containing the marker.
    start=lines.index('== begin');end=lines.index('== end',start)
    return '\n'.join(lines[start:end+1])+'\n'

def qemu_run(kernel,initrd,timeout):
    cmd=['qemu-system-x86_64','-accel','tcg','-cpu','qemu64','-m','128','-kernel',str(kernel),'-initrd',str(initrd),'-append',CMDLINE,'-display','none','-serial','stdio','-monitor','none','-no-reboot']
    # Poll serial output without blocking indefinitely; inject commands at the shell prompt.
    import os,select
    proc=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    output=bytearray();sent=False;deadline=time.monotonic()+timeout
    try:
        while time.monotonic()<deadline:
            if select.select([proc.stdout],[],[],0.2)[0]:
                part=os.read(proc.stdout.fileno(),65536)
                if not part: break
                output.extend(part)
                if not sent and b'~ # ' in output:
                    proc.stdin.write(b'dmesg -n 1; uname -sm; echo $((6*7)); sh /workload.sh\n');proc.stdin.flush();sent=True
                if sent and b'\n== end' in output: return bytes(output)
            if proc.poll() is not None: break
        raise RuntimeError('QEMU did not complete the workload')
    finally:
        if proc.poll() is None: proc.terminate()
        try: proc.wait(timeout=5)
        except subprocess.TimeoutExpired: proc.kill();proc.wait()
        (ROOT/'guest/qemu.log').write_bytes(output)

def main():
    p=argparse.ArgumentParser();p.add_argument('--timeout',type=int,default=300);args=p.parse_args()
    kernel=ROOT/'guest/bzImage';initrd=ROOT/'guest/initramfs.cpio'
    for file in (kernel,initrd):
        if not file.is_file(): raise SystemExit(f'MISSING: {file}. Run guest/build.sh on Linux. Boot verification has NOT passed.')
    ref=qemu_run(kernel,initrd,args.timeout)
    command=[str(ROOT/'.lake/build/bin/x64run'),'--max','3000000000','--expect','~ # ','--send','dmesg -n 1; uname -sm; echo $((6*7)); sh /workload.sh\n','--expect','\n== end','--send','@exit',str(kernel),str(initrd),CMDLINE]
    with (ROOT/'guest/lean.log').open('wb') as log:
        result=subprocess.run(command,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout)
    data=(ROOT/'guest/lean.log').read_bytes()
    if result.returncode: raise SystemExit('FAIL: model stopped; inspect guest/lean.log')
    for name,output in [('qemu',ref),('lean',data)]:
        if b'Linux x86_64' not in output or b'\n42\r\n' not in output:
            raise SystemExit(f'FAIL: {name} shell/architecture check')
        (ROOT/f'guest/workload.{name}.txt').write_text(workload(output))
    if workload(ref)!=workload(data): raise SystemExit('FAIL: workloads differ')
    report={'kernel_sha256':hashlib.sha256(kernel.read_bytes()).hexdigest(),'initrd_sha256':hashlib.sha256(initrd.read_bytes()).hexdigest(),'workload':'identical','architecture':'x86_64'}
    (ROOT/'guest/verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: x86-64 Linux shell and workload match QEMU')

if __name__=='__main__': main()
