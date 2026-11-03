#!/usr/bin/env python3
"""Generate, run both engines, compare, preserve replayable evidence."""
import argparse
import json
import subprocess
from pathlib import Path
from gen import generate
from compare import compare

ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser()
    p.add_argument('count',type=int,nargs='?',default=20000)
    p.add_argument('seed',type=int,nargs='?',default=1)
    args=p.parse_args()
    if args.count<=0: p.error('count must be positive')
    subprocess.run([str(ROOT/'test/harness/build.sh')],check=True)
    out=ROOT/'test/out';out.mkdir(exist_ok=True)
    prefix=out/f'v{args.seed}'
    generate(args.count,args.seed,prefix)
    q=out/f'q{args.seed}.txt';m=out/f'm{args.seed}.txt'
    command=['qemu-system-x86_64','-accel','tcg','-cpu','qemu64','-m','64','-kernel',str(ROOT/'test/harness/harness.elf'),'-initrd',str(prefix)+'.bin','-display','none','-serial',f'file:{q}','-monitor','none','-device','isa-debug-exit,iobase=0xf4,iosize=4','-no-reboot']
    result=subprocess.run(command,timeout=180)
    if result.returncode!=1: raise RuntimeError(f'QEMU exit status {result.returncode}; expected debug-exit status 1')
    with m.open('w') as log:
        subprocess.run([str(ROOT/'.lake/build/bin/x64test'),str(prefix)+'.bin'],stdout=log,check=True,timeout=300)
    return compare(str(prefix)+'.json',q,m)

if __name__=='__main__': raise SystemExit(main())
