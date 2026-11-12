#!/usr/bin/env python3
"""Exercise the FP oracle in the existing Linux/TCG guest. NOT hardware evidence.

Runs every campaign of a prepared bundle (normally a `--smoke` one: a sample of every family and
instruction) with the real oracle inside the x86-64 Linux guest under QEMU/TCG (`-cpu max`), in one
boot: the CPUID dump first, then each campaign whose CPUID features the TCG CPU reports (the others are
skipped and listed, as `native_fp.py run` does on hardware). It checks signal-frame plumbing, complete
and well-formed output, the calibration cases and that the YMM upper halves are captured; every TCG/model
difference is saved (`tcg-differences.json`) and counted per family. TCG disagrees with x87 C1, unmasked
SSE and other intentional probes, so differences are expected; crashes, malformed or missing output are
errors.
"""
import argparse
import collections
import importlib.util
import json
import subprocess
import time
from pathlib import Path

from native_fp import rows, normalize, differences, write_json, KINDS, parse_cpuid, has_feature, FEATURES
spec=importlib.util.spec_from_file_location('native_smoke',Path(__file__).parent/'native/smoke.py')
smoke=importlib.util.module_from_spec(spec);spec.loader.exec_module(smoke)
member=smoke.member


def vex(code):
    """(map, L, pp, opcode) of a VEX instruction after optional legacy prefixes, or None."""
    b = bytes.fromhex(code)
    i = 0
    while i < len(b) and b[i] in (0x26, 0x2e, 0x36, 0x3e, 0x64, 0x65, 0x66, 0x67, 0xf2, 0xf3, 0xf0):
        i += 1
    if i + 2 < len(b) and b[i] == 0xc5 and b[i + 1] >> 6 == 3:
        return 1, b[i + 1] >> 2 & 1, b[i + 1] & 3, b[i + 2]
    if i + 3 < len(b) and b[i] == 0xc4 and b[i + 1] >> 6 == 3:
        return b[i + 1] & 0x1f, b[i + 2] >> 2 & 1, b[i + 2] & 3, b[i + 3]
    return None


def tcg_aborts(meta):
    """QEMU 11.1.2 aborts (an assertion in TCG's translator, not a guest fault) on VEX.L = 1 of
    VROUNDSS/VROUNDSD (gen_VROUNDSx) and on VEX.NP.0F C4 (gen_pinsr); such cases cannot run under TCG
    and are left out of the smoke run (listed in summary.json); hardware runs them."""
    v = vex(meta['code'])
    return v is not None and (v[0] == 3 and v[3] in (0x0a, 0x0b) and v[1] == 1 or v[0] == 1 and v[3] == 0xc4 and v[2] == 0)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('bundle',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--timeout',type=int,default=600)
    args=p.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    repo=Path(__file__).resolve().parents[2]
    manifest=json.loads((args.bundle/'manifest.json').read_text())
    campaigns=manifest['campaigns']
    archive=member('fp-oracle',(args.bundle/'oracle').read_bytes(),0o100755)
    script='#!/bin/sh\nexport PATH=/bin:/sbin\n/fp-oracle cpuid\n'
    size=KINDS[manifest['kind']]['size'];kept={};left_out=[]
    for c in campaigns:
        metadata=json.loads((args.bundle/(c['name']+'.json')).read_text())
        data=(args.bundle/(c['name']+'.bin')).read_bytes()
        keep=[i for i,m in enumerate(metadata) if not tcg_aborts(m)]
        left_out+=[dict(m,campaign=c['name']) for i,m in enumerate(metadata) if tcg_aborts(m)]
        kept[c['name']]=keep
        c['count']=len(keep)
        body=b''.join(data[8+i*size:8+(i+1)*size] for i in keep)
        archive+=member(c['name']+'.bin',(len(keep)|1<<63).to_bytes(8,'little')+body)
        # run only if TCG reports the campaign's features: decided on the host after the CPUID dump would
        # need a second boot, so every campaign runs and the host discards (and reports) the gated ones
        script+=f'echo FP_BEGIN {c["name"]}\n/fp-oracle i386 < /{c["name"]}.bin\necho FP_STATUS {c["name"]} $?\n'
    script+='echo FP_ALL_DONE\n/bin/busybox poweroff -f\n'
    archive+=member('init',script.encode(),0o100755)
    archive+=member('TRAILER!!!',b'',0)
    base=(repo/'x86_64/guest/initramfs.cpio').read_bytes()
    initrd=args.output/'initramfs.cpio';initrd.write_bytes(base+b'\0'*(-len(base)%512)+archive)
    cmd=['qemu-system-x86_64','-accel','tcg','-cpu','max','-m','512','-kernel',str(repo/'x86_64/guest/bzImage'),
         '-initrd',str(initrd),'-append','console=ttyS0 nokaslr noapic nolapic loglevel=1','-display','none',
         '-serial','stdio','-monitor','none','-no-reboot']
    log_path=args.output/'guest.log';started=time.monotonic()
    with log_path.open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT)
        try:
            deadline=time.monotonic()+args.timeout
            while proc.poll() is None and time.monotonic()<deadline:
                if 'FP_ALL_DONE' in log_path.read_text(errors='replace'):break
                time.sleep(0.5)
        finally:
            if proc.poll() is None:proc.terminate()
            try:proc.wait(timeout=5)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()
    lines=[line.strip() for line in log_path.read_text(errors='replace').splitlines()]
    if 'FP_ALL_DONE' not in lines:raise RuntimeError('the guest did not finish (timeout?); inspect guest.log')
    c0=lines.index('BEGIN CPUID');c1=lines.index('END',c0)
    (args.output/'cpuid.txt').write_text('\n'.join(lines[c0:c1+1])+'\n')
    cpuid=parse_cpuid('\n'.join(lines[c0:c1+1]))
    features=sorted(f for f in FEATURES if has_feature(cpuid,f))
    cols=KINDS[manifest['kind']]
    bad=[];per_family=collections.Counter();cases=collections.Counter();skipped={};ymm=0;total=0;errors=[]
    for c in campaigns:
        name=c['name'];missing=[f for f in c.get('requires',[]) if f not in features]
        status=[l for l in lines if l.startswith(f'FP_STATUS {name} ')]
        if missing:
            skipped[name]=dict(count=c['count'],missing=missing);continue
        if status!=[f'FP_STATUS {name} 0']:
            errors.append(f'{name}: oracle status {status}');continue
        begin=lines.index(f'FP_BEGIN {name}');status_at=lines.index(f'FP_STATUS {name} 0')
        header=f'BEGIN {c["count"]:016x}'
        if header not in lines[begin:status_at]:
            errors.append(f'{name}: no output header');continue
        start=lines.index(header,begin)
        end=lines.index('END',start)
        path=args.output/(name+'.out');path.write_text('\n'.join(lines[start:end+1])+'\n')
        try:
            native=list(rows(path,c['count'],cols['native']))
        except ValueError as e:
            errors.append(f'{name}: {e}');continue
        full=json.loads((args.bundle/(name+'.json')).read_text())
        allmodel=list(rows(args.bundle/(name+'.model'),len(full),cols['model']))
        metadata=[full[i] for i in kept[name]];model=[allmodel[i] for i in kept[name]]
        for meta,h,m in zip(metadata,native,model):
            cases[meta['family']]+=1;total+=1
            if len(h)==100 and h[99]==1:ymm+=1
            try:
                diff=differences(meta,normalize(h),m)
            except ValueError as e:
                errors.append(f'{name}: {meta["family"]} {meta["instruction"]} {meta["code"]}: {e} (signal {h[1]}, trap {h[55]})');continue
            if diff:
                bad.append(dict(meta,campaign=name,differences=diff));per_family[meta['family']]+=1
    write_json(args.output/'tcg-differences.json',bad)
    summary=dict(cases=total,ymm_captured=ymm,features=features,skipped=skipped,errors=errors,
                 left_out_tcg_aborts=left_out,
                 families={f:dict(cases=cases[f],differences=per_family[f]) for f in sorted(cases)},
                 seconds=round(time.monotonic()-started,1))
    write_json(args.output/'summary.json',summary)
    calibration=[b for b in bad if b['family']=='calibration']
    print(f'CPUID dump: {c1-c0-1} rows; TCG features: {" ".join(features)}')
    for f in sorted(cases):
        print(f'  {f:24} {cases[f]:6} cases {per_family[f]:6} TCG differences')
    for name,s in skipped.items():
        print(f'  {name} skipped ({s["count"]} cases): TCG lacks {" ".join(s["missing"])}')
    if left_out:print(f'  {len(left_out)} cases left out: QEMU aborts on them (tcg_aborts)')
    print(f'{total} complete TCG observations in {len(campaigns)-len(skipped)} campaigns ({ymm} with YMM state); '
          f'{len(bad)} differences retained; {len(errors)} errors. NOT hardware validation.')
    if errors:raise RuntimeError('; '.join(errors))
    if calibration:raise RuntimeError(f'calibration mismatch: {calibration}')


if __name__=='__main__':main()
