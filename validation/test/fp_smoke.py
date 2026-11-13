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

It also exercises the oracle's input validation (native/record_check.h) on the guest: `oracle check` on
every campaign (a campaign with refused records is reported and not executed), and on a file of records
the oracle must refuse (unsupported PTE, length, EFLAGS, MXCSR, memory kind, FTW, system calls, a far
jump, a DS load), whose report must equal the host build's (check_records.c with the guest's vendor and
MisalignSse bit), and whose execution must stop at the first record with that reason, before running it.

The extended bundle's safety measures are exercised too: /proc is mounted, so the oracle's audit of the
low address space runs (its PASS line is required); `oracle layout` must report the image extent of the
ELF; a record that stores into the middle of the oracle's image must stop the oracle with the integrity
canary's error when the image is not write-protected (`oracle i386-unguarded`, a test mode) and with
the write-protection error otherwise; and every format-3 campaign (the extended families) runs twice,
the two outputs compared row by row (differences outside a case's observe fields are errors).
"""
import argparse
import collections
import importlib.util
import json
import struct
import subprocess
import tempfile
import time
from pathlib import Path

from native_fp import (rows, normalize, differences, write_json, KINDS, parse_cpuid, has_feature, FEATURES,
                       parse_check, build_checker, cols_of, repeat_differences)
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


def refused_records(record):
    """Variants of a valid record the oracle must refuse (or accept, depending on the processor: SYSENTER
    on AMD, MXCSR.MM with MisalignSse), and the valid record itself last."""
    def code(c):
        r=bytearray(record);c=bytes.fromhex(c);r[0]=len(c);r[1:16]=c.ljust(15,b'\xcc');return r
    out=[]
    r=bytearray(record);struct.pack_into('<Q',r,160,0x45);out.append(r)           # PTE: read-only, A = 0
    r=bytearray(record);r[0]=0;out.append(r)                                        # length 0
    r=bytearray(record);struct.pack_into('<Q',r,144,0x3202);out.append(r)          # IOPL 3
    r=bytearray(record);struct.pack_into('<I',r,432,0x41f80);out.append(r)         # MXCSR bit 18
    out+=[code('cd80'),code('0f05'),code('0f34'),code('8ed8'),code('2eea00000000 2300'.replace(' ',''))]
    # the extended rules: software interrupts, near transfers out of the INT3 filling (relative, into the
    # instruction itself, RET through the arena), bytes after the instruction without TF
    out+=[code('cd03'),code('cc'),code('f1'),code('ce'),code('ebfe'),code('e900100000'),code('c3'),code('9090')]
    r=bytearray(record);struct.pack_into('<I',r,436,5);out.append(r)               # memory kind 5
    r=bytearray(record);struct.pack_into('<H',r,444,0x100);out.append(r)           # FTW > 0xff
    r=bytearray(record);struct.pack_into('<I',r,432,0x21f80);out.append(r)         # MXCSR.MM
    out.append(bytearray(record))
    return b''.join(out),len(out)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('bundle',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--timeout',type=int,default=600)
    p.add_argument('--kernel',type=Path,help='guest kernel (default ../x86_64/guest/bzImage; the code16 family needs '
                   'one with CONFIG_MODIFY_LDT_SYSCALL and CONFIG_X86_16BIT)')
    args=p.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    repo=Path(__file__).resolve().parents[2]
    manifest=json.loads((args.bundle/'manifest.json').read_text())
    campaigns=[c for c in manifest['campaigns'] if c.get('included',True)]   # (--only bundles: the included ones)
    archive=member('fp-oracle',(args.bundle/'oracle').read_bytes(),0o100755)
    script='#!/bin/sh\nexport PATH=/bin:/sbin\nmkdir -p /proc\nmount -t proc proc /proc\n/fp-oracle cpuid\n'
    size=KINDS[manifest['kind']]['size'];kept={};left_out=[]
    for c in campaigns:
        metadata=json.loads((args.bundle/(c['name']+'.json')).read_text())
        data=(args.bundle/(c['name']+'.bin')).read_bytes()
        keep=[i for i,m in enumerate(metadata) if not tcg_aborts(m)]
        left_out+=[dict(m,campaign=c['name']) for i,m in enumerate(metadata) if tcg_aborts(m)]
        kept[c['name']]=keep
        c['count']=len(keep)
        size=cols_of(manifest['kind'],c)['size']
        body=b''.join(data[8+i*size:8+(i+1)*size] for i in keep)
        archive+=member(c['name']+'.bin',(len(keep)|1<<63|(1<<62 if c.get('format')==3 else 0)).to_bytes(8,'little')+body)
        # run only if TCG reports the campaign's features: decided on the host after the CPUID dump would
        # need a second boot, so every campaign runs and the host discards (and reports) the gated ones.
        # The oracle's dry run first: a campaign with refused records is not executed (reported).
        script+=(f'echo FP_CHECK {c["name"]}\n/fp-oracle check < /{c["name"]}.bin\nst=$?\n'
                 f'echo FP_CHECK_STATUS {c["name"]} $st\n'
                 f'echo FP_BEGIN {c["name"]}\n[ $st = 0 ] && /fp-oracle i386 < /{c["name"]}.bin\necho FP_STATUS {c["name"]} $?\n')
        if c.get('format')==3:   # the determinism check: a second pass
            script+=(f'echo FP_BEGIN2 {c["name"]}\n[ $st = 0 ] && /fp-oracle i386 < /{c["name"]}.bin 2>/dev/null\n'
                     f'echo FP_STATUS2 {c["name"]} $?\n')
    # probe records: variants of the first case of the bundle (the calibration NOP)
    size=KINDS[manifest['kind']]['size']
    first=bytearray((args.bundle/(campaigns[0]['name']+'.bin')).read_bytes()[8:8+size])
    struct.pack_into('<Q',first,144,0x202)   # (a fuzz record has TF set; the probes assume TF clear)
    first=bytes(first)
    probe,bad_count=refused_records(first)
    # the canary: MOV [middle of the oracle image], EAX (A3 moffs32); the image extent from the ELF header
    memsz=struct.unpack_from('<Q',(args.bundle/'oracle').read_bytes(),64+40)[0]
    target=(0x100000+memsz//2)&~3
    canary=bytearray(first);canary[0]=5;canary[1:16]=(b'\xa3'+struct.pack('<I',target)).ljust(15,b'\xcc')
    archive+=member('canary.bin',(1|1<<63).to_bytes(8,'little')+bytes(canary))
    script+=('echo FP_LAYOUT\n/fp-oracle layout\n'
             'echo FP_CANARY_UNGUARDED\n/fp-oracle i386-unguarded < /canary.bin 2>&1\necho FP_CANARY_UNGUARDED_STATUS $?\n'
             'echo FP_CANARY_GUARDED\n/fp-oracle i386 < /canary.bin 2>&1\necho FP_CANARY_GUARDED_STATUS $?\n')
    archive+=member('bad.bin',(bad_count|1<<63).to_bytes(8,"little")+probe)
    script+=('echo FP_BAD_CHECK\n/fp-oracle check < /bad.bin\necho FP_BAD_CHECK_STATUS $?\n'
             'echo FP_BAD_RUN\n/fp-oracle i386 < /bad.bin 2>&1\necho FP_BAD_RUN_STATUS $?\n')
    script+='echo FP_ALL_DONE\n/bin/busybox poweroff -f\n'
    archive+=member('init',script.encode(),0o100755)
    archive+=member('TRAILER!!!',b'',0)
    base=(repo/'x86_64/guest/initramfs.cpio').read_bytes()
    initrd=args.output/'initramfs.cpio';initrd.write_bytes(base+b'\0'*(-len(base)%512)+archive)
    cmd=['qemu-system-x86_64','-accel','tcg','-cpu','max','-m','512','-kernel',str(args.kernel or repo/'x86_64/guest/bzImage'),
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
    amd=cpuid.get((0,0),(0,0,0,0))[1:]==(0x68747541,0x444d4163,0x69746e65)
    flags=(['--amd'] if amd else [])+(['--misalign-sse'] if has_feature(cpuid,'misalignSse') else [])
    def guest_check(marker,status_marker,count):
        at=lines.index(marker);end=next(i for i in range(at,len(lines)) if lines[i].startswith(status_marker))
        body=[l for l in lines[at+1:end] if l.startswith(('CHECK ','REJECT ','END '))]
        return parse_check('\n'.join(body)+'\n',count),lines[end].split()[-1]
    # the oracle's validation on the guest = the host build of the same source, for the guest's processor
    with tempfile.TemporaryDirectory() as tmp:
        checker=build_checker(Path(tmp))
        host=subprocess.run([str(checker),*flags],input=(bad_count|1<<63).to_bytes(8,"little")+probe,capture_output=True)
    expected=parse_check(host.stdout.decode(),bad_count)
    refused,status=guest_check('FP_BAD_CHECK','FP_BAD_CHECK_STATUS',bad_count)
    if refused!=expected or status!='3' or len(refused)<bad_count-3:
        errors.append(f'oracle check on refused records: guest {refused} (status {status}), host {expected}')
    at=lines.index('FP_BAD_RUN');end=next(i for i in range(at,len(lines)) if lines[i].startswith('FP_BAD_RUN_STATUS'))
    if lines[end]!='FP_BAD_RUN_STATUS 1' or 'ERROR: unsupported data permission (value/negative errno: 0000000000000045 )' not in lines[at:end]:
        errors.append('oracle i386 did not stop at the refused first record: '+' | '.join(lines[at:end+1]))
    # the sandbox: mapping audit, image extent, integrity canary, write protection
    safety={}
    safety['audit']=sum(1 for l in lines if l.startswith('PASS: below 4 GiB only the arena'))
    if not safety['audit'] or any('WARNING: /proc/self/maps' in l for l in lines):
        errors.append('the oracle did not audit its mappings (/proc/self/maps)')
    at=lines.index('FP_LAYOUT')
    safety['layout']=lines[at+1]
    if lines[at+1].split()!=['IMAGE',f'{0x100000:016x}',f'{0x100000+memsz:016x}']:
        errors.append(f'oracle layout {lines[at+1]!r}, ELF image ends at {0x100000+memsz:#x}')
    for mode,want in (('UNGUARDED','ERROR: the oracle image changed while the instruction ran (integrity canary)'),
                      ('GUARDED','ERROR: the instruction accessed the oracle image (write-protected while it runs)')):
        at=lines.index(f'FP_CANARY_{mode}');end=next(i for i in range(at,len(lines)) if lines[i].startswith(f'FP_CANARY_{mode}_STATUS'))
        safety['canary_'+mode.lower()]=[l for l in lines[at+1:end+1] if l.startswith(('ERROR','FP_CANARY'))]
        if lines[end]!=f'FP_CANARY_{mode}_STATUS 1' or not any(l.startswith(want) for l in lines[at:end]):
            errors.append(f'canary test ({mode.lower()}): '+' | '.join(lines[at:end+1]))
    repeat=dict(campaigns=0,identical=0,expected=0,unexpected=0,examples=[])
    rejected={}
    for c in campaigns:
        name=c['name'];missing=[f for f in c.get('requires',[]) if f not in features]
        status=[l for l in lines if l.startswith(f'FP_STATUS {name} ')]
        refused,check_status=guest_check(f'FP_CHECK {name}',f'FP_CHECK_STATUS {name} ',c['count'])
        if missing:
            # not compared; but the guest ran it anyway (when the oracle check let it): the oracle must
            # survive the instructions TCG lacks, as it must on hardware
            s=skipped[name]=dict(count=c['count'],missing=missing)
            if refused: s['refused_by_oracle_check']=len(refused)
            else:
                s['executed_anyway']=status[0].split()[-1] if status else 'no status'
                if status==[f'FP_STATUS {name} 0']:
                    begin=lines.index(f'FP_BEGIN {name}');start=lines.index(f'BEGIN {c["count"]:016x}',begin)
                    vectors=collections.Counter(int(l.split()[55],16) for l in lines[start+1:start+1+c['count']])
                    s['vectors']={str(k):v for k,v in sorted(vectors.items())}
                else:errors.append(f'{name}: the oracle did not survive a campaign TCG lacks features for: {status}')
            continue
        if refused:
            rejected[name]=[dict(r,family=metadata['family'],instruction=metadata['instruction'])
                            for r in refused for metadata in [json.loads((args.bundle/(name+'.json')).read_text())[kept[name][r['index']]]]]
            continue
        if check_status!='0':errors.append(f'{name}: oracle check status {check_status}')
        if status!=[f'FP_STATUS {name} 0']:
            begin=lines.index(f'FP_BEGIN {name}')
            if any(l.startswith('ERROR: modify_ldt') for l in lines[begin:begin+40]):
                # a kernel without modify_ldt (CONFIG_MODIFY_LDT_SYSCALL/X86_16BIT, e.g. the tinyconfig guest):
                # the 16-bit code segment family cannot run; --kernel with such a kernel runs it
                skipped[name]=dict(count=c['count'],missing=['modify_ldt in the guest kernel'],executed_anyway='modify_ldt refused')
                continue
            errors.append(f'{name}: oracle status {status}');continue
        begin=lines.index(f'FP_BEGIN {name}');status_at=lines.index(f'FP_STATUS {name} 0')
        header=f'BEGIN {c["count"]:016x}'
        if header not in lines[begin:status_at]:
            errors.append(f'{name}: no output header');continue
        start=lines.index(header,begin)
        end=lines.index('END',start)
        path=args.output/(name+'.out');path.write_text('\n'.join(lines[start:end+1])+'\n')
        cols=cols_of(manifest['kind'],c)
        try:
            native=list(rows(path,c['count'],cols['native']))
        except ValueError as e:
            errors.append(f'{name}: {e}');continue
        full=json.loads((args.bundle/(name+'.json')).read_text())
        allmodel=list(rows(args.bundle/(name+'.model'),len(full),cols['model']))
        # the rows of the cases run, renumbered as the guest's subset (tcg_aborts left some out)
        metadata=[full[i] for i in kept[name]];model=[[k]+allmodel[i][1:] for k,i in enumerate(kept[name])]
        if c.get('format')==3:
            # the second pass: identical rows, except a case's observe fields
            b2=lines.index(f'FP_BEGIN2 {name}');s2=lines.index(header,b2);e2=lines.index('END',s2)
            path2=args.output/(name+'.rep2.out');path2.write_text('\n'.join(lines[s2:e2+1])+'\n')
            if f'FP_STATUS2 {name} 0' not in lines: errors.append(f'{name}: second pass failed')
            repeat['campaigns']+=1
            d=repeat_differences(path,path2,c['count'],cols['native'],(),())
            repeat['identical']+=not d
            for i,fields in d:
                of=set(metadata[i].get('observe_fields',()))
                ok='*' in of or set(fields)<=of
                repeat['expected' if ok else 'unexpected']+=1
                if not ok and len(repeat['examples'])<10: repeat['examples'].append(dict(campaign=name,index=i,fields=fields[:5]))
        for meta,h,m in zip(metadata,native,model):
            cases[meta['family']]+=1;total+=1
            if len(h)>=100 and h[99]==1:ymm+=1
            try:
                diff=differences(meta,normalize(h,0x07 if meta.get('code16') else 0x23),m)
            except ValueError as e:
                errors.append(f'{name}: {meta["family"]} {meta["instruction"]} {meta["code"]}: {e} (signal {h[1]}, trap {h[55]})');continue
            if diff:
                bad.append(dict(meta,campaign=name,differences=diff));per_family[meta['family']]+=1
    write_json(args.output/'tcg-differences.json',bad)
    if repeat['unexpected']: errors.append(f"second passes differ outside the observe fields: {repeat['examples']}")
    summary=dict(cases=total,ymm_captured=ymm,features=features,skipped=skipped,errors=errors,safety=safety,repeat=repeat,
                 rejected_by_oracle_check=rejected,refused_records_checked=bad_count,
                 left_out_tcg_aborts=left_out,
                 families={f:dict(cases=cases[f],differences=per_family[f]) for f in sorted(cases)},
                 seconds=round(time.monotonic()-started,1))
    write_json(args.output/'summary.json',summary)
    calibration=[b for b in bad if b['family']=='calibration']
    print(f'CPUID dump: {c1-c0-1} rows; TCG features: {" ".join(features)}')
    for f in sorted(cases):
        print(f'  {f:24} {cases[f]:6} cases {per_family[f]:6} TCG differences')
    for name,s in skipped.items():
        print(f'  {name} skipped ({s["count"]} cases): TCG lacks {" ".join(s["missing"])}'+
              (f'; executed anyway: oracle status {s["executed_anyway"]}, vectors {s.get("vectors")}' if 'executed_anyway' in s else
               f'; not executed: oracle check refuses {s.get("refused_by_oracle_check")} records'))
    if left_out:print(f'  {len(left_out)} cases left out: QEMU aborts on them (tcg_aborts)')
    for name,r in rejected.items():
        print(f'  {name} not executed: oracle check refuses {len(r)} records on this CPU: '+
              ', '.join(f'{x["index"]} {x["instruction"]} ({x["reason"]})' for x in r[:4]))
    print(f'oracle check: {len(campaigns)} campaigns checked on the guest; the {bad_count} probe records '
          f'reported as by the host build ({len(expected)} refused, vendor {"AMD" if amd else "not AMD"}); '
          f'execution stops at a refused record')
    print(f'sandbox: mapping audit passed in {safety["audit"]} oracle runs; {safety["layout"]}; canary: '
          f'{safety["canary_unguarded"][0]}; write protection: {safety["canary_guarded"][0]}')
    print(f'second passes of {repeat["campaigns"]} format-3 campaigns: {repeat["identical"]} identical; '
          f'{repeat["expected"]} cases differ only in observe fields, {repeat["unexpected"]} otherwise')
    print(f'{total} complete TCG observations in {len(campaigns)-len(skipped)-len(rejected)} campaigns ({ymm} with YMM state); '
          f'{len(bad)} differences retained; {len(errors)} errors. NOT hardware validation.')
    if errors:raise RuntimeError('; '.join(errors))
    if calibration:raise RuntimeError(f'calibration mismatch: {calibration}')


if __name__=='__main__':main()
