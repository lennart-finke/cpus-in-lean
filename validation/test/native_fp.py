#!/usr/bin/env python3
"""Prepare a self-contained IA-32 FP campaign; run on Linux without Lean/root/KVM.

Exit codes: 0 exact agreement, 1 failures/strict differences, 2 approximation
observations requiring review (not a clean validation pass).
"""
import argparse
import base64
import collections
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
# Bundle formats. v1: 648-byte records, 83 native / 55 model columns. v2 (prepared now): each
# record is followed by YMM0..7[255:128] (128 bytes); rows add their final values (16 columns)
# and, on the native side, whether the signal frame had AVX state (1 column). The count header
# of a v2 campaign file has bit 63 set.
KINDS={'ia32-fp-v1':dict(size=648,native=83,model=55),'ia32-fp-v2':dict(size=776,native=100,model=71)}
KIND='ia32-fp-v2'
SIZE=KINDS[KIND]['size']
# CPUID features a case family may require (fp_cases.FAMILIES): leaf, subleaf, register
# (0 EAX .. 3 EDX), bit; names as in x86_32/X86/Cpuid.lean.
FEATURES={
    'fpu':(1,0,3,0),'mmx':(1,0,3,23),'fxsr':(1,0,3,24),'sse':(1,0,3,25),'sse2':(1,0,3,26),
    'sse3':(1,0,2,0),'pclmulqdq':(1,0,2,1),'ssse3':(1,0,2,9),'fma':(1,0,2,12),'sse41':(1,0,2,19),
    'sse42':(1,0,2,20),'movbe':(1,0,2,22),'popcnt':(1,0,2,23),'aes':(1,0,2,25),'xsave':(1,0,2,26),
    'osxsave':(1,0,2,27),'avx':(1,0,2,28),'f16c':(1,0,2,29),'rdrand':(1,0,2,30),
    'bmi1':(7,0,1,3),'avx2':(7,0,1,5),'bmi2':(7,0,1,8),'rdseed':(7,0,1,18),'adx':(7,0,1,19),
    'clflushopt':(7,0,1,23),'clwb':(7,0,1,24),'sha':(7,0,1,29),'rdpid':(7,0,2,22),
    'xsaveopt':(0xd,1,0,0),'xsavec':(0xd,1,0,1),'xsaves':(0xd,1,0,3),
    'lahfsahf':(0x80000001,0,2,0),'abm':(0x80000001,0,2,5),'sse4a':(0x80000001,0,2,6),
    'misalignSse':(0x80000001,0,2,7),'prefetchw':(0x80000001,0,2,8),'mwaitx':(0x80000001,0,2,29),
    'mmxext':(0x80000001,0,3,22),'rdtscp':(0x80000001,0,3,27),'clzero':(0x80000008,0,1,0),
    'rdpru':(0x80000008,0,1,4),'wbnoinvd':(0x80000008,0,1,9),
    'xgetbv1':(0xd,1,0,2),
}
FEATURES.update({'clfsh':(1,0,3,19),'monitor':(1,0,2,3),'mcommit':(0x80000008,0,1,8)})  # Gpr families
FEATURES.update({'lm':(0x80000001,0,3,29)})  # long-mode family (native_longmode.py)


def parse_cpuid(text):
    """{(leaf, subleaf): (eax, ebx, ecx, edx)} from `oracle cpuid` output."""
    lines=[l.split() for l in text.splitlines() if l.strip()]
    if not lines or lines[0]!=['BEGIN','CPUID'] or lines[-1]!=['END']: raise ValueError('malformed CPUID dump')
    out={}
    for f in lines[1:-1]:
        if len(f)!=6 or any(not re.fullmatch('[0-9a-f]{16}',x) for x in f): raise ValueError('malformed CPUID row')
        v=[int(x,16) for x in f];out[(v[0],v[1])]=tuple(v[2:])
    return out


def has_feature(dump,name):
    leaf,sub,reg,bit=FEATURES[name]
    regs=dump.get((leaf,sub))
    return regs is not None and dump.get((leaf&0x80000000,0),(0,))[0]>=leaf and (regs[reg]>>bit)&1==1


def digest(path):
    with path.open('rb') as f:
        h=hashlib.sha256()
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
        return h.hexdigest()


def write_json(path,obj):
    path.write_text(json.dumps(obj,indent=2)+'\n')


def verify(directory,manifest):
    if manifest['kind'] not in KINDS: raise ValueError('wrong bundle format')
    for name,expected in manifest['sha256'].items():
        if Path(name).is_absolute() or '..' in Path(name).parts: raise ValueError('unsafe manifest path')
        if digest(directory/name)!=expected: raise ValueError('input changed: '+name)


def rows(path,count,columns):
    with path.open() as f:
        if f.readline().strip()!=f'BEGIN {count:016x}': raise ValueError(f'{path}: wrong header')
        for index in range(count):
            fields=f.readline().split()
            if len(fields)!=columns or any(not re.fullmatch('[0-9a-f]{16}',x) for x in fields):
                raise ValueError(f'{path}: malformed/truncated row {index}')
            values=[int(x,16) for x in fields]
            if values[0]!=index: raise ValueError(f'{path}: missing/duplicate/reordered row {index}')
            yield values
        if f.readline().strip()!='END' or f.read().strip(): raise ValueError(f'{path}: wrong trailer')


def normalize(h):
    """A native row in the model's column order (v2 rows: plus the YMM upper halves, or None
    for them when the signal frame had no AVX state)."""
    if h[4]!=0x23: raise ValueError('oracle did not execute in IA-32 compatibility mode')
    signals={3:5,6:4,12:11,13:11,14:11,16:8,17:7,19:8}   # 17 #AC: SIGBUS
    if h[55] not in signals or h[1]!=signals[h[55]]: raise ValueError('unexpected signal/vector pair')
    ip=h[3]-(h[55]==3)
    row=[h[0],h[55],h[56],ip,h[5]]+[r&0xffffffff for r in h[6:14]]+h[22:38]+[h[54]]+h[61:83]+h[58:61]
    if len(h)==100: row+=h[83:99] if h[99]==1 else [None]*16
    return row


LABELS=['index','vector','error','eip','eflags']+[f'r{k}' for k in range(8)]+[
    f'xmm{k//2}.{("lo","hi")[k%2]}' for k in range(16)]+[
    'mxcsr','fcw','fsw','ftw','fop','fip','fdp']+[
    f'st{k//2}.{("sig","se")[k%2]}' for k in range(16)]+['memory.fnv32','page0.fnv64','page1.fnv64']+[
    f'ymmh{k//2}.{("lo","hi")[k%2]}' for k in range(16)]


def differences(meta,h,m):
    out=[]
    for k,(a,b) in enumerate(zip(h,m)):
        if k in (33,34,35): continue # Pointer/opcode update policies vary by CPU; retain raw observations.
        if a is None: continue # YMM state not available on this machine (normalize)
        if k==4:
            mask=meta['flags_mask'];a&=mask;b&=mask
        if k==30:
            a&=0x1f7f;b&=0x1f7f # Reserved bits 7 and 13..15.
        if k==31:
            mask=meta['sw_mask'];a&=mask;b&=mask
            if meta['instruction'] in ('fprem','fprem1') and (a|b)&0x400:
                # Quotient bits are undefined until reduction has completed.
                a&=~0x4300;b&=~0x4300
        if 36<=k<52:
            logical=(k-36)//2
            # Empty-register payloads are not architectural values. Both tags
            # and TOP are checked separately; do not hide a stack mismatch.
            ht=(h[31]>>11)&7;mt=(m[31]>>11)&7
            if not (h[32]>>(ht+logical)%8)&1 and not (m[32]>>(mt+logical)%8)&1: continue
        if a!=b: out.append(dict(field=LABELS[k],hardware=f'{a:x}',model=f'{b:x}'))
    return out


def classify(meta,diff):
    if meta.get('policy')!='observe':return 'strict_mismatches'
    for d in diff:
        if meta['family'].startswith('x87_') and d['field'].startswith('st'):continue
        if meta['family']=='sse_random' and d['field'] in ('xmm0.lo','xmm0.hi'):continue
        if d['field']=='fsw' and (int(d['hardware'],16)^int(d['model'],16))&~0x23f==0:continue
        return 'strict_mismatches'
    return 'observations'


def compare(directory, result):
    manifest=json.loads((directory/'manifest.json').read_text());verify(directory,manifest)
    host=json.loads((result/'hardware.json').read_text())
    if host['kind']!=manifest['kind'] or host['manifest_sha256']!=digest(directory/'manifest.json'):
        raise ValueError('hardware provenance does not match bundle')
    cols=KINDS[manifest['kind']]
    summary=dict(kind=manifest['kind'],strict_mismatches=0,observations=0,cases=0,skipped=0,
                 ymm_unavailable=0,campaigns={},
                 excluded_fields=['reserved FCW bits','undefined FSW condition codes',
                                  'empty x87 register payloads','FIP/FDP/FOP (raw values retained)'])
    with (result/'mismatches.jsonl').open('w') as bad:
        for spec in manifest['campaigns']:
            name=spec['name'];run=host['results'][name]
            if run.get('skipped'):
                # the machine lacks a required CPUID feature (fp_cases.FAMILIES); reported, not compared
                summary['skipped']+=spec['count']
                summary['campaigns'][name]=dict(count=spec['count'],skipped=run['skipped'])
                continue
            path=result/(name+'.out')
            if run['returncode']!=0 or digest(path)!=run['output_sha256']:
                raise ValueError(name+': failed or modified hardware run')
            metadata=json.loads((directory/(name+'.json')).read_text())
            if len(metadata)!=spec['count']: raise ValueError('metadata count changed')
            counts=collections.Counter();pointer_diffs=0;no_ymm=0
            # Exhaust both generators, including their END/extra-data validation.
            native=list(rows(path,spec['count'],cols['native']))
            model=list(rows(directory/(name+'.model'),spec['count'],cols['model']))
            for meta,h,m in zip(metadata,native,model):
                h=normalize(h);diff=differences(meta,h,m)
                # v2 rows whose signal frame had no AVX state: YMM columns not compared (counted)
                if len(h)>len(LABELS)-16 and h[-1] is None: no_ymm+=1
                pointer_diffs+=h[33:36]!=m[33:36]
                if diff:
                    category=classify(meta,diff)
                    summary[category]+=1;counts[category]+=1
                    bad.write(json.dumps(dict(meta,campaign=name,category=category,differences=diff))+'\n')
            summary['cases']+=spec['count']
            summary['ymm_unavailable']+=no_ymm
            summary['campaigns'][name]=dict(counts,count=spec['count'],pointer_differences=pointer_diffs,
                                            ymm_unavailable=no_ymm)
    write_json(result/'comparison.json',summary)
    print(f"{summary['cases']} cases; {summary['strict_mismatches']} strict mismatches; "
          f"{summary['observations']} approximation/domain observations"+
          (f"; {summary['skipped']} skipped (CPUID feature missing)" if summary['skipped'] else '')+
          (f"; YMM not compared in {summary['ymm_unavailable']} (no AVX state in the signal frame)"
           if summary['ymm_unavailable'] else ''),flush=True)
    return 1 if summary['strict_mismatches'] else 2 if summary['observations'] else 0


def prepare(args):
    from fp_cases import cases
    out=args.directory.resolve();out.mkdir(parents=True,exist_ok=False)
    subprocess.run(['lake','build','x86fp'],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('fp_builder',ROOT/'test/native/build.py')
    builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
    builder.build(ROOT/'test/native',out/'oracle',REPO/'x86_64/test/harness/link.py','fp')
    shutil.copyfile(__file__,out/'native_fp.py')
    sources=[Path(__file__),ROOT/'test/fp_cases.py',ROOT/'test/native_cases.py',ROOT/'test/native_xsave.py',ROOT/'FpMain.lean',
             ROOT/'test/native/build.py',ROOT/'test/native/signal_oracle.c',ROOT/'test/native/signal_enter.S',
             ROOT/'test/native/start.S',REPO/'x86_64/test/harness/link.py']
    sources+=[REPO/'x86_32/X86.lean']+sorted((REPO/'x86_32/X86').rglob('*.lean'))
    sources+=[ROOT/'test/native_crypto.py']   # Crypto case families (fp_cases.FAMILIES)
    sources+=[ROOT/'test/gpr_cases.py']   # Gpr families (fp_cases.FAMILIES)
    sources+=[ROOT/'test/native_avx.py',ROOT/'test/gen_avx.py',ROOT/'test/isa_forms.py']   # Avx families
    for source in sources:
        target=out/'sources'/source.relative_to(REPO)
        target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
    manifest=dict(kind=KIND,seed=args.seed,count=args.count,smoke=args.smoke,
                  sources={str(p.relative_to(REPO)):digest(p) for p in sources},
                  model_sha256=digest(ROOT/'.lake/build/bin/x86fp'),campaigns=[],sha256={})
    # Bounded batches keep signal runs, model replay and failure artifacts manageable.
    batch=[];metadata=[];families=collections.Counter();smoke_counts=collections.Counter()
    requires=[]   # CPUID features required by every case of the current batch
    def flush():
        if not batch:return
        name=f'campaign-{len(manifest["campaigns"]):03d}'
        (out/(name+'.bin')).write_bytes((len(batch)|1<<63).to_bytes(8,'little')+b''.join(batch))
        write_json(out/(name+'.json'),metadata)
        with (out/(name+'.model')).open('w') as log:
            subprocess.run([str(ROOT/'.lake/build/bin/x86fp'),'--compat',str(out/(name+'.bin'))],
                           stdout=log,check=True,timeout=args.timeout)
        list(rows(out/(name+'.model'),len(batch),KINDS[KIND]['model']))
        manifest['campaigns'].append(dict(name=name,count=len(batch),**(dict(requires=requires[:]) if requires else {})))
        print(name,len(batch),'model cases complete',flush=True)
        batch.clear();metadata.clear()
    for raw,meta in cases(args.seed,args.count):
        if any(f not in FEATURES for f in meta.get('requires',[])):
            raise ValueError(f'unknown CPUID feature in {meta["family"]}: {meta["requires"]}')
        if meta.get('requires',[])!=requires:
            flush();requires=meta.get('requires',[])
        if args.smoke:
            # Retain a sample from every family/instruction; don't take a prefix.
            key=(meta['family'],meta['instruction'])
            smoke_counts[key]+=1
            if smoke_counts[key]>2: continue
        assert len(raw)==SIZE
        meta=dict(meta,index=len(batch));batch.append(raw);metadata.append(meta)
        families[meta['family']]+=1
        if len(batch)==args.batch_size: flush()
    flush()
    manifest['families']=dict(families)
    for p in sorted(out.rglob('*')):
        if p.is_file():manifest['sha256'][str(p.relative_to(out))]=digest(p)
    write_json(out/'manifest.json',manifest)
    archive=out.with_name(out.name+'.tar.gz')
    with tarfile.open(archive,'x:gz') as tar:tar.add(out,arcname=out.name)
    # A pasteable installer with no network dependency; execute in a new temp directory.
    payload=base64.b64encode(archive.read_bytes()).decode()
    script=out.with_name(out.name+'-paste.sh')
    script.write_text("#!/usr/bin/env bash\nset -eu\nFP_DIR=$(mktemp -d \"${TMPDIR:-/tmp}/ia32-fp.XXXXXXXX\")\n"
        "export FP_DIR\npython3 - <<'FP_UNPACK'\nimport base64,io,os,tarfile\n"
        "data=base64.b64decode('''\n"+'\n'.join(payload[i:i+100] for i in range(0,len(payload),100))+"\n''')\n"
        "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tar:\n    tar.extractall(os.environ['FP_DIR'])\n"
        "FP_UNPACK\n"+f'python3 "$FP_DIR/{out.name}/native_fp.py" run "$FP_DIR/{out.name}"\n')
    print(f'Prepared {sum(families.values())} cases: {archive}\nPasteable installer: {script}\nHardware has NOT run.')


def run(args):
    directory=args.directory.resolve();manifest=json.loads((directory/'manifest.json').read_text())
    verify(directory,manifest)
    if platform.system()!='Linux' or platform.machine()!='x86_64':
        raise RuntimeError('requires x86-64 Linux with IA-32 compatibility support')
    result=(args.result or directory/'results').resolve();result.mkdir(parents=True,exist_ok=False)
    host=dict(kind=manifest['kind'],manifest_sha256=digest(directory/'manifest.json'),
              uname=list(platform.uname()),cpuinfo=Path('/proc/cpuinfo').read_text(),
              execution='native Linux signals, IA-32 compatibility mode; no KVM/TCG backend',
              started=time.time(),results={})
    write_json(result/'hardware.json',host)
    print('Results:',result,flush=True)
    try:
        # Every CPUID leaf and subleaf of this machine, kept in the results archive.
        dump=subprocess.run([str(directory/'oracle'),'cpuid'],stdin=subprocess.DEVNULL,capture_output=True,
                            text=True,timeout=args.timeout,check=True).stdout
        (result/'cpuid.txt').write_text(dump);cpuid=parse_cpuid(dump)
        host['cpuid']=dict(file='cpuid.txt',sha256=digest(result/'cpuid.txt'),
                           features=sorted(f for f in FEATURES if has_feature(cpuid,f)))
        write_json(result/'hardware.json',host)
        for spec in manifest['campaigns']:
            name=spec['name'];path=result/(name+'.out');started=time.monotonic()
            missing=[f for f in spec.get('requires',[]) if not has_feature(cpuid,f)]
            if missing:
                print(name,'skipped: CPUID lacks',' '.join(missing),flush=True)
                host['results'][name]=dict(skipped='missing CPUID features: '+' '.join(missing))
                write_json(result/'hardware.json',host);continue
            print(name,spec['count'],'native cases...',flush=True)
            with (directory/(name+'.bin')).open('rb') as inp,path.open('w') as out,(result/(name+'.log')).open('w') as err:
                proc=subprocess.run([str(directory/'oracle'),'i386'],stdin=inp,stdout=out,stderr=err,timeout=args.timeout)
            host['results'][name]=dict(returncode=proc.returncode,output_sha256=digest(path),seconds=time.monotonic()-started)
            write_json(result/'hardware.json',host)
            if proc.returncode: raise RuntimeError(f'{name}: oracle exited {proc.returncode}; inspect {name}.log')
            list(rows(path,spec['count'],KINDS[manifest['kind']]['native']))
        return compare(directory,result)
    except Exception as exc:
        (result/'run-error.txt').write_text(f'{type(exc).__name__}: {exc}\n')
        raise
    finally:
        archive=result.with_name(result.name+'.tar.gz')
        with tarfile.open(archive,'x:gz') as tar:tar.add(result,arcname=result.name)
        print('Return this results archive:',archive,flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    for name in ('prepare','run','compare'):
        q=sub.add_parser(name);q.add_argument('directory',type=Path)
        q.add_argument('--timeout',type=int,default=600)
        if name=='prepare':
            q.add_argument('--seed',type=int,default=20261111)
            q.add_argument('--count',type=int,default=10000,help='random cases per x87 and SSE family, in addition to directed cases')
            q.add_argument('--batch-size',type=int,default=5000)
            q.add_argument('--smoke',action='store_true',help='small plumbing check, not full coverage')
        else:q.add_argument('--result',type=Path)
    args=p.parse_args()
    if args.action=='prepare':
        if not re.fullmatch('[A-Za-z0-9_-]+',args.directory.name):p.error('bundle name must be letters/digits/underscore/hyphen')
        if not 0<=args.count<=100000 or not 1<=args.batch_size<=20000:p.error('count 0..100000; batch size 1..20000')
    try:
        if args.action=='compare': return compare(args.directory,args.result or args.directory/'results')
        return globals()[args.action](args) or 0
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError) as e:
        print(f'ERROR: {e}',file=sys.stderr);return 1


if __name__=='__main__':sys.exit(main())
