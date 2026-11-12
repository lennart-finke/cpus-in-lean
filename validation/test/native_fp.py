#!/usr/bin/env python3
"""Prepare a self-contained IA-32 FP campaign; run on Linux without Lean/root/KVM.

  prepare DIR [--seed S --count N] [--only 035-065] [--resume OLD_BUNDLE OLD_RESULT] [--smoke]
  run DIR [--result RES]                       on the target machine (the paste script does this)
  compare DIR --result RES [--merge BUNDLE RES]... [--out OUT]     stored model results vs hardware
  recompare DIR --result RES [--merge BUNDLE RES]... [--out OUT]   the CURRENT model vs stored hardware
  summary OUT                                  counts by family, instruction and field, with example cases
  unpack PASTE_SCRIPT [--out DIR]              the exact bundle a paste script carries (to compare its results)

Exit codes: 0 exact agreement, 1 failures/strict differences/incomplete comparison, 2 approximation
observations requiring review (not a clean validation pass).
"""
import argparse
import base64
import collections
import concurrent.futures
import hashlib
import importlib.util
import io
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
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

HEX16=re.compile('[0-9a-f]{16}')
# The Linux signal of every exception vector a user-mode instruction can raise (arch/x86/kernel/traps.c,
# mm/fault.c): #DE, #MF, #XM SIGFPE; #DB, #BP SIGTRAP; #OF, #BR, #GP, #PF SIGSEGV; #UD SIGILL;
# #NP, #SS, #AC SIGBUS. The oracle handles exactly these signals (signal_oracle.c, `signals[]`, plus
# SIGUSR1 for its own entry); a case whose model result is another vector cannot be observed natively.
VECTOR_SIGNAL={0:8,1:5,3:5,4:11,5:11,6:4,11:7,12:7,13:11,14:11,16:8,17:7,19:8}
CODE_PAGE=range(0x20000,0x21000)   # the oracle's code page (0xCC outside the instruction at 0x20100)
# A campaign whose oracle process fails this many times (one case each), or times out this often, is
# given up (its remaining cases are recorded as not run).
MAX_CASE_FAILURES=50
MAX_TIMEOUTS=3


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


def rows(path,count,columns,missing=frozenset()):
    """The rows of a complete oracle/model output, in order; `missing` are indices the runner reported
    as not executed (rejected, failed or not run: hardware.json), which must be absent."""
    with path.open() as f:
        if f.readline().strip()!=f'BEGIN {count:016x}': raise ValueError(f'{path}: wrong header')
        for index in range(count):
            if index in missing: continue
            fields=f.readline().split()
            if len(fields)!=columns or any(not HEX16.fullmatch(x) for x in fields):
                raise ValueError(f'{path}: malformed/truncated row {index}')
            values=[int(x,16) for x in fields]
            if values[0]!=index: raise ValueError(f'{path}: missing/duplicate/reordered row {index}')
            yield values
        if f.readline().strip()!='END' or f.read().strip(): raise ValueError(f'{path}: wrong trailer')


def complete_prefix(path,count,columns):
    """(header present, the complete well-formed rows before the first damaged/missing one, whole output
    complete) of a possibly interrupted oracle output."""
    got=[]
    if not path.exists(): return False,got,False
    with path.open(errors='replace') as f:
        if f.readline().strip()!=f'BEGIN {count:016x}': return False,got,False
        for index in range(count):
            line=f.readline()
            fields=line.split()
            if not line.endswith('\n') or len(fields)!=columns or any(not HEX16.fullmatch(x) for x in fields) \
                    or int(fields[0],16)!=index:
                return True,got,False
            got.append(fields)
        return True,got,f.readline().strip()=='END' and not f.read().strip()


def normalize(h):
    """A native row in the model's column order (v2 rows: plus the YMM upper halves, or None
    for them when the signal frame had no AVX state)."""
    if h[4]!=0x23: raise ValueError('oracle did not execute in IA-32 compatibility mode')
    if VECTOR_SIGNAL.get(h[55])!=h[1]: raise ValueError('unexpected signal/vector pair')
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


# ---------------------------------------------------------------------------------------------------
# Input validation: the oracle's own (record_check.h, compiled for the host) and the model-side checks


def parse_check(text,count):
    """REJECT lines of `oracle check` / check_records output: [{index, value, reason}]."""
    lines=text.splitlines()
    if not lines or lines[0].split()!=['CHECK',f'{count:016x}']: raise ValueError('malformed check output (header)')
    out=[]
    for line in lines[1:-1]:
        f=line.split(maxsplit=3)
        if len(f)!=4 or f[0]!='REJECT' or not HEX16.fullmatch(f[1]) or not HEX16.fullmatch(f[2]):
            raise ValueError('malformed check output: '+line)
        out.append(dict(index=int(f[1],16),value=f[2].lstrip('0') or '0',reason=f[3].strip()))
    if len(lines)<2 or lines[-1].split()!=['END',f'{len(out):016x}']: raise ValueError('malformed check output (trailer)')
    if any(not 0<=r['index']<count for r in out) or len({r['index'] for r in out})!=len(out):
        raise ValueError('malformed check output (indices)')
    return out


def build_checker(directory):
    """Compile native/check_records.c (the oracle's record_check.h) for this host."""
    cc=os.environ.get('HOST_CC','cc')
    path=directory/'check_records'
    subprocess.run([cc,'-O2','-Wall','-Wextra','-Werror','-o',str(path),str(ROOT/'test/native/check_records.c')],check=True)
    return path


def check_records(checker,path,count,requires=()):
    """Records of a campaign file that the oracle would refuse on the EPYC (vendor AMD; MisalignSse only
    for campaigns that require it)."""
    flags=['--amd']+(['--misalign-sse'] if 'misalignSse' in requires else [])
    with path.open('rb') as f:
        p=subprocess.run([str(checker),*flags],stdin=f,capture_output=True,text=True)
    if p.returncode not in (0,3): raise ValueError(f'{path.name}: record check failed: {p.stderr.strip()}')
    return parse_check(p.stdout,count)


def model_problems(metadata,model_rows):
    """Cases whose model result the oracle could not observe: an exception vector without a Linux signal
    the oracle handles, or control leaving the oracle's code page (it would stop the batch)."""
    out=[]
    for meta,m in zip(metadata,model_rows):
        if m[1] not in VECTOR_SIGNAL:
            out.append(dict(meta,problem=f'model raises vector {m[1]}, which has no handled Linux signal'))
        elif m[3] not in CODE_PAGE:
            out.append(dict(meta,problem=f'model EIP {m[3]:#x} leaves the oracle code page'))
    return out


# ---------------------------------------------------------------------------------------------------
# Hardware results: complete, partial (rejected/failed cases) and failed campaigns


def ranges(indices):
    """[[first, last], ...] of a sorted index list."""
    out=[]
    for i in sorted(indices):
        if out and out[-1][1]==i-1: out[-1][1]=i
        else: out.append([i,i])
    return out


def hardware_state(result,spec,run,cols,keep=True):
    """(status, rows, missing) of one campaign of a results directory: status 'ok' (every case observed),
    'partial', 'failed' (no case observed), 'skipped' (CPUID feature missing), 'not_run'; rows the native
    rows in index order; missing {index: reason} for every case without a row. Never raises for a failed
    run; raises for a damaged/modified result (hash mismatch, malformed output). keep=False: every row is
    still read and checked, but only their number is returned (in place of the rows)."""
    collect=list if keep else (lambda it:sum(1 for _ in it))
    name=spec['name'];count=spec['count'];path=result/(name+'.out')
    if run is None: return 'not_run',[],{i:'not run' for i in range(count)}
    if run.get('skipped'): return 'skipped',[],{}
    if 'status' in run:
        # this runner: rejected and failed cases are recorded, the output holds every other row
        missing={}
        for r in run.get('rejected',[]): missing[r['index']]='rejected by the oracle: '+r['reason']
        for r in run.get('failed_cases',[]):
            missing[r['index']]='oracle failed on this case'+(' (timeout)' if r.get('timeout') else f' (exit {r.get("returncode")})')
        for a,b in run.get('not_run',[]):
            for i in range(a,b+1): missing[i]='not run (campaign given up)'
        if run['status']=='error' or not path.exists():
            return 'failed',[],{i:missing.get(i,'runner error: '+run.get('error','no output')) for i in range(count)}
        if digest(path)!=run['output_sha256']: raise ValueError(name+': modified hardware output')
        got=collect(rows(path,count,cols,frozenset(missing)))
        return ('ok' if not missing else 'partial' if got else 'failed'),got,missing
    # results of the first runner (one oracle process per campaign, no case-level recovery)
    if path.exists() and digest(path)!=run['output_sha256']: raise ValueError(name+': modified hardware output')
    if run['returncode']==0:
        return 'ok',collect(rows(path,count,cols)),{}
    # failed batch: the complete rows before the failure are genuine observations; the case being read or
    # run when the oracle stopped, and every later one, have none
    _,got,_=complete_prefix(path,count,cols)
    got=collect([int(x,16) for x in f] for f in got)
    n=got if isinstance(got,int) else len(got)
    missing={i:'not run (batch ended)' for i in range(n+1,count)}
    if n<count: missing[n]=f'oracle exited {run["returncode"]} on this case (see {name}.log)'
    return ('partial' if got else 'failed'),got,missing


def load_source(bundle,result):
    bundle=Path(bundle).resolve();result=Path(result).resolve()
    manifest=json.loads((bundle/'manifest.json').read_text());verify(bundle,manifest)
    host=json.loads((result/'hardware.json').read_text())
    if host['kind']!=manifest['kind'] or host['manifest_sha256']!=digest(bundle/'manifest.json'):
        raise ValueError(f'{result}: hardware provenance does not match bundle {bundle}')
    return dict(bundle=bundle,result=result,manifest=manifest,host=host)


RANK={'ok':0,'partial':1,'skipped':2,'failed':3,'not_run':4}


def evaluate(sources,out,model=None,jobs=None):
    with tempfile.TemporaryDirectory() as tmp:
        return _evaluate(sources,out,model,jobs,Path(tmp))


def _evaluate(sources,out,model,jobs,tmp):
    """Compare hardware rows with model rows, campaign by campaign, over one or more (bundle, results)
    sources (a base run plus resume runs): each campaign is taken from the source with the most complete
    run. `model` None: the model rows stored in the bundle; else the path of an x86fp executable that is
    run now on the bundle's (verified) inputs. Writes comparison.json, mismatches.jsonl, summary.txt."""
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    kind=sources[0]['manifest']['kind']
    if any(s['manifest']['kind']!=kind for s in sources): raise ValueError('bundles of different formats')
    cols=KINDS[kind]
    candidates=collections.defaultdict(list)
    for s in sources:
        for spec in s['manifest']['campaigns']:
            candidates[spec['name']].append((s,spec))
    plan={}
    for name in sorted(candidates):
        best=None
        for s,spec in candidates[name]:
            if not spec.get('included',True): continue
            state=hardware_state(s['result'],spec,s['host']['results'].get(name),cols['native'],keep=False)
            if best is None or RANK[state[0]]<RANK[best[2][0]]: best=(s,spec,state)
        plan[name]=best
    # the current model on every input (recompare), in parallel, into a temporary directory
    model_files={}
    if model is not None:
        def replay(name,s,spec):
            path=tmp/(name+'.model')
            with path.open('w') as log:
                subprocess.run([str(model),*s['manifest'].get('model_args',['--compat']),str(s['bundle']/(name+'.bin'))],
                               stdout=log,check=True,timeout=3600)
            return path
        with concurrent.futures.ThreadPoolExecutor(jobs or os.cpu_count()) as pool:
            futures={name:pool.submit(replay,name,p[0],p[1]) for name,p in plan.items()
                     if p is not None and p[2][0] in ('ok','partial')}
            model_files={name:f.result() for name,f in futures.items()}
    summary=dict(kind=kind,model=('stored in the bundle' if model is None else 'current'),
                 model_sha256=(sorted({s['manifest'].get('model_sha256','?') for s in sources}) if model is None else digest(Path(model))),
                 sources=[dict(bundle=str(s['bundle']),manifest_sha256=digest(s['bundle']/'manifest.json'),
                               result=str(s['result']),hardware_sha256=digest(s['result']/'hardware.json'))
                          for s in sources],
                 strict_mismatches=0,observations=0,cases=0,total_cases=0,skipped=0,not_compared=0,
                 not_included=0,ymm_unavailable=0,incomplete_campaigns=[],not_included_campaigns=[],
                 campaigns={},families={},
                 excluded_fields=['reserved FCW bits','undefined FSW condition codes',
                                  'empty x87 register payloads','FIP/FDP/FOP (raw values retained)'])
    families=collections.defaultdict(collections.Counter)
    with (out/'mismatches.jsonl').open('w') as bad:
        for name,p in plan.items():
            if p is None:
                count=max(spec['count'] for _,spec in candidates[name])
                # in no bundle given (a resume bundle alone: its base run observed these)
                summary['campaigns'][name]=dict(status='not_included',count=count)
                summary['total_cases']+=count;summary['not_included']+=count
                summary['not_included_campaigns'].append(name)
                continue
            s,spec,(status,_,_)=p
            status,native,missing=hardware_state(s['result'],spec,s['host']['results'].get(name),cols['native'])
            count=spec['count'];summary['total_cases']+=count
            entry=dict(status=status,count=count,source=str(s['result']))
            shas={c[0]['manifest']['sha256'].get(name+'.bin',c[1].get('bin_sha256')) for c in candidates[name]}
            if len(shas)>1: entry['inputs_differ_between_sources']=True
            if status=='skipped':
                entry['skipped']=s['host']['results'][name]['skipped'];summary['skipped']+=count
                summary['campaigns'][name]=entry;continue
            reasons=collections.defaultdict(list)
            for i,why in missing.items(): reasons[why].append(i)
            if reasons: entry['not_compared']={why:ranges(ix) for why,ix in sorted(reasons.items())}
            summary['not_compared']+=len(missing)
            if status!='ok': summary['incomplete_campaigns'].append(name)
            if not native:
                entry['compared']=0;summary['campaigns'][name]=entry;continue
            metadata=json.loads((s['bundle']/(name+'.json')).read_text())
            if len(metadata)!=count: raise ValueError(name+': metadata count changed')
            model_path=model_files[name] if model is not None else s['bundle']/(name+'.model')
            model_rows=list(rows(model_path,count,cols['model']))
            counts=collections.Counter();pointer_diffs=0;no_ymm=0
            for h in native:
                index=h[0];meta=metadata[index];m=model_rows[index]
                families[meta['family']]['compared']+=1
                try:
                    h=normalize(h)
                except ValueError as e:
                    # an observation the comparison cannot interpret is a strict mismatch, never dropped
                    diff=[dict(field='signal/mode',hardware=f'signal {h[1]} trap {h[55]} cs {h[4]:#x}',model=f'vector {m[1]}',
                               note=str(e))]
                else:
                    diff=differences(meta,h,m)
                    if len(h)>len(LABELS)-16 and h[-1] is None: no_ymm+=1
                    pointer_diffs+=h[33:36]!=m[33:36]
                if diff:
                    category=classify(meta,diff)
                    summary[category]+=1;counts[category]+=1;families[meta['family']][category]+=1
                    bad.write(json.dumps(dict(meta,campaign=name,category=category,differences=diff))+'\n')
            summary['cases']+=len(native);summary['ymm_unavailable']+=no_ymm
            entry.update(counts,compared=len(native),pointer_differences=pointer_diffs,ymm_unavailable=no_ymm)
            summary['campaigns'][name]=entry
    summary['families']={f:dict(c) for f,c in sorted(families.items())}
    write_json(out/'comparison.json',summary)
    text=summary_text(summary,out/'mismatches.jsonl')
    (out/'summary.txt').write_text(text)
    print(headline(summary),flush=True)
    return exit_code(summary)


def exit_code(summary):
    """1: strict mismatches, or cases of the given bundles without a hardware observation (rejected, failed,
    not run); 2: only observations; 0: exact agreement. Campaigns in none of the bundles (a resume bundle
    compared alone) are listed but do not count."""
    return 1 if summary['strict_mismatches'] or summary['not_compared'] else 2 if summary['observations'] else 0


def name_list(names):
    """campaign-036 campaign-037 ... campaign-065 -> 'campaign-036..065' (runs of consecutive numbers)."""
    runs=[]
    for n in names:
        m=re.fullmatch(r'(.*-)(\d+)',n)
        if runs and m and runs[-1][0]==m[1] and int(m[2])==runs[-1][2]+1: runs[-1][2]+=1
        elif m: runs.append([m[1],int(m[2]),int(m[2]),len(m[2])])
        else: runs.append([n,None,None,0])
    return ' '.join(r[0] if r[1] is None else f'{r[0]}{r[1]:0{r[3]}d}'+(f'..{r[2]:0{r[3]}d}' if r[2]>r[1] else '') for r in runs)


def headline(summary):
    s=summary
    line=(f"{s['cases']} of {s['total_cases']} cases compared; {s['strict_mismatches']} strict mismatches; "
          f"{s['observations']} approximation/domain observations"+
          (f"; {s['skipped']} skipped (CPUID feature missing)" if s['skipped'] else '')+
          (f"; YMM not compared in {s['ymm_unavailable']} (no AVX state in the signal frame)" if s['ymm_unavailable'] else ''))
    if s['not_compared']:
        by=collections.defaultdict(list)
        for n in s['incomplete_campaigns']: by[s['campaigns'][n]['status']].append(n)
        line+=(f"\nNOT COMPARED: {s['not_compared']} cases without a hardware observation; "+
               '; '.join(f"{status}: {name_list(names)}" for status,names in sorted(by.items())))
    if s.get('not_included'):
        line+=(f"\nNot in these bundles: {s['not_included']} cases ({name_list(s['not_included_campaigns'])}); "
               f"compare together with the earlier run (--merge BUNDLE RESULT)")
    return line


def summary_text(summary,mismatches,examples=3):
    """Counts by family, by family and instruction, and by differing field, with example case ids
    (campaign:index)."""
    fam=collections.defaultdict(lambda:collections.defaultdict(lambda:dict(strict_mismatches=0,observations=0,
                                fields=collections.Counter(),examples=[])))
    fields=collections.defaultdict(lambda:[collections.Counter(),[]])
    with Path(mismatches).open() as f:
        for line in f:
            d=json.loads(line);e=fam[d['family']][d['instruction']]
            e[d['category']]+=1
            for x in d['differences']:
                e['fields'][x['field']]+=1
                fields[x['field']][0][d['family']]+=1
                if len(fields[x['field']][1])<examples: fields[x['field']][1].append(f"{d['campaign']}:{d['index']}")
            if len(e['examples'])<examples: e['examples'].append(f"{d['campaign']}:{d['index']}")
    out=[headline(summary),'']
    out.append(f"{'family':28}{'compared':>10}{'strict':>8}{'observe':>9}")
    for name,c in summary['families'].items():
        out.append(f"{name:28}{c.get('compared',0):>10}{c.get('strict_mismatches',0):>8}{c.get('observations',0):>9}")
    out+=['','By family and instruction (differences only; fields; example cases campaign:index):']
    for name in sorted(fam):
        for ins in sorted(fam[name]):
            e=fam[name][ins]
            out.append(f"  {name}/{ins}: strict {e['strict_mismatches']}, observe {e['observations']}; "
                       +', '.join(f'{k} {v}' for k,v in e['fields'].most_common(6))+'; e.g. '+' '.join(e['examples']))
    out+=['','By field (cases with that field different; families; examples):']
    for name,(c,ex) in sorted(fields.items(),key=lambda x:-sum(x[1][0].values())):
        out.append(f"  {name}: {sum(c.values())} ("+', '.join(f'{k} {v}' for k,v in c.most_common(5))+'); e.g. '+' '.join(ex))
    if summary['not_compared']:
        out+=['','Not compared:']
        for n in summary['incomplete_campaigns']:
            c=summary['campaigns'][n]
            out.append(f"  {n} ({c['status']}, {c['count']} cases): "+
                       ('; '.join(f'{why}: {rr}' for why,rr in c.get('not_compared',{}).items()) or c['status']))
    return '\n'.join(out)+'\n'


def compare(directory,result,merge=(),out=None):
    """The model results stored in the bundle(s) against the hardware results."""
    sources=[load_source(directory,result)]+[load_source(b,r) for b,r in merge]
    return evaluate(sources,out or (Path(result) if not merge else Path(result).with_name(Path(result).name+'-combined')))


def recompare(args):
    """The CURRENT model (x86fp) on the stored inputs, against the stored hardware results. Nothing in
    the bundles or results is written; the comparison goes to --out (default: next to the results)."""
    sources=[load_source(args.directory,args.result)]+[load_source(b,r) for b,r in (args.merge or [])]
    model=args.model
    if model is None:
        subprocess.run(['lake','build','x86fp'],cwd=ROOT,check=True)
        model=ROOT/'.lake/build/bin/x86fp'
    model=Path(model).resolve()
    out=args.out or Path(args.result).resolve().with_name(Path(args.result).name+'-recompare-'+digest(model)[:12])
    out=Path(out)
    if out.exists() and not (out/'comparison.json').exists() and any(out.iterdir()):
        raise ValueError(f'{out} exists and is not a comparison directory')
    print(f'model {model} (sha256 {digest(model)[:16]}...) -> {out}',flush=True)
    return evaluate(sources,out,model=model,jobs=args.jobs)


# ---------------------------------------------------------------------------------------------------
# Prepare


def parse_only(text):
    """'035-065' or '35,40-42' -> set of campaign numbers."""
    out=set()
    for part in text.split(','):
        a,_,b=part.partition('-')
        out.update(range(int(a),int(b or a)+1))
    return out


def completed(bundle,result):
    """{campaign name: .bin sha256} of the campaigns with a complete run in an earlier result."""
    s=load_source(bundle,result);done={}
    cols=KINDS[s['manifest']['kind']]['native']
    for spec in s['manifest']['campaigns']:
        if not spec.get('included',True): continue
        status,_,_=hardware_state(s['result'],spec,s['host']['results'].get(spec['name']),cols,keep=False)
        if status=='ok': done[spec['name']]=dict(count=spec['count'],sha256=s['manifest']['sha256'][spec['name']+'.bin'])
    return s,done


def include_campaign(name,number,count,sha,done,select):
    """Whether a regenerated campaign goes into the bundle: not when --only leaves it out or an earlier run
    observed it completely (`done`: completed()); the inputs of such a campaign must regenerate
    bit-identically, or its earlier hardware results would not belong to these inputs."""
    if name in done:
        if (done[name]['count'],done[name]['sha256'])!=(count,sha):
            raise ValueError(f'{name}: regenerated inputs differ from the earlier bundle (its hardware results would not apply)')
        return False
    return select is None or number in select


def prepare(args):
    from fp_cases import cases
    out=args.directory.resolve()
    base=None;done={};select=parse_only(args.only) if args.only else None
    if args.resume:
        base,done=completed(*args.resume)
        if (base['manifest']['seed'],base['manifest']['count'])!=(args.seed,args.count) or base['manifest'].get('smoke'):
            raise ValueError('--resume needs the seed and count of the earlier bundle (and no --smoke)')
    out.mkdir(parents=True,exist_ok=False)
    subprocess.run(['lake','build','x86fp'],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location('fp_builder',ROOT/'test/native/build.py')
    builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
    builder.build(ROOT/'test/native',out/'oracle',REPO/'x86_64/test/harness/link.py','fp')
    work=tempfile.TemporaryDirectory();checker=build_checker(Path(work.name))
    shutil.copyfile(__file__,out/'native_fp.py')
    sources=[Path(__file__),ROOT/'test/fp_cases.py',ROOT/'test/native_cases.py',ROOT/'test/native_xsave.py',ROOT/'FpMain.lean',
             ROOT/'test/native/build.py',ROOT/'test/native/signal_oracle.c',ROOT/'test/native/signal_enter.S',
             ROOT/'test/native/start.S',REPO/'x86_64/test/harness/link.py']
    sources+=[REPO/'x86_32/X86.lean']+sorted((REPO/'x86_32/X86').rglob('*.lean'))
    sources+=[ROOT/'test/native_crypto.py']   # Crypto case families (fp_cases.FAMILIES)
    sources+=[ROOT/'test/gpr_cases.py']   # Gpr families (fp_cases.FAMILIES)
    sources+=[ROOT/'test/native_avx.py',ROOT/'test/gen_avx.py',ROOT/'test/isa_forms.py']   # Avx families
    sources+=[ROOT/'test/fp_cases_sse.py',ROOT/'test/native_avx2.py',ROOT/'test/gen_avx2.py',
              ROOT/'test/native_longmode.py',ROOT/'test/native_openq.py']   # Sse, Avx2, long-mode, open questions
    sources+=[ROOT/'test/native/record_check.h',ROOT/'test/native/check_records.c']   # input validation
    for source in sources:
        target=out/'sources'/source.relative_to(REPO)
        target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
    manifest=dict(kind=KIND,seed=args.seed,count=args.count,smoke=args.smoke,
                  sources={str(p.relative_to(REPO)):digest(p) for p in sources},
                  model_sha256=digest(ROOT/'.lake/build/bin/x86fp'),model_args=['--compat'],campaigns=[],sha256={})
    # Bounded batches keep signal runs, model replay and failure artifacts manageable.
    batch=[];metadata=[];families=collections.Counter();smoke_counts=collections.Counter()
    requires=[]   # CPUID features required by every case of the current batch
    problems=[]   # records the oracle would refuse, model results it could not observe
    included_cases=0
    def flush():
        nonlocal included_cases
        if not batch:return
        number=len(manifest['campaigns']);name=f'campaign-{number:03d}'
        data=(len(batch)|1<<63).to_bytes(8,'little')+b''.join(batch)
        sha=hashlib.sha256(data).hexdigest()
        entry=dict(name=name,count=len(batch),**(dict(requires=requires[:]) if requires else {}),bin_sha256=sha)
        include=include_campaign(name,number,len(batch),sha,done,select)
        with tempfile.NamedTemporaryFile(suffix='.bin',dir=work.name,delete=False) as f: f.write(data)
        rejected=check_records(checker,Path(f.name),len(batch),requires)
        os.unlink(f.name)
        if rejected and include:
            problems.extend(dict(metadata[r['index']],campaign=name,problem=f"oracle refuses it: {r['reason']} ({r['value']})")
                            for r in rejected)
        elif rejected:
            print(f'WARNING: {name} (not included) has {len(rejected)} records the oracle refuses',flush=True)
        if include:
            (out/(name+'.bin')).write_bytes(data)
            write_json(out/(name+'.json'),metadata)
            with (out/(name+'.model')).open('w') as log:
                subprocess.run([str(ROOT/'.lake/build/bin/x86fp'),'--compat',str(out/(name+'.bin'))],
                               stdout=log,check=True,timeout=args.timeout)
            problems.extend(dict(p,campaign=name) for p in
                            model_problems(metadata,rows(out/(name+'.model'),len(batch),KINDS[KIND]['model'])))
            included_cases+=len(batch)
            print(name,len(batch),'model cases complete',flush=True)
        else:
            entry['included']=False
            print(name,len(batch),'cases: not included'+(' (complete in the earlier run; inputs identical)' if name in done else ''),flush=True)
        manifest['campaigns'].append(entry)
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
    work.cleanup()
    if problems:
        shutil.rmtree(out)
        for p in problems[:50]: print('INVALID:',p['campaign'],p['index'],p['family'],p['instruction'],p['code'],'--',p['problem'],file=sys.stderr)
        raise ValueError(f'{len(problems)} cases the oracle cannot run as the model does (listed above); nothing prepared')
    if base is not None:
        missing=sorted(set(done)-{c['name'] for c in manifest['campaigns']})
        if missing: raise ValueError('earlier campaigns no longer generated: '+' '.join(missing))
        manifest['resume']=dict(base_manifest_sha256=digest(base['bundle']/'manifest.json'),
                                base_hardware_sha256=digest(base['result']/'hardware.json'),
                                completed_in_base=sorted(done))
    manifest['families']=dict(families)
    for p in sorted(out.rglob('*')):
        if p.is_file():manifest['sha256'][str(p.relative_to(out))]=digest(p)
    write_json(out/'manifest.json',manifest)
    archive,script=package(out)
    included=[c for c in manifest['campaigns'] if c.get('included',True)]
    print(f'Prepared {included_cases} cases in {len(included)} campaigns (of {sum(families.values())} generated, '
          f'{len(manifest["campaigns"])} campaigns): {archive}\nPasteable installer: {script}\nHardware has NOT run.')


def package(out):
    """The bundle as a .tar.gz and as a pasteable installer with no network dependency, which unpacks
    into a new temporary directory and runs it (`unpack` recovers the bundle from the installer)."""
    archive=out.with_name(out.name+'.tar.gz')
    with tarfile.open(archive,'x:gz') as tar:tar.add(out,arcname=out.name)
    payload=base64.b64encode(archive.read_bytes()).decode()
    script=out.with_name(out.name+'-paste.sh')
    script.write_text("#!/usr/bin/env bash\nset -eu\nFP_DIR=$(mktemp -d \"${TMPDIR:-/tmp}/ia32-fp.XXXXXXXX\")\n"
        "export FP_DIR\npython3 - <<'FP_UNPACK'\nimport base64,io,os,tarfile\n"
        "data=base64.b64decode('''\n"+'\n'.join(payload[i:i+100] for i in range(0,len(payload),100))+"\n''')\n"
        "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tar:\n    tar.extractall(os.environ['FP_DIR'])\n"
        "FP_UNPACK\n"+f'python3 "$FP_DIR/{out.name}/native_fp.py" run "$FP_DIR/{out.name}"\n')
    return archive,script


# ---------------------------------------------------------------------------------------------------
# Run (on the target machine)


def tail(path,lines=20):
    try: return '\n'.join(path.read_text(errors='replace').splitlines()[-lines:])
    except OSError: return ''


def run_campaign(directory,spec,result,kind,timeout):
    """Run one campaign with case-level recovery: the oracle's dry run (`oracle check`) first, refused
    records are reported and skipped; when the oracle process fails or times out during a case, that case
    is recorded as failed and the oracle is restarted on the remaining ones (at most MAX_CASE_FAILURES
    times, MAX_TIMEOUTS timeouts). The rows of all executed cases go to <name>.out with their campaign
    indices; the outputs of the individual oracle processes are kept (<name>.raw, <name>.partN.raw/.log)."""
    name=spec['name'];count=spec['count'];size=KINDS[kind]['size'];cols=KINDS[kind]['native']
    oracle=str(directory/'oracle');data=(directory/(name+'.bin')).read_bytes()
    flag=int.from_bytes(data[:8],'little')&1<<63
    started=time.monotonic()
    rec=dict(status='ok',returncode=0)
    check=subprocess.run([oracle,'check'],input=data,capture_output=True,timeout=timeout)
    if check.returncode not in (0,3):
        raise RuntimeError(f'oracle check exited {check.returncode}: {check.stderr.decode(errors="replace").strip()}')
    rejected=parse_check(check.stdout.decode(),count)
    if rejected: rec['rejected']=rejected
    skip={r['index'] for r in rejected}
    pending=[i for i in range(count) if i not in skip]
    observed={};failures=[];part=0;not_run=[]
    while pending:
        part+=1
        stem=name if part==1 else f'{name}.part{part}'
        raw=result/(stem+'.raw');log=result/(stem+'.log')
        sub=(len(pending)|flag).to_bytes(8,'little')+b''.join(data[8+i*size:8+(i+1)*size] for i in pending)
        timed_out=False;rc=None
        with raw.open('w') as o,log.open('w') as e:
            try:
                rc=subprocess.run([oracle,'i386'],input=sub,stdout=o,stderr=e,timeout=timeout).returncode
            except subprocess.TimeoutExpired:
                rc=None;timed_out=True
        header,got,complete=complete_prefix(raw,len(pending),cols)
        for k,fields in enumerate(got): observed[pending[k]]=fields[1:]
        rec['returncode']=rc
        if rc==0 and complete:
            pending=[];break
        if not header:
            # the oracle stopped before its first case (startup or calibration): nothing more can run
            not_run=pending;rec.update(error=f'oracle stopped before the first case (exit {rc}): {tail(log,5)}');break
        if len(got)==len(pending):
            rec['exit_after_last_case']=rc;pending=[];break   # every row is there; the exit status is kept
        failures.append(dict(index=pending[len(got)],returncode=rc,timeout=timed_out,log=stem+'.log',message=tail(log,3)))
        print(f'  {name}: case {pending[len(got)]} failed ({"timeout" if timed_out else f"exit {rc}"}): {tail(log,1)}',flush=True)
        pending=pending[len(got)+1:]
        if len(failures)>=MAX_CASE_FAILURES or sum(f['timeout'] for f in failures)>=MAX_TIMEOUTS:
            not_run=pending;rec['error']=f'given up after {len(failures)} failed cases';break
    path=result/(name+'.out')
    if part==1 and not rejected and not failures and not not_run:
        (result/(name+'.raw')).rename(path)   # the oracle's output as it is
    else:
        with path.open('w') as o:
            o.write(f'BEGIN {count:016x}\n')
            for i in sorted(observed): o.write(f'{i:016x} '+' '.join(observed[i])+'\n')
            o.write('END\n')
    if failures: rec['failed_cases']=failures
    if not_run: rec['not_run']=ranges(not_run)
    if rejected or failures or not_run:
        rec['status']='partial' if observed else 'failed'
    rec.update(output_sha256=digest(path),seconds=time.monotonic()-started,parts=part)
    return rec


def run(args):
    directory=args.directory.resolve();manifest=json.loads((directory/'manifest.json').read_text())
    verify(directory,manifest)
    if platform.system()!='Linux' or platform.machine()!='x86_64':
        raise RuntimeError('requires x86-64 Linux with IA-32 compatibility support')
    result=(args.result or directory/'results').resolve();result.mkdir(parents=True,exist_ok=False)
    host=dict(kind=manifest['kind'],manifest_sha256=digest(directory/'manifest.json'),
              uname=list(platform.uname()),cpuinfo=tail(Path('/proc/cpuinfo'),100000),
              execution='native Linux signals, IA-32 compatibility mode; no KVM/TCG backend',
              runner='case-level recovery',started=time.time(),results={})
    write_json(result/'hardware.json',host)
    print('Results:',result,flush=True)
    trouble=[]
    try:
        # Every CPUID leaf and subleaf of this machine, kept in the results archive.
        dump=subprocess.run([str(directory/'oracle'),'cpuid'],stdin=subprocess.DEVNULL,capture_output=True,
                            text=True,timeout=args.timeout,check=True).stdout
        (result/'cpuid.txt').write_text(dump);cpuid=parse_cpuid(dump)
        host['cpuid']=dict(file='cpuid.txt',sha256=digest(result/'cpuid.txt'),
                           features=sorted(f for f in FEATURES if has_feature(cpuid,f)))
        write_json(result/'hardware.json',host)
        for spec in manifest['campaigns']:
            name=spec['name']
            if not spec.get('included',True): continue   # a resume bundle: observed by the earlier run
            missing=[f for f in spec.get('requires',[]) if not has_feature(cpuid,f)]
            if missing:
                print(name,'skipped: CPUID lacks',' '.join(missing),flush=True)
                host['results'][name]=dict(skipped='missing CPUID features: '+' '.join(missing))
                write_json(result/'hardware.json',host);continue
            print(name,spec['count'],'native cases...',flush=True)
            try:
                rec=run_campaign(directory,spec,result,manifest['kind'],args.timeout)
            except Exception as exc:   # one campaign's failure never ends the run
                rec=dict(status='error',returncode=None,error=f'{type(exc).__name__}: {exc}')
            host['results'][name]=rec;write_json(result/'hardware.json',host)
            if rec['status']!='ok':
                trouble.append(name)
                print(f'  {name}: {rec["status"]}: {len(rec.get("rejected",[]))} rejected, '
                      f'{len(rec.get("failed_cases",[]))} failed'+(f'; {rec["error"]}' if 'error' in rec else ''),flush=True)
        host['finished']=time.time();write_json(result/'hardware.json',host)
        code=compare(directory,result)
        if trouble: print('Campaigns with rejected, failed or unrun cases:',' '.join(trouble),flush=True)
        return 1 if trouble else code
    except Exception as exc:
        (result/'run-error.txt').write_text(f'{type(exc).__name__}: {exc}\n')
        raise
    finally:
        archive=result.with_name(result.name+'.tar.gz')
        with tarfile.open(archive,'x:gz') as tar:tar.add(result,arcname=result.name)
        print('Return this results archive:',archive,flush=True)


def unpack(args):
    """Extract the bundle a paste script carries: the inputs, model results and manifest that its hardware
    results refer to (hardware.json names the manifest's hash)."""
    text=args.directory.read_text()
    m=re.search(r"b64decode\('''\n(.*?)\n'''\)",text,re.S)
    if not m: raise ValueError(f'{args.directory}: not a paste script of this tool')
    data=base64.b64decode(m[1].replace('\n',''))
    dest=(args.out or args.directory.resolve().parent).resolve()
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tar:
        names=tar.getnames();top={Path(n).parts[0] for n in names}
        if len(top)!=1 or any(Path(n).is_absolute() or '..' in Path(n).parts for n in names):
            raise ValueError('unexpected archive layout')
        bundle=dest/top.pop()
        if bundle.exists(): raise ValueError(f'{bundle} exists')
        dest.mkdir(parents=True,exist_ok=True)
        tar.extractall(dest,**(dict(filter='data') if hasattr(tarfile,'data_filter') else {}))
    manifest=json.loads((bundle/'manifest.json').read_text());verify(bundle,manifest)
    print(f'{bundle}: {sum(c["count"] for c in manifest["campaigns"] if c.get("included",True))} cases; '
          f'manifest sha256 {digest(bundle/"manifest.json")}')


def main():
    p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    sub=p.add_subparsers(dest='action',required=True)
    for name in ('prepare','run','compare','recompare','summary','unpack'):
        q=sub.add_parser(name);q.add_argument('directory',type=Path)
        if name=='summary':
            q.add_argument('--examples',type=int,default=3);continue
        if name=='unpack':
            q.add_argument('--out',type=Path,help='directory to extract into (default: next to the script)');continue
        q.add_argument('--timeout',type=int,default=120 if name=='run' else 600,
                       help='seconds per oracle/model process (run: a 5,000-case batch takes about 1 s on an EPYC 7742)')
        if name=='prepare':
            q.add_argument('--seed',type=int,default=20261111)
            q.add_argument('--count',type=int,default=10000,help='random cases per x87 and SSE family, in addition to directed cases')
            q.add_argument('--batch-size',type=int,default=5000)
            q.add_argument('--smoke',action='store_true',help='small plumbing check, not full coverage')
            q.add_argument('--only',help='campaign numbers to include, e.g. 035-065 or 3,40-42 (the others are generated, hashed and left out)')
            q.add_argument('--resume',nargs=2,type=Path,metavar=('BUNDLE','RESULT'),
                           help='include only the campaigns without a complete run in RESULT (of BUNDLE); '
                                'the others must regenerate bit-identically')
        else:
            q.add_argument('--result',type=Path)
        if name in ('compare','recompare'):
            q.add_argument('--merge',nargs=2,type=Path,action='append',metavar=('BUNDLE','RESULT'),
                           help='further (bundle, results) pairs, e.g. a resume run; each campaign is taken from the most complete run')
            q.add_argument('--out',type=Path,help='comparison directory')
        if name=='recompare':
            q.add_argument('--model',type=Path,help='x86fp executable (default: lake build x86fp)')
            q.add_argument('--jobs',type=int)
    args=p.parse_args()
    if args.action=='prepare':
        if not re.fullmatch('[A-Za-z0-9_-]+',args.directory.name):p.error('bundle name must be letters/digits/underscore/hyphen')
        if not 0<=args.count<=100000 or not 1<=args.batch_size<=20000:p.error('count 0..100000; batch size 1..20000')
        if args.only and not re.fullmatch(r'\d+(-\d+)?(,\d+(-\d+)?)*',args.only):p.error('--only: e.g. 035-065')
    try:
        if args.action=='compare':
            return compare(args.directory,args.result or args.directory/'results',args.merge or (),args.out)
        if args.action=='recompare':
            if args.result is None:p.error('recompare needs --result')
            return recompare(args)
        if args.action=='summary':
            s=json.loads((args.directory/'comparison.json').read_text())
            print(summary_text(s,args.directory/'mismatches.jsonl',args.examples),end='')
            return exit_code(s)
        return globals()[args.action](args) or 0
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError) as e:
        print(f'ERROR: {e}',file=sys.stderr);return 1


if __name__=='__main__':sys.exit(main())
