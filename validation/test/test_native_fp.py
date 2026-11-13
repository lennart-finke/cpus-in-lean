"""Coverage and fail-closed evidence checks for the user-mode FP campaign."""
import collections
import json
import struct
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from fp_cases import cases, X87, TRANS, SIZE
import native_fp
from native_fp import (classify, differences, rows, verify, digest, normalize, compare, write_json,
                       parse_cpuid, has_feature, KINDS)


class Coverage(unittest.TestCase):
    def test_record_integrity_and_directed_coverage(self):
        counts=collections.Counter();ops=set();control=collections.defaultdict(set)
        for raw,m in cases(123,100):
            self.assertIn(len(raw),(SIZE,native_fp.FORMAT3['size']))
            self.assertEqual(raw[1:1+raw[0]].hex(),m['code'])
            # TF only in the extended families (the encoding fuzz single-steps every case)
            if len(raw)==SIZE: self.assertEqual(struct.unpack_from('<Q',raw,144)[0]&0x100,0)
            self.assertLess(struct.unpack_from('<H',raw,444)[0],256)
            self.assertLess(struct.unpack_from('<I',raw,436)[0],5)   # memory kinds 0..3, 4 = XSAVE image
            counts[m['family']]+=1
            ops.add(m['instruction'])
            if m['family']=='x87_matrix':control[m['instruction']].add((m['pc'],m['rc'],m['operand_class']))
        self.assertTrue({op for op,_ in X87+TRANS}<=ops)
        self.assertTrue(all(len(c)==3*4*22 for c in control.values()))
        self.assertEqual(counts['sse_matrix'],49152)
        self.assertEqual(counts['fp_save'],96)
        self.assertEqual(counts['fp_restore'],8)
        self.assertEqual(counts['x87_pending'],9)
        for family in ('mmx_integer','sse_integer','x87_memory','simd_memory_fault','sse_control'):
            self.assertGreater(counts[family],0)

    def test_generation_is_reproducible(self):
        import hashlib
        def fingerprint():
            h=hashlib.sha256()
            for raw,m in cases(7,20):h.update(raw);h.update(json.dumps(m,sort_keys=True).encode())
            return h.hexdigest()
        self.assertEqual(fingerprint(),fingerprint())


class Evidence(unittest.TestCase):
    def test_comparison_report_and_output_integrity(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);result=root/'results';result.mkdir()
            h=[0]*83;h[1]=5;h[2]=128;h[4]=0x23;h[55]=3;h[3]=0x20102
            def output(values):
                return 'BEGIN 0000000000000001\n'+' '.join(f'{v:016x}' for v in values)+'\nEND\n'
            (root/'c.model').write_text(output(normalize(h)))
            write_json(root/'c.json',[dict(index=0,family='calibration',instruction='nop',flags_mask=0x8d5,sw_mask=0xb8ff)])
            write_json(root/'manifest.json',dict(kind='ia32-fp-v1',campaigns=[dict(name='c',count=1)],
                sha256={name:digest(root/name) for name in ('c.model','c.json')}))
            (result/'c.out').write_text(output(h))
            write_json(result/'hardware.json',dict(kind='ia32-fp-v1',manifest_sha256=digest(root/'manifest.json'),
                results={'c':dict(returncode=0,output_sha256=digest(result/'c.out'))}))
            self.assertEqual(compare(root,result),0)
            self.assertEqual(json.loads((result/'comparison.json').read_text())['cases'],1)
            with (result/'c.out').open('a') as f:f.write('extra\n')
            with self.assertRaises(ValueError):compare(root,result)

    def test_truncated_reordered_extra_and_malformed_records_rejected(self):
        line=' '.join(['0'*16]*55)
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'out'
            valid='BEGIN 0000000000000001\n'+line+'\nEND\n'
            p.write_text(valid);self.assertEqual(len(list(rows(p,1,55))),1)
            for bad in (valid.replace('END',''),valid+'junk\n',valid.replace(line,line[17:]),
                        valid.replace(line,'0000000000000001'+line[16:])):
                p.write_text(bad)
                with self.assertRaises(ValueError):list(rows(p,1,55))

    def test_changed_bundle_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'input';p.write_bytes(b'a')
            m=dict(kind='ia32-fp-v1',sha256={'input':digest(p)})
            verify(Path(d),m);p.write_bytes(b'b')
            with self.assertRaises(ValueError):verify(Path(d),m)

    def test_approximation_policy_does_not_hide_faults_or_stack_changes(self):
        m=dict(family='x87_transcendental',policy='observe')
        def diff(field,a='1',b='0'):return [dict(field=field,hardware=a,model=b)]
        self.assertEqual(classify(m,diff('st0.sig')),'observations')
        self.assertEqual(classify(m,diff('fsw','20')),'observations')
        for field in ('vector','error','eip','r0','ftw','memory.fnv32'):
            self.assertEqual(classify(m,diff(field)),'strict_mismatches')
        self.assertEqual(classify(m,diff('fsw','800')),'strict_mismatches')

    def test_defined_state_is_checked_and_empty_payloads_excluded(self):
        m=[0]*55;h=m.copy()
        meta=dict(instruction='fadd',flags_mask=0x8d5,sw_mask=0xbaff)
        h[36]=12;self.assertEqual(differences(meta,h,m),[])
        h[32]=m[32]=1
        self.assertEqual(differences(meta,h,m)[0]['field'],'st0.sig')
        for k in (1,2,3,4,5,13,29,30,31,32,52,53,54):
            h=m.copy();h[k]^=1
            self.assertTrue(differences(meta,h,m),k)

    def test_native_mapping_and_terminator(self):
        h=[0]*83;h[1]=5;h[4]=0x23;h[55]=3;h[3]=0x20103
        h[61:83]=list(range(22));r=normalize(h)
        self.assertEqual(len(r),55);self.assertEqual(r[3],0x20102)
        self.assertEqual(r[30:52],list(range(22)))
        h[4]=0x33
        with self.assertRaises(ValueError):normalize(h)


class FormatV2(unittest.TestCase):
    def test_records_carry_ymm_upper_halves(self):
        raw,m=next(iter(cases(1,1)))
        self.assertEqual(len(raw),KINDS['ia32-fp-v2']['size'])
        self.assertNotIn('requires',m)

    def test_ymm_columns_compared_only_when_available(self):
        h=[0]*100;h[1]=5;h[4]=0x23;h[55]=3;h[3]=0x20103
        h[83:99]=list(range(16));h[99]=1
        r=normalize(h);self.assertEqual(len(r),71);self.assertEqual(r[55:71],list(range(16)))
        m=r.copy();m[60]^=1
        meta=dict(instruction='nop',flags_mask=0x8d5,sw_mask=0xb8ff)
        self.assertEqual(differences(meta,r,m)[0]['field'],'ymmh2.hi')
        h[99]=0;r=normalize(h)
        self.assertEqual(differences(meta,r,m),[])

    def test_cpuid_dump_and_feature_gating(self):
        dump=('BEGIN CPUID\n'+' '.join(f'{v:016x}' for v in (0,0,0xd,0,0,0))+'\n'+
              ' '.join(f'{v:016x}' for v in (1,0,0x830f10,0,1,0))+'\n'+
              ' '.join(f'{v:016x}' for v in (0x80000000,0,0x80000001,0,0,0))+'\nEND\n')
        d=parse_cpuid(dump)
        self.assertTrue(has_feature(d,'sse3'))
        self.assertFalse(has_feature(d,'avx'))
        self.assertFalse(has_feature(d,'bmi1'))   # leaf 7 absent
        with self.assertRaises(ValueError):parse_cpuid(dump.replace('END\n',''))

    def test_skipped_campaign_is_reported_not_compared(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);result=root/'results';result.mkdir()
            write_json(root/'c.json',[dict(index=0,family='f',instruction='x',flags_mask=0x8d5,sw_mask=0xb8ff)])
            write_json(root/'manifest.json',dict(kind='ia32-fp-v2',campaigns=[dict(name='c',count=1,requires=['avx'])],
                sha256={'c.json':digest(root/'c.json')}))
            write_json(result/'hardware.json',dict(kind='ia32-fp-v2',manifest_sha256=digest(root/'manifest.json'),
                results={'c':dict(skipped='missing CPUID features: avx')}))
            self.assertEqual(compare(root,result),0)
            self.assertEqual(json.loads((result/'comparison.json').read_text())['skipped'],1)


import argparse  # noqa: E402
import contextlib  # noqa: E402
import io  # noqa: E402
import os  # noqa: E402
import re  # noqa: E402
import shutil  # noqa: E402
import subprocess  # noqa: E402
import sys  # noqa: E402
from unittest import mock  # noqa: E402

import fp_cases  # noqa: E402
import native_fp  # noqa: E402

HERE=Path(__file__).resolve().parent
CC=shutil.which(os.environ.get('HOST_CC','cc'))


def compiled_checker(tmp):
    return native_fp.build_checker(Path(tmp))


class OracleInputValidation(unittest.TestCase):
    """native/record_check.h is the oracle's own validation; prepare runs its host build on every campaign."""

    @unittest.skipUnless(CC,'no host C compiler')
    def test_every_generated_record_is_accepted(self):
        # all families (small count): no record the oracle would refuse on the EPYC
        with tempfile.TemporaryDirectory() as d:
            checker=compiled_checker(d);groups=collections.defaultdict(list)
            for raw,m in cases(123,100):groups[tuple(m.get('requires',())),len(raw)].append(raw)
            for (requires,size),records in groups.items():
                v3=size==native_fp.FORMAT3['size']
                p=Path(d)/'c.bin';p.write_bytes((len(records)|1<<63|(1<<62 if v3 else 0)).to_bytes(8,'little')+b''.join(records))
                self.assertEqual(native_fp.check_records(checker,p,len(records),requires),[],requires)

    @unittest.skipUnless(CC,'no host C compiler')
    def test_each_rule(self):
        base=bytearray(fp_cases.record('90'))
        def code(c):
            r=bytearray(base);c=bytes.fromhex(c);r[0]=len(c);r[1:16]=c.ljust(15,b'\xcc');return r
        def put(fmt,off,v):
            r=bytearray(base);struct.pack_into(fmt,r,off,v);return r
        probes=[(base,None),(put('<Q',160,0x45),'unsupported data permission'),(put('<Q',168,0x47),'unsupported data permission'),
                (put('<Q',160,0),None),(put('<Q',168,0x65),None),(put('B',0,0),'bad instruction length'),
                (put('B',0,16),'bad instruction length'),(put('<Q',144,0x3202),'EFLAGS'),(put('<Q',144,0x200),'EFLAGS'),
                (put('<Q',144,0x40ed7),None),(put('<I',432,0x41f80),'reserved MXCSR'),(put('<I',432,0x21f80),'reserved MXCSR'),
                (put('<I',436,5),'memory kind'),(put('<I',436,4),None),(put('<H',444,0x100),'FTW'),
                (code('cd80'),'INT 80h'),(code('cd03'),'software interrupt'),(code('cd21'),'software interrupt'),(code('0f05'),'SYSCALL'),
                (code('660f05'),'SYSCALL'),(code('0f34'),None),(code('0f07'),None),(code('ea00000000 2300'.replace(' ','')),'far'),
                (code('9a000000002300'),'far'),(code('cb'),'far'),(code('cf'),'far'),(code('ff2b'),'far'),(code('ff6b00'),'far'),
                (code('ff23'),'near transfer target'),(code('8ed8'),'DS/ES/FS/GS'),(code('8ed0'),None),(code('1f'),'DS/ES/FS/GS'),(code('17'),None),
                (code('0fa1'),'DS/ES/FS/GS'),(code('c503'),'DS/ES/FS/GS'),(code('c5f877'),None),(code('c4e27850'),None),
                (code('0fb203'),None),(code('0fb403'),'DS/ES/FS/GS')]
        with tempfile.TemporaryDirectory() as d:
            checker=compiled_checker(d)
            p=Path(d)/'c.bin';p.write_bytes((len(probes)|1<<63).to_bytes(8,'little')+b''.join(bytes(r) for r,_ in probes))
            got={r['index']:r['reason'] for r in native_fp.check_records(checker,p,len(probes),())}
            for i,(_,why) in enumerate(probes):
                if why is None:self.assertNotIn(i,got,probes[i][0][:8].hex())
                else:self.assertIn(why,got.get(i,''),i)
            # (the indices below are those of the probes above)
            # the target's processor: SYSENTER refused unless AMD, MXCSR.MM only with MisalignSse
            out=subprocess.run([str(checker)],input=p.read_text('latin-1'),capture_output=True,text=True,encoding='latin-1')
            self.assertIn('SYSENTER',{r['index']:r['reason'] for r in native_fp.parse_check(out.stdout,len(probes))}[20])
            self.assertEqual(out.returncode,3)
            got=native_fp.check_records(checker,p,len(probes),('misalignSse',))
            self.assertNotIn(11,{r['index'] for r in got})
            p.write_bytes(p.read_bytes()+b'x')
            with self.assertRaises(ValueError):native_fp.check_records(checker,p,len(probes),())

    def test_oracle_source_runs_the_shared_check(self):
        oracle=(HERE/'native/signal_oracle.c').read_text()
        header=(HERE/'native/record_check.h').read_text()
        self.assertIn('#include "record_check.h"',oracle)
        # validated in the per-record loop before the record's memory is set up and it runs
        loop=oracle[oracle.rindex('for(u64 index=0;index<count;index++)'):]
        self.assertLess(loop.index('record_check('),loop.index('memory_prepare();'))
        self.assertIn('check_input()',oracle)
        # the PTE values the generators may use are exactly the ones both checks accept
        accepted={int(x,16) for x in re.findall(r'pte != (0x[0-9a-f]+|0)\b',header)}
        self.assertEqual(accepted,set(fp_cases.ORACLE_PTES))
        self.assertIn('input.pte[p]==0x65',oracle);self.assertIn('input.pte[p]!=0x67',oracle)
        # every vector the comparison maps has its Linux signal handled by the oracle
        handled={int(x) for x in re.search(r'int signals\[\]=\{([0-9,]+)\}',oracle)[1].split(',')}
        self.assertTrue(set(native_fp.VECTOR_SIGNAL.values())<=handled-{10})

    def test_generator_refuses_unsupported_pte(self):
        with self.assertRaises(AssertionError):fp_cases.record('90',permissions=(0x45,0x67))
        perms={m.get('permissions') for _,m in cases(5,10) if m['family']=='gpr_cache'}
        self.assertEqual(perms,{(0x67,0x67),(0x65,0x67),(0,0x67)})

    def test_model_problems(self):
        meta=[dict(index=0),dict(index=1),dict(index=2)]
        m=[[0,3,0,0x20101],[1,2,0,0x20100],[2,3,0,0x30000]]
        self.assertEqual([p['index'] for p in native_fp.model_problems(meta,m)],[1,2])


# A stand-in for the oracle (the runner's tests run anywhere): `cpuid`, `check` (refuses PTE 0x45) and
# `i386`, whose behaviour per record follows its seed: 0xDEAD the process fails, 0xBEEF it hangs,
# 0xCA1B (first record) it fails before its first case; PTE 0x45 it stops with the oracle's message.
FAKE_ORACLE=r'''#!/usr/bin/env python3
import struct,sys,time
mode=sys.argv[1]
if mode=='cpuid':
    print('BEGIN CPUID');print(' '.join('%016x'%v for v in (0,0,1,0,0,0)));print(' '.join('%016x'%v for v in (1,0,0,0,0,1)));print('END');sys.exit(0)
data=sys.stdin.buffer.read();n=struct.unpack_from('<Q',data)[0]&~(1<<63)
recs=[data[8+i*776:8+(i+1)*776] for i in range(n)]
seed=lambda r:struct.unpack_from('<I',r,152)[0];pte=lambda r:struct.unpack_from('<Q',r,160)[0]
if mode=='check':
    bad=[i for i,r in enumerate(recs) if pte(r)==0x45]
    print('CHECK %016x '%n)
    for i in bad:print('REJECT %016x %016x unsupported data permission'%(i,0x45))
    print('END %016x '%len(bad));sys.exit(3 if bad else 0)
if seed(recs[0])==0xCA1B:sys.stderr.write('ERROR: NOP mode/IP/trap calibration\n');sys.exit(1)
sys.stderr.write('PASS: calibration\n')
print('BEGIN %016x '%n,flush=True)
for i,r in enumerate(recs):
    if pte(r)==0x45:sys.stderr.write('ERROR: unsupported data permission (value/negative errno: 0000000000000045 )\n');sys.exit(1)
    if seed(r)==0xDEAD:sys.stderr.write('ERROR: signal outside instruction buffer\n');sys.exit(1)
    if seed(r)==0xBEEF:time.sleep(60)
    h=[0]*100;h[0]=i;h[1]=5;h[3]=0x20102;h[4]=0x23;h[55]=3;h[6]=seed(r)
    print(' '.join('%016x'%v for v in h)+' ',flush=True)
print('END')
'''
# A stand-in for x86fp: the model row of each record (EAX = the seed, as the fake oracle), or with
# EAX + 1 for seed 7 (a model change).
FAKE_MODEL=r'''#!/usr/bin/env python3
import struct,sys
data=open(sys.argv[-1],'rb').read();n=struct.unpack_from('<Q',data)[0]&~(1<<63)
print('BEGIN %016x'%n)
for i in range(n):
    s=struct.unpack_from('<I',data,8+i*776+152)[0]
    row=[i,3,0,0x20101,0]+[s+(DELTA if s==7 else 0)]+[0]*65
    print(' '.join('%016x'%v for v in row))
print('END')
'''


def model_row(i,seed):
    h=[0]*100;h[0]=i;h[1]=5;h[3]=0x20102;h[4]=0x23;h[55]=3;h[6]=seed
    return [0 if v is None else v for v in normalize(h)]


def make_bundle(root,campaigns,included=None):
    """campaigns: [(requires, [(seed, pte0), ...]), ...]; a bundle as prepare writes it, with the fake oracle."""
    root.mkdir();manifest=dict(kind='ia32-fp-v2',seed=1,count=1,model_sha256='fake',campaigns=[],sha256={})
    for k,(requires,recs) in enumerate(campaigns):
        name=f'campaign-{k:03d}'
        raw=[fp_cases.record('90',seed=s,permissions=(0x67,0x67)) for s,_ in recs]
        raw=[r[:160]+struct.pack('<Q',p)+r[168:] for r,(_,p) in zip(raw,recs)]
        data=(len(raw)|1<<63).to_bytes(8,'little')+b''.join(raw)
        entry=dict(name=name,count=len(raw),bin_sha256=native_fp.hashlib.sha256(data).hexdigest(),
                   **(dict(requires=requires) if requires else {}))
        if included is not None and k not in included:
            entry['included']=False
        else:
            (root/(name+'.bin')).write_bytes(data)
            write_json(root/(name+'.json'),[dict(index=i,family='fake',instruction=f'seed{s}',code='90',flags_mask=0x8d5,sw_mask=0xb8ff)
                                            for i,(s,_) in enumerate(recs)])
            (root/(name+'.model')).write_text(f'BEGIN {len(raw):016x}\n'+''.join(' '.join(f'{v:016x}' for v in model_row(i,s))+'\n'
                                                                             for i,(s,_) in enumerate(recs))+'END\n')
        manifest['campaigns'].append(entry)
    (root/'oracle').write_text(FAKE_ORACLE);(root/'oracle').chmod(0o755)
    for p in sorted(root.iterdir()):manifest['sha256'][p.name]=digest(p)
    write_json(root/'manifest.json',manifest)
    return root


def run_fake(bundle,result,timeout=5):
    args=argparse.Namespace(directory=bundle,result=result,timeout=timeout)
    with mock.patch('platform.system',return_value='Linux'),mock.patch('platform.machine',return_value='x86_64'):
        return native_fp.run(args)


class Runner(unittest.TestCase):
    """The runner keeps going: refused records are skipped, a failing or hanging case is recorded and the
    oracle restarted after it, a campaign that fails before its first case is recorded; compare lists all."""

    def test_partial_run_and_comparison(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            bundle=make_bundle(root/'b',[
                ((),[(1,0x67),(2,0x67)]),                                                    # clean
                ((),[(1,0x67),(2,0x67),(3,0x45),(4,0x67),(0xDEAD,0x67),(6,0x67),(0xBEEF,0x67),(8,0x67)]),
                ((),[(0xCA1B,0x67),(2,0x67)]),                                               # fails at start
                (['avx'],[(1,0x67)]),                                                        # CPUID gated
                ((),[(1,0x67),(2,0x67),(3,0x67)])])                                          # after the failures
            with contextlib.redirect_stdout(io.StringIO()):
                code=run_fake(bundle,root/'r',timeout=3)
            self.assertEqual(code,1)
            host=json.loads((root/'r/hardware.json').read_text())
            r=host['results']
            self.assertEqual(r['campaign-000']['status'],'ok');self.assertEqual(r['campaign-004']['status'],'ok')
            self.assertEqual(r['campaign-000']['returncode'],0)
            self.assertEqual(r['campaign-003'],dict(skipped='missing CPUID features: avx'))
            b=r['campaign-001'];self.assertEqual(b['status'],'partial')
            self.assertEqual([x['index'] for x in b['rejected']],[2])
            self.assertEqual([(x['index'],x['returncode'],x['timeout']) for x in b['failed_cases']],[(4,1,False),(6,None,True)])
            self.assertIn('signal outside instruction buffer',b['failed_cases'][0]['message'])
            self.assertEqual(r['campaign-002']['status'],'failed');self.assertEqual(r['campaign-002']['not_run'],[[0,1]])
            self.assertIn('calibration',r['campaign-002']['error'])
            # the stitched output: the five executed rows of campaign-001 with their campaign indices
            self.assertEqual([v[0] for v in rows(root/'r/campaign-001.out',8,100,frozenset({2,4,6}))],[0,1,3,5,7])
            c=json.loads((root/'r/comparison.json').read_text())
            self.assertEqual((c['cases'],c['total_cases'],c['not_compared'],c['skipped']),(10,16,5,1))
            self.assertEqual(c['incomplete_campaigns'],['campaign-001','campaign-002'])
            self.assertEqual(c['campaigns']['campaign-001']['not_compared'],
                             {'oracle failed on this case (exit 1)':[[4,4]],'oracle failed on this case (timeout)':[[6,6]],
                              'rejected by the oracle: unsupported data permission':[[2,2]]})
            self.assertEqual(c['strict_mismatches'],0)
            self.assertTrue((root/'r.tar.gz').exists())
            self.assertIn('NOT COMPARED: 5 cases',(root/'r/summary.txt').read_text())
            # damage is still refused
            with (root/'r/campaign-004.out').open('a') as f:f.write('x\n')
            with contextlib.redirect_stdout(io.StringIO()),self.assertRaises(ValueError):
                compare(bundle,root/'r')

    def test_legacy_failed_campaign_salvages_complete_rows(self):
        # results of the first runner: a batch that ended with exit 1 after three rows
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);bundle=make_bundle(root/'b',[((),[(1,0x67),(2,0x67),(3,0x67),(4,0x67),(5,0x67)])])
            res=root/'r';res.mkdir()
            (res/'campaign-000.out').write_text('BEGIN 0000000000000005 \n'+''.join(
                ' '.join(f'{v:016x}' for v in [i,5,0,0x20102,0x23]+[s]+[0]*94)+' \n' for i,s in enumerate((1,2,3))))
            write_json(res/'hardware.json',dict(kind='ia32-fp-v2',manifest_sha256=digest(bundle/'manifest.json'),
                results={'campaign-000':dict(returncode=1,output_sha256=digest(res/'campaign-000.out'))}))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(compare(bundle,res,out=root/'c'),1)
            c=json.loads((root/'c/comparison.json').read_text())
            self.assertEqual((c['cases'],c['not_compared']),(3,2))
            self.assertEqual(c['campaigns']['campaign-000']['not_compared'],
                             {'not run (batch ended)':[[4,4]],'oracle exited 1 on this case (see campaign-000.log)':[[3,3]]})

    def test_resume_merge_and_recompare(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            first=[((),[(1,0x67),(2,0x67)]),((),[(3,0x67),(0xDEAD,0x67),(5,0x67)]),((),[(6,0x67),(7,0x67)])]
            base=make_bundle(root/'base',first)
            with contextlib.redirect_stdout(io.StringIO()):
                run_fake(base,root/'base-r')
                s,done=native_fp.completed(base,root/'base-r')
            self.assertEqual(sorted(done),['campaign-000','campaign-002'])
            # campaign-001 fixed (the failing case replaced); the others must regenerate identically
            fixed=[first[0],((),[(3,0x67),(4,0x67),(5,0x67)]),first[2]]
            plan=[]
            for k,(req,recs) in enumerate(fixed):
                raw=[fp_cases.record('90',seed=x,permissions=(0x67,0x67)) for x,_ in recs]
                data=(len(raw)|1<<63).to_bytes(8,'little')+b''.join(raw)
                plan.append(native_fp.include_campaign(f'campaign-{k:03d}',k,len(raw),native_fp.hashlib.sha256(data).hexdigest(),done,None))
            self.assertEqual(plan,[False,True,False])
            with self.assertRaises(ValueError):native_fp.include_campaign('campaign-000',0,2,'0'*64,done,None)
            self.assertEqual(native_fp.include_campaign('campaign-005',5,1,'0'*64,{},native_fp.parse_only('003-005,9')),True)
            self.assertEqual(native_fp.parse_only('035-037,40'),{35,36,37,40})
            resume=make_bundle(root/'resume',fixed,included={1})
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(run_fake(resume,root/'resume-r'),0)   # campaigns of the base run: listed, not counted
            alone=json.loads((root/'resume-r/comparison.json').read_text())
            self.assertEqual((alone['cases'],alone['not_included'],alone['not_compared']),(3,4,0))
            self.assertEqual(json.loads((root/'resume-r/hardware.json').read_text())['results'].keys(),{'campaign-001'})
            # one comparison over both runs: every campaign from its complete run
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(compare(resume,root/'resume-r',merge=[(base,root/'base-r')]),0)
            c=json.loads((root/'resume-r-combined/comparison.json').read_text())
            self.assertEqual((c['cases'],c['total_cases'],c['not_compared'],c['not_included']),(7,7,0,0))
            self.assertEqual(c['campaigns']['campaign-001']['source'],str((root/'resume-r').resolve()))
            self.assertEqual(c['campaigns']['campaign-000']['source'],str((root/'base-r').resolve()))
            self.assertTrue(c['campaigns']['campaign-001']['inputs_differ_between_sources'])
            # recompare: the current model on the stored inputs; nothing in the bundles/results changes
            model=root/'x86fp';model.write_text(FAKE_MODEL.replace('DELTA','0'));model.chmod(0o755)
            before={p:digest(p) for p in root.rglob('*') if p.is_file() and 'recompare' not in str(p) and p!=model}
            args=argparse.Namespace(directory=resume,result=root/'resume-r',merge=[(base,root/'base-r')],model=model,
                                    out=None,jobs=2)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(native_fp.recompare(args),0)
            model.write_text(FAKE_MODEL.replace('DELTA','1'))
            args.out=root/'again'
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(native_fp.recompare(args),1)
            bad=[json.loads(l) for l in (root/'again/mismatches.jsonl').read_text().splitlines()]
            self.assertEqual([(b['campaign'],b['index'],b['differences'][0]['field']) for b in bad],[('campaign-002',1,'r0')])
            self.assertIn('fake/seed7: strict 1',(root/'again/summary.txt').read_text())
            self.assertEqual(before,{p:digest(p) for p in before})
            # the paste script carries the exact bundle
            _,script=native_fp.package(resume)
            with contextlib.redirect_stdout(io.StringIO()):
                native_fp.unpack(argparse.Namespace(directory=script,out=root/'unpacked'))
            self.assertEqual({p.name:digest(p) for p in (root/'unpacked/resume').iterdir()},{p.name:digest(p) for p in resume.iterdir()})
            # an input that no longer matches its manifest hash is refused
            with (base/'campaign-000.bin').open('ab') as f:f.write(b'x')
            with contextlib.redirect_stdout(io.StringIO()),self.assertRaises(ValueError):
                native_fp.recompare(args)



def v3(code,flags=0x202,ext=None,**kw):
    """A format-3 record (native_ext.record3) with an optionally replaced extension."""
    import native_ext
    r=bytearray(native_ext.record3(code,flags=flags,**kw))
    if ext is not None: r[776:904]=ext.ljust(128,b'\0')
    return bytes(r)


def check_v3(checker,d,records):
    p=Path(d)/'v3.bin';p.write_bytes((len(records)|3<<62).to_bytes(8,'little')+b''.join(records))
    return {r['index']:r['reason'] for r in native_fp.check_records(checker,p,len(records),())}


class ExtendedRules(unittest.TestCase):
    """The rules of the extended bundle: software interrupts, near transfers, trailing bytes and TF, MOV SS
    with TF, the v3 extension; the decoder against the model; the comparison of format-3 rows."""

    @unittest.skipUnless(CC,'no host C compiler')
    def test_transfer_trailing_and_extension_rules(self):
        import native_ext
        probes=[(v3('cc'),'software interrupt'),(v3('ce'),'software interrupt'),(v3('f1'),'software interrupt'),
                (v3('eb10'),None),(v3('ebfe'),'near transfer target'),(v3('eb80'),None),(v3('e900100000'),'near transfer target'),
                (v3('66e90010'),'near transfer target'),(v3('0f8410000000'),None),(v3('e2f0'),None),(v3('e3fd'),None),(v3('e3fe'),'near transfer target'),
                # RET through the arena: a code-page pointer at ESP (a patch) / random data
                (v3('c3',regs={4:0x10100},patches=[(0x100,0x20180)]),None),(v3('c3',regs={4:0x10100}),'near transfer target'),
                (v3('c3',regs={4:0x10100},permissions=(0,0x67)),None),(v3('c3',regs={4:0x200000}),'outside the arena'),
                (v3('ffd0',regs={0:0x20200}),None),(v3('ffd0',regs={0:0x100000}),'near transfer target'),
                (v3('ff13',regs={3:0x10040},patches=[(0x40,0x20300)]),None),(v3('ff23',regs={3:0x8000}),None),
                (v3('ff23',regs={3:0x30000}),'outside the arena'),
                # bytes after the instruction: only with TF; not after MOV/POP SS; MOV/POP SS not with TF
                (v3('9090'),'bytes after the instruction'),(v3('9090',flags=0x302),None),(v3('0f38f0c11c'),None),
                (v3('8fe878c2c1'),None),(v3('8fe878c2c105'),'bytes after'),(v3('17'),None),(v3('17',flags=0x302),'MOV/POP SS'),
                (v3('8ed090',flags=0x302),'MOV/POP SS'),(v3('3e3e3e3e3e3e3e3e3e3e3e3e3e3e90'),None),
                # the extension
                (v3('90',ext=struct.pack('<I',4)),'extension flags'),(v3('90',ext=struct.pack('<IHH',2,0,8129)),'dump window'),
                (v3('90',ext=struct.pack('<IHHQQB',0,0,0,0,0,9)),'eight arena patches'),
                (v3('90',ext=struct.pack('<IHHQQB7xHHI',0,0,0,0,0,1,8190,0,1)),'outside the arena'),
                (v3('90',ext=struct.pack('<IHHQQB7xHHI',0,0,0,0,0,1,8000,48,1)),None),
                (v3('90',ext=struct.pack('<IHHQQB7xHHI',0,0,0,0,0,1,8000,49,1)),'outside the arena'),
                (v3('90',ext=struct.pack('<IHHQQB',0,0,0,0,0,0)+b'\1'),'reserved'),
                (v3('90',ext=struct.pack('<IHHQQB7xHHI',0,0,0,0,0,0,4,0,1)),'unused arena patch'),
                # mode 1 (a 16-bit code segment, IP 0100h, DS based at the arena): 16-bit targets and operands
                (v3('eb10',mode=1),None),(v3('e90010',mode=1),'near transfer target'),(v3('e9fdff',mode=1),'near transfer target'),
                (v3('66e910000000',mode=1),None),(v3('c3',mode=1,regs={4:0x10100},patches=[(0x100,0x0180)]),None),
                (v3('c3',mode=1,regs={4:0x10100},patches=[(0x100,0x2180)]),'near transfer target'),
                (v3('ff27',mode=1,regs={3:0x40},patches=[(0x40,0x0200)]),None),(v3('ffd0',mode=1,regs={0:0x20200}),None),(v3('ffd0',mode=1,regs={0:0x1200}),'near transfer target'),
                (v3('90',ext=struct.pack('<IHHQQB3xB',0,0,0,0,0,0,2)),'mode')]
        with tempfile.TemporaryDirectory() as d:
            got=check_v3(compiled_checker(d),d,[r for r,_ in probes])
        for i,(r,why) in enumerate(probes):
            if why is None: self.assertNotIn(i,got,(i,r[1:1+r[0]].hex()))
            else: self.assertIn(why,got.get(i,''),(i,r[1:1+r[0]].hex()))

    @unittest.skipUnless(CC,'no host C compiler')
    def test_decoder_matches_python_layout_and_the_model(self):
        """rc_decode (C), native_ext.layout (Python) and the model's decoded length agree on random encodings."""
        import random as _r, native_ext, native_fuzz
        rng=_r.Random(5);codes=[native_fuzz.random_encoding(rng)[0][:15] for _ in range(3000)]
        codes+=[bytes.fromhex(c) for c in ('90','0f38f0c1','c4e27850','62c0','8fe878c2c105','67c4e26d900400','f6c001','f7c001000000',
                                          '66f7c00100','a1001000','67a10010','c8100003','0f7803','660f780102','f20f78c10102','0f0f0001')]
        with tempfile.TemporaryDirectory() as d:
            src=Path(d)/'dec.c'
            src.write_text('#include <stdio.h>\n#include "record_check.h"\nint main(void){char line[64];'
                           'while(fgets(line,64,stdin)){unsigned char b[40];unsigned n=0,x;'
                           'for(int i=0;i<40;i++)b[i]=0xcc;'
                           'while(sscanf(line+2*n,"%2x",&x)==1&&n<15){b[n++]=x;}'
                           'struct rc_insn r;rc_decode(b,&r);printf("%u %x\\n",r.len,r.op);}return 0;}\n')
            subprocess.run([CC,'-O1','-I',str(HERE/'native'),'-o',str(Path(d)/'dec'),str(src)],check=True)
            out=subprocess.run([str(Path(d)/'dec')],input=''.join(c.hex()+'\n' for c in codes),capture_output=True,text=True,check=True)
        c_lens=[tuple(int(x,16) if k else int(x) for k,x in enumerate(l.split())) for l in out.stdout.splitlines()]
        py=[native_ext.layout(c)[:2] for c in codes]
        self.assertEqual(c_lens,py)
        # the model's decode (x86fp --probe; 0 = not decoded, e.g. #PF or #GP at the length limit)
        if native_ext.X86FP.exists():
            raws=[native_ext.record3(c,flags=0x302) for c in codes]
            probe=native_ext._run_model(raws,True,True,native_ext.X86FP)
            for c,p,(n,_) in zip(codes,probe,py):
                if p[6]: self.assertEqual(p[6],n,c.hex())

    def test_format3_rows_and_observe_fields(self):
        h=[0]*110;h[1]=11;h[4]=0x23;h[55]=14;h[57]=0x11000;h[3]=0x20100;h[99]=1
        h[100]=0x20123;h[101]=0x10345;h[102:110]=list(range(1,9))
        r=normalize(h);self.assertEqual(len(r),82)
        self.assertEqual(r[71:74],[0x20123,0x10345,0x11000]);self.assertEqual(r[74:],list(range(1,9)))
        h[55]=13;self.assertEqual(normalize(h)[73],0)   # CR2 only for #PF
        meta=dict(instruction='x',flags_mask=0x8d5,sw_mask=0xb8ff)
        m=list(r);m[71]^=1
        self.assertEqual(differences(meta,r,m),[])                       # FIP64/FDP64: only on request
        self.assertEqual({d['field'] for d in differences(dict(meta,compare_pointers=True),r,m)},{'fip64'})
        m[33]^=1   # FOP/FIP/FDP: always (x86fp reports them as the signal frame's XSAVE stores them)
        self.assertEqual({d['field'] for d in differences(meta,r,m)},{'fop'})
        self.assertEqual(classify(dict(meta,observe_fields=['fop','fip64']),differences(meta,r,m)),'strict_mismatches')
        m=list(r);m[75]^=1
        self.assertEqual(differences(meta,r,m)[0]['field'],'dump1')
        # undefined flags: the pinned ones (every arithmetic flag since the extended EPYC run) strictly,
        # others compared as observations; observe fields; '*'
        m=list(r);m[4]^=0x800
        dm=dict(meta,flags_mask=0xd5,flags_observe=0x800)
        diff=differences(dm,r,m);self.assertEqual(diff[0]['field'],'eflags')
        self.assertEqual(classify(dm,diff),'strict_mismatches')
        with mock.patch.object(native_fp,'PINNED_UNDEFINED',0):
            diff=differences(dm,r,m);self.assertEqual(diff[0]['field'],'eflags.undefined')
            self.assertEqual(classify(dm,diff),'observations')
            m[4]^=0x801;diff=differences(dm,r,m);self.assertEqual(classify(dm,diff),'strict_mismatches')
        self.assertEqual(classify(dict(meta,observe_fields=['r0']),[dict(field='r0')]),'observations')
        self.assertEqual(classify(dict(meta,observe_fields=['r0']),[dict(field='r0'),dict(field='r1')]),'strict_mismatches')
        self.assertEqual(classify(dict(meta,observe_fields=['*']),[dict(field='vector')]),'observations')
        # the full control word where the case asks for it
        m=list(r);m[30]^=0x80
        self.assertEqual(differences(meta,r,m),[])
        self.assertEqual(differences(dict(meta,fcw_full=True),r,m)[0]['field'],'fcw')

    def test_model_problems_format3(self):
        meta=[dict(index=0),dict(index=1)]
        m=[[0,14,6,0x20100]+[0]*69+[0x3F000]+[0]*8,[1,14,6,0x20100]+[0]*69+[0x40000]+[0]*8]
        self.assertEqual([p['index'] for p in native_fp.model_problems(meta,m)],[1])

    def test_oracle_sandbox_in_source(self):
        oracle=(HERE/'native/signal_oracle.c').read_text()
        handler=oracle[oracle.index('static void handler('):oracle.index('static void execute(')]
        # the image is made writable first thing in the handler, read-only before the instruction, and
        # its digest is checked before the handler writes anything
        self.assertLess(handler.index('protect(7)'),handler.index('struct context *c'))
        self.assertLess(handler.index('image_hash=image_digest()'),handler.index('protect(5)'))
        self.assertLess(handler.index('image_digest()!=image_hash'),handler.index('observed=*c'))
        self.assertIn('audit_maps();',oracle);self.assertIn('mov %%ax,%%fs; mov %%ax,%%gs',oracle)
        self.assertIn('oracle_image_end',(HERE/'native/signal_enter.S').read_text())


class Determinism(unittest.TestCase):
    def test_topology_and_cpu_choice(self):
        info='processor\t: 0\nphysical id\t: 0\ncore id\t\t: 0\n\nprocessor\t: 1\nphysical id\t: 0\ncore id\t\t: 0\n\n' \
             'processor\t: 2\nphysical id\t: 0\ncore id\t\t: 1\n'
        topo=native_fp.cpu_topology(info)
        self.assertEqual(topo,{0:('0','0'),1:('0','0'),2:('0','1')})
        self.assertEqual(native_fp.choose_cpus('auto',{0,1,2},topo)[0],[0,2])
        self.assertEqual(native_fp.choose_cpus(None,{1,2},{})[0],[1,2])
        self.assertEqual(native_fp.choose_cpus(None,{3},{})[0],[3,3])
        self.assertEqual(native_fp.choose_cpus('2,0',{0,1,2},topo)[0],[2,0])
        with self.assertRaises(ValueError): native_fp.choose_cpus('0,7',{0,1,2},topo)

    def test_repeated_run_pinned_and_compared(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            bundle=make_bundle(root/'b',[((),[(1,0x67),(2,0x67)]),((),[(3,0x67),(0xD1FF,0x67),(5,0x67)]),
                                         ((),[(0xD1FE,0x67)])])
            # the fake oracle observes seeds 0xD1FF/0xD1FE differently in its second pass (FP_PASS=2);
            # case 0 of campaign-002 marks EAX ('r0') as an observe field
            (bundle/'oracle').write_text(FAKE_ORACLE.replace("h[6]=seed(r)",
                "h[6]=seed(r)+(1 if seed(r) in (0xD1FF,0xD1FE) and __import__('os').environ.get('FP_PASS')=='2' else 0)"))
            meta=json.loads((bundle/'campaign-002.json').read_text());meta[0]['observe_fields']=['r0']
            write_json(bundle/'campaign-002.json',meta)
            man=json.loads((bundle/'manifest.json').read_text())
            for p in ('oracle','campaign-002.json'): man['sha256'][p]=digest(bundle/p)
            man['run_defaults']=dict(repeat=2,pin='auto');write_json(bundle/'manifest.json',man)
            pinned=[]
            with mock.patch.object(native_fp.os,'sched_setaffinity',lambda pid,cpus:pinned.append(sorted(cpus)),create=True), \
                 mock.patch.object(native_fp.os,'sched_getaffinity',lambda pid:{0,1,2,3},create=True), \
                 mock.patch.object(native_fp,'cpu_topology',lambda text:{0:('0','0'),1:('0','0'),2:('0','1'),3:('0','1')}), \
                 contextlib.redirect_stdout(io.StringIO()):
                code=run_fake(bundle,root/'r')
            self.assertEqual(code,1)
            host=json.loads((root/'r/hardware.json').read_text())
            self.assertEqual(host['repeat']['cpus'],[0,2])
            self.assertIn([0],pinned);self.assertIn([2],pinned);self.assertEqual(pinned[-1],[0,1,2,3])
            r=host['results']
            self.assertTrue(r['campaign-000']['repeat'][0]['identical'])
            self.assertEqual(r['campaign-001']['repeat'][0]['differing'],[dict(index=1,fields=['r0'])])
            self.assertEqual(r['campaign-001']['repeat'][0]['cpu'],2);self.assertEqual(r['campaign-001']['cpu'],0)
            self.assertTrue((root/'r/campaign-001.rep2.out').exists())
            c=json.loads((root/'r/comparison.json').read_text())['determinism']
            self.assertEqual((c['campaigns'],c['identical'],c['differing_cases'],c['expected'],c['unexpected']),(3,1,2,1,1))
            self.assertEqual(c['examples'][0]['campaign'],'campaign-001')
            # the model comparison used the first pass only: no strict mismatch
            self.assertEqual(json.loads((root/'r/comparison.json').read_text())['strict_mismatches'],0)

    def test_bundle_without_model_files(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);bundle=make_bundle(root/'b',[((),[(1,0x67),(2,0x67)])])
            (bundle/'campaign-000.model').unlink()
            man=json.loads((bundle/'manifest.json').read_text());del man['sha256']['campaign-000.model']
            man['model_files']=False;write_json(bundle/'manifest.json',man)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(run_fake(bundle,root/'r'),0)   # not compared on the target
                with self.assertRaises(ValueError): compare(bundle,root/'r')
            model=root/'x86fp';model.write_text(FAKE_MODEL.replace('DELTA','0'));model.chmod(0o755)
            args=argparse.Namespace(directory=bundle,result=root/'r',merge=[],model=model,out=root/'c',jobs=1)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(native_fp.recompare(args),0)
            self.assertEqual(json.loads((root/'c/comparison.json').read_text())['cases'],2)


if __name__=='__main__':unittest.main()
