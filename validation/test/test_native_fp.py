"""Coverage and fail-closed evidence checks for the user-mode FP campaign."""
import collections
import json
import struct
import tempfile
import unittest
from pathlib import Path

from fp_cases import cases, X87, TRANS, SIZE
from native_fp import classify, differences, rows, verify, digest, normalize, compare, write_json


class Coverage(unittest.TestCase):
    def test_record_integrity_and_directed_coverage(self):
        counts=collections.Counter();ops=set();control=collections.defaultdict(set)
        for raw,m in cases(123,100):
            self.assertEqual(len(raw),SIZE)
            self.assertEqual(raw[1:1+raw[0]].hex(),m['code'])
            self.assertEqual(struct.unpack_from('<Q',raw,144)[0]&0x100,0)
            self.assertLess(struct.unpack_from('<H',raw,444)[0],256)
            self.assertLess(struct.unpack_from('<I',raw,436)[0],4)
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


if __name__=='__main__':unittest.main()
