"""Coverage, isolation and reproducibility gates for the twelve-target campaign."""
import collections
import json
import struct
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from native_hunt import TARGETS, decode_accesses, triage, vectors


class HuntCoverage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases={a:list(vectors(a,[20261023,20261024],20)) for a in ('i386','x86_64')}

    def test_twelve_targets_and_mutations(self):
        seen=set()
        for arch,cases in self.cases.items():
            counts=collections.Counter(m['campaign'] for _,_,m in cases)
            seen.update(counts)
            self.assertTrue(all(n>=200 for n in counts.values()),counts)
            self.assertEqual({m['source_seed'] for _,_,m in cases if 'source_seed' in m}, {20261023,20261024})
            for index,(model,native,meta) in enumerate(cases):
                self.assertEqual(meta['index'],index)
                self.assertEqual(len(model),88 if arch=='i386' else 440)
                self.assertEqual(len(native),440)
                self.assertEqual(native[1:1+native[0]].hex(),meta['code'])
                self.assertEqual(model[:1+model[0]],native[:1+native[0]])
                self.assertEqual(struct.unpack_from('<I',native,152)[0],meta['data_seed'])
                self.assertEqual(struct.unpack_from('<I',native,432)[0],meta['mxcsr'])
                regs=struct.unpack_from('<16Q',native,16)
                flags=struct.unpack_from('<Q',native,144)[0]
                self.assertEqual(decode_accesses(arch,bytes.fromhex(meta['code']),regs,flags),meta['accesses'])
        self.assertEqual(seen,set(TARGETS))
        self.assertEqual(len(seen),12)

    def test_seeded_generation_is_reproducible(self):
        self.assertEqual(self.cases['i386'],list(vectors('i386',[20261023,20261024],20)))

    def test_rejects_unsafe_or_unbounded_instructions(self):
        regs=[0]*16;regs[3]=regs[4]=0x10800
        for code in ('0f05','ffd3','ff23','c3','f348a5'):
            with self.assertRaises(AssertionError):decode_accesses('x86_64',bytes.fromhex(code),regs,0x202)
        regs[3]=0x12000
        with self.assertRaises(AssertionError):decode_accesses('x86_64',bytes.fromhex('8903'),regs,0x202)
        regs[3]=0x10000;regs[1]=0xffffffffffffffff
        with self.assertRaises(AssertionError):decode_accesses('x86_64',bytes.fromhex('480fab0b'),regs,0x202)
        regs[4]=0x11ffc
        with self.assertRaises(AssertionError):decode_accesses('x86_64',bytes.fromhex('8f0424'),regs,0x202)
        regs[3]=0x10fff
        with self.assertRaises(AssertionError):decode_accesses('x86_64',bytes.fromhex('f00103'),regs,0x202)

    def test_implicit_addresses_and_prefix_cancellation(self):
        regs=[0]*16;regs[4]=0x10800;regs[3]=0x10fff;regs[1]=0xffffffffffffffff
        self.assertEqual(decode_accesses('x86_64',bytes.fromhex('8f0424'),regs,0x202),[(0x10800,8),(0x10808,8)])
        self.assertEqual(decode_accesses('x86_64',bytes.fromhex('48668b03'),regs,0x202),[(0x10fff,2)])
        self.assertEqual(decode_accesses('x86_64',bytes.fromhex('480fab0b'),regs,0x202),[(0x10ff7,8)])
        regs[1]=0;regs[6]=regs[7]=0xffffffffffffffff
        self.assertEqual(decode_accesses('x86_64',bytes.fromhex('f3a7'),regs,0x202),[])

    def test_triage_exports_exact_records_without_claiming_bugs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);directory=root/'returned';out=root/'triage'
            fixture={}
            for arch in ('i386','x86_64'):
                dest=directory/arch;dest.mkdir(parents=True)
                pairs=self.cases[arch][:2];fixture[arch]=pairs[1]
                (dest/'vectors.bin').write_bytes(b''.join(m for m,_,_ in pairs))
                (dest/'native.bin').write_bytes(struct.pack('<Q',2)+b''.join(n for _,n,_ in pairs))
                (dest/'native.out').write_text('BEGIN\nfirst\nsecond\nEND\n')
            def fake_compare(args):
                for arch in fixture:
                    dest=out/arch;dest.mkdir(parents=True)
                    (dest/'model.out').write_text('BEGIN\nfirst\nsecond model\nEND\n')
                    meta=dict(fixture[arch][2],differences=['exception: differs'])
                    (dest/'mismatches.json').write_text(json.dumps([meta]))
                return 1
            with patch('native.compare',side_effect=fake_compare) as check:
                triage(directory,root/'prepared',out)
                check.assert_called_once()
            report=json.loads((out/'triage.json').read_text())
            self.assertIsNone(report['confirmed_distinct_bugs'])
            self.assertEqual(report['candidate_clusters'],2)
            for candidate in report['candidates']:
                dest=Path(candidate['path']);m,n,_=fixture[candidate['architecture']]
                self.assertEqual((dest/'vectors.bin').read_bytes(),m)
                self.assertEqual((dest/'native.bin').read_bytes(),struct.pack('<Q',1)+n)
                self.assertEqual((dest/'observed-row.txt').read_text(),'second\n')
                self.assertEqual(candidate['status'],'unconfirmed')


if __name__=='__main__':unittest.main()
