"""Ensure memory evidence cannot pass with missing bytes, faults or coverage."""
import collections
import struct
import tempfile
import unittest
from pathlib import Path
from native import differences, read_native
from native_memory import BASE, vectors, verify_case


class MemoryGate(unittest.TestCase):
    def test_cases_stay_in_arena_and_cover_permissions_addressing_and_rep(self):
        for arch in ('i386','x86_64'):
            families=collections.Counter();forms=set();permissions=set();fault_crossings=0
            for model,native,meta in vectors(arch,[42,43],4):
                families[meta['family']]+=1;forms.add(meta['form']);permissions.add(meta['permissions'])
                self.assertEqual(len(model),88 if arch=='i386' else 440)
                self.assertEqual(len(native),440)
                if meta['address']<BASE+4096<meta['address']+meta['width'] and 'none' in meta['permissions']:
                    fault_crossings+=1
            self.assertEqual(len(permissions),9)
            self.assertGreater(fault_crossings,100)
            for name in ('memory_load','memory_store','memory_cmpxchg','memory_push','memory_pop','memory_rep_movs'):
                self.assertGreater(families[name],100)
            self.assertIn('sib',forms)
            if arch=='x86_64':self.assertTrue({'rip','addr32','high_sib'}<=forms)

    def test_independent_address_decoder_rejects_escape(self):
        regs=[0]*16;regs[3]=0x20000
        with self.assertRaises(AssertionError):
            verify_case('x86_64',bytes.fromhex('488903'),regs,0x202,{'width':8,'address':0x20000})
        with self.assertRaises(AssertionError):
            verify_case('x86_64',bytes.fromhex('0f05'),regs,0x202,{'width':8,'address':BASE})

    def test_memory_and_fault_fields_are_compared(self):
        for arch in ('i386','x86_64'):
            h=[0]*61;m=[0]*(26 if arch=='i386' else 60)
            h[1:6]=[11,1,0x20100,0x23 if arch=='i386' else 0x33,0x202]
            h[55:58]=[14,4,0x11000];m[1:4]=[14,4,0x20100]
            m[12 if arch=='i386' else 20]=0x202;m[19 if arch=='i386' else 21]=0x11000
            self.assertEqual(differences(arch,{'mask':0xdd5},h,m),[])
            for field in (6,55,56,57,58,59,60):
                bad=h.copy();bad[field]^=1
                self.assertTrue(differences(arch,{'mask':0xdd5},bad,m),field)

    def test_memory_records_require_all_three_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'out'
            p.write_text('BEGIN 0000000000000001\n'+' '.join(['0000000000000000']*61)+'\nEND\n')
            self.assertEqual(len(read_native(p,1,61)),1)
            with self.assertRaises(ValueError):read_native(p,1,58)


if __name__=='__main__':unittest.main()
