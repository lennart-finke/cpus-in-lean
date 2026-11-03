"""Regression checks for the native oracle's scope and comparison boundary."""
import tempfile
import unittest
from pathlib import Path
from native import differences, read_native, register_only


class NativeGate(unittest.TestCase):
    def test_excludes_memory_system_and_segment_operations(self):
        for code in ['488b00','488900','50','58','9c','9d','c3','e800000000','0f05',
                     '0f34','cd80','8ed8','8cd8','f3a4','ff20','ffd0','0f22c0']:
            self.assertFalse(register_only(bytes.fromhex(code),'x86_64'),code)
        self.assertFalse(register_only(bytes.fromhex('f30f1000'),'x86_64','simd_move'))

    def test_accepts_register_ops_and_address_arithmetic(self):
        for code in ['4801d8','01d8','83c001','b801000000','488d0500000000','0f0b','0fc8','fec0']:
            self.assertTrue(register_only(bytes.fromhex(code),'x86_64'),code)
        self.assertTrue(register_only(bytes.fromhex('f30f10c1'),'x86_64','simd_move'))
        self.assertTrue(register_only(bytes.fromhex('40'),'i386'))
        self.assertFalse(register_only(bytes.fromhex('40'),'x86_64'))

    def test_comparison_checks_registers_flags_simd_and_mode(self):
        hardware=[0]*55;model=[0]*58
        hardware[1:6]=[5,128,0x20103,0x33,0x202]
        model[1]=3;model[3]=0x20102;model[20]=0x202
        spec={'mask':0xdd5}
        self.assertEqual(differences('x86_64',spec,hardware,model),[])
        for field in [3,4,5,6,21,22,53,54]:
            changed=hardware.copy();changed[field]^=1
            self.assertTrue(differences('x86_64',spec,changed,model),field)
        hardware[5]^=0x10
        self.assertEqual(differences('x86_64',{'mask':0xdd5 & ~0x10},hardware,model),[])

    def test_fault_flags_and_linux_signal_categories(self):
        h=[0]*55;m=[0]*58;h[1:6]=[8,3,0x20100,0x33,2];m[1]=19;m[3]=0x20100;m[20]=2
        self.assertEqual(differences('x86_64',{'mask':0},h,m),[])
        h[2]=1  # Integer division signal must not pass as an SSE exception.
        self.assertTrue(differences('x86_64',{'mask':0},h,m))
        h[2]=3;h[5]^=1  # Fault flags must compare even if completion flags are undefined.
        self.assertTrue(differences('x86_64',{'mask':0},h,m))

    def test_signal_backend_compares_raw_exception_and_error(self):
        h=[0]*58;m=[0]*58
        h[1:6]=[8,3,0x20100,0x33,2];h[55]=19
        m[1]=19;m[3]=0x20100;m[20]=2
        self.assertEqual(differences('x86_64',{'mask':0},h,m),[])
        for field in (55,56):
            changed=h.copy();changed[field]^=1
            self.assertTrue(differences('x86_64',{'mask':0},changed,m))

    def test_signal_backend_requires_extended_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'out'
            row=' '.join(['0000000000000000']*58)
            path.write_text('BEGIN 0000000000000001\n'+row+'\nEND\n')
            self.assertEqual(len(read_native(path,1,58)),1)
            with self.assertRaises(ValueError):
                read_native(path,1,55)
    def test_incomplete_or_duplicated_records_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'out'
            rows=[' '.join(f'{x:016x}' for x in [i]+[0]*54) for i in range(2)]
            good=['BEGIN 0000000000000002',*rows,'END']
            path.write_text('\n'.join(good)+'\n');self.assertEqual(len(read_native(path,2)),2)
            for bad in [good[:-1],[good[0],rows[0],rows[0],'END'],[good[0],rows[1],rows[0],'END'],
                        [good[0],rows[0]+' 0',rows[1],'END']]:
                path.write_text('\n'.join(bad)+'\n')
                with self.assertRaises(ValueError):
                    read_native(path,2)


if __name__=='__main__':
    unittest.main()
