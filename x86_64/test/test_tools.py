#!/usr/bin/env python3
"""Regression checks for the verification gate itself, including negative cases."""
import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from compare import compare, read
from gen import generate

class VerificationGate(unittest.TestCase):
    def test_complete_output_and_mismatch(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); row=[0]*58
            meta=root/'meta.json';meta.write_text(json.dumps([{'mask':0xdd5,'index':0,'family':'test','code':'90'}]))
            def write(path,r): path.write_text('BEGIN 1\n'+' '.join(f'{x:x}' for x in r)+'\nEND\n')
            q=root/'q';m=root/'m';write(q,row);write(m,row)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertFalse(compare(meta,q,m))
                row[4]=1;write(m,row)
                self.assertTrue(compare(meta,q,m))
            m.write_text('BEGIN 1\n')
            with self.assertRaises(ValueError): read(m,1)
    def test_determinism_and_vector_layout(self):
        with tempfile.TemporaryDirectory() as temp:
            a=Path(temp)/'a';b=Path(temp)/'b'
            with contextlib.redirect_stdout(io.StringIO()):
                generate(280,19,a);generate(280,19,b)
            data=a.with_suffix('.bin').read_bytes()
            self.assertEqual(data,b.with_suffix('.bin').read_bytes())
            self.assertEqual(len(data),280*440)
            for offset in range(0,len(data),440): self.assertTrue(1<=data[offset]<=15)
    def test_workload_requires_real_marker_lines(self):
        path=Path(__file__).resolve().parents[1]/'guest/check.py'
        spec=importlib.util.spec_from_file_location('guest_check',path)
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        with self.assertRaises(ValueError): module.workload(b'~ # echo "== begin"; echo "== end"\r\n')
        self.assertEqual(module.workload(b'prompt\r\n== begin\r\n42\r\n== end\r\n'),'== begin\n42\n== end\n')

if __name__=='__main__': unittest.main()
