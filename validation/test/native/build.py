#!/usr/bin/env python3
"""Build a freestanding Linux ELF64 oracle, including on macOS with clang."""
import importlib.util
import os
import platform
import struct
import subprocess
import sys
import tempfile
from pathlib import Path


def build(source, output, linker, backend='ptrace'):
    spec = importlib.util.spec_from_file_location('elf_link', linker)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        cc = [os.environ.get('CC', 'clang' if platform.system() == 'Darwin' else 'gcc')]
        if platform.system() == 'Darwin':
            cc += ['--target=x86_64-none-elf']
        cc += ['-m64', '-O2', '-Wall', '-Wextra', '-Werror', '-ffreestanding', '-fno-builtin', '-fno-pie',
               '-fno-pic', '-fno-stack-protector', '-fno-asynchronous-unwind-tables',
               '-mno-red-zone', '-mno-sse', '-mno-mmx']
        if backend in ('memory', 'fp'):
            cc += ['-DNATIVE_MEMORY']
        if backend == 'fp':
            cc += ['-DNATIVE_FP']
        objects = []
        sources = ['start.S', 'oracle.c'] if backend == 'ptrace' else ['start.S', 'signal_oracle.c', 'signal_enter.S']
        for name in sources:
            obj = tmp / (Path(name).stem + '.o')
            subprocess.run([*cc, '-c', str(source / name), '-o', str(obj)], check=True)
            objects.append(str(obj))
        # Reuse the strict ELF relocation implementation, then wrap its image in
        # ELF64 rather than the harness's ELF32 multiboot container.
        container = tmp / 'container'
        module.link(objects, container)
        data = container.read_bytes()
        entry = struct.unpack_from('<I', data, 24)[0]
        image = data[4096:]
        ident = b'\x7fELF\x02\x01\x01' + bytes(9)
        header = struct.pack('<16sHHIQQQIHHHHHH', ident, 2, 62, 1, entry, 64, 0, 0, 64, 56, 1, 0, 0, 0)
        ph = struct.pack('<IIQQQQQQ', 1, 7, 4096, module.BASE, module.BASE, len(image), len(image), 4096)
        output.write_bytes(header + ph + bytes(4096-len(header)-len(ph)) + image)
        output.chmod(0o755)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[3]  # repository root
    build(Path(__file__).resolve().parent, Path(sys.argv[1]), root / 'x86_64/test/harness/link.py')
