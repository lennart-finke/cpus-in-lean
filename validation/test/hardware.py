#!/usr/bin/env python3
"""Prepare locally, execute on Linux/KVM, then compare locally.

Only the small generated bundle needs to be copied to the x86 server. No Lean
installation or credentials are needed there. KVM is mandatory: no TCG fallback.

Architectures (`prepare --arch ...`):
  i386, x86_64  random single instructions (gen.py v1 vectors) in the ring-3 test harness;
  sys           the IA-32 system-test kernel (test/sys/, built here with clang) in its three passes
                (main; smp=2 on two CPUs; long=1), whole transcripts including the MODEL-ONLY parts,
                compared line by line with x86sys. This is the only way to see privileged behaviour
                (paging, SMEP/SMAP, #AC, call gates, task switches, VME, long-mode entry, SVM as KVM
                nests it) on the EPYC: the user-mode campaign (native_fp.py) cannot. Under KVM the local
                APIC, I/O APIC, PIC/PIT, SMM chipset, NMI delivery and nested SVM are KVM's emulation, not
                the processor's: differences there are not hardware evidence. No QEMU deviation rule is
                applied; every difference is listed for review (`compare` exits 1 if there is any).
"""
import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import struct
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # validation/: builds x86run and x86test
REPO = ROOT.parent
MODEL = {'i386': REPO / 'x86_32', 'x86_64': REPO / 'x86_64', 'sys': REPO / 'x86_32'}
# The system-test passes (test/sys/run.sh): name, kernel command line, CPUs
SYS_PASSES = [('main', '', 1), ('smp2', 'smp=2', 2), ('long', 'long=1', 1)]


def model_root(arch):
    """The Lake package that builds the arch's test executable (x86test, x86sys or x64test)."""
    return MODEL['x86_64'] if arch == 'x86_64' else ROOT


def model_exe(arch):
    return {'i386': 'x86test', 'x86_64': 'x64test', 'sys': 'x86sys'}[arch]


def model_sources(arch):
    """The semantics sources and the test driver whose identity is recorded with the evidence."""
    src = MODEL[arch] / ('X64' if arch == 'x86_64' else 'X86')
    return sorted(src.rglob('*.lean')) + [model_root(arch) / ('SysMain.lean' if arch == 'sys' else 'TestMain.lean')]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(command, **kwargs):
    return subprocess.run([str(x) for x in command], check=True, **kwargs)


def directed_sse(prefix):
    """Exercise DAZ MIN/MAX and all six unmasked SSE exception classes."""
    data = bytearray(prefix.with_suffix('.bin').read_bytes())
    meta = json.loads(prefix.with_suffix('.json').read_text())
    for mandatory, bits in [(b'', 32), (b'\x66', 64), (b'\xf3', 32), (b'\xf2', 64)]:
        one = 0x3f800000 if bits == 32 else 0x3ff0000000000000
        three = 0x40400000 if bits == 32 else 0x4008000000000000
        normal = 0x00800000 if bits == 32 else 0x0010000000000000
        largest = 0x7f7fffff if bits == 32 else 0x7fefffffffffffff
        cases = []
        for op in (0x5d, 0x5f):
            for sign in (0, 1 << (bits - 1)):
                for a, b in [(sign | 1, sign), (sign, sign | 1)]:
                    for daz in (0, 0x40):
                        cases.append(('daz_minmax', op, a, b, 0x1f80 | daz))
        for name, op, a, b, exception in [
            ('invalid', 0x5e, 0, 0, 0),
            ('denormal', 0x58, 1, one, 1),
            ('divide_zero', 0x5e, one, 0, 2),
            ('overflow', 0x59, largest, largest, 3),
            ('underflow', 0x59, normal, normal, 4),
            ('precision', 0x5e, one, three, 5),
        ]:
            for unmasked in (False, True):
                cases.append((name, op, a, b, 0x1f80 & ~(1 << (7 + exception)) if unmasked else 0x1f80))
        for name, op, a, b, mxcsr in cases:
            code = mandatory + bytes([0x0f, op, 0xc1])  # xmm0, xmm1
            regs = [0] * 16
            regs[4] = 0x8800
            xmm = [0x0123456789abcdef] * 32
            # Repeat lanes to avoid unrelated exceptions in packed operations.
            for reg, value in [(0, a), (1, b)]:
                lane = sum(value << shift for shift in range(0, 128, bits))
                xmm[reg * 2:reg * 2 + 2] = [lane & ((1 << 64) - 1), lane >> 64]
            data += struct.pack('<16s16QQII2Q32QII', bytes([len(code)]) + code + b'\xcc' * (15-len(code)),
                                *regs, 2, 1, 1, 0x67, 0x67, *xmm, mxcsr, 0)
            meta.append(dict(index=len(meta), family='hardware_' + name, code=code.hex(), mask=0xdd5))
    prefix.with_suffix('.bin').write_bytes(data)
    prefix.with_suffix('.json').write_text(json.dumps(meta))


def prepare(args):
    out = args.directory.resolve()
    out.mkdir(parents=True, exist_ok=False)
    manifest = dict(seed=args.seed, requested_count=args.count, architectures={}, sha256={})
    shutil.copyfile(__file__, out / 'hardware.py')
    for arch in args.arch:
        root = model_root(arch)
        exe = model_exe(arch)
        checked(['lake', 'build', exe], cwd=root)
        dest = out / arch
        dest.mkdir()
        if arch == 'sys':
            checked(['sh', ROOT / 'test/sys/build.sh'], env=dict(os.environ, OUT=str(dest / 'obj')))
            shutil.copyfile(dest / 'obj/systest.elf', dest / 'systest.elf')
            shutil.rmtree(dest / 'obj')
            manifest['architectures'][arch] = dict(passes=SYS_PASSES, model_sha256=digest(root / '.lake/build/bin' / exe))
            for source in model_sources(arch) + sorted((ROOT / 'test/sys').glob('*.[chS]')):
                manifest.setdefault('model_sources', {})[str(source.relative_to(REPO))] = digest(source)
            continue
        checked([sys.executable, root / 'test/gen.py', args.count, args.seed, dest / 'vectors'])
        if arch == 'x86_64':
            directed_sse(dest / 'vectors')
        size = 88 if arch == 'i386' else 440
        count = (dest / 'vectors.bin').stat().st_size // size
        manifest['architectures'][arch] = dict(count=count, model_sha256=digest(root / '.lake/build/bin' / exe))
        for name in ['boot.S', 'harness.c', 'link.ld' if arch == 'i386' else 'link.py']:
            shutil.copyfile(root / 'test/harness' / name, dest / name)
        # Keep the exact semantics source identity with the evidence.
        for source in model_sources(arch):
            manifest.setdefault('model_sources', {})[str(source.relative_to(REPO))] = digest(source)
    for path in sorted(out.rglob('*')):
        if path.is_file():
            manifest['sha256'][str(path.relative_to(out))] = digest(path)
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    archive = out.with_name(out.name + '.tar.gz')
    with tarfile.open(archive, 'x:gz') as tar:
        tar.add(out, arcname=out.name)
    print(f'Prepared {archive}; hardware has NOT been executed.')


def verify_inputs(directory, manifest):
    for name, expected in manifest['sha256'].items():
        if digest(directory / name) != expected:
            raise ValueError(f'input changed: {name}')


def run(args):
    directory = args.directory.resolve()
    manifest = json.loads((directory / 'manifest.json').read_text())
    verify_inputs(directory, manifest)
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        raise RuntimeError('hardware execution requires an x86-64 Linux host')
    # Opening the actual device is stronger than checking a filename or mode bits.
    fd = os.open('/dev/kvm', os.O_RDWR)
    os.close(fd)
    host = dict(uname=list(platform.uname()), cpuinfo=Path('/proc/cpuinfo').read_text(),
                lscpu=checked(['lscpu'], capture_output=True, text=True).stdout,
                qemu=checked(['qemu-system-x86_64', '--version'], capture_output=True, text=True).stdout,
                accelerator='kvm', cpu='host', results={})
    result_file = directory / 'hardware.json'
    if result_file.exists():
        raise FileExistsError('hardware.json already exists; use a fresh bundle for another run')
    result_file.write_text(json.dumps(host, indent=2) + '\n')
    for arch in manifest['architectures']:
        dest = directory / arch
        if arch == 'sys':
            host['results'][arch] = run_sys(dest, manifest['architectures'][arch]['passes'], args.timeout)
            result_file.write_text(json.dumps(host, indent=2) + '\n')
            continue
        with (dest / 'build.log').open('w') as log:
            flags = ['gcc', '-m32' if arch == 'i386' else '-m64', '-ffreestanding', '-fno-builtin',
                     '-fno-pic', '-fno-pie', '-fno-stack-protector', '-fno-asynchronous-unwind-tables', '-O2']
            if arch == 'x86_64':
                flags += ['-mno-red-zone', '-mno-sse', '-mno-mmx', '-msoft-float']
            for source in ['boot.S', 'harness.c']:
                checked(flags + ['-c', source, '-o', Path(source).stem + '.o'], cwd=dest, stdout=log, stderr=subprocess.STDOUT)
            link = (['ld', '-m', 'elf_i386', '-T', 'link.ld', '-o', 'harness.elf', 'boot.o', 'harness.o']
                    if arch == 'i386' else [sys.executable, 'link.py', 'harness.elf', 'boot.o', 'harness.o'])
            checked(link, cwd=dest, stdout=log, stderr=subprocess.STDOUT)
        command = ['qemu-system-x86_64', '-accel', 'kvm', '-cpu', 'host', '-smp', '1', '-m', '64',
                   '-kernel', 'harness.elf', '-initrd', 'vectors.bin', '-display', 'none',
                   '-serial', 'file:hardware.out', '-monitor', 'none', '-nic', 'none',
                   '-device', 'isa-debug-exit,iobase=0xf4,iosize=4', '-no-reboot']
        with (dest / 'qemu.log').open('w') as log:
            result = subprocess.run(command, cwd=dest, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        host['results'][arch] = dict(command=command, returncode=result.returncode,
                                    harness_sha256=digest(dest / 'harness.elf'))
        result_file.write_text(json.dumps(host, indent=2) + '\n')
        if result.returncode != 1:
            raise RuntimeError(f'{arch}: expected debug-exit status 1, got {result.returncode}; inspect qemu.log')
        validate_output(dest / 'hardware.out', manifest['architectures'][arch]['count'], arch)
        host['results'][arch]['output_sha256'] = digest(dest / 'hardware.out')
        result_file.write_text(json.dumps(host, indent=2) + '\n')
    print('Hardware execution complete. Copy the directory back and run compare.')


def run_sys(dest, passes, timeout):
    """The system-test kernel under KVM, one QEMU run per pass (whole transcript, no qemu=1)."""
    results = {}
    for name, cmdline, cpus in passes:
        command = ['qemu-system-x86_64', '-accel', 'kvm', '-cpu', 'host', '-smp', f'{cpus},sockets={cpus}', '-m', '64',
                   '-kernel', 'systest.elf', '-append', cmdline, '-display', 'none', '-serial', f'file:{name}.out',
                   '-monitor', 'none', '-nic', 'none', '-device', 'isa-debug-exit,iobase=0xf4,iosize=4', '-no-reboot']
        try:
            with (dest / f'{name}.qemu.log').open('w') as log:
                rc = subprocess.run(command, cwd=dest, stdout=log, stderr=subprocess.STDOUT, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            rc = 'timeout'
        out = dest / f'{name}.out'
        complete = out.exists() and 'END' in out.read_text(errors='replace').replace('\r', '').splitlines()
        results[name] = dict(command=command, returncode=rc, complete=complete,
                             output_sha256=digest(out) if out.exists() else None)
        print(f'sys {name}: exit {rc}, transcript {"complete" if complete else "INCOMPLETE"}', flush=True)
    return results


def compare_sys(dest, spec, result, timeout):
    """x86sys on the same kernel and command lines; every differing line is written out for review."""
    import difflib
    exe = ROOT / '.lake/build/bin/x86sys'
    if digest(exe) != spec['model_sha256']:
        raise ValueError('sys: model executable changed since preparation')
    differ = 0
    for name, cmdline, cpus in spec['passes']:
        r = result[name]
        hw_path = dest / f'{name}.out'
        if r['output_sha256'] is None or digest(hw_path) != r['output_sha256']:
            raise ValueError(f'sys {name}: missing or changed hardware transcript')
        model = subprocess.run([str(exe), '--smp', str(cpus), '--cmdline', cmdline, str(dest / 'systest.elf')],
                               capture_output=True, text=True, timeout=timeout).stdout.splitlines()
        hw = hw_path.read_text(errors='replace').replace('\r', '').splitlines()
        (dest / f'{name}.model').write_text('\n'.join(model) + '\n')
        diff = list(difflib.unified_diff(hw, model, f'{name}.out (KVM)', f'{name}.model (x86sys)', lineterm='', n=0))
        (dest / f'{name}.diff').write_text('\n'.join(diff) + '\n')
        split = model.index('MODEL-ONLY') if 'MODEL-ONLY' in model else len(model)
        changed = sum(1 for d in diff if d.startswith('+') and not d.startswith('+++'))
        differ += changed + (0 if r['complete'] else 1)
        print(f'sys {name}: {len(hw)} KVM lines, {len(model)} model lines ({split} before MODEL-ONLY); '
              f'{changed} model lines differ{"" if r["complete"] else "; KVM transcript INCOMPLETE"}; see sys/{name}.diff')
    return differ == 0


def validate_output(path, count, arch, extra_columns=0):
    lines = path.read_text().splitlines()
    if len(lines) != count + 2 or lines[-1] != 'END' or lines[0].split() != ['BEGIN', f'{count:0{8 if arch == "i386" else 16}x}']:
        raise ValueError(f'{path}: incomplete output or wrong record count')
    width, columns = (8, 22) if arch == 'i386' else (16, 58)
    columns += extra_columns
    for index, line in enumerate(lines[1:-1]):
        fields = line.split()
        if len(fields) != columns or any(not re.fullmatch(f'[0-9a-f]{{{width}}}', x) for x in fields):
            raise ValueError(f'{path}: malformed record {index}')
        if int(fields[0], 16) != index:
            raise ValueError(f'{path}: missing, duplicate, or reordered record {index}')


def compare(args):
    directory = args.directory.resolve()
    manifest = json.loads((directory / 'manifest.json').read_text())
    verify_inputs(directory, manifest)
    if not (directory / 'hardware.json').exists() and (directory / 'run-error.txt').exists():
        raise RuntimeError('hardware execution failed: ' + (directory / 'run-error.txt').read_text().strip())
    hardware = json.loads((directory / 'hardware.json').read_text())
    if hardware['accelerator'] != 'kvm' or hardware['cpu'] != 'host':
        raise ValueError('reference was not recorded with KVM and host CPU')
    failed = False
    for arch, spec in manifest['architectures'].items():
        dest = directory / arch
        result = hardware['results'][arch]
        if arch == 'sys':
            failed |= not compare_sys(dest, spec, result, args.timeout)
            continue
        if result['returncode'] != 1 or digest(dest / 'hardware.out') != result['output_sha256']:
            raise ValueError(f'{arch}: failed run or changed hardware output')
        validate_output(dest / 'hardware.out', spec['count'], arch)
        root = model_root(arch)
        exe = root / '.lake/build/bin' / ('x86test' if arch == 'i386' else 'x64test')
        if digest(exe) != spec['model_sha256']:
            raise ValueError(f'{arch}: model executable changed since preparation')
        command = [str(exe), str(dest / 'vectors.bin')]
        if arch == 'i386':
            command += [str(dest / 'vectors.meta'), str(dest / 'hardware.out')]
        with (dest / 'model.out').open('w') as log:
            model = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        if arch == 'i386':
            summary = (dest / 'model.out').read_text().splitlines()[-1:]
            passed = model.returncode == 0 and summary == [f'{spec["count"]} vectors compared, 0 mismatches']
            print(arch, *summary)
        else:
            if model.returncode != 0:
                raise RuntimeError('x86_64 model failed; inspect model.out')
            status = subprocess.run([sys.executable, str(root / 'test/compare.py'), str(dest / 'vectors.json'),
                                     str(dest / 'hardware.out'), str(dest / 'model.out')], capture_output=True, text=True)
            (dest / 'comparison.txt').write_text(status.stdout + status.stderr)
            print(arch, status.stdout, status.stderr, end='')
            passed = status.returncode == 0
        failed |= not passed
    return int(failed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ['prepare', 'run', 'compare']:
        p = sub.add_parser(name)
        p.add_argument('directory', type=Path)
        if name == 'prepare':
            p.add_argument('--arch', choices=['i386', 'x86_64', 'sys'], nargs='+', default=['i386', 'x86_64', 'sys'])
            p.add_argument('--count', type=int, default=10000)
            p.add_argument('--seed', type=int, default=20261021)
        else:
            p.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    if args.action == 'prepare' and not 1 <= args.count <= 20000:
        parser.error('count must be between 1 and 20000; use separate seeds for larger runs')
    try:
        return globals()[args.action](args) or 0
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        if args.action == 'run' and args.directory.is_dir():
            try:
                (args.directory / 'run-error.txt').write_text(f'{type(exc).__name__}: {exc}\n')
            except OSError:
                pass  # Still report the original failure if the bundle is read-only.
        print(f'ERROR: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
