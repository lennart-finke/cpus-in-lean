#!/usr/bin/env python3
"""Native CPU testing of register-only IA-32 and x86-64 instructions.

No KVM or sudo. By default, ordinary in-process signal handlers capture state;
the optional ptrace backend requires permission to trace our own child. The oracle is a
freestanding Linux ELF64 executable built locally, so the server needs Python 3
but no compiler or libraries. Signal contexts provide raw exception vectors and
error codes; the optional ptrace backend compares Linux signal categories only.
Memory, page-table state and segment selectors are not compared.
"""
import argparse
import collections
import importlib.util
import json
import platform
import struct
import subprocess
import sys
import tarfile
from pathlib import Path

from hardware import REPO, ROOT, MODEL, model_root, model_sources, checked, digest, directed_sse, validate_output, verify_inputs


def register_only(code, arch, family=''):
    """Conservative independent whitelist: no memory access, syscalls or segment changes."""
    pos = 0
    while pos < len(code) and (code[pos] in (0x26,0x2e,0x36,0x3e,0x64,0x65,0x66,0x67,0xf0,0xf2,0xf3)
                              or arch == 'x86_64' and 0x40 <= code[pos] <= 0x4f):
        pos += 1
    if pos == len(code):
        return False
    op = code[pos]; pos += 1
    def reg():
        return pos < len(code) and code[pos] >> 6 == 3
    if op == 0x0f:
        if pos == len(code):
            return False
        op = code[pos]; pos += 1
        if op == 0x0b or 0x80 <= op <= 0x8f or 0xc8 <= op <= 0xcf:
            return True
        if arch == 'x86_64' and (family.startswith('simd_') or family.startswith('hardware_')):
            return reg()
        # Leave zero-source BSF/BSR and double shifts with undefined results out.
        return reg() and (0x40 <= op <= 0x4f or 0x90 <= op <= 0x9f or
                          op in (0xa3,0xab,0xb3,0xbb,0xaf,0xb0,0xb1,0xb6,0xb7,0xbe,0xbf,0xba,0xc0,0xc1))
    if op < 0x40 and (op & 7) <= 5:
        return (op & 7) >= 4 or reg()
    if arch == 'i386' and (op in (0x27,0x2f,0x37,0x3f,0xd4,0xd5,0xd6) or 0x40 <= op <= 0x4f):
        return True
    if 0x70 <= op <= 0x7f or 0x90 <= op <= 0x99 or 0xb0 <= op <= 0xbf:
        return True
    if op in (0x9e,0x9f,0xa8,0xa9,0xe0,0xe1,0xe2,0xe3,0xe9,0xeb,0xf5,0xf8,0xf9,0xfc,0xfd):
        return True
    if op == 0x8d:  # LEA computes an address without accessing it.
        return pos < len(code) and code[pos] >> 6 != 3
    if op in (0x63,0x69,0x6b,0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x8b,
              0xc0,0xc1,0xd0,0xd1,0xd2,0xd3,0xf6,0xf7):
        return reg()
    if op in (0xfe,0xff):
        return reg() and (code[pos] >> 3) & 7 <= 1
    if op in (0xc6,0xc7):
        return reg() and (code[pos] >> 3) & 7 == 0
    return False


def decimal_vectors():
    """Boundary cases including high AAM/AAD bases excluded by the TCG generator."""
    for op in (0x27,0x2f,0x37,0x3f):
        for al in range(256):
            for flags in (2,3,0x12,0x13):
                regs = [0xff00 | al, 0, 0, 0, 0x8800, 0, 0, 0]
                mask = 0xdd5 & (~0x800 if op in (0x27,0x2f) else ~0x8c4)
                yield bytes([op]), regs, flags, mask
    for op in (0xd4,0xd5):
        for base in range(256):
            for ax in (0,0x7f,0x80,0xff,0x100,0xff00,0xffff):
                regs = [ax, 0, 0, 0, 0x8800, 0, 0, 0]
                yield bytes([op,base]), regs, 2, 0xdd5 & ~0x811


def prepare(args):
    if getattr(args,'hunt',False):
        from native_hunt import prepare_hunt
        return prepare_hunt(args)
    if getattr(args,'memory',False):
        from native_memory import prepare_memory
        return prepare_memory(args)
    seeds = args.seeds or [args.seed]
    out = args.directory.resolve();out.mkdir(parents=True, exist_ok=False)
    builder_spec = importlib.util.spec_from_file_location('native_build', ROOT / 'test/native/build.py')
    builder = importlib.util.module_from_spec(builder_spec);builder_spec.loader.exec_module(builder)
    builder.build(ROOT / 'test/native', out / 'oracle', MODEL['x86_64'] / 'test/harness/link.py', args.backend)
    for name, path in [('native.py', Path(__file__)), ('hardware.py', ROOT / 'test/hardware.py'),
                       ('oracle.c', ROOT / 'test/native/oracle.c'), ('start.S', ROOT / 'test/native/start.S'),
                       ('signal_oracle.c', ROOT / 'test/native/signal_oracle.c'), ('signal_enter.S', ROOT / 'test/native/signal_enter.S')]:
        (out / name).write_bytes(path.read_bytes())
    if args.focused_sse:
        from native_cases import focused_sse, saved_nan_case
        (out / 'native_cases.py').write_bytes((ROOT / 'test/native_cases.py').read_bytes())
        (out / 'fixtures').mkdir()
        (out / 'fixtures/native_nan_payload.json').write_bytes((ROOT / 'test/fixtures/native_nan_payload.json').read_bytes())
    manifest = dict(kind='native-'+args.backend, seed=seeds[0], seeds=seeds,
                    candidate_count=args.count, focused_sse=args.focused_sse, architectures={}, sha256={})
    for arch in ('i386','x86_64'):
        root = model_root(arch)
        exe = root / '.lake/build/bin' / ('x86test' if arch == 'i386' else 'x64test')
        checked(['lake','build',exe.name], cwd=root)
        dest = out / arch;dest.mkdir()
        size = 88 if arch == 'i386' else 440
        selected = bytearray();native = bytearray();meta = []
        def append(record, info):
            if len(meta)>=1000000:
                raise ValueError(f'{arch}: suite exceeds the oracle limit of 1000000 vectors')
            record = bytearray(record)
            # Match Linux's user execution environment: only arithmetic/TF/DF
            # flags are randomized and compared. IF is fixed, AC is disabled.
            offset, fmt = (48,'<I') if arch == 'i386' else (144,'<Q')
            flags = (struct.unpack_from(fmt,record,offset)[0] & 0xdd5) | 0x202
            struct.pack_into(fmt,record,offset,flags)
            selected.extend(record)
            if arch == 'i386':
                regs = list(struct.unpack_from('<8I',record,16)) + [0]*8
                native.extend(struct.pack('<16s16QQII2Q32QII',record[:16],*regs,flags,1,0,0x67,0x67,*([0]*32),0x1f80,0))
            else:
                native.extend(record)
            meta.append(dict(info,index=len(meta)))
        random_by_seed = {}
        for seed in seeds:
            prefix = dest / (f'candidates-{seed}' if len(seeds)>1 else 'candidates')
            checked([sys.executable,root / 'test/gen.py',args.count,seed,prefix])
            raw = prefix.with_suffix('.bin').read_bytes()
            original = ([dict(mask=int(line.split()[0],16),code=line.split()[1],family='random')
                         for line in prefix.with_suffix('.meta').read_text().splitlines()] if arch == 'i386'
                        else json.loads(prefix.with_suffix('.json').read_text()))
            before = len(meta)
            for index, info in enumerate(original):
                if register_only(bytes.fromhex(info['code']),arch,info['family']):
                    append(raw[index*size:(index+1)*size],dict(info,source_index=index,source_seed=seed))
            random_by_seed[str(seed)] = len(meta)-before
        if arch == 'x86_64':
            if args.focused_sse:
                for record, info in focused_sse():
                    if not register_only(bytes.fromhex(info['code']),arch,info['family']):
                        raise ValueError(f'focused case outside native scope: {info}')
                    append(record,info)
                record, info = saved_nan_case()
                append(record,info)
            # Retain the original 112 probes at the end for the Linux smoke test.
            prefix = dest / 'directed'
            prefix.with_suffix('.bin').write_bytes(b'')
            prefix.with_suffix('.json').write_text('[]')
            directed_sse(prefix)
            raw = prefix.with_suffix('.bin').read_bytes()
            for index, info in enumerate(json.loads(prefix.with_suffix('.json').read_text())):
                append(raw[index*size:(index+1)*size], info)
        if arch == 'i386':
            for code, regs, flags, mask in decimal_vectors():
                record = struct.pack('<B15s8III4H2H2I3I',len(code),code.ljust(15,b'\0'),*regs,flags,1,
                                     *([0x23]*4),0xffff,0xffff,0,0,0,0x67,0x67)
                append(record,dict(code=code.hex(),mask=mask,family='hardware_decimal'))
        (dest / 'vectors.bin').write_bytes(selected)
        (dest / 'vectors.json').write_text(json.dumps(meta))
        (dest / 'native.bin').write_bytes(struct.pack('<Q',len(meta)) + native)
        manifest['architectures'][arch] = dict(count=len(meta),model_sha256=digest(exe),
                                              random_by_seed=random_by_seed,
                                              generator_sha256=digest(root / 'test/gen.py'),
                                              families=dict(collections.Counter(m['family'] for m in meta)))
        # Save model output before leaving the local machine; this is never sent
        # to the native runner and cannot influence CPU observations.
        command = [exe,'--dump',dest / 'vectors.bin'] if arch == 'i386' else [exe,dest / 'vectors.bin']
        with (dest / 'model.out').open('w') as log:
            checked(command,stdout=log,timeout=300)
        validate_output(dest / 'model.out',len(meta),arch)
        print(arch, len(meta), 'selected vectors', flush=True)
    for path in out.rglob('*'):
        if path.is_file() and path.name != 'model.out':
            manifest['sha256'][str(path.relative_to(out))] = digest(path)
    for arch in manifest['architectures']:
        manifest['architectures'][arch]['model_output_sha256'] = digest(out / arch / 'model.out')
    (out / 'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    with tarfile.open(out.with_name(out.name+'.tar.gz'),'x:gz') as tar:
        tar.add(out,arcname=out.name,filter=lambda info: None if Path(info.name).name=='model.out' else info)
    print('Prepared',out.with_name(out.name+'.tar.gz'),'; native hardware has NOT run.')


def run(args):
    directory=args.directory.resolve()
    manifest=json.loads((directory/'manifest.json').read_text());verify_inputs(directory,manifest)
    if platform.system()!='Linux' or platform.machine()!='x86_64':
        raise RuntimeError('native execution requires Linux on x86-64')
    result=directory/'native.json'
    if result.exists():
        raise FileExistsError('native.json already exists; use a fresh bundle for another run')
    host=dict(kind=manifest['kind'],uname=list(platform.uname()),cpuinfo=Path('/proc/cpuinfo').read_text(),results={})
    result.write_text(json.dumps(host,indent=2)+'\n')
    for arch,spec in manifest['architectures'].items():
        dest=directory/arch
        with (dest/'native.bin').open('rb') as inp,(dest/'native.out').open('w') as out,(dest/'native.log').open('w') as err:
            proc=subprocess.run([str(directory/'oracle'),arch],stdin=inp,stdout=out,stderr=err,timeout=args.timeout)
        host['results'][arch]=dict(returncode=proc.returncode,output_sha256=digest(dest/'native.out'))
        result.write_text(json.dumps(host,indent=2)+'\n')
        if proc.returncode:
            raise RuntimeError(f'{arch}: native oracle exited {proc.returncode}: '+(dest/'native.log').read_text())
        read_native(dest/'native.out',spec['count'],native_columns(manifest['kind']))
        print(arch,spec['count'],'native vectors complete',flush=True)


def native_columns(kind):
    return {'native-ptrace':55,'native-signals':58,'native-memory':61}[kind]


def read_native(path,count,columns=55):
    lines=path.read_text().splitlines()
    if len(lines)!=count+2 or lines[0].split()!=['BEGIN',f'{count:016x}'] or lines[-1]!='END':
        raise ValueError(f'{path}: incomplete native output')
    out=[]
    for index,line in enumerate(lines[1:-1]):
        fields=line.split()
        if len(fields)!=columns or any(len(x)!=16 or any(c not in '0123456789abcdef' for c in x) for x in fields):
            raise ValueError(f'{path}: malformed native row {index}')
        row=[int(x,16) for x in fields]
        if row[0]!=index:
            raise ValueError(f'{path}: duplicate/missing/out-of-order row {index}')
        out.append(row)
    return out


def differences(arch,meta,hardware,model):
    result=[];vector=model[1]
    signal_codes={0:(8,{1}),1:(5,{2}),3:(5,{1,128}),6:(4,{1,2}),19:(8,{3,4,5,6,7,8})}
    memory=len(hardware)==61
    if memory:
        signal_codes.update({12:(11,{128}),13:(11,{128}),14:(11,{1,2})})
    if vector not in signal_codes:
        return [f'unexpected model exception {vector}; manual investigation required']
    sig,codes=signal_codes[vector]
    if hardware[1]!=sig or hardware[2] not in codes:
        result.append(f'outcome: native signal/code={hardware[1]}/{hardware[2]}, model vector={vector}')
    if len(hardware)>=58:
        if hardware[55]!=vector or hardware[56]!=model[2]:
            result.append(f'exception: native vector/error={hardware[55]}/{hardware[56]}, model={vector}/{model[2]}')
    expected_cs=0x23 if arch=='i386' else 0x33
    if hardware[4]!=expected_cs:
        result.append(f'CPU mode: CS={hardware[4]:x}, expected={expected_cs:x}')
    # Linux reports RIP after the INT3 terminator, model reports target before it.
    ip=hardware[3]-(hardware[1]==5 and hardware[2] in (1,128))
    if ip!=model[3]:
        result.append(f'IP: native={ip:x}, model={model[3]:x}')
    count=8 if arch=='i386' else 16;mask=(1<<32)-1 if arch=='i386' else (1<<64)-1
    for k in range(count):
        if hardware[6+k]&mask!=model[4+k]:
            result.append(f'r{k}: native={hardware[6+k]&mask:x}, model={model[4+k]:x}')
    flagmask=(meta['mask'] if vector in (1,3) else 0xdd5)&0xdd5
    flags=model[12 if arch=='i386' else 20]
    if hardware[5]&flagmask!=flags&flagmask:
        result.append(f'flags (mask={flagmask:x}): native={hardware[5]&flagmask:x}, model={flags&flagmask:x}')
    if arch=='x86_64':
        for k in range(32):
            if hardware[22+k]!=model[25+k]:
                result.append(f'xmm{k//2}.{"hi" if k%2 else "lo"}: native={hardware[22+k]:x}, model={model[25+k]:x}')
        if hardware[54]!=model[57]:
            result.append(f'MXCSR: native={hardware[54]:x}, model={model[57]:x}')
    if memory:
        if vector==14 and hardware[57]!=model[19 if arch=='i386' else 21]:
            result.append(f'CR2: native={hardware[57]:x}, model={model[19 if arch=="i386" else 21]:x}')
        expected=[model[18 if arch=='i386' else 22]]
        expected += ([model[22]|(model[23]<<32),model[24]|(model[25]<<32)] if arch=='i386' else model[58:60])
        for label,actual,wanted in zip(('memory FNV32','page0 FNV64','page1 FNV64'),hardware[58:61],expected):
            if actual!=wanted:
                result.append(f'{label}: native={actual:x}, model={wanted:x}')
    return result


def compare(args):
    directory=args.directory.resolve();local=args.prepared.resolve()
    manifest=json.loads((directory/'manifest.json').read_text());verify_inputs(directory,manifest)
    if digest(directory/'manifest.json')!=digest(local/'manifest.json'):
        raise ValueError('returned manifest differs from prepared manifest')
    host=json.loads((directory/'native.json').read_text())
    if host['kind'] not in ('native-ptrace','native-signals','native-memory') or host['kind']!=manifest['kind']:
        raise ValueError('wrong oracle kind')
    replay=getattr(args,'replay_to',None)
    report=replay.resolve() if replay else directory
    if replay:
        report.mkdir(parents=True,exist_ok=False)
    summary=dict(kind=host['kind'],architectures={});failed=False
    if replay:
        summary.update(mode='model-replay',native_directory=str(directory),prepared_directory=str(local),
                       manifest_sha256=digest(directory/'manifest.json'),
                       native_run_sha256=digest(directory/'native.json'),comparator_sha256=digest(Path(__file__)))
    for arch,spec in manifest['architectures'].items():
        memory=host['kind']=='native-memory'
        extra=(4 if arch=='i386' else 2) if memory else 0
        dest=directory/arch;res=host['results'][arch]
        if res['returncode']!=0 or res['output_sha256']!=digest(dest/'native.out'):
            raise ValueError(f'{arch}: failed run or changed native output')
        modelpath=local/arch/'model.out'
        if digest(modelpath)!=spec['model_output_sha256']:
            raise ValueError(f'{arch}: model output changed')
        validate_output(modelpath,spec['count'],arch,extra)
        provenance={}
        reportdest=report/arch
        if replay:
            reportdest.mkdir()
            root=model_root(arch)
            name='x86test' if arch=='i386' else 'x64test'
            checked(['lake','build',name],cwd=root)
            exe=root/'.lake/build/bin'/name
            modelpath=reportdest/'model.out'
            command=[exe,'--dump',dest/'vectors.bin'] if arch=='i386' else [exe,dest/'vectors.bin']
            if memory:
                command=[exe,'--native-memory',dest/'vectors.bin']
            with modelpath.open('w') as log:
                checked(command,stdout=log,timeout=300)
            validate_output(modelpath,spec['count'],arch,extra)
            provenance=dict(model_sha256=digest(exe),model_output_sha256=digest(modelpath),
                            original_model_output_sha256=spec['model_output_sha256'],
                            native_output_sha256=res['output_sha256'],
                            source_sha256={str(p.relative_to(REPO)):digest(p) for p in model_sources(arch)})
        model=[[int(x,16) for x in l.split()] for l in modelpath.read_text().splitlines()[1:-1]]
        native=read_native(dest/'native.out',spec['count'],native_columns(host['kind']))
        metadata=json.loads((dest/'vectors.json').read_text())
        mismatches=[]
        for meta,h,m in zip(metadata,native,model):
            diff=differences(arch,meta,h,m)
            if diff:
                mismatches.append(dict(meta,differences=diff))
        (reportdest/'mismatches.json').write_text(json.dumps(mismatches,indent=2)+'\n')
        summary['architectures'][arch]=dict(count=spec['count'],mismatches=len(mismatches),**provenance)
        print(arch,spec['count'],'vectors,',len(mismatches),'mismatches')
        for mismatch in mismatches[:10]:
            print(' ',mismatch['index'],mismatch['code'],'; '.join(mismatch['differences']))
        failed |= bool(mismatches)
    (report/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n')
    return int(failed)


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    for name in ('prepare','run','compare'):
        s=sub.add_parser(name);s.add_argument('directory',type=Path)
        if name=='prepare':
            s.add_argument('--count',type=int,default=20000,help='candidate count per architecture per seed')
            seeds=s.add_mutually_exclusive_group()
            seeds.add_argument('--seed',type=int,default=20261021)
            seeds.add_argument('--seeds',type=int,nargs='+',help='independent candidate-generation seeds')
            s.add_argument('--focused-sse',action='store_true',help='include full MXCSR matrix, boundaries and saved NaN case')
            s.add_argument('--memory',action='store_true',help='prepare isolated native memory/fault cases')
            s.add_argument('--hunt',action='store_true',help='prepare twelve targeted bug-hunting campaigns')
            s.add_argument('--backend',choices=('signals','ptrace'),default='signals')
        elif name=='run':
            s.add_argument('--timeout',type=int,default=300)
        else:
            s.add_argument('--prepared',type=Path,required=True)
            s.add_argument('--replay-to',type=Path,
                           help='build current models and compare saved hardware in a new report directory')
    args=p.parse_args()
    if args.action=='prepare' and not 1<=args.count<=1000000:
        p.error('count must be between 1 and 1000000')
    if args.action=='prepare' and args.seeds and len(set(args.seeds))!=len(args.seeds):
        p.error('seeds must be distinct')
    if args.action=='prepare' and args.memory and (args.focused_sse or args.backend!='signals'):
        p.error('--memory requires the signal backend and cannot combine with --focused-sse')
    try:
        return globals()[args.action](args) or 0
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError) as exc:
        if args.action=='run' and args.directory.is_dir():
            (args.directory/'run-error.txt').write_text(f'{type(exc).__name__}: {exc}\n')
        print(f'ERROR: {exc}',file=sys.stderr);return 1


if __name__=='__main__':
    sys.exit(main())
