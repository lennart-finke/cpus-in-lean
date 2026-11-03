"""Prepare bounded memory instructions for the Linux signal hardware oracle.

Virtual 0x10000..0x11fff maps to the models' existing physical data pages.
Permissions are RW, R, or genuinely unmapped; no host page-table assumptions.
"""
import collections
import importlib.util
import itertools
import json
import random
import struct
import sys
import tarfile
from pathlib import Path
from hardware import REPO, ROOT, MODEL, model_root, model_sources, checked, digest, validate_output

BASE = 0x10000
IP = 0x20100
PERMS = {'rw':0x67, 'r':0x65, 'none':0}
OFFSETS = (0,1,15,0xff8,0xffc,0xfff,0x1000,0x1001,0x1ff0)


def address_forms(arch):
    common = ['base','disp8','disp32','sib','absolute','stack_base']
    return common + (['addr32','rip','high_sib'] if arch=='x86_64' else [])


def encode(arch, opcode, width, form, address, regs, reg=0, mandatory=b''):
    prefix = mandatory or (b'\x66' if width==2 else b'')
    rex = 8 if width==8 and arch=='x86_64' else 0
    displacement = b''; sib = b''
    if form=='base':
        regs[3]=address;modrm=3
    elif form=='stack_base':
        regs[5]=address;modrm=0x45;displacement=b'\0'
    elif form=='disp8':
        regs[3]=address+16;modrm=0x43;displacement=b'\xf0'
    elif form=='disp32':
        regs[3]=address+0x1234;modrm=0x83;displacement=struct.pack('<i',-0x1234)
    elif form=='sib':
        regs[3]=address-28;regs[6]=7;modrm=4;sib=b'\xb3'
    elif form=='absolute':
        modrm=4 if arch=='x86_64' else 5
        sib=b'\x25' if arch=='x86_64' else b''
        displacement=struct.pack('<I',address)
    elif form=='addr32':
        prefix+=b'\x67';regs[3]=0x1234567800000000|address;modrm=3
    elif form=='high_sib':
        regs[12]=address-28;regs[9]=7;modrm=4;sib=b'\x8c';rex|=3
    elif form=='rip':
        modrm=5
        displacement=struct.pack('<i',address-(IP+len(prefix)+bool(rex)+len(opcode)+5))
    else:
        raise ValueError(form)
    return prefix+(bytes([0x40|rex]) if rex else b'')+opcode+bytes([modrm|(reg<<3)])+sib+displacement


def verify_case(arch, code, regs, flags, meta):
    """Decode the bounded addressing subset independently of the encoder/model."""
    pos=0;p66=False;addr32=arch=='i386';rep=False;rex=0
    while pos<len(code):
        b=code[pos]
        if b==0x66:p66=True
        elif b==0x67:addr32=True
        elif b==0xf3:rep=True
        elif arch=='x86_64' and 0x40<=b<=0x4f:rex=b&15
        else:break
        pos+=1
    op=code[pos];pos+=1
    if op==15:op=0x100+code[pos];pos+=1
    width=8 if rex&8 else 2 if p66 else 4
    if op in (0xa4,0xa5,0xaa,0xab,0xac,0xad):
        width=width if op&1 else 1
        count=regs[1] if rep else 1
        assert count<=16 and pos==len(code)
        accesses=[]
        if op in (0xa4,0xa5,0xac,0xad):accesses.append(regs[6])
        if op in (0xa4,0xa5,0xaa,0xab):accesses.append(regs[7])
        for address in accesses:
            last=address+(-1 if flags&0x400 else 1)*width*max(0,count-1)
            assert BASE<=min(address,last) and max(address,last)+width<=BASE+8192
        return
    if op in (0x50,0x58):
        width=2 if p66 else 4 if arch=='i386' else 8
        address=regs[4]-(width if op==0x50 else 0)
        assert pos==len(code)
    else:
        assert op in (0x88,0x89,0x8a,0x8b,0,1,0xf6,0xf7,0x1b0,0x1b1,0x1c0,0x1c1,
                      0x110,0x111,0x128,0x129,0x16f,0x17f)
        if op in (0x88,0x8a,0,0xf6,0x1b0,0x1c0):width=1
        if op in (0x110,0x111,0x128,0x129,0x16f,0x17f):width=16
        md=code[pos];pos+=1;mod=md>>6;rm=md&7
        assert mod!=3
        if op in (0xf6,0xf7):assert (md>>3)&7==3
        base=None;index=0;rip=False
        if rm==4:
            sib=code[pos];pos+=1
            idx=((sib>>3)&7)+(8 if rex&2 else 0)
            if idx!=4:index=regs[idx]*(1<<(sib>>6))
            base=(sib&7)+(8 if rex&1 else 0)
            if mod==0 and sib&7==5:base=None
        elif mod==0 and rm==5:
            rip=not addr32
        else:base=rm+(8 if rex&1 else 0)
        disp_size=1 if mod==1 else 4 if mod==2 or (mod==0 and base is None) else 0
        disp=int.from_bytes(code[pos:pos+disp_size],'little',signed=True);pos+=disp_size
        assert pos==len(code)
        address=((regs[base] if base is not None else IP+len(code) if rip else 0)+index+disp)&((1<<(32 if addr32 else 64))-1)
    assert width==meta['width'] and address==meta['address'],(code.hex(),address,meta)
    assert BASE<=address and address+width<=BASE+8192


def vectors(arch, seeds, random_count):
    widths=(1,2,4) if arch=='i386' else (1,2,4,8)
    forms=address_forms(arch)
    operations=('load','store','add','neg','xadd','cmpxchg')
    rng=random.Random(0x4d454d)
    serial=0

    def emit(code,regs,width,address,permissions,family,form,flags=None,source_seed=None):
        nonlocal serial
        flags=(0x202|(rng.getrandbits(12)&0x8d5)|(0x100 if serial%3==0 else 0)) if flags is None else flags
        seed=rng.getrandbits(32) or 1
        meta=dict(index=serial,code=code.hex(),mask=0xdd5,family=family,form=form,
                  width=width,address=address,permissions=permissions,data_seed=seed)
        if source_seed is not None:meta['source_seed']=source_seed
        verify_case(arch,code,regs,flags,meta)
        if arch=='i386':regs=[v&0xffffffff for v in regs[:8]]+[0]*8
        xmm=[rng.getrandbits(64) for _ in range(32)] if arch=='x86_64' else [0]*32
        ptes=[PERMS[p] for p in permissions]
        native=struct.pack('<16s16QQII2Q32QII',bytes([len(code)])+code.ljust(15,b'\xcc'),
                           *regs,flags,seed,1,*ptes,*xmm,0x1f80,0)
        model=native if arch=='x86_64' else struct.pack('<B15s8III4H2H2I3I',len(code),code.ljust(15,b'\0'),
                  *regs[:8],flags,seed,*([0x23]*4),0xffff,0xffff,0,0,3,*ptes)
        serial+=1
        return model,native,meta

    def registers():
        r=[rng.getrandbits(64 if arch=='x86_64' else 32) for _ in range(16)]
        r[4]=BASE+0x800
        return r

    def scalar(op,width,form,offset,permissions,source_seed=None):
        regs=registers();address=BASE+offset
        opcode={'load':bytes([0x8a+(width!=1)]),'store':bytes([0x88+(width!=1)]),
                'add':bytes([int(width!=1)]),'neg':bytes([0xf6+(width!=1)]),
                'xadd':bytes([15,0xc0+(width!=1)]),'cmpxchg':bytes([15,0xb0+(width!=1)])}[op]
        code=encode(arch,opcode,width,form,address,regs,3 if op=='neg' else 1 if op=='cmpxchg' else 0)
        return emit(code,regs,width,address,permissions,'memory_'+op,form,source_seed=source_seed)

    for op,width,form,offset,permissions in itertools.product(operations,widths,forms,OFFSETS,itertools.product(PERMS,repeat=2)):
        yield scalar(op,width,form,offset,permissions)
    if arch=='x86_64':
        for name,opcode,mandatory in [('movups_load',0x10,b''),('movups_store',0x11,b''),
                                     ('movaps_load',0x28,b''),('movaps_store',0x29,b''),
                                     ('movdqu_load',0x6f,b'\xf3'),('movdqu_store',0x7f,b'\xf3')]:
            for form,offset,permissions in itertools.product(forms,OFFSETS,itertools.product(PERMS,repeat=2)):
                regs=registers();address=BASE+offset
                code=encode(arch,bytes([15,opcode]),16,form,address,regs,mandatory=mandatory)
                yield emit(code,regs,16,address,permissions,'memory_'+name,form)
    for width,push,offset,permissions in itertools.product((2,4 if arch=='i386' else 8),(False,True),OFFSETS,itertools.product(PERMS,repeat=2)):
        regs=registers();address=BASE+offset;regs[4]=address+(width if push else 0)
        code=(b'\x66' if width==2 else b'')+bytes([0x50 if push else 0x58])
        yield emit(code,regs,width,address,permissions,'memory_push' if push else 'memory_pop','stack')
    for op,width,backward,count,tf,protection in itertools.product(('movs','stos','lods'),widths,(False,True),(0,1,4,8),(False,True),PERMS):
        regs=registers();regs[1]=count
        # Only one operand can fault: the other MOVS operand stays in the RW page.
        permissions=(protection,'rw') if backward else ('rw',protection)
        target=BASE+0x1004 if backward else BASE+0x1000-2*width
        safe=BASE+0x1800 if backward else BASE+0x800
        regs[6]=target if op=='lods' else safe
        regs[7]=target
        flags=0x202|(0x400 if backward else 0)|(0x100 if tf else 0)
        code=b'\xf3'+(b'\x66' if width==2 else b'')+(b'\x48' if width==8 else b'')+bytes([{'movs':0xa4,'stos':0xaa,'lods':0xac}[op]+(width!=1)])
        yield emit(code,regs,width,target,permissions,'memory_rep_'+op,'string',flags)
    for seed in seeds:
        rng=random.Random(seed)
        for _ in range(random_count):
            op=rng.choice(operations);width=rng.choice(widths);form=rng.choice(forms)
            offset=rng.randrange(8192-width+1)
            permissions=(rng.choice(tuple(PERMS)),rng.choice(tuple(PERMS)))
            yield scalar(op,width,form,offset,permissions,seed)


def prepare_memory(args, case_source=vectors, campaign=None):
    out=args.directory.resolve();out.mkdir(parents=True,exist_ok=False)
    spec=importlib.util.spec_from_file_location('native_build',ROOT/'test/native/build.py')
    builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
    builder.build(ROOT/'test/native',out/'oracle',MODEL['x86_64']/'test/harness/link.py','memory')
    for name in ('native.py','native_memory.py','hardware.py'):
        (out/name).write_bytes((ROOT/'test'/name).read_bytes())
    if campaign is not None:
        (out/'native_hunt.py').write_bytes((ROOT/'test/native_hunt.py').read_bytes())
    for name in ('signal_oracle.c','start.S','signal_enter.S','build.py'):
        (out/name).write_bytes((ROOT/'test/native'/name).read_bytes())
    seeds=args.seeds or [args.seed]
    manifest=dict(kind='native-memory',seeds=seeds,random_count_per_seed=args.count,
                  arena=dict(virtual=BASE,physical=0x8000,size=8192),architectures={},sha256={})
    if campaign is not None:
        manifest['campaign']=campaign
    for arch in ('i386','x86_64'):
        root=model_root(arch);dest=out/arch;dest.mkdir()
        exe=root/'.lake/build/bin'/('x86test' if arch=='i386' else 'x64test')
        checked(['lake','build',exe.name],cwd=root)
        model=bytearray();native=bytearray();meta=[]
        for m,n,info in case_source(arch,seeds,args.count):
            model.extend(m);native.extend(n);meta.append(info)
        if len(meta)>1000000:raise ValueError('suite exceeds native oracle limit')
        (dest/'vectors.bin').write_bytes(model)
        (dest/'native.bin').write_bytes(struct.pack('<Q',len(meta))+native)
        (dest/'vectors.json').write_text(json.dumps(meta))
        with (dest/'model.out').open('w') as log:
            checked([exe,'--native-memory',dest/'vectors.bin'],stdout=log,timeout=300)
        validate_output(dest/'model.out',len(meta),arch,4 if arch=='i386' else 2)
        manifest['architectures'][arch]=dict(count=len(meta),model_sha256=digest(exe),
            model_output_sha256=digest(dest/'model.out'),families=dict(collections.Counter(m['family'] for m in meta)),
            random_by_seed=dict(collections.Counter(str(m['source_seed']) for m in meta if 'source_seed' in m)))
        if campaign is not None:
            manifest['architectures'][arch]['source_sha256']={str(p.relative_to(REPO)):digest(p)
                for p in model_sources(arch)}
        print(arch,len(meta),'memory vectors prepared',flush=True)
    for path in out.rglob('*'):
        if path.is_file() and path.name!='model.out':manifest['sha256'][str(path.relative_to(out))]=digest(path)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    with tarfile.open(out.with_name(out.name+'.tar.gz'),'x:gz') as tar:
        tar.add(out,arcname=out.name,filter=lambda info:None if Path(info.name).name=='model.out' else info)
    print('Prepared',out.with_name(out.name+'.tar.gz'),'; native hardware has NOT run.')
