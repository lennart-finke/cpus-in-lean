"""Twelve falsification campaigns, with bounded native execution and exact reproducers.

No expected results are generated here. Hardware comparison stays strict; clusters
are triage candidates, never a claim that twelve independent bugs have been found.
"""
import argparse
import collections
import itertools
import json
import random
import struct
from pathlib import Path

from native_memory import BASE, IP, PERMS, prepare_memory

TARGETS = {
    'rmw_extended': 'NOT/INC/DEC/CMPXCHG8B, comparison success/failure, legal and illegal LOCK',
    'stack_alias': 'PUSH/POP aliases, post-increment destination addressing, IA-32 ENTER/PUSHA/POPA',
    'bit_strings': 'Signed register bit indexes, immediate indexes, page boundaries and address sizes',
    'shifts': 'Rotate/shift and double-shift counts, zero-count memory faults, defined flag masks',
    'divide': 'DIV/IDIV overflow and zero, implicit-register aliases and operand fault priority',
    'conditional': 'All CMOV conditions, false-condition loads, SETcc memory and high destination bits',
    'prefixes': 'REX cancellation, operand/address overrides, redundant prefixes and illegal LOCK',
    'rep_compare': 'REPE/REPNE CMPS/SCAS, zero count, DF, TF, partial progress and address size',
    'sqrt': 'Scalar/packed SQRT, signed zero, subnormals, NaNs and exception masks',
    'conversions': 'Float/integer and float-width conversion boundaries, rounding, DAZ and FTZ',
    'fp_compare': 'All CMP predicates, COMI/UCOMI, signaling/quiet NaNs and lane exception priority',
    'simd_memory': 'Scalar/partial XMM transfers, legacy arithmetic alignment and fault priority',
}
FLAGS = 0xdd5
ARITH = 0x8d5
PERMISSIONS = tuple(itertools.product(PERMS, repeat=2))


def prefix(width):
    return b'\x66' if width == 2 else b'\x48' if width == 8 else b''


def decode_accesses(arch, code, regs, flags):
    """Independent restricted decoder: reject control flow/system ops and arena escapes.

    This uses instruction bytes, not generator-supplied addresses/widths. Also checks
    implicit stack accesses, post-POP EA, signed bit offsets and all REP iterations.
    """
    pos=0; p66=False; p67=False; rep=0; rex=0; locked=False
    while pos<len(code):
        b=code[pos]
        if b in (0x66,0x67,0xf2,0xf3,0xf0,0x2e,0x3e):
            if b==0x66:p66=True
            if b==0x67:p67=True
            if b in (0xf2,0xf3):rep=b
            if b==0xf0:locked=True
            rex=0
        elif arch=='x86_64' and 0x40<=b<=0x4f:rex=b&15
        else:break
        pos+=1
    assert 1<=len(code)<=15 and pos<len(code)
    op=code[pos];pos+=1
    if op==0x0f:op=0x100+code[pos];pos+=1
    width=8 if rex&8 else 2 if p66 else 4
    stackwidth=2 if p66 else 4 if arch=='i386' else 8
    addr_bits=32 if arch=='i386' or p67 else 64
    assert not (arch=='i386' and p67), '16-bit addressing not mapped by this oracle'
    accesses=[]
    def access(address,n):
        assert BASE<=address and address+n<=BASE+8192,(code.hex(),hex(address),n)
        # LOCK/XCHG inputs avoid split-lock policy, which varies between kernels.
        if locked:assert address%max(n,1)==0 and address//64==(address+n-1)//64
        accesses.append((address,n))
    if op in (0xa6,0xa7,0xae,0xaf):
        assert rep in (0xf2,0xf3) and pos==len(code)
        width=width if op&1 else 1
        count=regs[1]&((1<<addr_bits)-1)
        assert count<=16
        for reg in ([6,7] if op in (0xa6,0xa7) else [7]):
            start=regs[reg]&((1<<addr_bits)-1)
            for k in range(count):access(start+(-1 if flags&0x400 else 1)*k*width,width)
        return accesses
    if 0x50<=op<=0x5f:
        assert pos==len(code)
        access(regs[4]-(stackwidth if op<0x58 else 0),stackwidth)
        return accesses
    if op==0xc9:
        assert pos==len(code)
        access(regs[5],stackwidth)
        return accesses
    if op in (0x60,0x61,0xc8):
        assert arch=='i386'
        if op in (0x60,0x61):
            assert pos==len(code)
            for k in range(8):
                access(regs[4]+(k*width if op==0x61 else -(k+1)*width),width)
        else:
            assert pos+3==len(code)
            allocation=int.from_bytes(code[pos:pos+2],'little');level=code[pos+2]&31
            for k in range(1,max(1,level)+1):access(regs[4]-k*width,width)
            if level:
                access(regs[4]-(level+1)*width,width)
                for k in range(1,level):access(regs[5]-k*width,width)
            access(regs[4]-(1+(level if level else 0))*width-allocation,width)
        return accesses
    scalar={0x01,0x39,0x85,0x87,0x88,0x89,0x8a,0x8b,0x8f,0xc0,0xc1,0xd2,0xd3,
            0xf6,0xf7,0xfe,0xff,0x1a3,0x1ab,0x1b3,0x1bb,0x1ba,0x1a4,0x1ac,
            0x1b0,0x1b1,0x1c0,0x1c1,0x1c7}
    simd={0x110,0x111,0x112,0x113,0x116,0x117,0x12a,0x12b,0x12c,0x12d,0x12e,0x12f,
          0x151,0x158,0x159,0x15a,0x15c,0x15e,0x16e,0x17e,0x1c2,0x1d6,0x1e7}
    assert op in scalar|simd or 0x140<=op<=0x14f or 0x190<=op<=0x19f
    assert arch=='x86_64' or op not in simd
    md=code[pos];pos+=1;mod=md>>6;group=(md>>3)&7;rm=md&7
    if op in (0xf6,0xf7):assert group>=2  # no unparsed TEST immediate
    if op==0xff:assert group in (0,1,6)  # no CALL/JMP
    if op==0xfe:assert group<2
    if op==0x8f:assert group==0
    if op==0x1c7:assert group==1 and width!=8  # no CMPXCHG16B
    if op==0x1ba:assert group>=4
    r=list(regs)
    if op==0x8f:r[4]+=stackwidth
    ea=None
    if mod!=3:
        base=None;index=0;rip=False
        if rm==4:
            sib=code[pos];pos+=1;idx=((sib>>3)&7)+(8 if rex&2 else 0)
            if idx!=4:index=r[idx]*(1<<(sib>>6))
            if mod!=0 or sib&7!=5:base=(sib&7)+(8 if rex&1 else 0)
        elif mod==0 and rm==5:rip=arch=='x86_64'
        else:base=rm+(8 if rex&1 else 0)
        n=1 if mod==1 else 4 if mod==2 or base is None else 0
        disp=int.from_bytes(code[pos:pos+n],'little',signed=True);pos+=n
        ea=((r[base] if base is not None else IP+len(code) if rip else 0)+index+disp)&((1<<addr_bits)-1)
    immediate=1 if op in (0xc0,0xc1,0x1ba,0x1a4,0x1ac,0x1c2) else 0
    imm=code[pos] if immediate else 0
    assert pos+immediate==len(code),code.hex()
    if op in (0x88,0x8a,0xc0,0xd2,0xf6,0xfe,0x1b0,0x1c0) or 0x190<=op<=0x19f:width=1
    if op==0x1c7:width=8
    if op in simd:
        width=(8 if p66 or rep==0xf2 else 4) if op in (0x12e,0x12f) else 16
        if op in (0x110,0x111,0x151,0x158,0x159,0x15a,0x15c,0x15e,0x1c2) and rep:
            width=8 if rep==0xf2 else 4
        if op in (0x12c,0x12d):width=8 if rep==0xf2 else 4
        if op==0x12a:width=8 if rex&8 else 4
        if op in (0x112,0x113,0x116,0x117,0x1d6) or op==0x17e and rep==0xf3:width=8
        if op==0x16e or op==0x17e and rep!=0xf3:width=8 if rex&8 else 4
    if op in (0x8f,0xff) and (op==0x8f or group==6):
        width=stackwidth
        access(regs[4]-(width if op==0xff else 0),width)
    if ea is not None:
        if op in (0x1a3,0x1ab,0x1b3,0x1bb):
            index=regs[group+(8 if rex&4 else 0)]&((1<<(width*8))-1)
            if index>>(width*8-1):index-=1<<(width*8)
            ea+=index//(width*8)*width
        access(ea,width)
    return accesses


def constants(bits):
    f,bias=(23,127) if bits==32 else (52,1023)
    one=bias<<f;normal=1<<f;inf=((1<<(bits-f-1))-1)<<f;sign=1<<(bits-1)
    return [0,sign,1,sign|1,normal-1,normal,normal+1,one-1,one,one+1,
            one+normal,sign|one,inf-1,inf,sign|inf,inf|(normal>>1)|0x123,inf|0x456]


def controls(range_masks=False):
    masks=(0x3f,0x3e,0x3d,0x1f,0)+( (0x37,0x2f) if range_masks else () )
    for mask,rounding,mode in itertools.product(masks,range(4),range(4)):
        yield (mask<<7)|(rounding<<13)|(0x40 if mode&1 else 0)|(0x8000 if mode&2 else 0)


def vectors(arch,seeds,random_count):
    rng=random.Random(0x48554e54);serial=0;pool=[]
    widths=(2,4) if arch=='i386' else (2,4,8)
    def regs():
        r=[rng.getrandbits(32 if arch=='i386' else 64) for _ in range(16)]
        r[1]=1;r[3]=BASE+0x800;r[4]=BASE+0x800;r[5]=BASE+0x800
        r[6]=BASE+0x400;r[7]=BASE+0x800
        return r
    def emit(target,scenario,code,r=None,permissions=('rw','rw'),flags=0x202,mask=FLAGS,
             xmm=None,mxcsr=0x1f80,seed=1,**details):
        nonlocal serial
        r=regs() if r is None else r
        if arch=='i386':r=[v&0xffffffff for v in r[:8]]+[0]*8
        accesses=decode_accesses(arch,code,r,flags)
        xx=xmm if xmm is not None else [rng.getrandbits(64) for _ in range(32)]
        pp=[PERMS[p] for p in permissions]
        n=struct.pack('<16s16QQII2Q32QII',bytes([len(code)])+code.ljust(15,b'\xcc'),
                      *r,flags,seed,1,*pp,*xx,mxcsr,0)
        m=n if arch=='x86_64' else struct.pack('<B15s8III4H2H2I3I',len(code),code.ljust(15,b'\0'),
              *r[:8],flags,seed,*([0x23]*4),0xffff,0xffff,0,0,3,*pp)
        meta=dict(index=serial,campaign=target,family='hunt_'+target,scenario=scenario,
                  code=code.hex(),mask=mask,permissions=permissions,accesses=accesses,
                  mxcsr=mxcsr,data_seed=seed,**details)
        serial+=1
        result=(m,n,meta);pool.append(result)
        return result

    # Scalar RMW paths not covered by the previous ADD/NEG/XADD/CMPXCHG campaign.
    for width,offset,perm in itertools.product(widths,(0x800,0xff8,0xfff),PERMISSIONS):
        for name,op,md in [('not',0xf7,0x13),('inc',0xff,3),('dec',0xff,0x0b)]:
            for lock in (False,True):
                if lock and offset%width:continue
                r=regs();r[3]=BASE+offset
                yield emit('rmw_extended',name,(b'\xf0' if lock else b'')+prefix(width)+bytes([op,md]),r,perm,locked=lock)
    for offset,perm,seed,match in itertools.product((0x800,0xff8,0xfff),PERMISSIONS,(0,1),(False,True)):
        r=regs();r[3]=BASE+offset;r[0]=0 if match else 0xffffffff;r[2]=0
        yield emit('rmw_extended','cmpxchg8b',b'\x0f\xc7\x0b',r,perm,seed=seed,compare_zero=match)

    for width,offset,perm in itertools.product((2,4 if arch=='i386' else 8),(0x808,0xff8,0xfff,0x1000),PERMISSIONS):
        pre=b'\x66' if width==2 else b''
        for name,body in [('push_sp','54'),('pop_sp','5c'),('pop_mem_sp','8f0424'),
                          ('pop_mem_sp_minus_width','8f4424'+bytes([256-width]).hex()),
                          ('push_mem_sp','ff3424'),('leave','c9')]:
            r=regs();r[4]=r[5]=BASE+offset
            yield emit('stack_alias',name,pre+bytes.fromhex(body),r,perm,width=width)
    if arch=='i386':
        for width,offset,perm in itertools.product(widths,(0xff8,0xfff,0x1000,0x1008,0x1040),PERMISSIONS):
            for op in (0x60,0x61):
                r=regs();r[4]=BASE+offset
                yield emit('stack_alias','pusha' if op==0x60 else 'popa',prefix(width)+bytes([op]),r,perm,width=width)
            for allocation,level in itertools.product((0,2,32,0x800),(0,1,2,4,31)):
                r=regs();r[4]=BASE+offset;r[5]=BASE+0x1008
                code=prefix(width)+b'\xc8'+struct.pack('<HB',allocation,level)
                yield emit('stack_alias','enter',code,r,perm,width=width,allocation=allocation,level=level)

    for width,idx,offset,perm in itertools.product(widths,(-129,-65,-33,-17,-1,0,15,16,31,32,63,64,127),
                                                  (0xfe0,0x1000),PERMISSIONS):
        for op in (0xa3,0xab,0xb3,0xbb):
            r=regs();r[3]=BASE+offset;r[1]=idx&((1<<64)-1)
            yield emit('bit_strings',f'op_{op:02x}',prefix(width)+bytes([15,op,0x0b]),r,perm,
                       mask=FLAGS&~0x894,bit_index=idx,width=width)
    for width,idx,perm in itertools.product(widths,(0,15,16,31,32,63,64,127,255),PERMISSIONS):
        r=regs();r[3]=BASE+0xfff
        yield emit('bit_strings','immediate_bts',prefix(width)+bytes([15,0xba,0x2b,idx]),r,perm,
                   mask=FLAGS&~0x894,bit_index=idx,width=width)

    for width,count,group,perm in itertools.product((1,)+widths,(0,1,2,7,8,15,16,31,32,63,64,255),range(8),PERMISSIONS):
        r=regs();r[3]=BASE+0xfff;r[1]=count
        masked=count&(63 if width==8 else 31)
        mask=FLAGS if masked==0 else FLAGS&(~0x10 if group>=4 else -1)&(~0x800 if masked!=1 else -1)
        if group>=4 and masked>=width*8:mask&=~1
        yield emit('shifts',f'group_{group}',prefix(width)+bytes([0xd2 if width==1 else 0xd3,3|(group<<3)]),
                   r,perm,flags=0xad7,mask=mask,count=count,width=width)
    for width,count,op,perm in itertools.product(widths,(0,1,2,15),(0xa4,0xac),PERMISSIONS):
        r=regs();r[3]=BASE+0xfff
        yield emit('shifts','double',prefix(width)+bytes([15,op,0x0b,count]),r,perm,
                   mask=FLAGS if count==0 else FLAGS&~0x10&(~0x800 if count!=1 else -1),count=count,width=width)

    for width,group,location,seed,high,low in itertools.product((1,)+widths,(6,7),('reg','mem'),(0,1),
                                                              (0,1,0xffffffffffffffff),(0,1,0x8000000000000000,0xffffffffffffffff)):
        for perm in ((('rw','rw'),) if location=='reg' else (('rw','rw'),('r','none'),('none','rw'))):
            r=regs();r[0]=low;r[2]=high;r[1]=0 if seed==0 else (1<<(width*8-1));r[3]=BASE+0xfff
            yield emit('divide','idiv' if group==7 else 'div',prefix(width)+bytes([0xf6 if width==1 else 0xf7,
                       (0xc1 if location=='reg' else 3)|(group<<3)]),r,perm,mask=FLAGS&~ARITH,seed=seed,
                       width=width,location=location)

    for width,cc,flags,perm in itertools.product(widths,range(16),(0x202,0xad7),PERMISSIONS):
        r=regs();r[3]=BASE+0xfff
        yield emit('conditional','cmov',prefix(width)+bytes([15,0x40+cc,3]),r,perm,flags=flags,condition=cc,width=width)
        if width==2:
            yield emit('conditional','setcc',bytes([15,0x90+cc,3]),r,perm,flags=flags,condition=cc)

    prefixes=[b'',b'\x66',b'\x66\x66',b'\x2e\x3e',b'\x66'*12]
    if arch=='x86_64':prefixes += [b'\x48\x66',b'\x66\x48',b'\x40\x66\x44',b'\x67',b'\x67\x48']
    for pre,body,perm in itertools.product(prefixes,('8b03','8903','8ac4','88e0','0f4403'),PERMISSIONS):
        r=regs();r[3]=BASE+0xff8
        yield emit('prefixes','override_order',pre+bytes.fromhex(body),r,perm,prefix=pre.hex())
    for body,perm in itertools.product(('3903','8503','8b03','8903','01c8','0fa30b','0f4403'),PERMISSIONS):
        yield emit('prefixes','illegal_lock',b'\xf0'+bytes.fromhex(body),permissions=perm)

    for width,op,rep,count,backward,tf,protection in itertools.product((1,)+widths,(0xa6,0xae),(0xf2,0xf3),
                                                                    (0,1,4,8),(False,True),(False,True),PERMS):
        r=regs();r[1]=count;r[0]=0
        r[7]=BASE+0x1004 if backward else BASE+0x1000-2*width
        r[6]=r[7]  # equal CMPS runs to completion or faults; only one shared operand page can fail
        perm=(protection,'rw') if backward else ('rw',protection)
        code=bytes([rep])+prefix(width)+bytes([op+(width!=1)])
        flags=0x202|(0x400 if backward else 0)|(0x100 if tf else 0)
        yield emit('rep_compare','cmps' if op==0xa6 else 'scas',code,r,perm,flags=flags,seed=0,
                   count=count,width=width)
        if arch=='x86_64':
            r[1]|=0x123400000000;r[6]|=0x567800000000;r[7]|=0x9abc00000000
            yield emit('rep_compare','addr32_cmps' if op==0xa6 else 'addr32_scas',b'\x67'+code,r,perm,
                       flags=flags,seed=0,count=count,width=width)
    # Unlike same-address CMPS, these distinguish source/destination fault order
    # and flag rollback after successful iterations. Only the target operand can fault.
    for width,source_fault,rep,backward,tf,seed in itertools.product((1,)+widths,(False,True),(0xf2,0xf3),
                                                                   (False,True),(False,True),(0,1)):
        r=regs();r[1]=8
        target=BASE+0x1004 if backward else BASE+0x1000-2*width
        safe=BASE+0x1800 if backward else BASE+0x800
        r[6],r[7]=(target,safe) if source_fault else (safe,target)
        perm=('none','rw') if backward else ('rw','none')
        yield emit('rep_compare','cmps_separate',bytes([rep])+prefix(width)+bytes([0xa6+(width!=1)]),r,perm,
                   flags=0xad7|(0x400 if backward else 0)|(0x100 if tf else 0),seed=seed,
                   width=width,source_fault=source_fault)

    if arch=='x86_64':
        def lanes(bits,left,right):
            xx=[rng.getrandbits(64) for _ in range(32)]
            for reg,values in ((0,left),(1,right)):
                packed=sum(values[k%len(values)]<<(k*bits) for k in range(128//bits))
                xx[reg*2:reg*2+2]=[packed&((1<<64)-1),packed>>64]
            return xx
        for pre,bits in ((b'',32),(b'\x66',64),(b'\xf3',32),(b'\xf2',64)):
            values=constants(bits)
            for value,mxcsr in itertools.product(values,controls()):
                for mixed in ((False,True) if pre in (b'',b'\x66') else (False,)):
                    yield emit('sqrt','mixed_invalid' if mixed else 'boundary',pre+b'\x0f\x51\xc1',
                               xmm=lanes(bits,[values[8]],[value,values[11]] if mixed else [value]),
                               mxcsr=mxcsr,value=hex(value),bits=bits)
            pairs=[(values[a],values[b]) for a,b in ((0,1),(8,8),(7,8),(8,7),(15,8),(8,15),(16,15),(15,16),(16,2),(2,16),(2,8),(8,2))]
            for (a,b),pred,mxcsr in itertools.product(pairs,range(8),controls()):
                for mixed in ((False,True) if pre in (b'',b'\x66') else (False,)):
                    yield emit('fp_compare','mixed_predicate' if mixed else 'predicate',pre+bytes([15,0xc2,0xc1,pred]),
                               xmm=lanes(bits,[a,values[16]] if mixed else [a],[b,values[8]] if mixed else [b]),
                               mxcsr=mxcsr,predicate=pred,bits=bits,left=hex(a),right=hex(b))
            if pre in (b'',b'\x66'):
                for (a,b),op,mxcsr in itertools.product(pairs,(0x2e,0x2f),controls()):
                    yield emit('fp_compare','ucomi' if op==0x2e else 'comi',pre+bytes([15,op,0xc1]),
                               xmm=lanes(bits,[a],[b]),mxcsr=mxcsr,bits=bits,left=hex(a),right=hex(b))
        for pre,bits in ((b'\xf3',32),(b'\xf2',64)):
            f=23 if bits==32 else 52;bias=127 if bits==32 else 1023
            values=constants(bits)+[((bias+power)<<f)+delta for power in (24,31,32,53,63) for delta in (-1,0,1)]
            values += [x|(1<<(bits-1)) for x in values[-15:]]
            if bits==64:
                values += [((bias+power)<<f)+delta for power in (-150,-149,-126,128) for delta in (-1,0,1)]
            for value,op,wide,mxcsr in itertools.product(values,(0x2c,0x2d,0x5a),(False,True),controls(True)):
                if op==0x5a and wide:continue
                yield emit('conversions','float_width' if op==0x5a else 'to_int_truncate' if op==0x2c else 'to_int_round',
                           pre+(b'\x48' if wide else b'')+bytes([15,op,0xc1]),xmm=lanes(bits,[0x123],[value]),
                           mxcsr=mxcsr,bits=bits,wide=wide,value=hex(value))
            for value,wide,mxcsr in itertools.product((0,1,(1<<24)-1,(1<<24)+1,(1<<31)-1,1<<31,
                                                     (1<<53)+1,(1<<63)-1,1<<63,(1<<64)-1),(False,True),controls()):
                r=regs();r[1]=value
                yield emit('conversions','from_int',pre+(b'\x48' if wide else b'')+b'\x0f\x2a\xc1',r,
                           mxcsr=mxcsr,bits=bits,wide=wide,value=hex(value))
        moves=[('movss_load','f30f1003'),('movss_store','f30f1103'),('movsd_load','f20f1003'),('movsd_store','f20f1103'),
               ('movlps_load','0f1203'),('movlps_store','0f1303'),('movhps_load','0f1603'),('movhps_store','0f1703'),
               ('movd_load','660f6e03'),('movd_store','660f7e03'),('movq_load','f30f7e03'),('movq_store','660fd603'),
               ('movq_gpr_load','66480f6e03'),('movq_gpr_store','66480f7e03'),
               ('movntps','0f2b03'),('movntpd','660f2b03'),('movntdq','660fe703'),
               ('addps','0f5803'),('addpd','660f5803'),('addss','f30f5803'),('addsd','f20f5803'),
               ('sqrtps','0f5103'),('sqrtss','f30f5103'),('cvtss2sd','f30f5a03'),('cvtsd2ss','f20f5a03')]
        for (name,code),offset,perm,seed,mxcsr in itertools.product(moves,(0x800,0x801,0xff0,0xff8,0xffc,0xfff),PERMISSIONS,(0,1),
                                                                  (0x1f80,0,0x9fc0)):
            r=regs();r[3]=BASE+offset
            yield emit('simd_memory',name,bytes.fromhex(code),r,perm,seed=seed,mxcsr=mxcsr)

    # Seeded mutations preserve validated addresses/opcodes. Perturb initial flags,
    # data and SIMD payloads; keep implicit counts/indexes and all GPRs bounded.
    templates=tuple(pool)
    for seed in seeds:
        rr=random.Random(seed)
        for _ in range(random_count):
            m,n,meta=rr.choice(templates);n=bytearray(n);m=bytearray(m)
            data_seed=rr.getrandbits(32);flags=0x202|(rr.getrandbits(12)&FLAGS)
            struct.pack_into('<I',n,152,data_seed);struct.pack_into('<Q',n,144,flags)
            if arch=='i386':
                struct.pack_into('<I',m,52,data_seed);struct.pack_into('<I',m,48,flags)
            else:
                # Flip a nearby representable bit in each source lane.
                for offset in (192,200):
                    struct.pack_into('<Q',n,offset,struct.unpack_from('<Q',n,offset)[0]^(1<<rr.randrange(64)))
                m=n
            r=list(struct.unpack_from('<16Q',n,16))
            try:accesses=decode_accesses(arch,bytes(n[1:1+n[0]]),r,flags)
            except AssertionError:continue  # DF mutations can turn a bounded string into an escape
            yield bytes(m),bytes(n),dict(meta,index=serial,source_seed=seed,source_index=meta['index'],
                                         data_seed=data_seed,accesses=accesses)
            serial+=1


def prepare_hunt(args):
    if args.memory or args.focused_sse or args.backend!='signals':
        raise ValueError('--hunt uses its own memory/signal campaigns; do not combine backend/suite options')
    if args.count<1 or args.count>100000:raise ValueError('hunt mutation count must be 1..100000 per seed')
    return prepare_memory(args,vectors,dict(name='twelve-target-hunt',target_bug_count=12,targets=TARGETS,
        counting='A target or failure cluster is not a confirmed distinct bug.',
        reference='https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html'))


def triage(directory,prepared,out):
    """Run the strict comparator first, then export clusters and one-case reproducers."""
    from native import compare
    compare(argparse.Namespace(directory=directory,prepared=prepared,replay_to=out))
    groups=collections.defaultdict(list)
    evidence={}
    for arch in ('i386','x86_64'):
        mismatches=json.loads((out/arch/'mismatches.json').read_text())
        if mismatches:
            evidence[arch]=((directory/arch/'vectors.bin').read_bytes(),
                            (directory/arch/'native.bin').read_bytes(),
                            (directory/arch/'native.out').read_text().splitlines(),
                            (out/arch/'model.out').read_text().splitlines())
        for item in mismatches:
            fields=tuple(sorted({d.split(':')[0].split(' (')[0] for d in item['differences']}))
            groups[(arch,item.get('campaign','unknown'),item.get('scenario','unknown'),fields)].append(item)
    candidates=[]
    for number,(key,items) in enumerate(sorted(groups.items()),1):
        arch,campaign,scenario,fields=key;case=min(items,key=lambda m:(len(m['code']),m['index']))
        dest=out/'candidates'/f'{number:03d}-{arch}-{campaign}';dest.mkdir(parents=True)
        size=88 if arch=='i386' else 440;idx=case['index']
        raw,native,observed,model=evidence[arch]
        (dest/'vectors.bin').write_bytes(raw[idx*size:(idx+1)*size])
        (dest/'native.bin').write_bytes(struct.pack('<Q',1)+native[8+idx*440:8+(idx+1)*440])
        (dest/'case.json').write_text(json.dumps(case,indent=2)+'\n')
        (dest/'observed-row.txt').write_text(observed[idx+1]+'\n')
        (dest/'model-row.txt').write_text(model[idx+1]+'\n')
        candidates.append(dict(id=number,status='unconfirmed',architecture=arch,campaign=campaign,scenario=scenario,
                               fields=fields,case_count=len(items),representative=idx,path=str(dest)))
    report=dict(target=12,confirmed_distinct_bugs=None,candidate_clusters=len(candidates),candidates=candidates,
                note='Clusters may share a root cause or reflect hardware/model scope differences. Review before counting bugs.')
    (out/'triage.json').write_text(json.dumps(report,indent=2)+'\n')
    print(len(candidates),'unconfirmed candidate clusters; see',out/'triage.json')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--prepared',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    triage(args.directory.resolve(),args.prepared.resolve(),args.out.resolve())
