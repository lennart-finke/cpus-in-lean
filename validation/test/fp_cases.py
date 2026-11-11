"""IA-32 FP inputs only. No CPU observation or model answer is used by generation.

Records use bundle format v2 (native_fp.py): the 648-byte v1 record followed by YMM0..7
bits 255:128 (16 quadwords). A case family may require CPUID features: register it in
FAMILIES with the feature names (native_fp.FEATURES, named as x86_32/X86/Cpuid.lean's
`Feature`); its cases then carry `requires` in their metadata, run in their own campaigns,
and are skipped (and reported) on a machine whose CPUID dump lacks a feature."""
import random
import struct

from native_cases import focused_sse, constants

SIZE = 776   # v2 record (V1_SIZE = 648 plus 128 bytes of YMM upper halves)
V1_SIZE = 648
ONE = (0x8000000000000000, 0x3fff)
VALUES = [
    (0, 0), (0, 0x8000), ONE, (ONE[0], 0xbfff),
    (0xc000000000000000, 0x4000), (0xa000000000000000, 0xc000),
    (1, 0), (0x7fffffffffffffff, 0), (ONE[0], 1), (ONE[0], 0),
    (0xffffffffffffffff, 0x7ffe), (ONE[0], 0x7fff), (ONE[0], 0xffff),
    (0xc000000000000123, 0x7fff), (0xe000000000000456, 0xffff),
    (0x8000000000000123, 0x7fff), (0x123456789abcdef, 0x4000),
    (0xffffffffffffffff, 0x3ffe), (0x8000000000000001, 0x3fff),
    (ONE[0], 0x3fbf), (ONE[0], 0x403e), (ONE[0], 0x403d),
]
X87 = [
    ('fadd', 'd8c1'), ('fmul', 'd8c9'), ('fsub', 'd8e1'), ('fsubr', 'd8e9'),
    ('fdiv', 'd8f1'), ('fdivr', 'd8f9'), ('faddp', 'dec1'), ('fmulp', 'dec9'),
    ('fsubp', 'dee9'), ('fsubrp', 'dee1'), ('fdivp', 'def9'), ('fdivrp', 'def1'),
    ('fsqrt', 'd9fa'), ('frndint', 'd9fc'), ('fscale', 'd9fd'), ('fxtract', 'd9f4'),
    ('fprem', 'd9f8'), ('fprem1', 'd9f5'), ('fcom', 'd8d1'), ('fucom', 'dde1'),
    ('fcompp', 'ded9'), ('fucompp', 'dae9'), ('fcomi', 'dbf1'), ('fucomi', 'dbe9'),
    ('fcomip', 'dff1'), ('fucomip', 'dfe9'), ('ftst', 'd9e4'), ('fxam', 'd9e5'),
    ('fchs', 'd9e0'), ('fabs', 'd9e1'), ('fxch', 'd9c9'), ('fld_st1', 'd9c1'),
    ('fst_st1', 'ddd1'), ('fstp_st1', 'ddd9'), ('ffree', 'ddc1'),
    ('fincstp', 'd9f7'), ('fdecstp', 'd9f6'),
]
TRANS = [('f2xm1','d9f0'), ('fyl2x','d9f1'), ('fyl2xp1','d9f9'),
         ('fpatan','d9f3'), ('fsin','d9fe'), ('fcos','d9ff'), ('fptan','d9f2'), ('fsincos','d9fb')]
IOPS = bytes.fromhex('60 61 62 63 64 65 66 67 68 69 6a 6b 74 75 76 d1 d2 d3 d4 d5 d8 d9 da db dc dd de df e0 e1 e2 e3 e4 e5 e8 e9 ea eb ec ed ee ef f1 f2 f3 f4 f5 f6 f8 f9 fa fb fc fd fe')


def record(code, *, a=ONE, b=ONE, cw=0x37f, sw=0, tags=255,
           mxcsr=0x1f80, xmm=None, mem=b'', seed=1, flags=0x202,
           address=0x10000, permissions=(0x67, 0x67), stack=None, memory_kind=0, ymmh=None):
    code = bytes.fromhex(code) if isinstance(code, str) else code
    assert 1 <= len(code) <= 15 and len(mem) <= 64
    regs = [0x12345678, 3, 0x76543210, address, 0x11800, address, address, address] + [0]*8
    xmm = xmm or [0x0123456789abcdef ^ (k*0x101010101010101) for k in range(32)]
    base = struct.pack('<16s16QQII2Q32QII', bytes([len(code)])+code.ljust(15,b'\xcc'),
                       *regs, flags, seed, 1, *permissions, *xmm, mxcsr, memory_kind)
    stack = stack or [a,b]+[(ONE[0]+k,0x4000+k) for k in range(6)]
    fp = struct.pack('<4HQ', cw, sw, tags, 0, 0)
    fp += b''.join(struct.pack('<QH6x', *v) for v in stack)
    ymmh = ymmh or [0xfedcba9876543210 ^ (k*0x1010101010101) for k in range(16)]
    return base+fp+mem.ljust(64,b'\0')+struct.pack('<16Q', *ymmh)


def meta(family, name, code, **kw):
    return dict(family=family, instruction=name, code=code if isinstance(code,str) else code.hex(),
                flags_mask=0x8d5, sw_mask=0xb8ff, **kw)


def x87_cases(rng, count):
    for code in ('90','d9d0'):
        yield record(code, sw=0x2800, tags=0xa5), meta('calibration','nop',code)
    for op, code in X87:
        for pc in (0,2,3):
            for rc in range(4):
                for j,a in enumerate(VALUES):
                    b = VALUES[(j*7+3) % len(VALUES)]
                    cw = 0x7f | pc<<8 | rc<<10
                    info = meta('x87_matrix',op,code,pc=pc,rc=rc,operand_class=j)
                    # Compare condition codes only where the instruction defines them.
                    if op in ('fcom','fucom','fcompp','fucompp','ftst','fxam','fprem','fprem1'):
                        info['sw_mask'] |= 0x4700
                    elif op.startswith(('fadd','fmul','fsub','fdiv')) or op in ('fsqrt','frndint'):
                        info['sw_mask'] |= 0x200
                    yield record(code,a=a,b=b,cw=cw,sw=(j%8)<<11), info
        # Every exception individually unmasked, all unmasked, and masked;
        # each empty/full-stack pattern under every TOP position.
        for mask in (0,0x3e,0x3d,0x3b,0x37,0x2f,0x1f,0x3f):
            for top in range(8):
                for tags in (0,255,255 ^ (1<<top),255 ^ (1<<((top+1)%8))):
                    j = (top+mask) % len(VALUES)
                    yield record(code,a=VALUES[j],b=VALUES[(j+4)%len(VALUES)],
                                 cw=0x340|mask,sw=top<<11,tags=tags), meta(
                                     'x87_exceptions',op,code,exception_mask=mask,top=top,tags=tags)
    for i in range(count):
        op,code = X87[i % len(X87)]
        def value():
            return rng.choice(VALUES) if rng.randrange(2) else (rng.getrandbits(64),rng.randrange(65536))
        yield record(code,a=value(),b=value(),cw=0x40|rng.choice((0,2,3))<<8|rng.randrange(4)<<10|
                     rng.choice((0x3f,0x3e,0x3d,0x3b,0x37,0x2f,0x1f,0)),
                     sw=rng.randrange(8)<<11,tags=rng.choice((255,255,0,rng.randrange(256)))), meta('x87_random',op,code)
    # Load/store and integer/BCD conversions, including rounding and failed writes.
    memory_ops = [('fld32','d903'),('fld64','dd03'),('fld80','db2b'),
                  ('fst32','d913'),('fstp32','d91b'),('fst64','dd13'),('fstp64','dd1b'),('fstp80','db3b'),
                  ('fild16','df03'),('fild32','db03'),('fild64','df2b'),('fist16','df13'),
                  ('fistp16','df1b'),('fist32','db13'),('fistp32','db1b'),('fistp64','df3b'),
                  ('fbld','df23'),('fbstp','df33'),('fldcw','d92b'),('fnstcw','d93b'),('fnstsw','dd3b')]
    for name,code in memory_ops:
        for rc in range(4):
            for j,a in enumerate(VALUES):
                payload = struct.pack('<QH',*a)
                if name == 'fldcw': payload = struct.pack('<H',0x37f|rc<<10)
                if name == 'fbld': payload = bytes([0x99]*9+[0x80 if j&1 else 0])
                for perms in ((0x67,0x67),(0x65,0x67),(0,0x67)):
                    yield record(code,a=a,mem=payload,cw=0x37f|rc<<10,permissions=perms), meta(
                        'x87_memory',name,code,rc=rc,operand_class=j,permissions=perms)
    for op,code in [('fld1','d9e8'),('fldl2t','d9e9'),('fldl2e','d9ea'),('fldpi','d9eb'),
                    ('fldlg2','d9ec'),('fldln2','d9ed'),('fldz','d9ee'),('fninit','dbe3'),('fnclex','dbe2')]:
        for rc in range(4):
            for top in range(8):
                yield record(code,cw=0x37f|rc<<10,sw=top<<11,tags=0),meta('x87_control',op,code,rc=rc,top=top)
    for op,code in TRANS:
        for rc in range(4):
            for j,a in enumerate(VALUES):
                for mask in (0x3f,0x3e,0x3d,0):
                    yield record(code,a=a,b=VALUES[(j+4)%len(VALUES)],cw=0x340|rc<<10|mask), meta(
                        'x87_transcendental',op,code,rc=rc,operand_class=j,
                        policy='observe',reason='implementation approximation/domain behavior; exact differences need review')
        # Neighbours of the 66-bit pi approximation and argument-reduction boundaries.
        for exponent in (0x3fbf,0x3ffe,0x3fff,0x4000,0x401f,0x403d,0x403e):
            for delta in (-2,-1,0,1,2):
                for sign in (0,0x8000):
                    a=(0xc90fdaa22168c235+delta,exponent|sign)
                    yield record(code,a=a,b=VALUES[4]),meta('x87_trans_boundary',op,code,
                        policy='observe',reason='transcendental approximation or undefined input domain')
    for code in ('9b','d9d0','d9e8','dbe2','0f77','0ffcc1','0f58c1','660f2a03','660f2ac1'):
        yield record(code,cw=0x37e,sw=0x8081),meta('x87_pending','pending_invalid',code)
    # Compare the defined save-image bytes; pointer fields, reserved bytes and
    # MXCSR_MASK are retained in memory but excluded from its canonical hash.
    for rc in range(4):
        for top in range(8):
            for name,code,kind in (('fxsave','0fae03',1),('fnstenv','d933',2),('fnsave','dd33',3)):
                yield record(code,cw=0x37f|rc<<10,sw=top<<11,memory_kind=kind),meta('fp_save',name,code,memory_kind=kind)
        fx=bytearray(64)
        struct.pack_into('<HHB',fx,0,0x37f|rc<<10,0,1)
        struct.pack_into('<I',fx,24,0x1f80|rc<<13)
        struct.pack_into('<QH',fx,32,*ONE)
        yield record('0fae0b',seed=0,mem=fx),meta('fp_restore','fxrstor','0fae0b')
        env=bytearray(64)
        struct.pack_into('<I',env,0,0x37f|rc<<10)
        struct.pack_into('<I',env,8,0xfffc)
        struct.pack_into('<QH',env,28,*ONE)
        yield record('dd23',seed=0,mem=env),meta('fp_restore','frstor','dd23')
    # Conditional moves: all condition combinations, including unordered.
    for first in (0xda,0xdb):
        for group in range(4):
            for flags in (0,1,4,0x40,0x45):
                code = bytes([first,0xc1+group*8])
                yield record(code,a=VALUES[2],b=VALUES[4],flags=0x202|flags), meta('x87_fcmov','fcmov',code)


def simd_cases(rng, count):
    # Reuse the exhaustive MXCSR matrix, remapping x86-64 XMM14/15 to IA-32 XMM0/1.
    for raw, old in focused_sse():
        r = bytearray(raw)
        code = bytes.fromhex(old['code'])
        if b'\x45' in code:
            code = code.replace(b'\x45',b'')
            code = code[:-1]+b'\xc1'
            r[176:208] = r[176+14*16:176+16*16]
        r[:16] = bytes([len(code)])+code.ljust(15,b'\xcc')
        struct.pack_into('<Q',r,144,0x202)
        extension = record('90')[440:]
        yield bytes(r)+extension, dict(meta('sse_'+old['family'].removeprefix('hardware_sse_'),old['scenario'],code),
                                      format=old['format'],mxcsr=old['mxcsr'])
    # Packed integer register and memory forms, saturation and shift boundaries.
    pats = (0,0xffffffffffffffff,0x8000800080008000,0x7fff7fff7fff7fff,
            0x8080808080808080,0x7f7f7f7f7f7f7f7f,1,7,8,15,16,31,32,63,64,65,255)
    for pfx in (b'',b'\x66'):
        for op in IOPS:
            for mem in (False,True):
                code = pfx+bytes([15,op,3 if mem else 0xc1])
                for j,p in enumerate(pats):
                    a,b = pats[(j+3)%len(pats)],p
                    xmm = [a,a,b,b]+[0x123456789abcdef]*28
                    yield record(code,a=(a,0xffff),b=(b,0xffff),xmm=xmm,mem=struct.pack('<QQ',b,b)), meta(
                        'sse_integer' if pfx else 'mmx_integer',f'{op:02x}',code,pattern=j,memory=mem)
        for op in (0x71,0x72,0x73):
            groups = (2,4,6) if op!=0x73 else ((2,3,6,7) if pfx else (2,6))
            for group in groups:
                for imm in (0,1,7,8,15,16,31,32,63,64,65,127,128,255):
                    code=pfx+bytes([15,op,0xc0|(group<<3),imm])
                    yield record(code,a=(pats[2],0xffff)),meta('simd_immediate','shift',code,imm=imm)
    for pfx,op,mods,immediate in [
        (p,op,(0xc1,3),False) for p in (b'',b'\x66') for op in (0x6e,0x7e,0x6f,0x7f)
    ]+[(p,0x70,(0xc1,3),True) for p in (b'',b'\x66',b'\xf3',b'\xf2')]+[
        (p,op,(0xc1,),True) for p in (b'',b'\x66') for op in (0xc4,0xc5)
    ]+[(p,0xd7,(0xc1,),False) for p in (b'',b'\x66')]+[
        (b'\xf3',0x7e,(0xc1,3),False),(b'\x66',0xd6,(0xc1,3),False),
        (b'\xf3',0xd6,(0xc1,),False),(b'\xf2',0xd6,(0xc1,),False),
        (b'',0xe7,(3,),False),(b'\x66',0xe7,(3,),False),
        (b'',0xf7,(0xc1,),False),(b'\x66',0xf7,(0xc1,),False),
        (b'',0xc3,(3,),False),(b'',0x2b,(3,),False),(b'\x66',0x2b,(3,),False),
    ]:
        for mod in mods:
            for imm in (range(256) if immediate else range(4)):
                code=pfx+bytes([15,op,mod])+(bytes([imm]) if immediate else b'')
                yield record(code,a=(pats[2],0xffff),b=(pats[3],0xffff),mem=bytes(range(64))),meta(
                    'simd_transfer',f'{pfx.hex()}0f{op:02x}',code,imm=imm)
    # SSE arithmetic/conversions/shuffles/moves, all mandatory-prefix forms below.
    forms=[]
    for pfx in (b'',b'\x66',b'\xf3',b'\xf2'):
        for op in (0x51,0x58,0x59,0x5c,0x5d,0x5e,0x5f,0x5a,0xc2,0x10,0x11):
            forms.append((pfx,op))
    forms += [(p,op) for p in (b'',b'\x66') for op in (0x2e,0x2f,0x54,0x55,0x56,0x57,0xc6,0x14,0x15,0x28,0x29)]
    forms += [(p,op) for p in (b'',b'\x66',b'\xf3',b'\xf2') for op in (0x2a,0x2c,0x2d)]
    forms += [(p,0x5b) for p in (b'',b'\x66',b'\xf3')]+[(p,0xe6) for p in (b'\x66',b'\xf3',b'\xf2')]
    forms += [(p,op) for p in (b'',b'\xf3') for op in (0x52,0x53)]
    for i in range(max(count,len(forms)*16)):
        pfx,op=forms[i%len(forms)]
        bits=64 if pfx in (b'\x66',b'\xf2') else 32
        c=constants(bits)
        choices=list(c.values())+[0,1,c['one']+1,c['normal']-1]
        lane=lambda: rng.choice(choices) if rng.randrange(4) else rng.getrandbits(bits)
        def packed(): return sum(lane() << (bits*k) for k in range(128//bits))
        a,b=packed(),packed()
        xmm=[a&((1<<64)-1),a>>64,b&((1<<64)-1),b>>64]+[0x13579bdf02468ace]*28
        mem=bool(rng.randrange(2));code=pfx+bytes([15,op,3 if mem else 0xc1])
        if op in (0xc2,0xc6): code+=bytes([rng.randrange(8 if op==0xc2 else 256)])
        mxcsr=(rng.choice((63,62,61,59,55,47,31,0))<<7)|(rng.randrange(4)<<13)|rng.choice((0,0x40,0x8000,0x8040))
        kw={} if op not in (0x52,0x53) else dict(policy='observe',reason='RCP/RSQRT are approximations, not correctly rounded operations')
        yield record(code,xmm=xmm,mxcsr=mxcsr,mem=b.to_bytes(16,'little')),meta('sse_random',f'{op:02x}',code,**kw)
    # Alignment, invalid MXCSR bits, fences, and valid EMMS. Later ISA extensions
    # are intentionally absent: modern hardware legitimately implements them.
    for code in ('0f2803','0f2903','660f6f03','660f7f03','0f1003','0f1103','f30f6f03','f30f7f03'):
        for offset in (0,1,2,4,8,15):
            for perms in ((0x67,0x67),(0x65,0x67),(0,0x67)):
                yield record(code,address=0x10000+offset,permissions=perms),meta('simd_memory_fault','move',code,offset=offset)
    for mx in (0x1f80,0xffff,0x11f80,0x80001f80):
        yield record('0fae13',mem=struct.pack('<I',mx)),meta('sse_control','ldmxcsr','0fae13')
    for code in ('0fae1b','0faee8','0faef0','0faef8','0f77'):
        yield record(code),meta('sse_control','control',code)


# Case families and the CPUID features they require (native_fp.FEATURES names). The
# baseline (x87, MMX, SSE, SSE2 on an x86-64 machine) needs none. Later ISA extensions add
# their own generator here, e.g. (sse3_cases, ('sse3',)).
FAMILIES = [
    (x87_cases, ()),
    (simd_cases, ()),
]


# Sse workstream: SSE3 (with FISTTP), SSSE3, SSE4.1, SSE4.2, SSE4a, MisalignSse (fp_cases_sse.py)
import fp_cases_sse  # noqa: E402
FAMILIES += [(lambda rng, n, name=name: getattr(fp_cases_sse, name)(rng, n), (feature,)) for name, feature in
             (('sse3_cases', 'sse3'), ('ssse3_cases', 'ssse3'), ('sse41_cases', 'sse41'),
              ('sse42_cases', 'sse42'), ('sse4a_cases', 'sse4a'), ('misalign_cases', 'misalignSse'))]


def cases(seed=20261111, count=10000):
    rng=random.Random(seed)
    for family, requires in FAMILIES:
        for raw, m in family(rng, count):
            yield raw, (dict(m, requires=list(requires)) if requires else m)
