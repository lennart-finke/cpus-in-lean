#!/usr/bin/env python3
"""Deterministic long-mode instruction vectors: widths, REX, aliases, addressing,
flags, privilege faults, and page permission/crossing faults. No oracle outputs are
computed here; QEMU and Lean consume identical initial bytes and registers.
"""
import collections
import json
import random
import struct
import sys
from pathlib import Path

ARITH=0x8d5
MASK=(1<<64)-1

def generate(count, seed, dest):
    rng=random.Random(seed)
    vectors=bytearray(); meta=[]
    families=['alu','alu_imm','mov','mov_imm','shift','unary','imul','extend','setcc','cmov','xadd','cmpxchg','bswap','lea','stack','invalid','privileged','div','mul','bit_scan','bit','double_shift','string','branch','call','loop','addressing','lock','simd_move','simd_integer','simd_shuffle','simd_shift','simd_float','simd_convert','simd_compare','test','incdec','xchg','extend_acc','flags','imul_imm','push_imm','stack_mem','indirect','ret','io','segment']
    for k in range(count):
        family=families[k % len(families)]
        patch_return=False
        xmm=[rng.getrandbits(64) for _ in range(32)]
        mxcsr=0x1f80 | rng.choice([0,0x40,0x8000,0x8040]) | (rng.randrange(4)<<13)
        # QEMU TCG does not deliver unmasked SIMD traps (upstream issue #215).
        # CheckMain exercises architectural exception delivery independently.
        width=rng.choice([1,2,4,8]); sizebits=width*8
        regs=[rng.getrandbits(64) for _ in range(16)]
        regs[4]=0x8800+rng.randrange(0,128)*8
        flags=2 | (rng.getrandbits(12)&ARITH)
        if rng.randrange(20)==0: flags |= 0x100
        flagmask=ARITH | 0x100 | 0x400
        reg=rng.randrange(16); rm=rng.randrange(16)
        rex=0x40 | (8 if width==8 else 0) | (4 if reg>=8 else 0) | (1 if rm>=8 else 0)
        # Sometimes omit REX to exercise AH/CH/DH/BH.
        if width!=8 and reg<8 and rm<8 and rng.randrange(2)==0: rex=0
        prefix=(b'\x66' if width==2 else b'') + (bytes([rex]) if rex else b'')
        memory=rng.randrange(3)==0
        disp=b''
        if memory:
            addr=rng.choice([0x8000+rng.randrange(8192-width+1),0x8ffd,0x8ffe,0x8fff])
            regs[rm]=addr
            if rm%8==4:
                # SIB base with no index; REX.X is absent.
                modrm=bytes([0x04|((reg&7)<<3),0x24])
            elif rm%8==5:
                modrm=bytes([0x40|((reg&7)<<3)|(rm&7),0])
            else: modrm=bytes([((reg&7)<<3)|(rm&7)])
        else: modrm=bytes([0xc0|((reg&7)<<3)|(rm&7)])
        def group(g):
            nonlocal prefix, rex
            rex &= ~4
            prefix=(b'\x66' if width==2 else b'')+(bytes([rex]) if rex else b'')
            return bytes([(modrm[0]&0xc7)|(g<<3)])+modrm[1:]
        def immediate(n): return rng.getrandbits(n*8).to_bytes(n,'little')
        if family=='alu':
            operation=rng.randrange(8); form=rng.randrange(2)*2+(width!=1)
            code=prefix+bytes([operation*8+form])+modrm
        elif family=='alu_imm':
            g=rng.randrange(8); short=width!=1 and rng.randrange(2)==0
            md=group(g)
            code=prefix+bytes([0x80 if width==1 else 0x83 if short else 0x81])+md+immediate(1 if width==1 or short else min(width,4))
        elif family=='mov': code=prefix+bytes([rng.choice([0x88,0x8a])+(width!=1)])+modrm
        elif family=='mov_imm':
            rex=(0x48 if width==8 else 0x40)|(1 if rm>=8 else 0)
            if rm<8 and width!=8 and rng.randrange(2)==0: rex=0
            prefix=(b'\x66' if width==2 else b'')+(bytes([rex]) if rex else b'')
            code=prefix+bytes([(0xb0 if width==1 else 0xb8)+(rm&7)])+immediate(width)
        elif family=='shift':
            g=rng.randrange(8); cnt=rng.choice([0,1,2,7,8,15,16,31,32,63,64,255])
            md=group(g); code=prefix+bytes([0xc0+(width!=1)])+md+bytes([cnt])
            cnt &= 63 if width==8 else 31
            if cnt:
                if g<4:
                    flagmask &= ~(0x800 if cnt!=1 else 0)
                else:
                    flagmask &= ~0x10
                    if cnt!=1: flagmask &= ~0x800
                    if cnt>=sizebits: flagmask &= ~1
        elif family=='unary':
            g=rng.choice([2,3]);md=group(g);code=prefix+bytes([0xf6+(width!=1)])+md
        elif family=='imul':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            code=prefix+b'\x0f\xaf'+modrm;flagmask &= ~0xd4
        elif family=='extend':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            code=prefix+b'\x0f'+bytes([rng.choice([0xb6,0xb7,0xbe,0xbf])])+modrm
        elif family=='setcc': code=prefix+b'\x0f'+bytes([0x90+rng.randrange(16)])+modrm
        elif family=='cmov':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            code=prefix+b'\x0f'+bytes([0x40+rng.randrange(16)])+modrm
        elif family=='xadd': code=prefix+b'\x0f'+bytes([0xc0+(width!=1)])+modrm
        elif family=='cmpxchg': code=prefix+b'\x0f'+bytes([0xb0+(width!=1)])+modrm
        elif family=='bswap':
            width=rng.choice([4,8]);prefix=bytes([0x40|(8 if width==8 else 0)|(1 if rm>=8 else 0)])
            code=prefix+b'\x0f'+bytes([0xc8+(rm&7)])
        elif family=='lea':
            # RIP-relative, absolute address-size override, and extended SIB addressing.
            width=rng.choice([2,4,8]); rex=0x40|(8 if width==8 else 0)|(4 if reg>=8 else 0)
            prefix=(b'\x66' if width==2 else b'')
            if rng.randrange(2): prefix+=b'\x67'
            code=prefix+bytes([rex,0x8d,0x05|((reg&7)<<3)])+immediate(4)
        elif family=='stack':
            width=rng.choice([2,8]);prefix=(b'\x66' if width==2 else b'')+bytes([0x40|(1 if rm>=8 else 0)])
            code=prefix+bytes([rng.choice([0x50,0x58])+(rm&7)])
        elif family=='invalid': code=rng.choice([b'\x0f\x0b',b'\x60',b'\x61',b'\x27',b'\x62\xc0',b'\xf0\x90',b'\xf0\x48\x01\xc0'])
        elif family=='privileged': code=rng.choice([b'\xf4',b'\xfa',b'\xfb',b'\x0f\x20\xc0',b'\x0f\x30',b'\x0f\x32',b'\x0f\x01\xf8'])
        elif family in ('div','mul'):
            g=rng.choice([6,7] if family=='div' else [4,5]);md=group(g)
            code=prefix+bytes([0xf6+(width!=1)])+md
            flagmask &= ~ARITH if family=='div' else ~0xd4
            if family=='div' and rng.randrange(2) and not (memory and rm==2): regs[2]=0
        elif family=='bit_scan':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            code=prefix+b'\x0f'+bytes([rng.choice([0xbc,0xbd])])+modrm
            flagmask &= ~0x895
            # Avoid undefined destination on a zero source.
            if not memory: regs[rm]|=1
        elif family=='bit':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            g=rng.randrange(4)
            if rng.randrange(2):
                md=group(g+4);code=prefix+b'\x0f\xba'+md+immediate(1)
            else:
                # Keep the signed memory bit-string offset inside the shared data area.
                if memory and reg==rm:
                    memory=False;modrm=bytes([0xc0|((reg&7)<<3)|(rm&7)])
                regs[reg]=rng.randrange(-64,65) & ((1<<(width*8))-1)
                if memory: regs[rm]=0x8800
                code=prefix+b'\x0f'+bytes([0xa3+g*8])+modrm
            flagmask &= ~0x894  # OF/SF/AF/PF undefined; ZF unchanged.
        elif family=='double_shift':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            cnt=rng.randrange(width*8)
            code=prefix+b'\x0f'+bytes([rng.choice([0xa4,0xac])])+modrm+bytes([cnt])
            if cnt:
                flagmask &= ~0x10
                if cnt!=1: flagmask &= ~0x800
        elif family=='string':
            memory=True
            # Small counts exercise both directions, REP stopping conditions and restart.
            regs[1]=rng.randrange(4);regs[6]=0x8108;regs[7]=0x9008
            if rng.randrange(2): flags |= 0x400
            code=rng.choice([b'',b'\xf2',b'\xf3'])+prefix+bytes([rng.choice([0xa4,0xa6,0xaa,0xac,0xae])+(width!=1)])
            # Same documented QEMU exclusion as the i386 suite: REP+TF may
            # report the instruction start after the final iteration.
            if code[0] in (0xf2,0xf3): flags &= ~0x100
        elif family=='branch':
            cc=rng.randrange(16)
            if rng.randrange(2): code=bytes([0x70+cc,32])
            else: code=b'\x0f'+bytes([0x80+cc])+struct.pack('<i',-32)
        elif family=='call': code=b'\xe8'+struct.pack('<i',32)
        elif family=='loop':
            regs[1]=rng.choice([0,1,2,0x100000000])
            code=rng.choice([b'',b'\x67'])+bytes([rng.choice([0xe0,0xe1,0xe2,0xe3]),32])
        elif family=='addressing':
            memory=False
            width=rng.choice([2,4,8]);base=rng.randrange(16);index=rng.randrange(16);scale=rng.randrange(4)
            rex=0x40|(8 if width==8 else 0)|(4 if reg>=8 else 0)|(2 if index>=8 else 0)|(1 if base>=8 else 0)
            prefix=(b'\x66' if width==2 else b'')+rng.choice([b'',b'\x67'])+bytes([rex])
            code=prefix+bytes([0x8d,0x84|((reg&7)<<3),(scale<<6)|((index&7)<<3)|(base&7)])+immediate(4)
        elif family=='lock':
            code=b'\xf0'+prefix+bytes([0x00+(width!=1)])+modrm
        elif family=='test':
            code=prefix+bytes([0x84+(width!=1)])+modrm
            flagmask &= ~0x10
        elif family=='incdec':
            md=group(rng.randrange(2));code=prefix+bytes([0xfe+(width!=1)])+md
        elif family=='xchg': code=prefix+bytes([0x86+(width!=1)])+modrm
        elif family=='extend_acc':
            code=prefix+bytes([rng.choice([0x98,0x99])])
        elif family=='flags':
            code=rng.choice([b'\x9e',b'\x9f',b'\xf5',b'\xf8',b'\xf9',b'\xfc',b'\xfd',b'\x9c',b'\x9d'])
            # POPF's TF affects the following instruction, outside this vector.
            if code==b'\x9d':
                patch_return=True;regs[4]=0x8800
        elif family=='imul_imm':
            if width==1: width=4;prefix=bytes([rex & ~8]) if rex else b''
            short=rng.randrange(2)
            code=prefix+bytes([0x6b if short else 0x69])+modrm+immediate(1 if short else min(width,4))
            flagmask &= ~0xd4
        elif family=='push_imm':
            narrow=rng.randrange(2)
            code=(b'\x66' if width==2 else b'')+bytes([0x6a if narrow else 0x68])+immediate(1 if narrow else 2 if width==2 else 4)
        elif family=='stack_mem':
            rex=(rex & ~12) | 0x40
            prefix=(b'\x66' if width==2 else b'')+bytes([rex])
            md=bytes([(modrm[0]&0xc7)|(6<<3)])+modrm[1:]
            if rng.randrange(2): code=prefix+b'\xff'+md
            else: code=prefix+b'\x8f'+bytes([modrm[0]&0xc7])+modrm[1:]
        elif family=='indirect':
            memory=False;regs[rm]=0x20180
            code=bytes([0x40|(1 if rm>=8 else 0),0xff,0xc0|(rng.choice([2,4])<<3)|(rm&7)])
        elif family=='ret':
            memory=True;patch_return=True;regs[4]=0x8800
            code=rng.choice([b'\xc3',b'\xc2\x20\x00'])
        elif family=='io':
            code=rng.choice([b'\xec',b'\xed',b'\xee',b'\xef',b'\xe4\x80',b'\xe6\x80'])
        elif family=='segment':
            memory=False;which=rng.choice([0,2,3,4,5]);load=rng.randrange(2)
            regs[rm]=rng.choice([0,0x10,0x1b,0x23,0x28,0xffff])
            code=bytes([0x40|(1 if rm>=8 else 0),0x8e if load else 0x8c,0xc0|(which<<3)|(rm&7)])
        elif family.startswith('simd_'):
            # Mandatory prefixes select instructions independently of REX.W.
            mandatory=b''; rex=0x40 | (4 if reg>=8 else 0) | (1 if rm>=8 else 0)
            immediate_bytes=b''
            if memory: regs[rm]=rng.choice([0x8100,0x8800,0x8ff0,0x8ff8,0x8fff])
            if family=='simd_move':
                mandatory,op=rng.choice([(p,o) for p in [b'',b'\x66',b'\xf2',b'\xf3'] for o in [0x10,0x11]]+[(p,o) for p in [b'',b'\x66'] for o in [0x28,0x29]]+[(p,o) for p in [b'\x66',b'\xf3'] for o in [0x6f,0x7f]]+[(b'\x66',0x6e),(b'\x66',0x7e),(b'\xf3',0x7e),(b'\x66',0xd6)])
                if op in (0x6e,0x7e) and rng.randrange(2): rex |= 8
            elif family=='simd_integer':
                mandatory=b'\x66'
                op=rng.choice([0xdb,0xdf,0xeb,0xef,0x60,0x61,0x62,0x68,0x69,0x6a,0x6c,0x6d,0x74,0x75,0x76,0x64,0x65,0x66,0xd4,0xd5,0xda,0xde,0xea,0xee,0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe])
            elif family=='simd_shuffle':
                mandatory,op=rng.choice([(b'\x66',0x70),(b'\xf2',0x70),(b'\xf3',0x70),(b'',0xc6),(b'\x66',0xc6)])
                immediate_bytes=immediate(1)
            elif family=='simd_shift':
                mandatory=b'\x66';op=rng.choice([0x71,0x72,0x73])
                g=rng.choice([2,4,6] if op!=0x73 else [2,3,6,7])
                rex &= ~4;modrm=bytes([0xc0|(g<<3)|(rm&7)]);memory=False
                immediate_bytes=bytes([rng.choice([0,1,7,8,15,16,31,32,63,64,127,128,255])])
            elif family in ('simd_float','simd_compare','simd_convert'):
                mandatory=rng.choice([b'',b'\x66',b'\xf2',b'\xf3'])
                if family=='simd_float':
                    op=rng.choice([0x51,0x58,0x59,0x5c,0x5d,0x5e,0x5f])
                    # TCG min/max compares DAZ-adjusted values but returns original
                    # denormal bits. Preserve architectural DAZ tests in CheckMain.
                    if op in (0x5d,0x5f): mxcsr &= ~0x40
                elif family=='simd_compare':
                    op=rng.choice([0xc2,0x2e,0x2f])
                    if op==0xc2: immediate_bytes=immediate(1)
                    else: mandatory=rng.choice([b'',b'\x66'])
                else:
                    op=rng.choice([0x2a,0x2c,0x2d,0x5a]);mandatory=rng.choice([b'\xf2',b'\xf3'])
                    if rng.randrange(2): rex |= 8
                bits=64 if mandatory in (b'\x66',b'\xf2') else 32
                special=([0,1,0x8000000000000000,0x7ff0000000000000,0xfff0000000000000,0x7ff8000000000123,0x7ff0000000000123,0x0010000000000000,0x000fffffffffffff,0x7fefffffffffffff,0x3ff0000000000000] if bits==64 else [0,1,0x80000000,0x7f800000,0xff800000,0x7fc00123,0x7f800123,0x00800000,0x007fffff,0x7f7fffff,0x3f800000])
                for r in (reg,rm):
                    value=0
                    for lane in range(128//bits):
                        v=rng.choice(special) if rng.randrange(2) else rng.getrandbits(bits)
                        value |= v<<(lane*bits)
                    xmm[r*2]=value&MASK;xmm[r*2+1]=value>>64
            code=mandatory+bytes([rex,0x0f,op])+modrm+immediate_bytes
        else: raise AssertionError(family)
        assert len(code)<=15
        ptes=[0x67,0x67]
        if memory and rng.randrange(5)==0:
            ptes[rng.randrange(2)]=rng.choice([0,1,3,5,7,0x25,0x27,0x8000000000000007])
        vectors += struct.pack('<16s16QQII2Q32QII', bytes([len(code)])+code+b'\xcc'*(15-len(code)),*regs,flags,rng.randrange(1,2**32),rng.randrange(2)|(2 if patch_return else 0),*ptes,*xmm,mxcsr,0)
        meta.append({'family':family,'code':code.hex(),'mask':flagmask,'seed':seed,'index':k})
    Path(str(dest)+'.bin').write_bytes(vectors)
    Path(str(dest)+'.json').write_text(json.dumps(meta))
    print(json.dumps(dict(collections.Counter(x['family'] for x in meta)),sort_keys=True))

if __name__=='__main__': generate(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
