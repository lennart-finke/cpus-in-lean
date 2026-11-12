#!/usr/bin/env python3
"""Instruction forms of the Zen 2 ISA beyond the core model, for test generation.

IMPLEMENTED lists the 0F / 0F 38 / 0F 3A / VEX forms of the EPYC 7742 (Zen 2) beyond the core model
(x86_32/X86/Exec.lean), grouped by the x86_32/X86/Ext/ module that implements them; the model
implements every row. Their 'ext' generators (gen_<owner>.py, xsave_gen.py, gen.py's ext_form) and the system tests
(sys/t_simd.c) test them against QEMU's EPYC-Rome CPU (test/qemu-cpu.sh); gen.py's 'ud' family
generates encodings that match no row and expects #UD from both. test_isa_forms.py cross-checks the
rows against LLVM's disassembler (-mcpu=znver2).

A form is (encoding, map, pp, opcode byte) plus an optional ModRM constraint:
  encoding  'legacy', 'vex', or 'legacy-lock' (the legacy form with a LOCK prefix)
  map       1 = 0F, 2 = 0F 38, 3 = 0F 3A
  pp        mandatory prefix: 0 none, 1 = 66, 2 = F3, 3 = F2 (as Inst.pp); None = any
  ops       opcode bytes
  modrm     None, or (mod, reg) with mod in {'mem', 'reg', None} and reg 0..7 or None, or
            (mod, reg, rms) with the tuple of allowed ModRM.rm values
  L, W      (VEX only, optional) the required VEX.L / VEX.W (0 or 1), None = any
Rows may be broader than the exact set of Zen 2 forms (e.g. a whole VEX opcode range; the 'ud' family
then does not test the difference); they must not be narrower, or the 'ud' family would generate a
form that Zen 2 (and QEMU) executes.
"""
from collections import namedtuple

Form = namedtuple('Form', 'feature owner encoding map pp ops modrm L W', defaults=(None, None))

def F(feature, owner, encoding, map_, pp, ops, modrm=None, L=None, W=None):
    return Form(feature, owner, encoding, map_, pp, tuple(ops), modrm, L, W)

def rng(a, b):
    return list(range(a, b + 1))

# The Zen 2 forms beyond the core model (owner = module in x86_32/X86/Ext/, which implements them).
IMPLEMENTED = [
    # --- Avx (x86_32/X86/Ext/Avx.lean; generator: gen_avx.py) --- exactly the AVX forms of Zen 2
    # (mandatory prefix, VEX.L, VEX.W, ModRM.mod/reg), so the 'ud' family tests their neighbours as #UD
    F('avx', 'Avx', 'vex', 1, 0, [0x10, 0x11, 0x14, 0x15, 0x28, 0x29, 0x2E, 0x2F] + rng(0x51, 0x5F) + [0xC2, 0xC6]),
    F('avx', 'Avx', 'vex', 1, 0, [0x2B], ('mem', None)),
    F('avx', 'Avx', 'vex', 1, 0, [0x50], ('reg', None)),
    F('avx', 'Avx', 'vex', 1, 0, [0x12, 0x16], None, 0),            # VMOVLPS/VMOVHLPS, VMOVHPS/VMOVLHPS
    F('avx', 'Avx', 'vex', 1, 0, [0x13, 0x17], ('mem', None), 0),
    F('avx', 'Avx', 'vex', 1, 0, [0x77]),                           # VZEROUPPER, VZEROALL
    F('avx', 'Avx', 'vex', 1, 0, [0xAE], ('mem', 2), 0),            # VLDMXCSR
    F('avx', 'Avx', 'vex', 1, 0, [0xAE], ('mem', 3), 0),            # VSTMXCSR
    F('avx', 'Avx', 'vex', 1, 1, [0x10, 0x11, 0x14, 0x15, 0x28, 0x29, 0x2E, 0x2F, 0x51] + rng(0x54, 0x5F) +
      [0x6F, 0x7C, 0x7D, 0x7F, 0xC2, 0xC6, 0xD0, 0xE6]),
    F('avx', 'Avx', 'vex', 1, 1, [0x2B, 0xE7], ('mem', None)),
    F('avx', 'Avx', 'vex', 1, 1, [0x50], ('reg', None)),
    F('avx', 'Avx', 'vex', 1, 1, [0x12, 0x13, 0x16, 0x17], ('mem', None), 0),
    F('avx', 'Avx', 'vex', 1, 1, rng(0x60, 0x6D) + [0x6E, 0x70, 0x74, 0x75, 0x76, 0x7E, 0xC4] + rng(0xD1, 0xD6) +
      rng(0xD8, 0xDF) + rng(0xE0, 0xE5) + rng(0xE8, 0xEF) + rng(0xF1, 0xF6) + rng(0xF8, 0xFE), None, 0),
    F('avx', 'Avx', 'vex', 1, 1, [0x71, 0x72], ('reg', 2), 0),      # VPSRLW/D imm
    F('avx', 'Avx', 'vex', 1, 1, [0x71, 0x72], ('reg', 4), 0),      # VPSRAW/D imm
    F('avx', 'Avx', 'vex', 1, 1, [0x71, 0x72, 0x73], ('reg', 6), 0),  # VPSLLW/D/Q imm
    F('avx', 'Avx', 'vex', 1, 1, [0x73], ('reg', 2), 0),            # VPSRLQ imm
    F('avx', 'Avx', 'vex', 1, 1, [0x73], ('reg', 3), 0),            # VPSRLDQ
    F('avx', 'Avx', 'vex', 1, 1, [0x73], ('reg', 7), 0),            # VPSLLDQ
    F('avx', 'Avx', 'vex', 1, 1, [0xC5, 0xD7, 0xF7], ('reg', None), 0),
    F('avx', 'Avx', 'vex', 1, 2, [0x10, 0x11, 0x12, 0x16, 0x2A, 0x2C, 0x2D, 0x51, 0x52, 0x53, 0x58, 0x59, 0x5A, 0x5B,
      0x5C, 0x5D, 0x5E, 0x5F, 0x6F, 0x7F, 0xC2, 0xE6]),
    F('avx', 'Avx', 'vex', 1, 2, [0x70, 0x7E], None, 0),            # VPSHUFHW, VMOVQ xmm, xmm/m64
    F('avx', 'Avx', 'vex', 1, 3, [0x10, 0x11, 0x12, 0x2A, 0x2C, 0x2D, 0x51, 0x58, 0x59, 0x5A, 0x5C, 0x5D, 0x5E, 0x5F,
      0x7C, 0x7D, 0xC2, 0xD0, 0xE6]),
    F('avx', 'Avx', 'vex', 1, 3, [0xF0], ('mem', None)),            # VLDDQU
    F('avx', 'Avx', 'vex', 1, 3, [0x70], None, 0),                  # VPSHUFLW
    F('avx', 'Avx', 'vex', 2, 1, rng(0x00, 0x0B) + rng(0x1C, 0x1E) + rng(0x20, 0x25) + [0x28, 0x29, 0x2B] +
      rng(0x30, 0x35) + rng(0x37, 0x41) + rng(0xDB, 0xDF), None, 0),
    F('avx', 'Avx', 'vex', 2, 1, [0x2A], ('mem', None), 0),         # VMOVNTDQA
    F('avx', 'Avx', 'vex', 2, 1, [0x0C, 0x0D, 0x0E, 0x0F], None, None, 0),   # VPERMILPS/PD, VTESTPS/PD
    F('avx', 'Avx', 'vex', 2, 1, [0x17]),                           # VPTEST
    F('avx', 'Avx', 'vex', 2, 1, [0x18], ('mem', None), None, 0),   # VBROADCASTSS m32
    F('avx', 'Avx', 'vex', 2, 1, [0x19, 0x1A], ('mem', None), 1, 0),  # VBROADCASTSD m64, VBROADCASTF128
    F('avx', 'Avx', 'vex', 2, 1, rng(0x2C, 0x2F), ('mem', None), None, 0),   # VMASKMOVPS/PD
    F('avx', 'Avx', 'vex', 3, 1, [0x04, 0x05, 0x4A, 0x4B], None, None, 0),   # VPERMILPS/PD imm, VBLENDVPS/PD
    F('avx', 'Avx', 'vex', 3, 1, [0x06, 0x18, 0x19], None, 1, 0),   # VPERM2F128, VINSERTF128, VEXTRACTF128
    F('avx', 'Avx', 'vex', 3, 1, [0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x40]),
    F('avx', 'Avx', 'vex', 3, 1, [0x0E, 0x0F, 0x14, 0x15, 0x16, 0x17, 0x20, 0x21, 0x22, 0x41, 0x42, 0x44, 0x60,
      0x61, 0x62, 0x63, 0xDF], None, 0),
    F('avx', 'Avx', 'vex', 3, 1, [0x4C], None, 0, 0),               # VPBLENDVB
    # --- Avx2 (x86_32/X86/Ext/Avx2.lean; generator: gen_avx2.py) --- exactly the AVX2, FMA3 and F16C
    # forms of Zen 2 (VEX.L, VEX.W, ModRM.mod/reg), so the 'ud' family tests their neighbours as #UD
    F('avx2', 'Avx2', 'vex', 1, 1, rng(0x60, 0x6D) + [0x70, 0x74, 0x75, 0x76] + rng(0xD1, 0xD5) + rng(0xD8, 0xDF) +
      rng(0xE0, 0xE5) + rng(0xE8, 0xEF) + rng(0xF1, 0xF6) + rng(0xF8, 0xFE), None, 1),
    F('avx2', 'Avx2', 'vex', 1, 1, [0x71, 0x72], ('reg', 2), 1),     # VPSRLW/D ymm, imm
    F('avx2', 'Avx2', 'vex', 1, 1, [0x71, 0x72], ('reg', 4), 1),     # VPSRAW/D ymm, imm
    F('avx2', 'Avx2', 'vex', 1, 1, [0x71, 0x72, 0x73], ('reg', 6), 1),  # VPSLLW/D/Q ymm, imm
    F('avx2', 'Avx2', 'vex', 1, 1, [0x73], ('reg', 2), 1),           # VPSRLQ ymm, imm
    F('avx2', 'Avx2', 'vex', 1, 1, [0x73], ('reg', 3), 1),           # VPSRLDQ ymm
    F('avx2', 'Avx2', 'vex', 1, 1, [0x73], ('reg', 7), 1),           # VPSLLDQ ymm
    F('avx2', 'Avx2', 'vex', 1, 1, [0xD7], ('reg', None), 1),        # VPMOVMSKB r32, ymm
    F('avx2', 'Avx2', 'vex', 1, 2, [0x70], None, 1),                 # VPSHUFHW ymm
    F('avx2', 'Avx2', 'vex', 1, 3, [0x70], None, 1),                 # VPSHUFLW ymm
    F('avx2', 'Avx2', 'vex', 2, 1, rng(0x00, 0x0B) + rng(0x1C, 0x1E) + rng(0x20, 0x25) + [0x28, 0x29, 0x2B] +
      rng(0x30, 0x35) + rng(0x37, 0x40), None, 1),
    F('avx2', 'Avx2', 'vex', 2, 1, [0x2A], ('mem', None), 1),        # VMOVNTDQA ymm
    F('avx2', 'Avx2', 'vex', 2, 1, [0x16, 0x36], None, 1, 0),        # VPERMPS, VPERMD
    F('avx2', 'Avx2', 'vex', 2, 1, [0x18], ('reg', None), None, 0),  # VBROADCASTSS xmm/ymm, xmm
    F('avx2', 'Avx2', 'vex', 2, 1, [0x19], ('reg', None), 1, 0),     # VBROADCASTSD ymm, xmm
    F('avx2', 'Avx2', 'vex', 2, 1, [0x45, 0x47]),                    # VPSRLVD/Q, VPSLLVD/Q
    F('avx2', 'Avx2', 'vex', 2, 1, [0x46, 0x58, 0x59, 0x78, 0x79], None, None, 0),   # VPSRAVD, VPBROADCASTx
    F('avx2', 'Avx2', 'vex', 2, 1, [0x5A], ('mem', None), 1, 0),     # VBROADCASTI128
    F('avx2', 'Avx2', 'vex', 2, 1, [0x8C, 0x8E], ('mem', None)),     # VPMASKMOVD/Q
    F('avx2', 'Avx2', 'vex', 2, 1, rng(0x90, 0x93), ('mem', None, (4,))),   # gathers (VSIB)
    F('fma', 'Avx2', 'vex', 2, 1, rng(0x96, 0x9F) + rng(0xA6, 0xAF) + rng(0xB6, 0xBF)),   # FMA3
    F('f16c', 'Avx2', 'vex', 2, 1, [0x13], None, None, 0),           # VCVTPH2PS
    F('f16c', 'Avx2', 'vex', 3, 1, [0x1D], None, None, 0),           # VCVTPS2PH
    F('avx2', 'Avx2', 'vex', 3, 1, [0x00, 0x01], None, 1, 1),        # VPERMQ, VPERMPD
    F('avx2', 'Avx2', 'vex', 3, 1, [0x02], None, None, 0),           # VPBLENDD
    F('avx2', 'Avx2', 'vex', 3, 1, [0x0E, 0x0F, 0x42], None, 1),     # VPBLENDW, VPALIGNR, VMPSADBW ymm
    F('avx2', 'Avx2', 'vex', 3, 1, [0x4C], None, 1, 0),              # VPBLENDVB ymm
    F('avx2', 'Avx2', 'vex', 3, 1, [0x38, 0x39, 0x46], None, 1, 0),  # VINSERTI128, VEXTRACTI128, VPERM2I128
    # --- Svm (generator: test/gen_svm.py): 0F 01 D8..DF, VMRUN, VMMCALL, VMLOAD, VMSAVE, STGI, CLGI,
    # SKINIT, INVLPGA (any mandatory prefix: none changes them on Zen 2 outside an SEV-ES guest)
    F('svm', 'Svm', 'legacy', 1, None, [0x01], ('reg', 3, (0, 1, 2, 3, 4, 5))),
    F('skinit', 'Svm', 'legacy', 1, None, [0x01], ('reg', 3, (6,))),
    F('svm', 'Svm', 'legacy', 1, None, [0x01], ('reg', 3, (7,))),
    # --- Sys (generator: test/gen_sys.py) ---
    F('syscall', 'Sys', 'legacy', 1, None, [0x05, 0x07]),
    F('sep', 'Sys', 'legacy', 1, None, [0x34, 0x35]),
    F('smap', 'Sys', 'legacy', 1, None, [0x01], ('reg', 1, (2,))),    # 0F 01 CA CLAC
    F('smap', 'Sys', 'legacy', 1, None, [0x01], ('reg', 1, (3,))),    # 0F 01 CB STAC
    F('altMovCr8', 'Sys', 'legacy-lock', 1, None, [0x20, 0x22], (None, 0)),
    # --- Xsave (generated by xsave_gen.py; NP forms only: with 66/F2/F3 they are #UD) ---
    F('xsave', 'Xsave', 'legacy', 1, 0, [0x01], ('reg', 2, (0, 1))),     # XGETBV, XSETBV
    F('xsave', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 4)),
    F('xsave', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 5)),
    F('xsaveopt', 'Xsave', 'legacy', 1, 0, [0xAE], ('mem', 6)),
    F('xsaves', 'Xsave', 'legacy', 1, 0, [0xC7], ('mem', 3)),
    F('xsavec', 'Xsave', 'legacy', 1, 0, [0xC7], ('mem', 4)),
    F('xsaves', 'Xsave', 'legacy', 1, 0, [0xC7], ('mem', 5)),
    # --- Sse (exact forms; generator: gen_sse.py) ---
    F('sse3', 'Sse', 'legacy', 1, 2, [0x12, 0x16]),                 # MOVSLDUP, MOVSHDUP
    F('sse3', 'Sse', 'legacy', 1, 3, [0x12]),                       # MOVDDUP
    F('sse3', 'Sse', 'legacy', 1, 3, [0xF0], ('mem', None)),        # LDDQU
    F('sse3', 'Sse', 'legacy', 1, 1, [0x7C, 0x7D, 0xD0]),           # HADDPD, HSUBPD, ADDSUBPD
    F('sse3', 'Sse', 'legacy', 1, 3, [0x7C, 0x7D, 0xD0]),           # HADDPS, HSUBPS, ADDSUBPS
    F('sse4a', 'Sse', 'legacy', 1, 1, [0x78], ('reg', 0)),          # EXTRQ xmm, imm8, imm8
    F('sse4a', 'Sse', 'legacy', 1, 3, [0x78], ('reg', None)),       # INSERTQ xmm, xmm, imm8, imm8
    F('sse4a', 'Sse', 'legacy', 1, 1, [0x79], ('reg', None)),       # EXTRQ xmm, xmm
    F('sse4a', 'Sse', 'legacy', 1, 3, [0x79], ('reg', None)),       # INSERTQ xmm, xmm
    F('sse4a', 'Sse', 'legacy', 1, 2, [0x2B], ('mem', None)),       # MOVNTSS
    F('sse4a', 'Sse', 'legacy', 1, 3, [0x2B], ('mem', None)),       # MOVNTSD
    F('ssse3', 'Sse', 'legacy', 2, 0, rng(0x00, 0x0B) + [0x1C, 0x1D, 0x1E]),   # MMX forms
    F('ssse3', 'Sse', 'legacy', 2, 1, rng(0x00, 0x0B) + [0x1C, 0x1D, 0x1E]),   # XMM forms
    F('ssse3', 'Sse', 'legacy', 3, 0, [0x0F]),                      # PALIGNR mm
    F('ssse3', 'Sse', 'legacy', 3, 1, [0x0F]),                      # PALIGNR xmm
    F('sse41', 'Sse', 'legacy', 2, 1, [0x10, 0x14, 0x15, 0x17] + rng(0x20, 0x25) + [0x28, 0x29, 0x2B] +
      rng(0x30, 0x35) + rng(0x38, 0x41)),
    F('sse41', 'Sse', 'legacy', 2, 1, [0x2A], ('mem', None)),       # MOVNTDQA
    F('sse42', 'Sse', 'legacy', 2, 1, [0x37]),                      # PCMPGTQ
    F('sse41', 'Sse', 'legacy', 3, 1, rng(0x08, 0x0E) + rng(0x14, 0x17) + rng(0x20, 0x22) + rng(0x40, 0x42)),
    F('sse42', 'Sse', 'legacy', 3, 1, rng(0x60, 0x63)),             # PCMPESTRM/I, PCMPISTRM/I
    # --- Crypto (gen_crypto.py): exactly the Zen 2 forms, so the 'ud' family tests the other
    # prefixes as #UD. TCG executes the SHA opcodes with any prefix; the model raises #UD (SDM "NP",
    # Bochs), and TestMain.qemuAsHardware accepts that for those 'ud' vectors.
    F('aes', 'Crypto', 'legacy', 2, 1, rng(0xDB, 0xDF)),
    F('sha', 'Crypto', 'legacy', 2, 0, rng(0xC8, 0xCD)),
    F('pclmulqdq', 'Crypto', 'legacy', 3, 1, [0x44]),
    F('aes', 'Crypto', 'legacy', 3, 1, [0xDF]),
    F('sha', 'Crypto', 'legacy', 3, 0, [0xCC]),
    # --- Gpr (x86_32/X86/Ext/Gpr.lean; generated by gen_gpr.py) --- exactly the defined forms
    F('popcnt', 'Gpr', 'legacy', 1, 2, [0xB8]),
    F('bmi1', 'Gpr', 'legacy', 1, 2, [0xBC]),                      # TZCNT
    F('abm', 'Gpr', 'legacy', 1, 2, [0xBD]),                       # LZCNT
    F('movbe', 'Gpr', 'legacy', 2, 0, [0xF0, 0xF1], ('mem', None)),
    F('movbe', 'Gpr', 'legacy', 2, 1, [0xF0, 0xF1], ('mem', None)),
    F('sse42', 'Gpr', 'legacy', 2, 3, [0xF0, 0xF1]),               # CRC32
    F('adx', 'Gpr', 'legacy', 2, 1, [0xF6]),                       # ADCX
    F('adx', 'Gpr', 'legacy', 2, 2, [0xF6]),                       # ADOX
    # (BMI: VEX.L = 1 is #UD, APM vol. 3 and SDM "VEX.LZ"; VEX.W is ignored outside 64-bit mode)
    F('bmi1', 'Gpr', 'vex', 2, 0, [0xF2, 0xF7], None, 0),          # ANDN, BEXTR
    F('bmi1', 'Gpr', 'vex', 2, 0, [0xF3], (None, 1), 0),           # BLSR
    F('bmi1', 'Gpr', 'vex', 2, 0, [0xF3], (None, 2), 0),           # BLSMSK
    F('bmi1', 'Gpr', 'vex', 2, 0, [0xF3], (None, 3), 0),           # BLSI
    F('bmi2', 'Gpr', 'vex', 2, 0, [0xF5], None, 0),                # BZHI
    F('bmi2', 'Gpr', 'vex', 2, 1, [0xF7], None, 0),                # SHLX
    F('bmi2', 'Gpr', 'vex', 2, 2, [0xF5, 0xF7], None, 0),          # PEXT, SARX
    F('bmi2', 'Gpr', 'vex', 2, 3, [0xF5, 0xF6, 0xF7], None, 0),    # PDEP, MULX, SHRX
    F('bmi2', 'Gpr', 'vex', 3, 3, [0xF0], None, 0),                # RORX
    F('rdrand', 'Gpr', 'legacy', 1, 0, [0xC7], ('reg', 6)),
    F('rdrand', 'Gpr', 'legacy', 1, 1, [0xC7], ('reg', 6)),
    F('rdseed', 'Gpr', 'legacy', 1, 0, [0xC7], ('reg', 7)),
    F('rdseed', 'Gpr', 'legacy', 1, 1, [0xC7], ('reg', 7)),
    F('rdpid', 'Gpr', 'legacy', 1, 2, [0xC7], ('reg', 7)),
    # (0F 01 CC..CF, FE, FF: no instruction on Zen 2; F8 SWAPGS: 64-bit mode only, LongMode)
    F('monitor', 'Gpr', 'legacy', 1, None, [0x01], ('reg', 1, (0, 1))),  # C8 MONITOR, C9 MWAIT
    F('rdtscp', 'Gpr', 'legacy', 1, None, [0x01], ('reg', 7, (1, 2, 3, 4, 5))),   # F9 RDTSCP, FA MONITORX/MCOMMIT, FB MWAITX, FC CLZERO, FD RDPRU
    F('clflush', 'Gpr', 'legacy', 1, 0, [0xAE], ('mem', 7)),
    F('clflushopt', 'Gpr', 'legacy', 1, 1, [0xAE], ('mem', 7)),
    F('clwb', 'Gpr', 'legacy', 1, 1, [0xAE], ('mem', 6)),
    F('wbnoinvd', 'Gpr', 'legacy', 1, 2, [0x09]),
    F('prefetchw', 'Gpr', 'legacy', 1, None, [0x0D], ('mem', None)),
    F('rdpmc', 'Gpr', 'legacy', 1, None, [0x33]),
]


def _matches(f, encoding, map_, pp, op, mod, reg, rm=None, L=None, W=None):
    if f.encoding != encoding or f.map != map_ or op not in f.ops:
        return False
    if f.pp is not None and f.pp != pp:
        return False
    # (L/W None = unknown: the form may be defined)
    if f.L is not None and L is not None and f.L != L or f.W is not None and W is not None and f.W != W:
        return False
    if f.modrm is not None:
        m, r = f.modrm[:2]
        # (mod None = unknown: the form may be defined)
        if m == 'mem' and mod == 3 or m == 'reg' and mod is not None and mod != 3:
            return False
        if r is not None and reg is not None and reg != r:
            return False
        if len(f.modrm) > 2 and rm is not None and rm not in f.modrm[2]:
            return False
    return True


def defined(encoding, map_, pp, op, mod=None, reg=None, rm=None, L=None, W=None):
    """The form (with ModRM mod/reg/rm and VEX.L/W if known; None = unknown) may be defined on Zen 2."""
    return any(_matches(f, encoding, map_, pp, op, mod, reg, rm, L, W) for f in IMPLEMENTED)


def vex_neighbours():
    """The undefined neighbours of the VEX forms: (map, pp, opcode, L) for every opcode byte that has a
    VEX row and every mandatory prefix and VEX.L under which the opcode is not defined for any VEX.W,
    ModRM.mod or ModRM.reg (#UD on Zen 2), in a fixed order."""
    ops = sorted({(f.map, op) for f in IMPLEMENTED if f.encoding == 'vex' for op in f.ops})
    return [(m, pp, op, L) for (m, op) in ops for pp in range(4) for L in range(2)
            if not defined('vex', m, pp, op, None, None, None, L, None)]


def model_has(feature):
    """`feature` (a Form.feature name) is a Zen 2 feature with forms in IMPLEMENTED."""
    return any(f.feature == feature for f in IMPLEMENTED)


if __name__ == '__main__':
    by = {}
    for f in IMPLEMENTED:
        by.setdefault(f.owner, set()).add(f.feature)
    for owner, feats in by.items():
        print('%-8s %s' % (owner, ' '.join(sorted(feats))))
    print('%d rows, %d VEX neighbours' % (len(IMPLEMENTED), len(vex_neighbours())))
