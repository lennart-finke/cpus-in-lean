"""Native campaign cases for open hardware questions that no other family observes (the list
"Open questions for the EPYC" in validation/README.md). Every case is a single user-mode instruction;
the ones whose Zen 2 outcome the manuals leave open are 'observe' (recorded, reported, not failed).

* decoder length limit (Decode.lean): an undefined 0F 38 / 0F 3A / VEX.0F38 opcode, prefix-padded so
  that its ModRM byte or imm8 is the 16th byte. The model decodes the full layout (0F 38: ModRM, 0F 3A:
  ModRM + imm8, VEX: ModRM) and raises #GP(0) for the 16-byte instruction (SDM vol. 3, table 6-2);
  QEMU raises #UD without fetching the last byte. The 15-byte controls are #UD in both.
* EVEX/XOP register forms (62 with mod = 11, 8F with reg != 0): #UD on Zen 2, which has neither.
* SHLD/SHRD r16 with a count of 17..31: result and flags undefined (SDM, APM); the model shifts the
  32-bit concatenation dst:src:dst.
* LOCK MOV CRn at CPL 3: LOCK MOV CR0 is AltMovCr8 (CR8) and #GP(0) at CPL 3; LOCK with CR2..CR4 is #UD
  in the model (APM defines LOCK only for CR0) before the CPL check.
* an SNaN m32/m64 operand of x87 arithmetic with a QNaN in ST(0): the model converts the memory
  operand first (IE, quieted) and then applies the two-QNaN rule (larger significand), as QEMU/Bochs.
* FYL2X/FPATAN with two NaN operands: the SDM's table 4-7 (larger significand).
* XGETBV with a 66/F2/F3 prefix (ECX = 3 here): #UD in the model (SDM "NP"); without the prefix
  ECX = 3 would be #GP(0).
"""
from fp_cases import record, meta

PAD = '2e'   # CS segment prefix: allowed before every encoding here, VEX included
OBS = dict(policy='observe', reason='open hardware question (validation/README.md, "Open questions for the EPYC")')
QNAN_A = (0xC000000000000123, 0x7fff)
QNAN_B = (0xE000000000000456, 0xffff)


def openq_cases(rng, count):
    # length limit: (name, encoding without padding, total length with the 16th byte)
    for name, body in (('len_0f38', '0f3850'), ('len_0f3a', '0f3a50c0'), ('len_vex0f38', 'c4e27850')):
        # the byte after `body` is ModRM (0F 38, VEX) or the imm8 (0F 3A, after the ModRM c0)
        for total in (15, 16):
            code = PAD * (total - 1 - len(body) // 2) + body
            yield record(code), meta('open_questions', f'{name}_{total}', code, length=total, **OBS)
    for code in ('62c0', '62f8', '8fc8', '8fe8', '8fe878c2c105'):
        yield record(code), meta('open_questions', 'evex_xop', code)
    for code in ('660fa4d811', '660fa4d814', '660fa4d81f', '660facd811', '660facd81f'):
        yield record(code), meta('open_questions', 'shld_shrd_r16_count', code, **OBS)
    for code in ('f00f20c0', 'f00f22c0', 'f00f20d8', 'f00f22d8', 'f00f20e0'):
        yield record(code), meta('open_questions', 'lock_mov_cr', code, **OBS)
    # FADD m32 / m64 at [EBX] (the data page): an SNaN with a larger significand than the QNaN in ST(0)
    for code, mem in (('d803', bytes.fromhex('ffffbf7f')), ('dc03', bytes.fromhex('ffffffffffff f77f'.replace(' ', ''))),
                      ('d80b', bytes.fromhex('ffffbf7f'))):
        yield record(code, a=(0xC000000000000001, 0x7fff), mem=mem), meta('open_questions', 'x87_snan_memory', code, **OBS)
    for code in ('d9f1', 'd9f3'):
        for a, b in ((QNAN_A, QNAN_B), (QNAN_B, QNAN_A)):
            yield record(code, a=a, b=b), meta('open_questions', 'x87_trans_two_nan', code, **OBS)


def openq_xsave_cases(rng, count):
    for code in ('660f01d0', 'f30f01d0', 'f20f01d0', '0f01d0'):
        yield record(code), meta('open_questions_xsave', 'xgetbv_prefix', code, **OBS)


FAMILIES = [(openq_cases, ()), (openq_xsave_cases, ('xsave', 'osxsave'))]
