"""Native campaign family of the long-mode work (x86_32/X86/Ext/LongMode*.lean).

The native oracle runs its cases as 32-bit code in compatibility mode under 64-bit Linux, and
`x86fp --compat` (FpMain.lean) runs them the same way on the model. These are the user-mode
instructions whose outcome differs between compatibility mode and legacy protected mode on AMD
(APM vol. 3): SYSENTER and SYSEXIT are #UD in long mode (legacy: SYSENTER enters the kernel, SYSEXIT
is #GP(0) at CPL 3), SWAPGS and RDFSBASE/RDGSBASE/WRFSBASE/WRGSBASE are #UD outside 64-bit mode, and,
for reference, instructions that compatibility mode keeps (ARPL, LAHF/SAHF, BOUND, the one-byte
INC/DEC forms that are REX prefixes in 64-bit mode). SYSCALL is left out: from compatibility mode it
really enters the Linux kernel (CSTAR), which the oracle must not do; so is INTO: x86fp has no IDT, so
software interrupts, which deliver within the instruction, are not comparable with the oracle's signal.
"""
from fp_cases import record, meta

OPS = [
    ('sysenter', '0f34'), ('sysexit', '0f35'), ('swapgs', '0f01f8'),
    ('rdfsbase', 'f30faec0'), ('rdgsbase', 'f30faec8'), ('wrfsbase', 'f30faed0'), ('wrgsbase', 'f30faed8'),
    ('sysret', '0f07'),
]


def longmode_cases(rng, count):
    for name, code in OPS:
        for flags in (0x202, 0xA02):
            yield record(code, flags=flags), meta('longmode', name, code, flags=flags)
    # INC/DEC r32 (40..4F: REX prefixes in 64-bit mode), LAHF/SAHF, ARPL r/m16, r16
    for op in range(0x40, 0x50):
        code = '%02x' % op
        yield record(code), meta('longmode', 'incdec', code)
    for code in ('9f', '9e', '63d8'):
        yield record(code), meta('longmode', 'compat_keep', code)
    # BOUND r32, m32&32 with the arena's bounds: in range and out of range (#BR)
    for code in ('6203', '620b'):
        yield record(code), meta('longmode', 'bound', code)


FAMILIES = [(longmode_cases, ('lm',))]
