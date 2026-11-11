"""'ext' generator rows of system workstream A (isa_forms.IMPLEMENTED, owner Sys) for gen.py.

The single-instruction tests run at CPL 3 in a harness that leaves EFER.SCE = 0, SYSENTER_CS = 0 and
CR4.SMAP/UMIP clear, so these forms check their CPL-3 fault behaviour against QEMU:
  0F 05 SYSCALL, 0F 07 SYSRET           #UD (EFER.SCE = 0; AMD APM vol. 3, SYSCALL/SYSRET)
  0F 34 SYSENTER                         #GP(0) (SYSENTER_CS is null)
  0F 35 SYSEXIT                          #GP(0) (CPL > 0)
  0F 01 CA CLAC, 0F 01 CB STAC           #UD (CPL > 0)
  LOCK 0F 20/22 with reg = 0 (CR8)       #GP(0) (CPL > 0); reg != 0: #UD (no CR10..CR12)
with random legacy prefixes (operand size, segment, REP). Their ring-0 behaviour is checked by the
system tests (test/sys/t_sysa.c).
"""
import random

FORMS = [
    ('syscall', b'\x0f\x05'), ('sysret', b'\x0f\x07'),
    ('sysenter', b'\x0f\x34'), ('sysexit', b'\x0f\x35'),
    ('clac', b'\x0f\x01\xca'), ('stac', b'\x0f\x01\xcb'),
]


def sys_form():
    """(instruction bytes, description) of a random Sys form."""
    pre = bytes(random.choice([0x66, 0x26, 0x2e, 0x36, 0x3e, 0x64, 0x65, 0xf2, 0xf3])
                for _ in range(random.choice([0, 0, 0, 1, 2])))
    if random.random() < 0.3:
        op = random.choice([0x20, 0x22])
        reg = random.choice([0, 0, 0, 2, 3, 4])
        body = bytes([0xf0, 0x0f, op, 0xc0 | (reg << 3) | random.randint(0, 7)])
        name = 'lockcr'
    else:
        name, body = random.choice(FORMS)
    insn = pre + body
    return insn, 'sys-%s:%s' % (name, insn.hex())
