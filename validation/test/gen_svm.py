"""'ext' generator rows of the SVM workstream (isa_forms.IMPLEMENTED, owner Svm) for gen.py.

The single-instruction tests run at CPL 3 with EFER.SVME = 0 (the harness never sets it), so the SVM
instructions check their mode/EFER.SVME rules against QEMU (AMD APM vol. 3):
  0F 01 D8 VMRUN, DA VMLOAD, DB VMSAVE, DD CLGI, DF INVLPGA   #UD (EFER.SVME = 0)
  0F 01 D9 VMMCALL                                         #UD (EFER.SVME = 0)
with random legacy prefixes (operand/address size, segment, REP: none changes these instructions).
Not generated: STGI (0F 01 DC) and SKINIT (0F 01 DE). The 7742 has SVM-Lock and SKINIT, so STGI
and SKINIT run with SVME = 0 and fault with #GP(0) at CPL 3 (vol. 3 STGI, SKINIT); TCG implements
neither SKINIT nor its CPUID bit and raises #UD. test/sys/t_svm.c checks both in its model-only part.
Their ring-0 and guest-mode behaviour is the system tests' (t_svm.c).
"""
import random

FORMS = [0xD8, 0xD9, 0xDA, 0xDB, 0xDD, 0xDF]


def svm_form():
    """(instruction bytes, description) of a random SVM form."""
    pre = bytes(random.choice([0x66, 0x67, 0x26, 0x2e, 0x36, 0x3e, 0x64, 0x65, 0xf2, 0xf3])
                for _ in range(random.choice([0, 0, 1, 2])))
    op = random.choice(FORMS)
    insn = pre + bytes([0x0f, 0x01, op])
    return insn, 'svm-%02x:%s' % (op, insn.hex())
