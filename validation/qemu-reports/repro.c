/* Linux user-space reproducer for the three QEMU x87 reports.
     gcc -m32 -O1 -mno-sse -fno-pie -no-pie -static -o repro repro.c
     ./repro              # on x86 hardware
     qemu-i386 ./repro    # under QEMU (TCG)
   Prints ST(0) [ST(1)] as sign/exponent_significand and the status word for each case. */
#include <stdio.h>

#include "repro_cases.h"

static void out(const char *name, const f80 *r0, int has1, const f80 *r1, unsigned short sw) {
	printf("%-18s st0=%04x_%016llx", name, r0->se, r0->sig);
	if (has1) printf(" st1=%04x_%016llx", r1->se, r1->sig);
	printf(" sw=%04x\n", sw);
}

int main(void) {
	report1();
	report2();
	report3();
	return 0;
}
