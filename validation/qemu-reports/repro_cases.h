/* x87 reproducers for the QEMU reports. Each case loads its operands, runs one instruction under a given
   control word, and reports ST(0) (and ST(1) where relevant) and the status word. The includer defines
   `out` (declared below). Plain i386 code, no SSE: build with -m32 -mno-sse. */
typedef struct { unsigned long long sig; unsigned short se; } __attribute__((packed)) f80;

static void out(const char *name, const f80 *st0, int has_st1, const f80 *st1, unsigned short sw);

/* globals referenced by name from the inline assembly */
__attribute__((used)) f80 A, B, R0, R1;
__attribute__((used)) unsigned short CW, SW;
__attribute__((used)) unsigned long long M64;
__attribute__((used)) double D64;
/* packed BCD 123456789012345678 (least significant byte first, sign byte last) */
__attribute__((used)) unsigned char BCD[10] = { 0x78, 0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12, 0x00 };

static void run2(const char *name, unsigned short cw, f80 st0, f80 st1, int op, int has1) {
	CW = cw; A = st0; B = st1;
	/* B is loaded first so that A ends up in ST(0) */
	switch (op) {
	case 0: __asm__ volatile("fninit; fldcw CW; fldt B; fldt A; fprem; fnstsw SW; fstpt R0; fstpt R1" ::: "memory"); break;
	case 1: __asm__ volatile("fninit; fldcw CW; fldt B; fldt A; frndint; fnstsw SW; fstpt R0; fstpt R1" ::: "memory"); break;
	case 2: __asm__ volatile("fninit; fldcw CW; fldt B; fldt A; fyl2x; fnstsw SW; fstpt R0" ::: "memory"); break;
	case 3: __asm__ volatile("fninit; fldcw CW; fldt A; fsin; fnstsw SW; fstpt R0" ::: "memory"); break;
	case 4: __asm__ volatile("fninit; fldcw CW; fldt A; fcos; fnstsw SW; fstpt R0" ::: "memory"); break;
	case 5: __asm__ volatile("fninit; fldcw CW; fldt A; fptan; fnstsw SW; fstpt R0; fstpt R1" ::: "memory"); break;
	}
	out(name, &R0, has1, &R1, SW);
}

static void run_load(const char *name, unsigned short cw, int op) {
	CW = cw;
	if (op == 0) __asm__ volatile("fninit; fldcw CW; fildll M64; fnstsw SW; fstpt R0" ::: "memory");
	else if (op == 1) __asm__ volatile("fninit; fldcw CW; fldl D64; fnstsw SW; fstpt R0" ::: "memory");
	else __asm__ volatile("fninit; fldcw CW; fbld BCD; fnstsw SW; fstpt R0" ::: "memory");
	out(name, &R0, 0, &R0, SW);
}

static const f80 ONE = { 0x8000000000000000ULL, 0x3FFF };

static void report1(void) {
	/* precision control: PC = 53 bits (CW 0x027F) or 24 bits (CW 0x007F), all exceptions masked */
	M64 = 0x4000000000000001ULL;                                      /* 2^62 + 1: correct on QEMU (control) */
	run_load("pc.fild_m64.pc53", 0x027F, 0);
	run_load("pc.fbld.pc53", 0x027F, 2);
	union { unsigned long long u; double d; } d = { 0x3FF0000000000001ULL };   /* 1 + 2^-52 */
	D64 = d.d;
	run_load("pc.fld_m64.pc24", 0x007F, 1);
	run2("pc.fprem.pc53", 0x027F, (f80){ 0xFFFFFFFFFFFFFFFFULL, 0x3FFF }, ONE, 0, 1);    /* (2 - 2^-63) rem 1 */
	run2("pc.frndint.pc24", 0x007F, (f80){ 0x8000008000000000ULL, 0x4017 }, ONE, 1, 0); /* 2^24 + 1 */
}

static void report2(void) {
	/* FYL2X: ST(1) * log2(ST(0)) with a denormal ST(1); default control word */
	run2("fyl2x.den.1", 0x037F, (f80){ 0x800000000000012DULL, 0x3FFF }, (f80){ 0x5EF54699B2EDECCAULL, 0x0000 }, 2, 0);
	run2("fyl2x.den.2", 0x037F, (f80){ 0x80000000000003A6ULL, 0x3FFF }, (f80){ 0x7B71AE5A99E3E9E7ULL, 0x0000 }, 2, 0);
}

static void report3(void) {
	/* FSIN, FCOS, FPTAN of 1.0; default control word (64-bit precision, round to nearest) */
	run2("fsin.1", 0x037F, ONE, ONE, 3, 0);
	run2("fcos.1", 0x037F, ONE, ONE, 4, 0);
	run2("fptan.1", 0x037F, ONE, ONE, 5, 1);
}
