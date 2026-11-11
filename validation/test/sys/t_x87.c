/* x87 arithmetic differential fuzzing (masked exceptions, valid stack use) against QEMU's softfloat.
   C1 (round-up indicator) is masked: QEMU does not implement it; see test_x87_model for it. */
#include "sys.h"

typedef struct { u64 sig; u16 se; } __attribute__((packed)) f80;

static u32 rs = 0x2545F491;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static u64 rnd64(void) { u64 h = rnd(); return (h << 32) | rnd(); }

static void gen(f80 *x) {
	u32 cls = rnd() % 17;
	u16 sign = (rnd() & 1) ? 0x8000 : 0;
	u64 s = rnd64();
	u16 e;
	switch (cls) {
	case 0: s = 0; e = 0; break;
	case 1: s &= ~(1ULL << 63); if (!s) s = 1; e = 0; break;              /* denormal */
	case 2: s |= 1ULL << 63; e = 0; break;                                /* pseudo-denormal */
	case 3: case 4: case 5: case 6: s |= 1ULL << 63; e = 16383 - 70 + rnd() % 140; break;
	case 7: s |= 1ULL << 63; e = 1 + rnd() % 0x7FFE; break;
	case 8: s |= 1ULL << 63; e = 0x7FFE - rnd() % 3; break;               /* near overflow */
	case 9: s |= 1ULL << 63; e = 1 + rnd() % 3; break;                    /* near underflow */
	case 10: s = 1ULL << 63; e = 0x7FFF; break;                           /* infinity */
	case 11: s |= 3ULL << 62; e = 0x7FFF; break;                          /* QNaN */
	case 12: s = (s & ~(3ULL << 62)) | (1ULL << 63) | 1; e = 0x7FFF; break; /* SNaN */
	case 13: s &= ~(1ULL << 63); e = 1 + rnd() % 0x7FFE; break;           /* unnormal */
	case 14: s = (s | (1ULL << 63)) & ~((1ULL << (40 + rnd() % 20)) - 1); e = 16383 + rnd() % 24; break; /* integers */
	case 15: s = (s | (1ULL << 63)) & 0xFFFFFF0000000000ULL; e = 16383 - 3 + rnd() % 8; break; /* short */
	default: s = (1ULL << 63) | (s & 0xFFFF); e = 16383 + rnd() % 64; break; /* near ties */
	}
	x->sig = s; x->se = sign | e;
}

__attribute__((used)) f80 A, B, R1, R2, R3;
__attribute__((used)) u32 M32, M32b; __attribute__((used)) u64 M64, M64b; __attribute__((used)) u8 BCD[10];
__attribute__((used)) u16 CW, SW;

#define SETUP "fninit\n fldcw CW\n fldt B\n fldt A\n"
#define TAIL2 "fnstsw SW\n fstpt R1\n fstpt R2\n"
#define TAIL1 "fnstsw SW\n fstpt R1\n"

static int isnan80(const f80 *x) { return (x->se & 0x7FFF) == 0x7FFF && (x->sig >> 63) && (x->sig << 1); }
static void p80(const f80 *x) { kprintf(" %x_%x%x", (u32)x->se, (u32)(x->sig >> 32), (u32)x->sig); }
/* Status as printed: exception flags without DE (printed separately as de=), and the condition codes
   only for operations that define them (compares, FXAM, FPREM; C1 never: QEMU lacks round-up). */
static int defines_cc(u32 op) { return op == 9 || (op >= 12 && op <= 17) || op == 35; }
static void status(u32 op) {
	u32 sw = SW, keep = 0x3D | (defines_cc(op) ? 0x4500 : 0);
	kprintf(" sw=%x de=%d\n", sw & keep, (sw >> 1) & 1);
}
static void line(u32 i, u32 op, int n) {
	kprintf("x87 %d op=%d cw=%x a", i, op, (u32)CW); p80(&A); kputs(" b"); p80(&B);
	kputs(" ->");
	if (n >= 1) p80(&R1);
	if (n >= 2) p80(&R2);
	if (n >= 3) p80(&R3);
	status(op);
}

void test_x87(void) {
	WRCR(0, (RDCR(0) & ~0xC) | 0x22);   /* EM = TS = 0, MP = NE = 1 */
	__asm__ volatile("fninit");

	/* constants under every rounding mode */
	for (u32 rc = 0; rc < 4; rc++) {
		CW = 0x37F | (rc << 10);
		__asm__ volatile("fninit\n fldcw CW\n fldpi\n fstpt R1\n fldl2t\n fstpt R2\n fldl2e\n fstpt R3" ::: "memory");
		kprintf("x87.const rc=%d", rc); p80(&R1); p80(&R2); p80(&R3);
		__asm__ volatile("fninit\n fldcw CW\n fldlg2\n fstpt R1\n fldln2\n fstpt R2\n fld1\n fstpt R3" ::: "memory");
		p80(&R1); p80(&R2); p80(&R3); kputc('\n');
	}

	u32 bad = 0;
	rs = fuzz_seed(rs);
	u32 n = param("x87", 2500);
	for (u32 i = 0; i < n; i++) {
		gen(&A); gen(&B);
		u32 pc = rnd() % 4;
		u32 op = rnd() % 36;
		/* QEMU wrongly applies precision control beyond the basic arithmetic (loads, FBLD, FRNDINT,
		   FPREM, FSCALE, FXTRACT, memory operands): there PC = 64 bits keeps the comparison meaningful */
		if (!(op <= 6 || op == 32 || op == 33 || op == 34)) pc = 3;
		CW = 0x7F | (pc << 8) | ((rnd() % 4) << 10);
		/* FSCALE with two NaNs: TCG returns ST(1)'s NaN instead of applying SDM table 4-7 (checked in
		   test_x87_model) */
		while (op == 8 && isnan80(&A) && isnan80(&B)) gen(&B);
		u32 eflags = 0;
		R1 = R2 = R3 = (f80){0, 0};
		switch (op) {
		case 0: __asm__ volatile(SETUP ".byte 0xd8,0xc1\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 1: __asm__ volatile(SETUP ".byte 0xd8,0xe1\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 2: __asm__ volatile(SETUP ".byte 0xd8,0xe9\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 3: __asm__ volatile(SETUP ".byte 0xd8,0xc9\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 4: __asm__ volatile(SETUP ".byte 0xd8,0xf1\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 5: __asm__ volatile(SETUP ".byte 0xd8,0xf9\n" TAIL2 ::: "memory"); line(i, op, 2); break;
		case 6: __asm__ volatile(SETUP ".byte 0xd9,0xfa\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 7: __asm__ volatile(SETUP ".byte 0xd9,0xfc\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 8: __asm__ volatile(SETUP ".byte 0xd9,0xfd\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 9: __asm__ volatile(SETUP ".byte 0xd9,0xf8\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 10: __asm__ volatile(SETUP ".byte 0xd9,0xf5\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 11: __asm__ volatile(SETUP ".byte 0xd9,0xf4\n fnstsw SW\n fstpt R1\n fstpt R2\n fstpt R3" ::: "memory"); line(i, op, 2); break;
		case 12: __asm__ volatile(SETUP ".byte 0xd8,0xd1\n" TAIL2 ::: "memory"); line(i, op, 0); break;
		case 13: __asm__ volatile(SETUP ".byte 0xdd,0xe1\n" TAIL2 ::: "memory"); line(i, op, 0); break;
		case 14: case 15:
			if (op == 14) __asm__ volatile(SETUP ".byte 0xdb,0xf1\n pushfl\n popl %0\n" TAIL2 : "=r"(eflags) :: "memory");
			else __asm__ volatile(SETUP ".byte 0xdb,0xe9\n pushfl\n popl %0\n" TAIL2 : "=r"(eflags) :: "memory");
			line(i, op, 0); kprintf("x87 %d eflags=%x\n", i, eflags & 0x8D5); break;
		case 16: __asm__ volatile(SETUP ".byte 0xd9,0xe5\n" TAIL2 ::: "memory"); line(i, op, 0); break;
		case 17: __asm__ volatile(SETUP ".byte 0xd9,0xe4\n" TAIL2 ::: "memory"); line(i, op, 0); break;
		case 18: __asm__ volatile(SETUP ".byte 0xd9,0xe0\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 19: __asm__ volatile(SETUP ".byte 0xd9,0xe1\n" TAIL2 ::: "memory"); line(i, op, 1); break;
		case 20: __asm__ volatile(SETUP "fsts M32\n" TAIL2 ::: "memory"); line(i, op, 0); kprintf("x87 %d m32=%x\n", i, M32); break;
		case 21: __asm__ volatile(SETUP "fstl M64\n" TAIL2 ::: "memory"); line(i, op, 0);
			kprintf("x87 %d m64=%x%x\n", i, (u32)(M64 >> 32), (u32)M64); break;
		case 22: case 23: case 24: case 25: {
			M64 = 0x1111111111111111ULL; for (int k = 0; k < 10; k++) BCD[k] = 0x22;
			if (op == 22) __asm__ volatile(SETUP "fistps M64\n fnstsw SW\n fstpt R1" ::: "memory");
			if (op == 23) __asm__ volatile(SETUP "fistpl M64\n fnstsw SW\n fstpt R1" ::: "memory");
			if (op == 24) __asm__ volatile(SETUP "fistpll M64\n fnstsw SW\n fstpt R1" ::: "memory");
			if (op == 25) __asm__ volatile(SETUP "fbstp BCD\n fnstsw SW\n fstpt R1" ::: "memory");
			line(i, op, 0);
			if (op == 25) kprintf("x87 %d bcd=%x%x%x\n", i, *(u16 *)(BCD + 8), *(u32 *)(BCD + 4), *(u32 *)BCD);
			else kprintf("x87 %d int=%x%x\n", i, (u32)(M64 >> 32), (u32)M64);
			break; }
		case 26: M32 = rnd(); __asm__ volatile("fninit\n fldcw CW\n flds M32\n fnstsw SW\n fstpt R1" ::: "memory");
			kprintf("x87 %d flds %x", i, M32); p80(&R1); status(op); break;
		case 27: M64 = rnd64(); __asm__ volatile("fninit\n fldcw CW\n fldl M64\n fnstsw SW\n fstpt R1" ::: "memory");
			kprintf("x87 %d fldl %x%x", i, (u32)(M64 >> 32), (u32)M64); p80(&R1); status(op); break;
		case 28: M32b = rnd(); __asm__ volatile(SETUP "fadds M32b\n" TAIL2 ::: "memory"); line(i, op, 1); kprintf("x87 %d m32b=%x\n", i, M32b); break;
		case 29: M64b = rnd64(); __asm__ volatile(SETUP "fdivl M64b\n" TAIL2 ::: "memory"); line(i, op, 1);
			kprintf("x87 %d m64b=%x%x\n", i, (u32)(M64b >> 32), (u32)M64b); break;
		case 30: M32b = rnd() % 200000 - 100000; __asm__ volatile(SETUP "fimull M32b\n" TAIL2 ::: "memory"); line(i, op, 1); kprintf("x87 %d i32=%x\n", i, M32b); break;
		case 31: { u8 *p = BCD; for (int k = 0; k < 9; k++) { u32 d = rnd() % 100; p[k] = (u8)(((d / 10) << 4) | (d % 10)); } p[9] = (rnd() & 1) ? 0x80 : 0;
			__asm__ volatile("fninit\n fldcw CW\n fbld BCD\n fnstsw SW\n fstpt R1" ::: "memory");
			kprintf("x87 %d fbld %x%x%x", i, *(u16 *)(BCD + 8), *(u32 *)(BCD + 4), *(u32 *)BCD); p80(&R1); status(op); break; }
		case 32: __asm__ volatile(SETUP ".byte 0xde,0xc1\n fnstsw SW\n fstpt R1" ::: "memory"); line(i, op, 1); break;   /* faddp */
		case 33: __asm__ volatile(SETUP ".byte 0xde,0xf9\n fnstsw SW\n fstpt R1" ::: "memory"); line(i, op, 1); break;   /* fdivp st(1)=st(1)/st */
		case 34: __asm__ volatile(SETUP ".byte 0xdc,0xe1\n" TAIL2 ::: "memory"); line(i, op, 2); break;                    /* dc e1: st(1) = st - st(1) */
		default: __asm__ volatile(SETUP ".byte 0xde,0xd9\n fnstsw SW" ::: "memory"); line(i, op, 0); break;              /* fcompp */
		}
		(void)bad;
	}
	__asm__ volatile("fninit");
}
