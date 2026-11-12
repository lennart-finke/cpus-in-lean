/* x87 machinery. test_x87_env is compared with QEMU (#NM rules, FNSAVE/FRSTOR, 16-bit FNSTENV);
   test_x87_model runs in the MODEL-ONLY section: stack faults, unmasked responses and #MF, FIP/FDP/FOP,
   C1 round-up, FPREM1 quotient bits and FERR#, none of which TCG models (expected values derived from
   the SDM in model-only.expected). */
#include "sys.h"

typedef struct { u64 sig; u16 se; } __attribute__((packed)) f80;
__attribute__((used)) f80 XA, XB, XR;
__attribute__((used)) u16 XCW, XSW;
__attribute__((used)) u32 XENV[27];
__attribute__((used)) float XHALF = 0.5f;
__attribute__((used)) f80 XBIG = { 0xFFFFFFFFFFFFFFFFULL, 0x7FFE };
__attribute__((used)) f80 XTHREE = { 0xC000000000000000ULL, 0x4000 };
__attribute__((used)) f80 XQA = { 0xB15C200000000000ULL, 0x4013 };
__attribute__((used)) f80 XQB = { 0x803CE00000000000ULL, 0x4001 };
__attribute__((used)) f80 XQNAN = { 0xC000000000000001ULL, 0x7FFF };   /* QNaN, small significand */
__attribute__((used)) f80 XSNAN = { 0xA000000000000000ULL, 0x7FFF };   /* SNaN, larger significand */
__attribute__((used)) f80 XQNAN2 = { 0xE000000000000000ULL, 0xFFFF };  /* QNaN, larger significand */
__attribute__((used)) f80 XP62 = { 0x8000000000000000ULL, 0x403D };      /* 2^62 */
__attribute__((used)) f80 XDEN = { 0x0000000000000001ULL, 0x0000 };      /* smallest denormal */
__attribute__((used)) u64 XM64;
__attribute__((used)) u32 XFL;
extern char x87_fadd_at[], x87_fdivp_at[];

static void p80(const char *k, const f80 *x) { kprintf(" %s=%x_%x%x", k, (u32)x->se, (u32)(x->sig >> 32), (u32)x->sig); }
static f80 env_st(int i) { f80 v; memcpy(&v, (u8 *)XENV + 28 + 10 * i, 10); return v; }

void test_x87_env(void) {
	u32 cr0 = RDCR(0);
	WRCR(0, (cr0 & ~0xC) | 0x22);
	/* #NM: TS for every ESC; WAIT only with TS and MP; EM for ESC but not WAIT */
	WRCR(0, RDCR(0) | 0x8);
	int a = TRY(__asm__ volatile("fld1\n fstp %%st(0)" ::: "memory"));
	int b = TRY(__asm__ volatile("fwait" ::: "memory"));
	WRCR(0, RDCR(0) & ~0x2);
	int c = TRY(__asm__ volatile("fwait" ::: "memory"));
	WRCR(0, (RDCR(0) & ~0x8) | 0x4);
	int d = TRY(__asm__ volatile("fninit" ::: "memory"));
	int e = TRY(__asm__ volatile("fwait" ::: "memory"));
	WRCR(0, (cr0 & ~0xC) | 0x22);
	kprintf("x87.nm: ts_esc=%x ts_mp_wait=%x ts_wait=%x em_esc=%x em_wait=%x\n", a, b, c, d, e);

	/* FNSAVE stores the environment and the stack, then reinitializes; FRSTOR restores */
	__asm__ volatile("fninit\n fldpi\n fld1\n fldz\n fnsave XENV\n fnstcw XCW\n fnstsw XSW" ::: "memory");
	kprintf("x87.fnsave: cw=%x sw=%x tw=%x after_cw=%x after_sw=%x", XENV[0] & 0xFFFF, XENV[1] & 0xFFFF,
	        XENV[2] & 0xFFFF, XCW, XSW);
	f80 s0 = env_st(0), s1 = env_st(1), s2 = env_st(2);
	p80("st0", &s0); p80("st1", &s1); p80("st2", &s2); kputc('\n');
	__asm__ volatile("frstor XENV\n fnstsw XSW\n fstpt XA\n fstpt XB\n fstpt XR" ::: "memory");
	kprintf("x87.frstor: sw=%x", XSW); p80("st0", &XA); p80("st1", &XB); p80("st2", &XR); kputc('\n');

	/* 16-bit FNSTENV (operand-size prefix): 14 bytes */
	for (int k = 0; k < 8; k++) XENV[k] = 0xAAAAAAAA;
	__asm__ volatile("fninit\n fld1\n data16 fnstenv XENV\n fstp %%st(0)" ::: "memory");
	kprintf("x87.fnstenv16: cw=%x sw=%x tw=%x next=%x\n", XENV[0] & 0xFFFF, XENV[0] >> 16, XENV[1] & 0xFFFF,
	        XENV[3] >> 16);
	__asm__ volatile("fninit");
}

/* Behaviour the AMD EPYC 7742 showed in the native campaign (validation/README.md, "Hardware tests"),
   where the model used to follow the SDM's pseudocode or QEMU: only non-waiting instructions run while
   an unmasked exception is pending, and FNINIT clears it. */
static void test_x87_epyc(void) {
	/* FCOMI with an empty stack and IE unmasked: ZF = PF = CF = 1 are written all the same */
	XCW = 0x37E;
	__asm__ volatile("fninit\n fldcw XCW\n xorl %%eax, %%eax\n incl %%eax\n .byte 0xdb,0xf1\n pushfl\n popl XFL\n"
	                 " fnstsw XSW\n fninit" ::: "eax", "memory");
	kprintf("x87m.epyc.fcomi: eflags=%x sw=%x", XFL & 0x8D5, XSW);
	/* FCOM likewise sets C3, C2, C0 = 111 */
	__asm__ volatile("fninit\n fldcw XCW\n .byte 0xd8,0xd1\n fnstsw XSW\n fninit" ::: "memory");
	kprintf(" fcom_sw=%x\n", XSW);
	/* FLD ST(1) with ST(1) empty and ST(7) in use: stack underflow (C1 = 0), the indefinite pushed */
	__asm__ volatile("fninit\n fld1\n fincstp\n fld %%st(1)\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf("x87m.epyc.fld: sw=%x", XSW); p80("st0", &XR); kputc('\n');
	/* FLDCW: reserved bits 7 and 13..15 read as 0, bit 6 as 1 */
	XCW = 0xFFFF;
	__asm__ volatile("fninit\n fldcw XCW\n fnstcw XCW\n fninit" ::: "memory");
	kprintf("x87m.epyc.fcw: %x", XCW);
	XCW = 0x0000;
	__asm__ volatile("fninit\n fldcw XCW\n fnstcw XCW\n fninit" ::: "memory");
	kprintf(" %x\n", XCW);
	/* F2XM1 of 3.0 (outside [-1, 1]): 3.0 with PE */
	__asm__ volatile("fninit\n fldt XTHREE\n f2xm1\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf("x87m.epyc.f2xm1: sw=%x", XSW); p80("st0", &XR); kputc('\n');
	/* FST m64 of a denormal: UE and PE, no DE */
	__asm__ volatile("fninit\n fldt XDEN\n fstl XM64\n fnstsw XSW\n fninit" ::: "memory");
	kprintf("x87m.epyc.fst: sw=%x m64=%x%x\n", XSW, (u32)(XM64 >> 32), (u32)XM64);
	/* FSCALE with OE unmasked and a massive overflow: +inf with OE, PE, C1 */
	XCW = 0x377;
	__asm__ volatile("fninit\n fldcw XCW\n fldt XP62\n fldt XBIG\n fscale\n fnstsw XSW\n fnsave XENV\n fninit" ::: "memory");
	f80 s0 = env_st(0);
	kprintf("x87m.epyc.fscale: sw=%x", XSW); p80("st0", &s0); kputc('\n');
}

void test_x87_model(void) {
	WRCR(0, (RDCR(0) & ~0xC) | 0x22);
	__asm__ volatile("fninit\n fld1\n fld1\n fld1\n fld1\n fld1\n fld1\n fld1\n fld1\n fld1\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf("x87m.overflow: sw=%x", XSW); p80("st0", &XR); kputc('\n');
	__asm__ volatile("fninit\n .byte 0xd8,0xc1\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf("x87m.underflow: sw=%x", XSW); p80("st0", &XR); kputc('\n');

	/* unmasked stack fault: nothing is written; ES pending; the next waiting instruction faults */
	XCW = 0x37E;
	__asm__ volatile("fninit\n fldcw XCW\n .byte 0xd8,0xc1\n fnstsw XSW\n fnstenv XENV" ::: "memory");
	kprintf("x87m.unmasked.stack: sw=%x tw=%x\n", XSW, XENV[2] & 0xFFFF);
	int a = TRY(__asm__ volatile("fwait" ::: "memory"));
	int b = TRY(__asm__ volatile("fld1" ::: "memory"));
	__asm__ volatile("fnclex");
	int c = TRY(__asm__ volatile("fwait" ::: "memory"));
	kprintf("x87m.mf: fwait=%x fld1=%x after_fnclex=%x\n", a, b, c);

	/* unmasked zero divide: no result, no pop; FIP/FCS/FOP recorded; FNSAVE shows the stack */
	XCW = 0x37B;
	__asm__ volatile("fninit\n fldcw XCW\n fld1\n fldz\n .globl x87_fdivp_at\nx87_fdivp_at: .byte 0xde,0xf9\n"
	                 " fnstsw XSW\n fnsave XENV" ::: "memory");
	f80 s0 = env_st(0), s1 = env_st(1);
	kprintf("x87m.unmasked.ze: sw=%x tw=%x fip_ok=%d fcs_fop=%x", XSW, XENV[2] & 0xFFFF,
	        XENV[3] == (u32)x87_fdivp_at, XENV[4]);
	p80("st0", &s0); p80("st1", &s1); kputc('\n');

	/* unmasked overflow to a register: the result is delivered with the exponent wrapped by 24576 */
	XCW = 0x377;
	__asm__ volatile("fninit\n fldcw XCW\n fldt XBIG\n fld %%st(0)\n .byte 0xde,0xc9\n fnstsw XSW\n fnsave XENV" ::: "memory");
	s0 = env_st(0);
	kprintf("x87m.ovf.wrap: sw=%x", XSW); p80("st0", &s0); kputc('\n');

	/* C1: rounded up */
	__asm__ volatile("fninit\n fld1\n fldt XTHREE\n .byte 0xde,0xf9\n fnstsw XSW\n fstpt XR" ::: "memory");
	kprintf("x87m.c1: sw=%x", XSW); p80("st0", &XR); kputc('\n');

	/* FPREM1 quotient bits (q = 362559, q mod 8 = 7: C0 = C3 = C1 = 1) */
	__asm__ volatile("fninit\n fldt XQB\n fldt XQA\n fprem1\n fnstsw XSW\n fninit" ::: "memory");
	kprintf("x87m.fprem1: sw=%x\n", XSW);

	/* FSCALE, two NaNs (SDM vol. 1 table 4-7): an SNaN and a QNaN give the QNaN; two QNaNs the larger
	   significand. ST(0) = XQNAN in both cases. */
	__asm__ volatile("fninit\n fldt XSNAN\n fldt XQNAN\n fscale\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf("x87m.fscale.nan: snan_qnan: sw=%x", XSW); p80("st0", &XR);
	__asm__ volatile("fninit\n fldt XQNAN2\n fldt XQNAN\n fscale\n fnstsw XSW\n fstpt XR\n fninit" ::: "memory");
	kprintf(" qnan_qnan: sw=%x", XSW); p80("st0", &XR); kputc('\n');

	/* FIP/FCS/FOP and FDP/FDS of the last non-control instruction (32-bit protected format) */
	__asm__ volatile("fninit\n fld1\n .globl x87_fadd_at\nx87_fadd_at: fadds XHALF\n fnstenv XENV\n fninit" ::: "memory");
	kprintf("x87m.env: cw=%x sw=%x tw=%x fip_ok=%d fcs_fop=%x fdp_ok=%d fds=%x\n", XENV[0], XENV[1], XENV[2],
	        XENV[3] == (u32)x87_fadd_at, XENV[4], XENV[5] == (u32)&XHALF, XENV[6]);

	/* CR0.NE = 0: a pending exception asserts FERR# (IRQ13) instead of #MF */
	XCW = 0x37B;
	WRCR(0, RDCR(0) & ~0x20);
	__asm__ volatile("fninit\n fldcw XCW\n fld1\n fldz\n .byte 0xde,0xf9" ::: "memory");
	int f = TRY(__asm__ volatile("fwait" ::: "memory"));
	__asm__ volatile("fninit");
	WRCR(0, RDCR(0) | 0x20);
	kprintf("x87m.ferr: fwait=%x\n", f);
	test_x87_epyc();
}
