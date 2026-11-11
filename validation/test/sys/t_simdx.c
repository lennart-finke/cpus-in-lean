/* MMX/SSE machinery. test_simd_exc is compared with QEMU: #UD/#NM conditions (CR0.EM/TS,
   CR4.OSFXSR), alignment, undefined prefix combinations, LDMXCSR/FXRSTOR reserved bits, the FXSAVE
   image and FXRSTOR. test_simd_model runs in the MODEL-ONLY section: what TCG does not model
   (unmasked SIMD exceptions, #MF for MMX instructions, the MMX exponent word, FIP/FDP in FXSAVE,
   the SDM's two-NaN rule, MIN/MAX with DAZ, RCP/RSQRT special cases); expected values derived from
   the SDM in model-only.expected. */
#include "sys.h"

static u8 xc[48] __attribute__((aligned(16)));
void (*volatile simdx_codep)(void) = (void (*)(void))xc;
__attribute__((used, aligned(16))) u8 XM[64];
__attribute__((used, aligned(16))) u8 XF[512], XF2[512];
__attribute__((used, aligned(16))) u32 XV[32], XW[32];
__attribute__((used)) u32 XMX;
__attribute__((used)) u16 XCW2;
__attribute__((used)) u32 XENV2[7];

/* Run the bytes with ESI = EDI = `mem`, EAX = ECX = 0; returns the vector (0xFFFF: none). */
static int runb(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) xc[k] = b[k];
	xc[n] = 0xC3;
	return TRY(__asm__ volatile("xorl %%eax, %%eax\n xorl %%ecx, %%ecx\n call *simdx_codep"
	                            :: "S"(mem), "D"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}
#define R(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runb(sizeof _b, _b, mem); })

static void ldx(void) {   /* XMM0..7 from XV */
	__asm__ volatile("movdqu XV, %%xmm0\n movdqu XV+16, %%xmm1\n movdqu XV+32, %%xmm2\n movdqu XV+48, %%xmm3\n"
	                 "movdqu XV+64, %%xmm4\n movdqu XV+80, %%xmm5\n movdqu XV+96, %%xmm6\n movdqu XV+112, %%xmm7" ::: "memory");
}
static void stx(void) {   /* XMM0..7 to XW */
	__asm__ volatile("movdqu %%xmm0, XW\n movdqu %%xmm1, XW+16\n movdqu %%xmm2, XW+32\n movdqu %%xmm3, XW+48\n"
	                 "movdqu %%xmm4, XW+64\n movdqu %%xmm5, XW+80\n movdqu %%xmm6, XW+96\n movdqu %%xmm7, XW+112" ::: "memory");
}
static void px(const char *k, const u32 *p) { kprintf(" %s=%x%x%x%x", k, p[3], p[2], p[1], p[0]); }
static void pb(const char *k, const u8 *p, int n) { kprintf(" %s=", k); for (int i = n - 1; i >= 0; i--) { kputc("0123456789abcdef"[p[i] >> 4]); kputc("0123456789abcdef"[p[i] & 15]); } }

static void cr0set(u32 em_ts) { WRCR(0, (RDCR(0) & ~0xC) | 0x22 | em_ts); }
static void cr4sse(int on) { WRCR(4, on ? RDCR(4) | 0x600 : RDCR(4) & ~0x600); }

void test_simd_exc(void) {
	cr0set(0);
	cr4sse(1);
	__asm__ volatile("fninit");
	memset(XM, 0, sizeof XM);
	*(u32 *)XM = 0x1F80;

	/* CR4.OSFXSR = 0: SSE instructions #UD; MMX and the MMX forms of the SSE integer additions,
	   MOVNTI, fences and FXSAVE are not affected */
	cr4sse(0);
	kprintf("simd.noosfxsr: addps=%x paddb=%x pshufw=%x pavgb=%x paddq=%x pextrw=%x movntq=%x cvtpi2ps=%x",
		R(XM, 0x0F, 0x58, 0xC1), R(XM, 0x0F, 0xFC, 0xC1), R(XM, 0x0F, 0x70, 0xC1, 0x1B), R(XM, 0x0F, 0xE0, 0xC1),
		R(XM, 0x0F, 0xD4, 0xC1), R(XM, 0x0F, 0xC5, 0xC1, 0x01), R(XM, 0x0F, 0xE7, 0x06), R(XM, 0x0F, 0x2A, 0xC1));
	kprintf(" ldmxcsr=%x paddb_x=%x movnti=%x sfence=%x lfence=%x mfence=%x fxsave=%x emms=%x\n",
		R(XM, 0x0F, 0xAE, 0x16), R(XM, 0x66, 0x0F, 0xFC, 0xC1), R(XM, 0x0F, 0xC3, 0x06),
		R(XM, 0x0F, 0xAE, 0xF8), R(XM, 0x0F, 0xAE, 0xE8), R(XM, 0x0F, 0xAE, 0xF0), R(XF, 0x0F, 0xAE, 0x06), R(XM, 0x0F, 0x77));
	cr4sse(1);
	/* CR0.EM: MMX/SSE #UD, FXSAVE #NM, fences unaffected */
	cr0set(4);
	kprintf("simd.em: addps=%x paddb=%x emms=%x ldmxcsr=%x fxsave=%x fxrstor=%x sfence=%x movnti=%x\n",
		R(XM, 0x0F, 0x58, 0xC1), R(XM, 0x0F, 0xFC, 0xC1), R(XM, 0x0F, 0x77), R(XM, 0x0F, 0xAE, 0x16),
		R(XF, 0x0F, 0xAE, 0x06), R(XF, 0x0F, 0xAE, 0x0E), R(XM, 0x0F, 0xAE, 0xF8), R(XM, 0x0F, 0xC3, 0x06));
	/* CR0.TS: #NM */
	cr0set(8);
	kprintf("simd.ts: addps=%x paddb=%x emms=%x ldmxcsr=%x stmxcsr=%x fxsave=%x fxrstor=%x sfence=%x movnti=%x\n",
		R(XM, 0x0F, 0x58, 0xC1), R(XM, 0x0F, 0xFC, 0xC1), R(XM, 0x0F, 0x77), R(XM, 0x0F, 0xAE, 0x16),
		R(XM, 0x0F, 0xAE, 0x1E), R(XF, 0x0F, 0xAE, 0x06), R(XF, 0x0F, 0xAE, 0x0E), R(XM, 0x0F, 0xAE, 0xF8),
		R(XM, 0x0F, 0xC3, 0x06));
	cr0set(0);
	__asm__ volatile("fninit");

	/* 16-byte alignment of 128-bit operands */
	u8 *mis = XM + 8;
	kprintf("simd.align: movaps=%x movups=%x addps=%x addss=%x paddb=%x movdqa=%x movdqu=%x movntps=%x",
		R(mis, 0x0F, 0x28, 0x06), R(mis, 0x0F, 0x10, 0x06), R(mis, 0x0F, 0x58, 0x06), R(mis, 0xF3, 0x0F, 0x58, 0x06),
		R(mis, 0x66, 0x0F, 0xFC, 0x06), R(mis, 0x66, 0x0F, 0x6F, 0x06), R(mis, 0xF3, 0x0F, 0x6F, 0x06), R(mis, 0x0F, 0x2B, 0x06));
	kprintf(" punpcklbw=%x cvtps2pd=%x movlps=%x movq=%x cvtpd2ps=%x pshufd=%x fxsave=%x fxrstor=%x err=%x\n",
		R(mis, 0x66, 0x0F, 0x60, 0x06), R(mis, 0x0F, 0x5A, 0x06), R(mis, 0x0F, 0x12, 0x06), R(mis, 0xF3, 0x0F, 0x7E, 0x06),
		R(mis, 0x66, 0x0F, 0x5A, 0x06), R(mis, 0x66, 0x0F, 0x70, 0x06, 0x00), R(XF + 8, 0x0F, 0xAE, 0x06),
		R(XF + 8, 0x0F, 0xAE, 0x0E), last.err);

	/* undefined opcodes and prefix combinations */
	kprintf("simd.undef: f3_andps=%x f2_movq=%x movsldup=%x addsubpd=%x haddpd=%x punpcklqdq_mmx=%x",
		R(XM, 0xF3, 0x0F, 0x54, 0xC1), R(XM, 0xF2, 0x0F, 0x6F, 0xC1), R(XM, 0xF3, 0x0F, 0x12, 0xC1),
		R(XM, 0x66, 0x0F, 0xD0, 0xC1), R(XM, 0x66, 0x0F, 0x7C, 0xC1), R(XM, 0x0F, 0x6C, 0xC1));
	kprintf(" psrlw_mem=%x pextrw_mem=%x movmskps_mem=%x movntps_reg=%x psrldq_mmx=%x psraq=%x",
		R(XM, 0x0F, 0x71, 0x16, 0x01), R(XM, 0x0F, 0xC5, 0x06, 0x00), R(XM, 0x0F, 0x50, 0x06),
		R(XM, 0x0F, 0x2B, 0xC1), R(XM, 0x0F, 0x73, 0xD9, 0x01), R(XM, 0x66, 0x0F, 0x73, 0xE1, 0x01));
	kprintf(" xsave=%x grp15_reg0=%x maskmovq_mem=%x movq2dq_mem=%x f2_cvtdq2ps=%x 0fe6=%x\n",
		R(XF, 0x0F, 0xAE, 0x26), R(XM, 0x0F, 0xAE, 0xC0), R(XM, 0x0F, 0xF7, 0x06), R(XM, 0xF3, 0x0F, 0xD6, 0x06),
		R(XM, 0xF2, 0x0F, 0x5B, 0xC1), R(XM, 0x0F, 0xE6, 0xC1));

	/* prefix precedence: F2/F3 over 66, the last of F2/F3 wins (XMM0 = 1.5 lanes, XMM1 = 2^k lanes) */
	{
		static const u8 seqs[4][6] = { { 0x66, 0xF3, 0x0F, 0x58, 0xC1 }, { 0xF3, 0x66, 0x0F, 0x58, 0xC1 },
		                               { 0xF3, 0xF2, 0x0F, 0x58, 0xC1 }, { 0xF2, 0xF3, 0x0F, 0x58, 0xC1 } };
		kputs("simd.prefix:");
		for (int s = 0; s < 4; s++) {
			for (int k = 0; k < 4; k++) { XV[k] = 0x3FC00000; XV[4 + k] = 0x40000000 + (k << 23); }
			ldx();
			runb(5, seqs[s], XM);
			stx();
			px("r", XW);
		}
		kputc('\n');
	}

	/* LDMXCSR/STMXCSR, reserved bits */
	*(u32 *)XM = 0x9FFF;
	int a = R(XM, 0x0F, 0xAE, 0x16);
	*(u32 *)XM = 0;
	int b = R(XM, 0x0F, 0xAE, 0x1E);
	u32 got = *(u32 *)XM;
	*(u32 *)XM = 0x11F80;
	int c = R(XM, 0x0F, 0xAE, 0x16);
	u32 errc = last.err;
	*(u32 *)XM = 0;
	R(XM, 0x0F, 0xAE, 0x1E);
	kprintf("simd.ldmxcsr: ld=%x st=%x val=%x rsvd=%x err=%x after=%x\n", a, b, got, c, errc, *(u32 *)XM);
	*(u32 *)XM = 0x1F80;
	R(XM, 0x0F, 0xAE, 0x16);

	/* FXSAVE image: x87 stack (TOP = 6), MXCSR, XMM; reserved areas untouched */
	__asm__ volatile("fninit\n fldpi\n fld1" ::: "memory");
	XCW2 = 0x27F;
	__asm__ volatile("fldcw XCW2" ::: "memory");
	for (int k = 0; k < 32; k++) XV[k] = 0x01020304 * (k + 1);
	ldx();
	*(u32 *)XM = 0xBFA5;
	R(XM, 0x0F, 0xAE, 0x16);
	memset(XF, 0xAA, 512);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf("simd.fxsave:");
	pb("cw", XF, 2); pb("sw", XF + 2, 2); pb("tw", XF + 4, 1); pb("mxcsr", XF + 24, 4); pb("mask", XF + 28, 4);
	pb("st0", XF + 32, 10); pb("st1", XF + 48, 10); kputc('\n');
	kputs("simd.fxsave.xmm:");
	pb("x0", XF + 160, 16); pb("x7", XF + 272, 16); pb("rsvd", XF + 288, 4); pb("sw_area", XF + 464, 4); kputc('\n');
	/* with OSFXSR = 0: no MXCSR, MXCSR_MASK or XMM state */
	cr4sse(0);
	memset(XF2, 0xAA, 512);
	R(XF2, 0x0F, 0xAE, 0x06);
	cr4sse(1);
	kputs("simd.fxsave.noosfxsr:");
	pb("cw", XF2, 2); pb("sw", XF2 + 2, 2); pb("tw", XF2 + 4, 1); pb("mxcsr", XF2 + 24, 4); pb("mask", XF2 + 28, 4);
	pb("st0", XF2 + 32, 10); pb("x0", XF2 + 160, 16); kputc('\n');

	/* FXRSTOR: TOP = 3, R3 and R4 valid, another MXCSR and XMM */
	memset(XF, 0, 512);
	*(u16 *)XF = 0x37F; *(u16 *)(XF + 2) = 0x1800; XF[4] = 0x18;
	*(u32 *)(XF + 24) = 0x9FC0; *(u32 *)(XF + 28) = 0xFFFF;
	*(u64 *)(XF + 32) = 0x8000000000000000ULL; *(u16 *)(XF + 40) = 0x3FFF;     /* ST0 = 1 */
	*(u64 *)(XF + 48) = 0xC000000000000000ULL; *(u16 *)(XF + 56) = 0x4000;     /* ST1 = 3 */
	for (int k = 0; k < 128; k++) XF[160 + k] = (u8)(k * 7 + 1);
	int r1 = R(XF, 0x0F, 0xAE, 0x0E);
	stx();
	__asm__ volatile("fnstenv XENV2\n stmxcsr XMX" ::: "memory");
	kprintf("simd.fxrstor: vec=%x cw=%x sw=%x tw=%x mxcsr=%x", r1, XENV2[0] & 0xFFFF, XENV2[1] & 0xFFFF, XENV2[2] & 0xFFFF, XMX);
	px("x0", XW); px("x7", XW + 28); kputc('\n');
	XF[24] = 0x80; XF[26] = 0x01;      /* MXCSR bit 16 */
	for (int k = 0; k < 128; k++) XF[160 + k] = 0x55;
	int r2 = R(XF, 0x0F, 0xAE, 0x0E);
	u32 e2 = last.err;
	stx();
	kprintf("simd.fxrstor.rsvd: vec=%x err=%x", r2, e2); px("x0", XW);
	cr4sse(0);
	int r3 = R(XF, 0x0F, 0xAE, 0x0E);
	cr4sse(1);
	stx();
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	kprintf(" noosfxsr=%x mxcsr=%x", r3, XMX); px("x0", XW); kputc('\n');
	__asm__ volatile("fninit");
	*(u32 *)XM = 0x1F80;
	R(XM, 0x0F, 0xAE, 0x16);

	/* x87 -> MMX transitions with TOP != 0; CVTPI2PD from memory does not switch */
	__asm__ volatile("fninit\n fld1\n fld1" ::: "memory");
	R(XM, 0x0F, 0xFC, 0xC1);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf("simd.mmx.enter: top=%d tags=%x", (*(u16 *)(XF + 2) >> 11) & 7, XF[4]);
	__asm__ volatile("fninit\n fld1" ::: "memory");
	R(XM, 0x66, 0x0F, 0x2A, 0x06);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf(" cvtpi2pd_mem: top=%d tags=%x", (*(u16 *)(XF + 2) >> 11) & 7, XF[4]);
	__asm__ volatile("fninit\n fld1" ::: "memory");
	R(XM, 0x66, 0x0F, 0x2A, 0xC1);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf(" cvtpi2pd_reg: top=%d tags=%x", (*(u16 *)(XF + 2) >> 11) & 7, XF[4]);
	__asm__ volatile("fninit\n fld1" ::: "memory");
	R(XM, 0x0F, 0x2A, 0x06);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf(" cvtpi2ps_mem: top=%d tags=%x", (*(u16 *)(XF + 2) >> 11) & 7, XF[4]);
	__asm__ volatile("fninit\n fld1" ::: "memory");
	R(XM, 0x0F, 0x77);
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf(" emms: top=%d tags=%x\n", (*(u16 *)(XF + 2) >> 11) & 7, XF[4]);
	__asm__ volatile("fninit");
}

void test_simd_model(void) {
	cr0set(0);
	cr4sse(1);
	__asm__ volatile("fninit");
	/* an MMX write sets the exponent word of the register to all ones; the full tag is "special" */
	*(u64 *)XM = 0x0123456789ABCDEFULL;
	__asm__ volatile("fninit\n fldz\n fstp %%st(0)" ::: "memory");     /* R7 = +0 */
	R(XM, 0x0F, 0x6F, 0x3E);                                            /* movq mm7, [esi] */
	R(XF, 0x0F, 0xAE, 0x06);
	__asm__ volatile("fnstenv XENV2" ::: "memory");
	kprintf("simdm.mmx.exp:"); pb("r7", XF + 32 + 7 * 16, 10);
	kprintf(" tag7=%x\n", (XENV2[2] >> 14) & 3);
	__asm__ volatile("fninit");

	/* encodings outside the opcode map (blank cells of SDM vol. 2, tables A-3/A-4): the model raises #UD;
	   TCG executes 66 0F 77 as EMMS and 66 0F 12 /r with a register operand as MOVHLPS */
	kprintf("simdm.undef: 66_emms=%x movlpd_reg=%x\n", R(XM, 0x66, 0x0F, 0x77), R(XM, 0x66, 0x0F, 0x12, 0xC1));
	__asm__ volatile("fninit");

	/* pending unmasked x87 exception: MMX instructions and EMMS raise #MF, SSE-only ones do not;
	   CVTPI2PS always switches to MMX (#MF), CVTPI2PD only from an MMX register */
	XCW2 = 0x37B;     /* ZE unmasked */
	__asm__ volatile("fninit\n fldcw XCW2\n fldz\n fld1\n fdiv %%st(1), %%st" ::: "memory");   /* 1/0: ES set */
	kprintf("simdm.mf: paddb=%x emms=%x addps=%x cvtpi2ps_mem=%x cvtpi2pd_mem=%x cvtpi2pd_reg=%x movq2dq=%x fxsave=%x\n",
		R(XM, 0x0F, 0xFC, 0xC1), R(XM, 0x0F, 0x77), R(XM, 0x0F, 0x58, 0xC1), R(XM, 0x0F, 0x2A, 0x06),
		R(XM, 0x66, 0x0F, 0x2A, 0x06), R(XM, 0x66, 0x0F, 0x2A, 0xC1), R(XM, 0xF3, 0x0F, 0xD6, 0xC1), R(XF, 0x0F, 0xAE, 0x06));
	__asm__ volatile("fninit");

	/* unmasked SIMD exceptions: #XM with OSXMMEXCPT, #UD without; flags set, destination kept */
	for (int k = 0; k < 4; k++) { XV[k] = 0x7F800001; XV[4 + k] = 0x3F800000; }   /* SNaN, 1.0 */
	XV[1] = 0x3F800000;
	ldx();
	*(u32 *)XM = 0x1F00;     /* IM unmasked... and every other mask set */
	R(XM, 0x0F, 0xAE, 0x16);
	int v1 = R(XM, 0x0F, 0x58, 0xC1);
	stx();
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	kprintf("simdm.xm.ie: vec=%x mxcsr=%x", v1, XMX); px("x0", XW);
	cr4sse(0); WRCR(4, RDCR(4) | 0x200);    /* OSFXSR only */
	*(u32 *)XM = 0x1F00;
	R(XM, 0x0F, 0xAE, 0x16);
	int v2 = R(XM, 0x0F, 0x58, 0xC1);
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	kprintf(" noxmmexcpt=%x mxcsr=%x\n", v2, XMX);
	cr4sse(1);
	/* unmasked DE in one lane suppresses the masked PE of another lane */
	XV[0] = 0x00000001; XV[1] = 0x3F800000; XV[2] = 0x3F800000; XV[3] = 0x3F800000;
	XV[4] = 0x3F800000; XV[5] = 0x33800000; XV[6] = 0x3F800000; XV[7] = 0x3F800000;   /* 1 + 2^-24: inexact */
	ldx();
	*(u32 *)XM = 0x1E80;     /* DM unmasked */
	R(XM, 0x0F, 0xAE, 0x16);
	int v3 = R(XM, 0x0F, 0x58, 0xC1);
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	kprintf("simdm.xm.de: vec=%x mxcsr=%x", v3, XMX);
	/* unmasked PE: #XM; unmasked OE: OE and PE; unmasked UE with an exact tiny result: UE only */
	XV[0] = 0x3F800000; XV[4] = 0x33800000; ldx();
	*(u32 *)XM = 0x0F80; R(XM, 0x0F, 0xAE, 0x16);
	int v4 = R(XM, 0xF3, 0x0F, 0x58, 0xC1);
	u32 m4; __asm__ volatile("stmxcsr XMX" ::: "memory"); m4 = XMX;
	XV[0] = 0x7F7FFFFF; XV[4] = 0x7F7FFFFF; ldx();
	*(u32 *)XM = 0x1B80; R(XM, 0x0F, 0xAE, 0x16);    /* OM unmasked */
	int v5 = R(XM, 0xF3, 0x0F, 0x59, 0xC1);
	u32 m5; __asm__ volatile("stmxcsr XMX" ::: "memory"); m5 = XMX;
	XV[0] = 0x00800000; XV[4] = 0x3F000000; ldx();      /* 2^-126 * 0.5: exact denormal */
	*(u32 *)XM = 0x1780; R(XM, 0x0F, 0xAE, 0x16);    /* UM unmasked */
	int v6 = R(XM, 0xF3, 0x0F, 0x59, 0xC1);
	u32 m6; __asm__ volatile("stmxcsr XMX" ::: "memory"); m6 = XMX;
	kprintf(" pe=%x mxcsr=%x oe=%x mxcsr=%x ue=%x mxcsr=%x\n", v4, m4, v5, m5, v6, m6);
	/* COMISS signals IE for a QNaN, UCOMISS only for an SNaN */
	XV[0] = 0x7FC00000; XV[4] = 0x3F800000; ldx();
	*(u32 *)XM = 0x1F00; R(XM, 0x0F, 0xAE, 0x16);
	kprintf("simdm.xm.comiss: comiss=%x ucomiss=%x\n", R(XM, 0x0F, 0x2F, 0xC1), R(XM, 0x0F, 0x2E, 0xC1));
	*(u32 *)XM = 0x1F80; R(XM, 0x0F, 0xAE, 0x16);

	/* two NaN operands: the first source operand, quieted (SDM vol. 1, table 4-7) */
	XV[0] = 0x7F800001; XV[4] = 0x7FC00002;    /* SNaN, QNaN */
	XV[1] = 0x7FC00001; XV[5] = 0x7FC00009;    /* QNaN, QNaN with larger payload */
	XV[2] = 0xFFA00000; XV[6] = 0x7F800003;    /* SNaN, SNaN */
	XV[3] = 0x3F800000; XV[7] = 0xFF800001;    /* 1.0, SNaN */
	ldx();
	R(XM, 0x0F, 0x58, 0xC1);
	stx();
	kprintf("simdm.nan2:"); px("addps", XW);
	XV[0] = 0x00000001; XV[1] = 0x7FF00000; XV[4] = 0x00000002; XV[5] = 0x7FF80000;  /* binary64 SNaN, QNaN */
	ldx();
	R(XM, 0xF2, 0x0F, 0x59, 0xC1);
	stx();
	px("mulsd", XW); kputc('\n');

	/* MIN/MAX with DAZ: denormal operands are zeros, and the returned operand is the zero */
	XV[0] = 0x00000001; XV[4] = 0x3F800000; XV[1] = 0x80000005; XV[5] = 0x00000003;
	XV[2] = 0x3F800000; XV[6] = 0x80400000; XV[3] = 0; XV[7] = 0;
	ldx();
	*(u32 *)XM = 0x1FC0; R(XM, 0x0F, 0xAE, 0x16);
	R(XM, 0x0F, 0x5D, 0xC1);
	stx();
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	kprintf("simdm.min.daz:"); px("minps", XW); kprintf(" mxcsr=%x\n", XMX);
	*(u32 *)XM = 0x1F80; R(XM, 0x0F, 0xAE, 0x16);

	/* RCP/RSQRT special cases: denormals give infinities, tiny reciprocals flush to zero, RSQRT of a
	   negative number is the QNaN indefinite, no flags */
	XV[4] = 0x00000010; XV[5] = 0x7F000000; XV[6] = 0x80000000; XV[7] = 0x7F7FFFFF;
	ldx();
	R(XM, 0x0F, 0x53, 0xC1);
	stx();
	kprintf("simdm.rcp:"); px("rcpps", XW);
	XV[4] = 0x80400000; XV[5] = 0x00000010; XV[6] = 0x7F800000; XV[7] = 0xBF800000;
	ldx();
	R(XM, 0x0F, 0x52, 0xC1);
	stx();
	__asm__ volatile("stmxcsr XMX" ::: "memory");
	px("rsqrtps", XW); kprintf(" mxcsr=%x\n", XMX);

	/* FXSAVE records FIP/FCS/FOP and FDP/FDS of the last x87 instruction */
	__asm__ volatile("fninit\n .globl simdm_fld_at\n simdm_fld_at: flds XM" ::: "memory");
	extern char simdm_fld_at[];
	R(XF, 0x0F, 0xAE, 0x06);
	kprintf("simdm.fxsave.ptrs: fip_ok=%d fcs=%x fop=%x fdp_ok=%d fds=%x\n", *(u32 *)(XF + 8) == (u32)simdm_fld_at,
		*(u16 *)(XF + 12), *(u16 *)(XF + 6), *(u32 *)(XF + 16) == (u32)XM, *(u16 *)(XF + 20));
	__asm__ volatile("fninit");
}
