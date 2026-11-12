/* AVX (x86_32/X86/Ext/Avx.lean, Vex.lean). test_avx is compared with QEMU:
   - avx.ud/avx.nm: the #UD/#NM matrix of VEX instructions (CR4.OSXSAVE, XCR0[2:1], CR0.TS, CR0.EM,
     CR4.OSFXSR, VEX.L/VEX.W/VEX.vvvv/ModRM.mod constraints, prefixes before VEX);
   - avx.align: only the explicitly aligned moves (class 1) fault on misaligned operands, VEX.256
     ones need 32-byte alignment;
   - avx.zero: VEX.128 zeroes bits 255:128 of the destination, legacy SSE keeps them; VZEROUPPER,
     VZEROALL;
   - avx.mask: VMASKMOVPS/PD fault suppression across a not-present page and a read-only page;
   - avx.ldmxcsr, avx.w, avx.vvvv, avx.code16 (VEX in a 16-bit protected-mode code segment);
   - avxk lines: random cases of the AVX-only shuffles, permutes, broadcasts, inserts/extracts,
     masked moves, blends, tests and the 32 VCMP predicates, recomputed by test/avx_ref.py check.
   test_avx_model runs in the MODEL-ONLY section (expected values in model-only.expected): VEX.L = 1 of
   the LIG scalar forms, is4 with imm8[7] = 1, MXCSR.MM, unmasked SIMD exceptions, #AC.
   TCG deviations: rules in qemu-deviations.txt (avx.*). */
#include "sys.h"

static u32 rs = 0x510E527F;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

static u8 code[64] __attribute__((aligned(16)));
void (*volatile avx_codep)(void) = (void (*)(void))code;
/* YMMk = YI[8k .. 8k+7] (bits 127:0 in the first four words) */
__attribute__((used, aligned(32))) u32 YI[64], YO[64];
__attribute__((used, aligned(64))) u8 AM[512];
__attribute__((used)) u32 GI[3], GO[3], FLO, MXI = 0x1F80, MXO;

/* Run the bytes with YMM0..7 = YI, MXCSR = MXI, EAX/ECX/EDX = GI, ESI = EDI = mem, arithmetic flags
   clear; returns the vector (0xFFFF: none). YO, GO, FLO, MXO hold the state after (also after a
   fault). Needs AVX enabled. */
static int runy(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) code[k] = b[k];
	code[n] = 0xC3;
	int v = TRY(__asm__ volatile(
		"ldmxcsr MXI\n"
		"vmovdqu YI, %%ymm0\n vmovdqu YI+32, %%ymm1\n vmovdqu YI+64, %%ymm2\n vmovdqu YI+96, %%ymm3\n"
		"vmovdqu YI+128, %%ymm4\n vmovdqu YI+160, %%ymm5\n vmovdqu YI+192, %%ymm6\n vmovdqu YI+224, %%ymm7\n"
		"movl GI, %%eax\n movl GI+4, %%ecx\n movl GI+8, %%edx\n movl %%esi, %%edi\n"
		"pushfl\n andl $~0x8D5, (%%esp)\n popfl\n"
		"call *avx_codep\n"
		"pushfl\n popl FLO\n movl %%eax, GO\n movl %%ecx, GO+4\n movl %%edx, GO+8\n"
		:: "S"(mem) : "memory", "eax", "ecx", "edx", "edi", "cc"));
	__asm__ volatile("stmxcsr MXO\n"
		"vmovdqu %%ymm0, YO\n vmovdqu %%ymm1, YO+32\n vmovdqu %%ymm2, YO+64\n vmovdqu %%ymm3, YO+96\n"
		"vmovdqu %%ymm4, YO+128\n vmovdqu %%ymm5, YO+160\n vmovdqu %%ymm6, YO+192\n vmovdqu %%ymm7, YO+224\n"
		"ldmxcsr MXI" ::: "memory");
	return v;
}
#define Y(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runy(sizeof _b, _b, mem); })
/* The same without touching vector state (for the #UD/#NM checks) */
static int runn(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) code[k] = b[k];
	code[n] = 0xC3;
	return TRY(__asm__ volatile("call *avx_codep" :: "S"(mem), "D"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}
#define N(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runn(sizeof _b, _b, mem); })

static void xsetbv(u32 v) { __asm__ volatile(".byte 0x0f,0x01,0xd1" :: "c"(0), "a"(v), "d"(0)); }
static void cr0set(u32 bits) { WRCR(0, (RDCR(0) & ~0xC) | 0x22 | bits); }
static void avx_on(void) { WRCR(4, RDCR(4) | 0x40600); xsetbv(7); cr0set(0); }
static void py(const char *k, const u32 *p) {   /* a 256-bit value, high word first */
	kprintf(" %s=", k);
	for (int w = 7; w >= 0; w--) puthex(p[w]);
}
static void px(const char *k, const u32 *p) { kprintf(" %s=%x%x%x%x", k, p[3], p[2], p[1], p[0]); }
static void yfill(void) { for (int k = 0; k < 64; k++) YI[k] = rnd(); }
static int memcmp_eq(const u32 *a, const u32 *b) { for (int k = 0; k < 8; k++) if (a[k] != b[k]) return 0; return 1; }

/* VEX prefix: map 1..3, pp, L, W, vvvv (register number); C5 when possible */
static int vexp(u8 *b, int map, int pp, int L, int W, int vvvv) {
	u8 p = (u8)((~vvvv & 15) << 3 | L << 2 | pp);
	if (map == 1 && !W) { b[0] = 0xC5; b[1] = (u8)(0x80 | p); return 2; }
	b[0] = 0xC4; b[1] = (u8)(0xE0 | map); b[2] = (u8)(W << 7 | p); return 3;
}

/* ---- #UD / #NM ---- */

static void t_ud(void) {
	/* vaddps ymm0, ymm1, ymm2; vzeroupper; vpermilps ymm0, ymm1, ymm2 (W0); vmovd xmm0, eax */
	avx_on();
	WRCR(4, RDCR(4) & ~0x40000);
	int a0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2), a1 = N(AM, 0xC5, 0xF8, 0x77);
	WRCR(4, RDCR(4) | 0x40000);
	xsetbv(3);
	int b0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2), b1 = N(AM, 0xC5, 0xF8, 0x77);
	xsetbv(1);
	int c0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2);
	xsetbv(7);
	cr0set(8);   /* TS */
	int d0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2), d1 = N(AM, 0xC5, 0xF8, 0x77), d2 = N(AM, 0xC4, 0xE2, 0x75, 0x0C, 0xC2);
	int d3 = N(AM, 0xC5, 0xF0, 0x28, 0xC1);                     /* vmovaps with vvvv != 1111b: #UD first */
	int d4 = N(AM, 0xC4, 0xE2, 0xF5, 0x0C, 0xC2);               /* vpermilps with VEX.W = 1 */
	int d5 = N(AM, 0xC4, 0xE2, 0x7D, 0x41, 0xC1);               /* vphminposuw with VEX.L = 1 */
	cr0set(4);   /* EM: ignored by VEX instructions */
	int e0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2), e1 = N(AM, 0xC5, 0xF8, 0x77);
	cr0set(0);
	WRCR(4, RDCR(4) & ~0x200);   /* OSFXSR = 0: ignored by VEX instructions */
	int f0 = N(AM, 0xC5, 0xF4, 0x58, 0xC2), f1 = N(AM, 0xC5, 0xF9, 0x6E, 0xC0);
	WRCR(4, RDCR(4) | 0x200);
	kprintf("avx.ud: noosxsave=%x,%x xcr0_3=%x,%x xcr0_1=%x\n", a0, a1, b0, b1, c0);
	kprintf("avx.nm: ts=%x,%x,%x vvvv=%x w1=%x l1=%x\n", d0, d1, d2, d3, d4, d5);
	kprintf("avx.em: %x,%x noosfxsr=%x,%x\n", e0, e1, f0, f1);
	/* prefixes before VEX (#UD), LOCK, unknown maps */
	kprintf("avx.prefix: 66=%x f3=%x f2=%x lock=%x map0=%x map4=%x seg=%x a16=%x\n",
		N(AM, 0x66, 0xC5, 0xF4, 0x58, 0xC2), N(AM, 0xF3, 0xC5, 0xF4, 0x58, 0xC2), N(AM, 0xF2, 0xC5, 0xF4, 0x58, 0xC2),
		N(AM, 0xF0, 0xC5, 0xF4, 0x58, 0x06), N(AM, 0xC4, 0xE0, 0x74, 0x58, 0xC2), N(AM, 0xC4, 0xE4, 0x74, 0x58, 0xC2),
		N(AM, 0x3E, 0xC5, 0xF4, 0x58, 0x06), N(AM, 0x67, 0xC5, 0xF4, 0x58, 0xC2));
	/* VEX.W: #UD for the W0-only forms; ignored by VPEXTRD, VMOVD, VCVTSI2SS outside 64-bit mode */
	yfill(); GI[0] = 0x12345678;
	kprintf("avx.w: permilps=%x broadcastss=%x insertf128=%x maskmovps=%x testps=%x blendvps=%x perm2f128=%x",
		Y(AM, 0xC4, 0xE2, 0xF5, 0x0C, 0xC2), Y(AM, 0xC4, 0xE2, 0xFD, 0x18, 0x06), Y(AM, 0xC4, 0xE3, 0xF5, 0x18, 0xC2, 0x01),
		Y(AM, 0xC4, 0xE2, 0xF1, 0x2C, 0x06), Y(AM, 0xC4, 0xE2, 0xFD, 0x0E, 0xC1), Y(AM, 0xC4, 0xE3, 0xF1, 0x4A, 0xC2, 0x30),
		Y(AM, 0xC4, 0xE3, 0xF5, 0x06, 0xC2, 0x21));
	int w0 = Y(AM, 0xC4, 0xE3, 0xF9, 0x16, 0xC0, 0x02);       /* vpextrd eax, xmm0, 2 (W1) */
	u32 g = GO[0];
	int w1 = Y(AM, 0xC4, 0xE1, 0xF9, 0x6E, 0xC0);             /* vmovd xmm0, eax (W1) */
	kprintf(" pextrd=%x eax=%x movd=%x", w0, g, w1); px("x0", YO);
	kputc('\n');
	/* VEX.vvvv: 1111b required by single-source forms, all four bits on the EPYC 7742 (C4 with vvvv[3] alone
	   wrong: #UD); as a register number, vvvv[3] is ignored */
	kprintf("avx.vvvv: movaps=%x zeroupper=%x movd=%x ptest=%x c4bit3=%x", Y(AM, 0xC5, 0xF0, 0x28, 0xC1), Y(AM, 0xC5, 0xF0, 0x77),
		Y(AM, 0xC5, 0xF1, 0x6E, 0xC0), Y(AM, 0xC4, 0xE2, 0x71, 0x17, 0xC1), Y(AM, 0xC4, 0xE1, 0x38, 0x28, 0xC1));
	py("y0", YO);
	kprintf(" vaddbit3=%x", Y(AM, 0xC4, 0xE1, 0x3C, 0x58, 0xC2));   /* vaddps ymm0, ymm8 (= ymm0), ymm2 */
	py("y0", YO); 
	/* VMOVSS/SD: load and store need VEX.vvvv = 1111b on the EPYC 7742 (the manuals name only the store) */
	kprintf(" movss_ld=%x", Y(AM, 0xC5, 0xE2, 0x10, 0x06)); py("y0", YO);
	kprintf(" movsd_ld=%x movss_st=%x\n", Y(AM, 0xC4, 0xE1, 0x43, 0x10, 0x06), Y(AM, 0xC5, 0xE2, 0x11, 0x06));
	/* ModRM.mod: memory-only and register-only forms */
	kprintf("avx.mod: movntps_reg=%x movlps_st_reg=%x maskmovps_reg=%x broadcastf128_reg=%x movmskps_mem=%x pextrw_mem=%x shiftimm_mem=%x lddqu_reg=%x\n",
		Y(AM, 0xC5, 0xFC, 0x2B, 0xC1), Y(AM, 0xC5, 0xF8, 0x13, 0xC1), Y(AM, 0xC4, 0xE2, 0x71, 0x2C, 0xC2),
		Y(AM, 0xC4, 0xE2, 0x7D, 0x1A, 0xC1), Y(AM, 0xC5, 0xF8, 0x50, 0x06), Y(AM, 0xC5, 0xF9, 0xC5, 0x06, 0x01),
		Y(AM, 0xC5, 0xF9, 0x71, 0x16, 0x01), Y(AM, 0xC5, 0xFF, 0xF0, 0xC1));
	/* VEX.L: VEX.128-only forms */
	kprintf("avx.l: movhlps=%x pinsrw=%x pextrb=%x insertps=%x dppd=%x pcmpistri=%x aesenc=%x pclmul=%x ldmxcsr=%x broadcastsd_l0=%x perm2f128_l0=%x\n",
		Y(AM, 0xC5, 0xF4, 0x12, 0xC2), Y(AM, 0xC5, 0xF5, 0xC4, 0xC0, 0x01), Y(AM, 0xC4, 0xE3, 0x7D, 0x14, 0xC0, 0x01),
		Y(AM, 0xC4, 0xE3, 0x75, 0x21, 0xC2, 0x10), Y(AM, 0xC4, 0xE3, 0x75, 0x41, 0xC2, 0x31), Y(AM, 0xC4, 0xE3, 0x7D, 0x63, 0xC1, 0x00),
		Y(AM, 0xC4, 0xE2, 0x75, 0xDC, 0xC2), Y(AM, 0xC4, 0xE3, 0x75, 0x44, 0xC2, 0x00), Y(AM, 0xC5, 0xFC, 0xAE, 0x16),
		Y(AM, 0xC4, 0xE2, 0x79, 0x19, 0x06), Y(AM, 0xC4, 0xE3, 0x71, 0x06, 0xC2, 0x20));
}

/* ---- alignment ---- */

static void t_align(void) {
	avx_on();
	yfill();
	for (int k = 0; k < 512; k++) AM[k] = (u8)rnd();
	u8 *a = AM + 64;
	kprintf("avx.align: movaps128=%x,%x,%x movaps256=%x,%x,%x movdqa256=%x,%x movntps256=%x,%x movntdq256=%x movntdqa=%x,%x movapd_st=%x,%x\n",
		Y(a, 0xC5, 0xF8, 0x28, 0x06), Y(a + 8, 0xC5, 0xF8, 0x28, 0x06), Y(a + 16, 0xC5, 0xF8, 0x28, 0x06),
		Y(a, 0xC5, 0xFC, 0x28, 0x06), Y(a + 16, 0xC5, 0xFC, 0x28, 0x06), Y(a + 4, 0xC5, 0xFC, 0x28, 0x06),
		Y(a, 0xC5, 0xFD, 0x6F, 0x06), Y(a + 16, 0xC5, 0xFD, 0x6F, 0x06),
		Y(a, 0xC5, 0xFC, 0x2B, 0x06), Y(a + 16, 0xC5, 0xFC, 0x2B, 0x06), Y(a + 16, 0xC5, 0xFD, 0xE7, 0x06),
		Y(a + 16, 0xC4, 0xE2, 0x79, 0x2A, 0x06), Y(a + 8, 0xC4, 0xE2, 0x79, 0x2A, 0x06),
		Y(a + 32, 0xC5, 0xFD, 0x29, 0x06), Y(a + 48, 0xC5, 0xFD, 0x29, 0x06));
	kprintf("avx.unaligned: movups=%x movdqu=%x addps=%x paddb=%x broadcastf128=%x lddqu=%x permilps=%x movntdq_st=%x",
		Y(a + 1, 0xC5, 0xFC, 0x10, 0x06), Y(a + 3, 0xC5, 0xFE, 0x6F, 0x06), Y(a + 5, 0xC5, 0xFC, 0x58, 0x06),
		Y(a + 7, 0xC5, 0xF9, 0xFC, 0x06), Y(a + 9, 0xC4, 0xE2, 0x7D, 0x1A, 0x06), Y(a + 11, 0xC5, 0xFF, 0xF0, 0x06),
		Y(a + 13, 0xC4, 0xE3, 0x7D, 0x04, 0x06, 0x1B), Y(a + 8, 0xC5, 0xF9, 0xE7, 0x06));
	py("y0", YO); kputc('\n');
}

/* ---- zeroing of bits 255:128 ---- */

static void t_zero(void) {
	avx_on();
	for (int k = 0; k < 32; k++) ((u32 *)AM)[k] = rnd();
	yfill(); Y(AM, 0x0F, 0x58, 0xC1);                    /* addps xmm0, xmm1 (legacy) */
	kputs("avx.zero: legacy"); py("y0", YO);
	yfill(); Y(AM, 0xC5, 0xF0, 0x58, 0xC2);              /* vaddps xmm0, xmm1, xmm2 */
	kputs(" vex128"); py("y0", YO);
	yfill(); Y(AM, 0xC5, 0xF4, 0x58, 0xC2);              /* vaddps ymm0, ymm1, ymm2 */
	kputs(" vex256"); py("y0", YO);
	yfill(); Y(AM, 0xF3, 0x0F, 0x10, 0x06);              /* movss xmm0, [esi] */
	kputs(" movss"); py("y0", YO);
	yfill(); Y(AM, 0xC5, 0xFA, 0x10, 0x06);              /* vmovss xmm0, [esi] */
	kputs(" vmovss"); py("y0", YO);
	yfill(); Y(AM, 0xC5, 0xF2, 0x10, 0xC2);              /* vmovss xmm0, xmm1, xmm2 */
	kputs(" vmovss3"); py("y0", YO);
	yfill(); GI[0] = 0x89ABCDEF; Y(AM, 0xC5, 0xF9, 0x6E, 0xC0);   /* vmovd xmm0, eax */
	kputs(" vmovd"); py("y0", YO);
	yfill(); Y(AM, 0xC4, 0xE3, 0x7D, 0x19, 0xC8, 0x01);  /* vextractf128 xmm0, ymm1, 1 */
	kputs(" vextractf128"); py("y0", YO);
	yfill(); Y(AM, 0xC5, 0xF9, 0x73, 0xD1, 0x08);        /* vpsrlq xmm0, xmm1, 8 (destination VEX.vvvv) */
	kputs(" vpsrlq"); py("y0", YO); py("y1", YO + 8);
	kputc('\n');
	yfill(); Y(AM, 0xC5, 0xF8, 0x77);                    /* vzeroupper */
	kputs("avx.zeroupper:");
	for (int k = 0; k < 8; k++) py(k ? "" : "y", YO + 8 * k);
	kputc('\n');
	yfill(); Y(AM, 0xC5, 0xFC, 0x77);                    /* vzeroall */
	kputs("avx.zeroall:");
	for (int k = 0; k < 8; k++) py(k ? "" : "y", YO + 8 * k);
	kputc('\n');
	/* VZEROUPPER does not touch MXCSR or the x87/MMX state */
	MXI = 0x1F80 | 0x3F; yfill(); Y(AM, 0xC5, 0xF8, 0x77); MXI = 0x1F80;
	kprintf("avx.zeroupper.mxcsr: %x\n", MXO);
}

/* ---- VMASKMOVPS/PD with paging ---- */

static void t_mask(void) {
	avx_on();
	u32 *pd = page_alloc(1), *pt = page_alloc(1);
	u8 *fr = page_alloc(3);
	for (u32 i = 0; i < 16; i++) pd[i] = (i << 22) | 0x87;
	u32 L = 0x40000000;
	pd[L >> 22] = (u32)pt | 7;
	pt[0] = (u32)fr | 7; pt[1] = 0; pt[2] = ((u32)fr + 0x2000) | 5;   /* RW, not present, read-only */
	for (int k = 0; k < 0x1000; k++) fr[k] = (u8)(k * 7 + 3), fr[0x2000 + k] = (u8)(k * 5 + 1);
	WRCR(3, (u32)pd);
	WRCR(4, RDCR(4) | 0x10);
	WRCR(0, RDCR(0) | 0x80010000);    /* PG, WP */
	u8 *e = (u8 *)(L + 0x1000);       /* first byte of the not-present page */
	yfill();
	for (int k = 0; k < 8; k++) YI[k] = 0;   /* the load destination: the line does not depend on the seed */
	/* masks in YMM1: element k selected iff its sign bit is set */
	for (int k = 0; k < 8; k++) YI[8 + k] = k < 2 ? 0x80000000 : 0x7FFFFFFF;
	int l0 = Y(e - 8, 0xC4, 0xE2, 0x71, 0x2C, 0x06);      /* vmaskmovps xmm0, xmm1, [e-8]: elements 2, 3 masked out */
	u32 r0[8]; memcpy(r0, YO, 32);
	int l1 = Y(e - 8, 0xC4, 0xE2, 0x75, 0x2C, 0x06);      /* ymm: elements 2..7 masked out */
	u32 r1[8]; memcpy(r1, YO, 32);
	for (int k = 0; k < 8; k++) YI[8 + k] = 0;
	int l2 = Y(e + 64, 0xC4, 0xE2, 0x75, 0x2C, 0x06);     /* all masked out, on the not-present page */
	u32 r2[8]; memcpy(r2, YO, 32);
	YI[8 + 2] = 0x80000000;
	int l3 = Y(e - 8, 0xC4, 0xE2, 0x71, 0x2C, 0x06);      /* element 2 selected: #PF at e */
	u32 cr2a = last.cr2 - L, erra = last.err;
	/* VMASKMOVPD: qword masks */
	for (int k = 0; k < 8; k++) YI[8 + k] = (k == 1) ? 0x80000000 : 0;
	int l4 = Y(e - 8, 0xC4, 0xE2, 0x75, 0x2D, 0x06);      /* element 0 selected (in the present page) */
	u32 r4[8]; memcpy(r4, YO, 32);
	kprintf("avx.mask.load: ps128=%x", l0); py("r", r0); kprintf(" ps256=%x", l1); py("r", r1);
	kprintf(" none=%x", l2); py("r", r2); kprintf(" sel=%x cr2=%x err=%x pd=%x", l3, cr2a, erra, l4); py("r", r4);
	kputc('\n');
	/* stores: data YMM0, mask YMM1 */
	yfill();
	for (int k = 0; k < 8; k++) YI[8 + k] = k < 2 ? 0x80000000 : 0;
	int s0 = Y(e - 8, 0xC4, 0xE2, 0x75, 0x2E, 0x06);      /* vmaskmovps [e-8], ymm1, ymm0 */
	u32 h0 = ((u32 *)(e - 8))[0], h1 = ((u32 *)(e - 8))[1];
	YI[8 + 3] = 0x80000000;
	u32 b0 = ((u32 *)(e - 16))[2];
	int s1 = Y(e - 16, 0xC4, 0xE2, 0x75, 0x2E, 0x06);     /* element 3 at e - 4; element 4.. masked out */
	u32 b1 = ((u32 *)(e - 16))[2];
	YI[8 + 4] = 0x80000000;
	u32 c0 = ((u32 *)(e - 16))[0];
	int s2 = Y(e - 16, 0xC4, 0xE2, 0x75, 0x2E, 0x06);     /* element 4 at e: #PF, nothing written */
	u32 cr2b = last.cr2 - L, errb = last.err, c1 = ((u32 *)(e - 16))[0];
	for (int k = 0; k < 8; k++) YI[8 + k] = 0;
	int s3 = Y((u8 *)(L + 0x2000), 0xC4, 0xE2, 0x75, 0x2E, 0x06);   /* all masked out, read-only page */
	YI[8 + 1] = 0x80000000;
	int s4 = Y((u8 *)(L + 0x2000), 0xC4, 0xE2, 0x75, 0x2F, 0x06);   /* vmaskmovpd: element 0 selected: #PF (W) */
	u32 errc = last.err;
	WRCR(0, RDCR(0) & ~0x80010000);
	kprintf("avx.mask.store: lo=%x %x %x mid=%x before=%x after=%x pf=%x cr2=%x err=%x unchanged=%x ro_none=%x ro_sel=%x err=%x\n",
		s0, h0, h1, s1, b0, b1, s2, cr2b, errb, c0 == c1, s3, s4, errc);
}

/* ---- VLDMXCSR / VSTMXCSR ---- */

static void t_mxcsr(void) {
	avx_on();
	u32 *m = (u32 *)(AM + 128);
	m[0] = 0x9FC0;
	int a = Y(m, 0xC5, 0xF8, 0xAE, 0x16);                 /* vldmxcsr [esi] */
	u32 v0 = MXO;
	m[1] = 0;
	int b = Y(m + 1, 0xC5, 0xF8, 0xAE, 0x1E);             /* vstmxcsr [esi] */
	m[2] = 0x11F80;
	int c = Y(m + 2, 0xC5, 0xF8, 0xAE, 0x16);             /* reserved bit: #GP(0) */
	u32 v2 = MXO;
	kprintf("avx.ldmxcsr: ld=%x mxcsr=%x st=%x mem=%x rsvd=%x err=%x after=%x unaligned=%x\n", a, v0, b, m[1], c, last.err, v2,
		Y(AM + 129, 0xC5, 0xF8, 0xAE, 0x1E));
}

/* ---- VEX in a 16-bit protected-mode code segment ---- */

#define CODE16_AVX 0xA8
__asm__(".globl avx16\navx16: .code16\n"
	" .byte 0xC5, 0xF4, 0x58, 0xC2\n"                 /* vaddps ymm0, ymm1, ymm2 */
	" .byte 0xC4, 0xE3, 0x7D, 0x04, 0xD9, 0x1B\n"     /* vpermilps ymm3, ymm1, 0x1B */
	" .byte 0xC5, 0xF9, 0x7E, 0xC8\n"                 /* vmovd eax, xmm1 */
	" .byte 0x66, 0xCB\n"                             /* lretl */
	" .code32\n");
extern char avx16[];
__attribute__((used)) struct { u32 off; u16 sel; } __attribute__((packed)) fp16;

static void t_code16(void) {
	avx_on();
	gdt[CODE16_AVX >> 3] = seg_desc((u32)avx16 & ~0xFFFF, 0xFFFF, 0x9A, 0x0);
	fp16.off = (u32)avx16 & 0xFFFF; fp16.sel = CODE16_AVX;
	yfill();
	int v = TRY(__asm__ volatile(
		"vmovdqu YI, %%ymm0\n vmovdqu YI+32, %%ymm1\n vmovdqu YI+64, %%ymm2\n vmovdqu YI+96, %%ymm3\n"
		"lcall *fp16\n movl %%eax, GO\n"
		"vmovdqu %%ymm0, YO\n vmovdqu %%ymm3, YO+96\n" ::: "memory", "eax", "ecx", "edx", "cc"));
	kprintf("avx.code16: vec=%x", v);
	if (v == 0xFFFF) { py("y0", YO); py("y3", YO + 24); kprintf(" eax=%x", GO[0]); }
	kputc('\n');
}

/* ---- avxk: random cases of the AVX-only operations (test/avx_ref.py) ---- */

/* binary32/binary64 lane generators for the compares: zeros, denormals, infinities, NaNs, equal
   values */
static u32 f32(void) {
	u32 s = rnd() & 0x80000000, m = rnd() & 0x7FFFFF;
	switch (rnd() % 10) {
	case 0: return s;
	case 1: return s | (m ? m : 1);
	case 2: return s | 0x7F800000;
	case 3: return s | 0x7FC00000 | (m & 0x3FFFFF);
	case 4: return s | 0x7F800000 | ((m & 0x3FFFFF) ? (m & 0x3FFFFF) : 1);
	case 5: return s | 0x3F800000;
	default: return s | ((120 + rnd() % 16) << 23) | (m & 0x7F0000);
	}
}
static void f64(u32 *p) {
	u32 s = rnd() & 0x80000000, h = rnd() & 0xFFFFF, l = rnd();
	switch (rnd() % 10) {
	case 0: p[0] = 0; p[1] = s; break;
	case 1: p[0] = l | 1; p[1] = s | (h & 0xF); break;
	case 2: p[0] = 0; p[1] = s | 0x7FF00000; break;
	case 3: p[0] = l; p[1] = s | 0x7FF80000 | (h & 0x7FFFF); break;
	case 4: p[0] = l | 1; p[1] = s | 0x7FF00000 | (h & 0x7FFFF); break;
	case 5: p[0] = 0; p[1] = s | 0x3FF00000; break;
	default: p[0] = l & 0xFFFF0000; p[1] = s | ((1015 + rnd() % 16) << 20) | (h & 0xF0000); break;
	}
}

struct kop { const char *name; u8 map, pp, op, l, w, flags; };
enum { KV = 1, KI = 2, KM = 4, KR = 8, KS = 16, K4 = 32, KF = 64, KD = 128 };
/* (KV: VEX.vvvv = ymm1 source, else 1111b; KI imm8; KM memory only; KR register only; KS store;
   K4 is4 = ymm3; KF/KD: FP inputs, single/double; l: 0, 1, 2 = random) */
static const struct kop kops[] = {
	{ "permilps_i", 3, 1, 0x04, 2, 0, KI }, { "permilpd_i", 3, 1, 0x05, 2, 0, KI },
	{ "permilps_v", 2, 1, 0x0C, 2, 0, KV }, { "permilpd_v", 2, 1, 0x0D, 2, 0, KV },
	{ "perm2f128", 3, 1, 0x06, 1, 0, KV | KI },
	{ "shufps", 1, 0, 0xC6, 2, 0, KV | KI }, { "shufpd", 1, 1, 0xC6, 2, 0, KV | KI },
	{ "unpcklps", 1, 0, 0x14, 2, 0, KV }, { "unpckhpd", 1, 1, 0x15, 2, 0, KV },
	{ "broadcastss", 2, 1, 0x18, 2, 0, KM }, { "broadcastsd", 2, 1, 0x19, 1, 0, KM },
	{ "broadcastf128", 2, 1, 0x1A, 1, 0, KM },
	{ "insertf128", 3, 1, 0x18, 1, 0, KV | KI }, { "extractf128", 3, 1, 0x19, 1, 0, KI | KS },
	{ "maskmovps_ld", 2, 1, 0x2C, 2, 0, KV | KM }, { "maskmovpd_ld", 2, 1, 0x2D, 2, 0, KV | KM },
	{ "maskmovps_st", 2, 1, 0x2E, 2, 0, KV | KM | KS }, { "maskmovpd_st", 2, 1, 0x2F, 2, 0, KV | KM | KS },
	{ "blendps", 3, 1, 0x0C, 2, 0, KV | KI }, { "blendpd", 3, 1, 0x0D, 2, 0, KV | KI },
	{ "blendvps", 3, 1, 0x4A, 2, 0, KV | K4 }, { "blendvpd", 3, 1, 0x4B, 2, 0, KV | K4 },
	{ "testps", 2, 1, 0x0E, 2, 0, 0 }, { "testpd", 2, 1, 0x0F, 2, 0, 0 }, { "ptest", 2, 1, 0x17, 2, 0, 0 },
	{ "movddup", 1, 3, 0x12, 2, 0, 0 }, { "movsldup", 1, 2, 0x12, 2, 0, 0 }, { "movshdup", 1, 2, 0x16, 2, 0, 0 },
	{ "cmpps", 1, 0, 0xC2, 2, 0, KV | KI | KF }, { "cmppd", 1, 1, 0xC2, 2, 0, KV | KI | KD },
	{ "cmpss", 1, 2, 0xC2, 0, 0, KV | KI | KF }, { "cmpsd", 1, 3, 0xC2, 0, 0, KV | KI | KD },
};
#define NKOPS (sizeof kops / sizeof kops[0])

static void k_case(u32 n, const struct kop *o) {
	u8 b[16];
	int L = o->l == 2 ? (int)(rnd() % 2) : o->l;
	int mem = (o->flags & KM) || (!(o->flags & KR) && rnd() % 3 == 0);
	int k = vexp(b, o->map, o->pp, L, o->w, (o->flags & KV) ? 1 : 0);
	u8 imm = rnd();
	if (o->op == 0xC2 && o->map == 1) imm = rnd() % 4 ? imm & 31 : imm;
	if (o->flags & K4) imm = (u8)((imm & 0x0F) | 0x30);
	b[k++] = o->op;
	/* reg = 0 (destination, or the stored source), r/m = ymm2 or [esi] */
	b[k++] = mem ? 0x06 : 0xC2;
	if ((o->flags & (KI | K4)) || o->map == 3) b[k++] = imm;
	yfill();
	for (int w = 0; w < 24; w++) ((u32 *)AM)[w] = rnd();
	u8 *m = AM + 4 * (rnd() % 8);
	if (o->flags & (KF | KD)) {
		for (int r = 1; r <= 2; r++)
			for (int w = 0; w < 8; w += (o->flags & KD) ? 2 : 1) {
				u32 *p = YI + 8 * r + w;
				if (o->flags & KD) f64(p); else p[0] = f32();
			}
		for (int w = 0; w < 8; w++) {
			if (rnd() % 4 == 0) YI[16 + w] = YI[8 + w];     /* equal operands */
			((u32 *)m)[w] = YI[16 + w];
		}
		MXI = 0x1F80 | (rnd() % 2 ? 0x40 : 0) | (rnd() % 4 == 0 ? 0x8000 : 0);
	}
	if (o->op >= 0x2C && o->op <= 0x2F && o->map == 2)       /* masks: a mix of selected elements */
		for (int w = 0; w < 8; w++) YI[8 + w] = rnd() % 2 ? YI[8 + w] | 0x80000000 : YI[8 + w] & 0x7FFFFFFF;
	u32 min[8], ymi[8];
	memcpy(min, m, 32);
	memcpy(ymi, YI, 32);
	int v = runy(k, b, m);
	MXI = 0x1F80;
	kprintf("avxk %d %s l=%d", n, o->name, L);
	if ((o->flags & (KI | K4)) || o->map == 3) kprintf(" imm=%x", imm);
	py("d", ymi); if (o->flags & KV) py("a", YI + 8);
	if (mem) py("m", min); else py("b", YI + 16);
	if (o->flags & K4) py("c", YI + 24);
	kprintf(" -> vec=%x", v);
	if (v == 0xFFFF) {
		if (!(o->flags & KS)) py("r", YO);
		else if (mem) py("mem", (u32 *)m);
		else py("r2", YO + 16);
		kprintf(" fl=%x mx=%x", FLO & 0x8D5, MXO);
	}
	kputc('\n');
}

void test_avx(void) {
	if (!has_feature(1, 0, 2, 26) || !has_feature(1, 0, 2, 28)) { kputs("avx: not reported\n"); return; }
	u32 cr0 = RDCR(0), cr4 = RDCR(4);
	rs = fuzz_seed(rs);
	t_ud();
	t_align();
	t_zero();
	t_mask();
	t_mxcsr();
	t_code16();
	avx_on();
	u32 nk = param("avxk", 1500);
	for (u32 k = 0; k < nk; k++) k_case(k, &kops[rnd() % NKOPS]);
	MXI = 0x1F80;
	__asm__ volatile("vzeroall\n ldmxcsr MXI" ::: "memory");
	WRCR(0, cr0); WRCR(4, cr4);
}

/* ---- MODEL-ONLY ---- */

static u8 ucode[64];
static u8 ustk[256] __attribute__((aligned(16)));
__attribute__((used)) u32 au_ebx, au_esp, au_fl, au_eip;
/* Run the bytes at CPL 3 with EBX = au_ebx and EFLAGS = fl; 0x40: completed (INT 0x40) */
static int urun(const u8 *b, int n, u32 fl) {
	for (int k = 0; k < n; k++) ucode[k] = b[k];
	ucode[n] = 0xCD; ucode[n + 1] = 0x40;
	au_esp = (u32)ustk + sizeof ustk; au_fl = fl; au_eip = (u32)ucode;
	return TRY(__asm__ volatile(
		"pushl $0x23\n pushl au_esp\n pushl au_fl\n pushl $0x1B\n pushl au_eip\n"
		"movl $0x23, %%eax\n movl %%eax, %%ds\n movl %%eax, %%es\n movl %%eax, %%fs\n movl %%eax, %%gs\n"
		"movl au_ebx, %%ebx\n iret" ::: "eax", "ebx", "ecx", "edx", "esi", "edi", "memory"));
}
#define UA(off, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; au_ebx = (u32)AM + 256 + (off); urun(_b, sizeof _b, 0x40202); })

void test_avx_model(void) {
	if (!has_feature(1, 0, 2, 28)) return;
	u32 cr0 = RDCR(0), cr4 = RDCR(4);
	avx_on();
	/* VEX.L = 1 of the LIG scalar forms: the same result as VEX.L = 0, bits 255:128 zeroed (TCG: #UD,
	   bits 255:128 kept, or an abort for VROUNDSS/SD) */
	rs = 0x1F83D9AB;
	yfill();
	u32 r0[8], r1[8];
	static const u8 lig[][6] = {
		{ 0xC5, 0xF2, 0x58, 0xC2 }, { 0xC5, 0xF6, 0x58, 0xC2 },                 /* vaddss L0, L1 */
		{ 0xC5, 0xF3, 0x5E, 0xC2 }, { 0xC5, 0xF7, 0x5E, 0xC2 },                 /* vdivsd */
		{ 0xC5, 0xF2, 0xC2, 0xC2, 0x1D }, { 0xC5, 0xF6, 0xC2, 0xC2, 0x1D },     /* vcmpss ge_oq */
		{ 0xC5, 0xF2, 0x10, 0xC2 }, { 0xC5, 0xF6, 0x10, 0xC2 },                 /* vmovss xmm, xmm, xmm */
		{ 0xC5, 0xF3, 0x2A, 0xC0 }, { 0xC5, 0xF7, 0x2A, 0xC0 },                 /* vcvtsi2sd xmm0, xmm1, eax */
		{ 0xC4, 0xE3, 0x71, 0x0A, 0xC2, 0x01 }, { 0xC4, 0xE3, 0x75, 0x0A, 0xC2, 0x01 },   /* vroundss */
		{ 0xC5, 0xFA, 0x2D, 0xC1 }, { 0xC5, 0xFE, 0x2D, 0xC1 },                 /* vcvtss2si eax, xmm1 */
	};
	static const u8 ligl[] = { 4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 6, 6, 4, 4 };
	kputs("avxm.lig:");
	GI[0] = 0xFFFFFF85;
	for (int k = 0; k < 14; k += 2) {
		int a = runy(ligl[k], lig[k], AM); memcpy(r0, YO, 32); u32 g0 = GO[0];
		int b = runy(ligl[k + 1], lig[k + 1], AM); memcpy(r1, YO, 32);
		int same = a == b && memcmp_eq(r0, r1);
		kprintf(" %x/%x%s", a, b, same && GO[0] == g0 ? "=" : "!");
	}
	py("y0", YO); kputc('\n');
	/* is4: imm8[7] is ignored outside 64-bit mode (vblendvps ymm0, ymm1, ymm2, ymm3 with 0xB0) */
	yfill();
	Y(AM, 0xC4, 0xE3, 0x75, 0x4A, 0xC2, 0x30); memcpy(r0, YO, 32);
	Y(AM, 0xC4, 0xE3, 0x75, 0x4A, 0xC2, 0xBF); memcpy(r1, YO, 32);
	kprintf("avxm.is4: same=%d", memcmp_eq(r0, r1)); py("y0", r0); kputc('\n');
	/* MXCSR.MM (AMD misaligned SSE mode) does not apply to VEX: aligned moves still fault, the others
	   never did */
	MXI = 0x21F80;
	u8 *a = AM + 64;
	kprintf("avxm.mm: movaps=%x movaps256_16=%x movntdqa=%x addps=%x legacy_movaps=%x legacy_addps=%x\n",
		Y(a + 8, 0xC5, 0xF8, 0x28, 0x06), Y(a + 16, 0xC5, 0xFC, 0x28, 0x06), Y(a + 8, 0xC4, 0xE2, 0x79, 0x2A, 0x06),
		Y(a + 4, 0xC5, 0xFC, 0x58, 0x06), Y(a + 8, 0x0F, 0x28, 0x06), Y(a + 8, 0x0F, 0x58, 0x06));
	MXI = 0x1F80;
	/* unmasked SIMD exceptions: #XM with the flags set and the destination unchanged; #UD with
	   CR4.OSXMMEXCPT = 0 */
	yfill();
	YI[8] = 0x3F800000; YI[16] = 0; YI[8 + 5] = 0x7F800000; YI[16 + 5] = 0x7F800000;   /* 1/0 (low), inf-inf (high) */
	MXI = 0x1F80 & ~0x200;        /* ZE unmasked */
	int x0 = Y(AM, 0xC5, 0xF4, 0x5E, 0xC2);                /* vdivps ymm0, ymm1, ymm2 */
	u32 m0 = MXO, same0 = YO[0] == YI[0] && YO[7] == YI[7];
	MXI = 0x1F80 & ~0x80;         /* IE unmasked: inf - inf in the high half */
	int x1 = Y(AM, 0xC5, 0xF4, 0x5C, 0xC2);                /* vsubps ymm0, ymm1, ymm2 */
	u32 m1 = MXO;
	WRCR(4, RDCR(4) & ~0x400);
	int x2 = Y(AM, 0xC5, 0xF4, 0x5C, 0xC2);
	WRCR(4, RDCR(4) | 0x400);
	MXI = 0x1F80;
	kprintf("avxm.xm: divps=%x mxcsr=%x unchanged=%d subps=%x mxcsr=%x noxmmexcpt=%x\n", x0, m0, same0, x1, m1, x2);
	/* VDPPS ymm0, ymm1, ymm2, 0xF1 with only IE unmasked: the stages (all multiplies, the first
	   additions, the last additions) span both 128-bit lanes, so the SNaN product of the low lane (#XM,
	   IE) suppresses the inexact last addition 1 + 2^-24 of the high lane (no PE). The inputs are printed
	   for test/avx_ref.py (a = YMM1, b = YMM2). TCG has no staging. */
	yfill();
	for (int k = 0; k < 8; k++) { YI[8 + k] = 0x3F800000; YI[16 + k] = 0x3F800000; }
	YI[8] = 0x7F800001;                                   /* low lane: SNaN * 1.0, then 1.0 * 1.0 */
	YI[16 + 5] = 0; YI[16 + 6] = 0x33800000; YI[16 + 7] = 0;   /* high lane products 1, 0, 2^-24, 0 */
	MXI = 0x1F00;
	int dp = Y(AM, 0xC4, 0xE3, 0x75, 0x40, 0xC2, 0xF1);
	kprintf("avxm.dpps256: imm=f1 mx=1f00"); py("a", YI + 8); py("b", YI + 16);
	kprintf(" vec=%x mxo=%x unchanged=%d\n", dp, MXO, memcmp_eq(YO, YI));
	/* VHADDPS/VHADDPD/VHSUBPS ymm0, ymm1, ymm2 with two-NaN pairs in both lanes: HADD returns the NaN of
	   the higher element (the manuals' first operand), HSUB of the lower (Sse.hop; checked by
	   test/avx_ref.py; TCG returns the larger significand) */
	{
		static const u32 hn[16] = { 0x7FC00001, 0x7FC00002, 0x7F800003, 0x7FC00004, 0x7FC00011, 0x7FC00012, 0x3F800000, 0x7F800014,
		                            0xFFC00005, 0x3F800000, 0x7F800006, 0x7F800007, 0x7FC00015, 0x7FC00016, 0x7FC00017, 0x7FC00018 };
		for (int k = 0; k < 16; k++) YI[8 + k] = hn[k];
		MXI = 0x1F80;
		kprintf("avxm.hnan256: mx=1f80"); py("a", YI + 8); py("b", YI + 16);
		int h0 = Y(AM, 0xC5, 0xF7, 0x7C, 0xC2); kprintf(" vhaddps=%x", h0); py("r", YO); kprintf(" mxo=%x", MXO);
		int h1 = Y(AM, 0xC5, 0xF7, 0x7D, 0xC2); kprintf(" vhsubps=%x", h1); py("r", YO); kprintf(" mxo=%x", MXO);
		kputc('\n');
		/* binary64: (QNaN, QNaN) | (SNaN, 1.0) in each lane */
		static const u32 hd[16] = { 1, 0x7FF80000, 2, 0x7FF80000, 3, 0x7FF00000, 0, 0x3FF00000,
		                            4, 0x7FF00000, 5, 0x7FF00000, 6, 0xFFF80000, 7, 0x7FF80000 };
		for (int k = 0; k < 16; k++) YI[8 + k] = hd[k];
		kprintf("avxm.hnan256pd: mx=1f80"); py("a", YI + 8); py("b", YI + 16);
		int h2 = Y(AM, 0xC5, 0xF5, 0x7C, 0xC2); kprintf(" vhaddpd=%x", h2); py("r", YO); kprintf(" mxo=%x", MXO);
		int h3 = Y(AM, 0xC5, 0xF5, 0x7D, 0xC2); kprintf(" vhsubpd=%x", h3); py("r", YO); kprintf(" mxo=%x\n", MXO);
	}
	MXI = 0x1F80;
	/* #AC at CPL 3 with CR0.AM and EFLAGS.AC: VEX operands must be aligned to min(size, 16) (AMD APM
	   vol. 2, table 8-7: 256-bit media 16); class-1 moves raise #GP first; VMASKMOVPx never #AC */
	WRCR(0, RDCR(0) | 0x40000);
	kprintf("avxm.ac: movups256_8=%x movups256_16=%x addss_2=%x addss_4=%x movsd_4=%x movaps_8=%x broadcastss_2=%x maskmovps_4=%x vmovd_2=%x pextrw_1=%x\n",
		UA(8, 0xC5, 0xFC, 0x10, 0x03), UA(16, 0xC5, 0xFC, 0x10, 0x03), UA(2, 0xC5, 0xF2, 0x58, 0x03), UA(4, 0xC5, 0xF2, 0x58, 0x03),
		UA(4, 0xC5, 0xFB, 0x10, 0x03), UA(8, 0xC5, 0xF8, 0x28, 0x03), UA(2, 0xC4, 0xE2, 0x79, 0x18, 0x03),
		UA(4, 0xC4, 0xE2, 0x71, 0x2C, 0x03), UA(2, 0xC5, 0xF9, 0x6E, 0x03), UA(1, 0xC4, 0xE3, 0x79, 0x15, 0x03, 0x00));
	WRCR(0, RDCR(0) & ~0x40000);
	/* the VEX.vvvv/L/W #UD checks come before #NM (QEMU checks VEX.L and VEX.W after CR0.TS) */
	cr0set(8);
	kprintf("avxm.ud_before_nm: w1=%x l1=%x movd_l1=%x\n", N(AM, 0xC4, 0xE2, 0xF5, 0x0C, 0xC2), N(AM, 0xC4, 0xE2, 0x7D, 0x41, 0xC1),
		N(AM, 0xC5, 0xFD, 0x7E, 0xC0));
	cr0set(0);
	MXI = 0x1F80;
	__asm__ volatile("vzeroall\n ldmxcsr MXI" ::: "memory");
	WRCR(0, cr0); WRCR(4, cr4);
}
