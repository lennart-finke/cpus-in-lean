/* AVX2, FMA3, F16C (x86_32/X86/Ext/Avx2.lean). test_avx2 is compared with QEMU:
   - avx2.cpuid, avx2.ud, avx2.nm: CPUID bits; the #UD encodings (VEX.L/VEX.W/VEX.vvvv/ModRM.mod of the
     AVX2-only forms, no FMA4 on Zen 2, the gather rules: ModRM.mod = 11b, no VSIB byte, dest/mask/index
     not distinct, 16-bit addressing); #NM with CR0.TS;
   - avx2.gather: every gather form and length with in-range indices (all scales, negative indices,
     masks with selected and masked-out elements, VEX.128 zeroing);
   - avx2.gather.pf: a gather whose fourth selected element is on a not-present page: #PF with the
     elements before it loaded and their mask elements cleared, the others untouched; masked-out
     elements on that page do not fault; a zero mask makes no access; the restarted instruction
     completes;
   - avx2.maskmov: VPMASKMOVD/Q stores next to a read-only page with the selected elements writable;
   - avx2.fma: FMA special cases (0 * inf + QNaN/SNaN/number, NaN operand order, signed zeros,
     exact cancellation in every rounding mode, the underflow boundary with FTZ/DAZ, overflow);
   - avx2k / avx2g lines: random cases recomputed by test/avx2_ref.py (independent reference: exact
     FMA with fractions, binary16 conversions, permutes, variable shifts, per-lane shuffles, gathers).
   test_avx2_model runs in the MODEL-ONLY section (model-only.expected): VEX.L = 1 of the scalar FMA forms,
   VCVTPS2PH ignoring MXCSR.FTZ and VCVTPH2PS ignoring DAZ without DE (TCG applies both), unmasked
   SIMD exceptions of FMA and VCVTPS2PH (destination/memory unchanged), VPMASKMOV loads not touching
   masked-out elements and stores that fault writing nothing, #AC for gathers and VPMASKMOV at CPL 3,
   a gather fault with masks of mixed sign/value bits, segment-limit faults of gather elements, and
   #UD before #NM; plus avx2m random F16C lines with denormals and FTZ/DAZ (avx2_ref.py). */
#include "sys.h"

static u32 rs = 0x9B05688C;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

static u8 code[64] __attribute__((aligned(16)));
void (*volatile avx2_codep)(void) = (void (*)(void))code;
/* YMMk = YI[8k .. 8k+7] (bits 127:0 in the first four words) */
__attribute__((used, aligned(32))) u32 Y2I[64], Y2O[64];
__attribute__((used, aligned(64))) u32 GM[1024];   /* gather / memory operand area */
__attribute__((used)) u32 G2I[3], G2O[3], FL2O, MX2I = 0x1F80, MX2O;

/* Run the bytes with YMM0..7 = Y2I, MXCSR = MX2I, EAX/ECX/EDX = G2I, ESI = EDI = mem, arithmetic flags
   clear; returns the vector (0xFFFF: none). Y2O, G2O, FL2O, MX2O hold the state after (also after a
   fault). Needs AVX enabled. */
static int runy(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) code[k] = b[k];
	code[n] = 0xC3;
	int v = TRY(__asm__ volatile(
		"ldmxcsr MX2I\n"
		"vmovdqu Y2I, %%ymm0\n vmovdqu Y2I+32, %%ymm1\n vmovdqu Y2I+64, %%ymm2\n vmovdqu Y2I+96, %%ymm3\n"
		"vmovdqu Y2I+128, %%ymm4\n vmovdqu Y2I+160, %%ymm5\n vmovdqu Y2I+192, %%ymm6\n vmovdqu Y2I+224, %%ymm7\n"
		"movl G2I, %%eax\n movl G2I+4, %%ecx\n movl G2I+8, %%edx\n movl %%esi, %%edi\n"
		"pushfl\n andl $~0x8D5, (%%esp)\n popfl\n"
		"call *avx2_codep\n"
		"pushfl\n popl FL2O\n movl %%eax, G2O\n movl %%ecx, G2O+4\n movl %%edx, G2O+8\n"
		:: "S"(mem) : "memory", "eax", "ecx", "edx", "edi", "cc"));
	__asm__ volatile("stmxcsr MX2O\n"
		"vmovdqu %%ymm0, Y2O\n vmovdqu %%ymm1, Y2O+32\n vmovdqu %%ymm2, Y2O+64\n vmovdqu %%ymm3, Y2O+96\n"
		"vmovdqu %%ymm4, Y2O+128\n vmovdqu %%ymm5, Y2O+160\n vmovdqu %%ymm6, Y2O+192\n vmovdqu %%ymm7, Y2O+224\n"
		"ldmxcsr MX2I" ::: "memory");
	return v;
}
#define Y(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runy(sizeof _b, _b, mem); })
static int runn(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) code[k] = b[k];
	code[n] = 0xC3;
	return TRY(__asm__ volatile("call *avx2_codep" :: "S"(mem), "D"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}
#define N(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runn(sizeof _b, _b, mem); })

static void xsetbv(u32 v) { __asm__ volatile(".byte 0x0f,0x01,0xd1" :: "c"(0), "a"(v), "d"(0)); }
static void cr0set(u32 bits) { WRCR(0, (RDCR(0) & ~0xC) | 0x22 | bits); }
static void avx_on(void) { WRCR(4, RDCR(4) | 0x40600); xsetbv(7); cr0set(0); }
static void py(const char *k, const u32 *p) {   /* a 256-bit value, high word first */
	kprintf(" %s=", k);
	for (int w = 7; w >= 0; w--) puthex(p[w]);
}
static void yfill(void) { for (int k = 0; k < 64; k++) Y2I[k] = rnd(); }
static void gfill(u32 n) { for (u32 w = 0; w < 1024; w++) GM[w] = (w * 0x9E3779B1u) ^ (n * 0x85EBCA6Bu); }

/* VEX prefix: map 1..3, pp, L, W, vvvv (register number); C5 when possible */
static int vexp(u8 *b, int map, int pp, int L, int W, int vvvv) {
	u8 p = (u8)((~vvvv & 15) << 3 | L << 2 | pp);
	if (map == 1 && !W) { b[0] = 0xC5; b[1] = (u8)(0x80 | p); return 2; }
	b[0] = 0xC4; b[1] = (u8)(0xE0 | map); b[2] = (u8)(W << 7 | p); return 3;
}

/* A gather VEX.66.0F38 op (90..93) dest, [ESI + index*2^scale + disp8], mask; returns the length */
static int gather_bytes(u8 *b, int op, int L, int W, int dest, int mask, int index, int scale, int disp) {
	int k = vexp(b, 2, 1, L, W, mask);
	b[k++] = (u8)op;
	b[k++] = (u8)(0x44 | dest << 3);                    /* mod 01, rm 100: VSIB + disp8 */
	b[k++] = (u8)(scale << 6 | index << 3 | 6);         /* base ESI */
	b[k++] = (u8)disp;
	return k;
}

/* ---- CPUID, #UD, #NM ---- */

static void t_ud(void) {
	u32 r[4];
	cpuid(1, 0, r);
	u32 c1 = r[2];
	kprintf("avx2.cpuid: fma=%d f16c=%d avx2=%d fma4=%d\n", (c1 >> 12) & 1, (c1 >> 29) & 1,
		has_feature(7, 0, 1, 5), has_feature(0x80000001, 0, 2, 16));
	avx_on();
	u8 *m = (u8 *)(GM + 512);
	kprintf("avx2.ud: permq_w0=%x permq_l0=%x permd_w1=%x permd_l0=%x bcasti128_reg=%x bcasti128_l0=%x bcastsd_l0=%x pbroadcastb_w1=%x pblendd_w1=%x psravd_w1=%x inserti128_l0=%x extracti128_vvvv=%x perm2i128_w1=%x pblendvb_w1=%x movntdqa_reg=%x pmovmskb_mem=%x pmaskmov_reg=%x cvtph2ps_w1=%x cvtps2ph_vvvv=%x\n",
		N(m, 0xC4, 0xE3, 0x7D, 0x00, 0xC1, 0x1B), N(m, 0xC4, 0xE3, 0xF9, 0x00, 0xC1, 0x1B), N(m, 0xC4, 0xE2, 0xF5, 0x36, 0xC2),
		N(m, 0xC4, 0xE2, 0x71, 0x36, 0xC2), N(m, 0xC4, 0xE2, 0x7D, 0x5A, 0xC1), N(m, 0xC4, 0xE2, 0x79, 0x5A, 0x06),
		N(m, 0xC4, 0xE2, 0x79, 0x19, 0xC1), N(m, 0xC4, 0xE2, 0xFD, 0x78, 0xC1), N(m, 0xC4, 0xE3, 0xF5, 0x02, 0xC2, 0x55),
		N(m, 0xC4, 0xE2, 0xF5, 0x46, 0xC2), N(m, 0xC4, 0xE3, 0x71, 0x38, 0xC2, 0x01), N(m, 0xC4, 0xE3, 0x75, 0x39, 0xC1, 0x01),
		N(m, 0xC4, 0xE3, 0xF5, 0x46, 0xC2, 0x21), N(m, 0xC4, 0xE3, 0xF5, 0x4C, 0xC2, 0x30), N(m, 0xC4, 0xE2, 0x7D, 0x2A, 0xC1),
		N(m, 0xC5, 0xFD, 0xD7, 0x06), N(m, 0xC4, 0xE2, 0x75, 0x8C, 0xC2), N(m, 0xC4, 0xE2, 0xF9, 0x13, 0xC1),
		N(m, 0xC4, 0xE3, 0x75, 0x1D, 0xC1, 0x00));
	/* no FMA4 (VEX.0F3A 68 VFMADDPS, 5C VFMADDSUBPS, 78 VFNMADDPS, 6A VFMADDSS), no VAES / VPCLMULQDQ ymm */
	kprintf("avx2.ud.fma4: 68=%x 5c=%x 78=%x 6a=%x 7f=%x vaesenc256=%x vpclmul256=%x phminposuw256=%x\n",
		N(m, 0xC4, 0xE3, 0x71, 0x68, 0xC2, 0x30), N(m, 0xC4, 0xE3, 0x71, 0x5C, 0xC2, 0x30), N(m, 0xC4, 0xE3, 0x71, 0x78, 0xC2, 0x30),
		N(m, 0xC4, 0xE3, 0x71, 0x6A, 0xC2, 0x30), N(m, 0xC4, 0xE3, 0xF1, 0x7F, 0xC2, 0x30), N(m, 0xC4, 0xE2, 0x75, 0xDC, 0xC2),
		N(m, 0xC4, 0xE3, 0x75, 0x44, 0xC2, 0x00), N(m, 0xC4, 0xE2, 0x7D, 0x41, 0xC1));
	/* gathers: vpgatherdd ymm0, [esi+ymm1*4], ymm2 and its broken variants */
	kprintf("avx2.ud.gather: mod3=%x norm=%x dm=%x di=%x mi=%x a16=%x\n",
		N(m, 0xC4, 0xE2, 0x6D, 0x90, 0xC1), N(m, 0xC4, 0xE2, 0x6D, 0x90, 0x06),
		N(m, 0xC4, 0xE2, 0x7D, 0x90, 0x04, 0x8E), N(m, 0xC4, 0xE2, 0x6D, 0x90, 0x04, 0x86),
		N(m, 0xC4, 0xE2, 0x6D, 0x90, 0x04, 0x96), N(m, 0x67, 0xC4, 0xE2, 0x6D, 0x90, 0x04, 0x8E));
	cr0set(8);   /* TS */
	kprintf("avx2.nm: paddb256=%x gather=%x fma=%x cvtph2ps=%x\n", N(m, 0xC5, 0xF5, 0xFC, 0xC2),
		N(m, 0xC4, 0xE2, 0x6D, 0x90, 0x04, 0x8E), N(m, 0xC4, 0xE2, 0x71, 0x98, 0xC2), N(m, 0xC4, 0xE2, 0x7D, 0x13, 0xC1));
	cr0set(0);
	xsetbv(3);
	kprintf("avx2.ud.xcr0: paddb256=%x fma=%x\n", N(m, 0xC5, 0xF5, 0xFC, 0xC2), N(m, 0xC4, 0xE2, 0x71, 0x98, 0xC2));
	xsetbv(7);
}

/* ---- gathers ---- */

static void t_gather(void) {
	avx_on();
	static const u8 ops[] = { 0x90, 0x91, 0x92, 0x93 };
	for (int o = 0; o < 4; o++)
		for (int L = 0; L < 2; L++)
			for (int W = 0; W < 2; W++) {
				u8 b[8];
				int scale = (int)(rnd() % 4), disp = (int)(rnd() % 64) - 32;
				int k = gather_bytes(b, ops[o], L, W, 0, 2, 1, scale, disp);
				yfill();
				gfill(o * 4 + L * 2 + W);
				/* indices in YMM1: dwords or qwords in [-48, 48) */
				for (int e = 0; e < 8; e++) {
					int ix = (int)(rnd() % 96) - 48;
					if (ops[o] & 1) { if (e % 2 == 0) { Y2I[8 + e] = (u32)ix; Y2I[8 + e + 1] = ix < 0 ? ~0u : 0; } }
					else Y2I[8 + e] = (u32)ix;
				}
				u32 yi[24];
				memcpy(yi, Y2I, sizeof yi);
				int v = runy(k, b, (u8 *)GM + 2048);
				kprintf("avx2.gather %02x L=%d W=%d s=%d d=%d vec=%x", ops[o], L, W, scale, disp, v);
				py("x", yi + 8); py("m", yi + 16); py("d", yi);
				py("r", Y2O); py("mo", Y2O + 16); py("xo", Y2O + 8);
				kputc('\n');
			}
}

/* page setup: PL+0 RW, PL+0x1000 not present, PL+0x2000 read-only (as t_avx.c), PL+0x3000 RW (the
   frame behind PL+0x1000), PL+0x4000 read-only */
static u32 PL = 0x40000000;
static u32 *pg_pt;
static void paging_on(void) {
	u32 *pd = page_alloc(1), *pt = page_alloc(1);
	u8 *fr = page_alloc(3);
	for (u32 i = 0; i < 16; i++) pd[i] = (i << 22) | 0x87;
	pd[PL >> 22] = (u32)pt | 7;
	pt[0] = (u32)fr | 7; pt[1] = 0; pt[2] = ((u32)fr + 0x2000) | 5;
	pt[3] = ((u32)fr + 0x1000) | 7;   /* the frame of the not-present page, mapped here */
	pt[4] = ((u32)fr + 0x2000) | 5;   /* read-only again, after the writable PL + 0x3000 */
	for (int k = 0; k < 0x1000; k++) fr[k] = (u8)(k * 7 + 3), fr[0x1000 + k] = (u8)(k * 3 + 11), fr[0x2000 + k] = (u8)(k * 5 + 1);
	pg_pt = pt;
	WRCR(3, (u32)pd);
	WRCR(4, RDCR(4) | 0x10);
	WRCR(0, RDCR(0) | 0x80010000);    /* PG, WP */
}
static void paging_off(void) { WRCR(0, RDCR(0) & ~0x80010000); }

static void t_gather_pf(void) {
	avx_on();
	paging_on();
	u8 *e = (u8 *)(PL + 0x1000);      /* first byte of the not-present page */
	u8 b[8];
	/* vpgatherdd ymm0, [esi + ymm1*4 + 0], ymm2; ESI = e - 16: indices 0..3 present, 4.. not present */
	int k = gather_bytes(b, 0x90, 1, 0, 0, 2, 1, 2, 0);
	yfill();
	static const int ix[8] = { 0, 3, 1, 2, 4, 6, 5, 7 };
	for (int i = 0; i < 8; i++) { Y2I[8 + i] = (u32)ix[i]; Y2I[16 + i] = (i == 3 || i == 5) ? 0x7FFFFFFF : 0x80000000 | rnd(); }
	u32 yi[24];
	memcpy(yi, Y2I, sizeof yi);
	int v0 = runy(k, b, e - 16);
	u32 cr2 = last.cr2 - PL, err = last.err;
	kprintf("avx2.gather.pf: vec=%x cr2=%x err=%x", v0, cr2, err);
	py("m", yi + 16); py("r", Y2O); py("mo", Y2O + 16);
	/* restart after mapping the page (the frame of e mapped at PL + 0x1000) */
	memcpy(Y2I, Y2O, 96);
	pg_pt[1] = pg_pt[3]; invlpg((u32)e);
	int v1 = runy(k, b, e - 16);
	kprintf(" restart=%x", v1); py("r", Y2O); py("mo", Y2O + 16);
	kputc('\n');
	pg_pt[1] = 0; invlpg((u32)e);
	/* masked-out elements on the not-present page: no fault; zero mask: no access, mask cleared */
	yfill();
	for (int i = 0; i < 8; i++) { Y2I[8 + i] = (u32)ix[i]; Y2I[16 + i] = ix[i] < 4 ? 0x80000000 : 0x7FFFFFFF; }
	int v2 = runy(k, b, e - 16);
	u32 r2[16]; memcpy(r2, Y2O, 32); memcpy(r2 + 8, Y2O + 16, 32);
	for (int i = 0; i < 8; i++) Y2I[16 + i] = 0x7FFFFFFF & rnd();
	int v3 = runy(k, b, e + 64);
	kprintf("avx2.gather.pf.masked: vec=%x", v2); py("r", r2); py("mo", r2 + 8);
	kprintf(" zero=%x", v3); py("r", Y2O); py("mo", Y2O + 16);
	/* vgatherqpd xmm0 (two elements): the second on the not-present page */
	int k2 = gather_bytes(b, 0x93, 0, 1, 0, 2, 1, 0, 0);
	yfill();
	Y2I[8] = 0; Y2I[9] = 0; Y2I[10] = 16; Y2I[11] = 0;
	Y2I[17] = 0x80000000; Y2I[19] = 0x80000000;
	memcpy(yi, Y2I, sizeof yi);
	int v4 = runy(k2, b, e - 8);
	kprintf(" qpd=%x cr2=%x", v4, last.cr2 - PL); py("d", yi); py("r", Y2O); py("mo", Y2O + 16);
	kputc('\n');
	paging_off();
}

/* ---- VPMASKMOVD/Q stores next to a read-only page ---- */

static void t_maskmov(void) {
	avx_on();
	paging_on();
	u8 *ro = (u8 *)(PL + 0x4000);
	yfill();
	for (int i = 0; i < 8; i++) Y2I[8 + i] = i < 4 ? 0x80000000 : 0;    /* elements 0..3 selected */
	/* vpmaskmovd [ro-16], ymm1, ymm0: the selected elements below the read-only page */
	int s0 = Y(ro - 16, 0xC4, 0xE2, 0x75, 0x8E, 0x06);
	u32 *w = (u32 *)(ro - 16);
	kprintf("avx2.maskmov.store: ro=%x mem=%x,%x,%x,%x", s0, w[0], w[1], w[2], w[3]);
	for (int i = 0; i < 8; i++) Y2I[8 + i] = 0;
	Y2I[8 + 1] = 0x80000000;     /* vpmaskmovq: element 0 selected, in the writable page */
	int s1 = Y(ro - 8, 0xC4, 0xE2, 0xF5, 0x8E, 0x06);
	kprintf(" q=%x mem=%x,%x", s1, w[2], w[3]);
	for (int i = 0; i < 8; i++) Y2I[8 + i] = 0x7FFFFFFF;
	int s2 = Y(ro, 0xC4, 0xE2, 0x75, 0x8E, 0x06);              /* nothing selected on the read-only page */
	Y2I[8 + 2] = 0x80000000;
	int s3 = Y(ro, 0xC4, 0xE2, 0x75, 0x8E, 0x06);              /* element 2 selected: #PF (write) */
	kprintf(" none=%x sel=%x err=%x cr2=%x\n", s2, s3, last.err, last.cr2 - PL);
	/* loads with every selected element present */
	yfill();
	for (int i = 0; i < 8; i++) Y2I[8 + i] = i % 3 ? 0x80000000 : 0x7FFFFFFF;
	int l0 = Y(ro - 32, 0xC4, 0xE2, 0x75, 0x8C, 0x06);
	kprintf("avx2.maskmov.load: d=%x", l0); py("r", Y2O);
	int l1 = Y(ro - 32, 0xC4, 0xE2, 0xF1, 0x8C, 0x06);
	kprintf(" q128=%x", l1); py("r", Y2O); kputc('\n');
	paging_off();
}

/* ---- FMA special cases ---- */

static u32 fma_case(int op, int W, u32 mx, const u32 *x, const u32 *y, const u32 *z) {
	/* vfmadd...ps/pd xmm0 (op1 = x), xmm1 (op2 = y), xmm2 (op3 = z): scalar opcodes use element 0 */
	yfill();
	for (int k = 0; k < 4; k++) { Y2I[k] = x[k]; Y2I[8 + k] = y[k]; Y2I[16 + k] = z[k]; }
	u8 b[8];
	int n = vexp(b, 2, 1, 0, W, 1);
	b[n++] = (u8)op; b[n++] = 0xC2;
	MX2I = mx;
	int v = runy(n, b, GM);
	MX2I = 0x1F80;
	return (u32)v;
}

static void t_fma(void) {
	avx_on();
	/* binary32 operands: +0, -0, +inf, -inf, QNaN a, SNaN b, 1.0, -1.0, denormal, max, min normal */
	static const u32 sv[] = { 0, 0x80000000, 0x7F800000, 0xFF800000, 0x7FC00011, 0x7F800022, 0x3F800000, 0xBF800000,
		0x00000123, 0x7F7FFFFF, 0x00800000, 0x7FC00033, 0xFF800044 };
	static const char *names[] = { "+0", "-0", "+inf", "-inf", "qnan", "snan", "1", "-1", "den", "max", "minn", "qnan2", "snan2" };
	/* the special-case table: x * y + z (132 form, op 0x98 with op3 = y via r/m: x = op1, y = op3, z = op2) */
	static const u8 tab[][3] = {
		{ 0, 2, 6 }, { 2, 0, 6 }, { 0, 2, 4 }, { 2, 1, 4 }, { 0, 2, 5 }, { 3, 0, 1 },
		{ 4, 5, 11 }, { 11, 4, 5 }, { 6, 11, 4 }, { 5, 4, 11 }, { 6, 6, 5 }, { 12, 6, 4 },
		{ 2, 6, 3 }, { 2, 7, 2 }, { 6, 2, 3 }, { 0, 6, 1 }, { 1, 6, 1 }, { 0, 7, 0 }, { 1, 1, 1 },
		{ 6, 6, 7 }, { 8, 6, 0 }, { 8, 8, 0 }, { 9, 9, 3 }, { 10, 10, 0 }, { 9, 6, 9 },
	};
	for (u32 t = 0; t < sizeof tab / sizeof tab[0]; t++) {
		kprintf("avx2.fma %s*%s+%s:", names[tab[t][0]], names[tab[t][1]], names[tab[t][2]]);
		for (int rc = 0; rc < 4; rc++) {
			u32 x[4] = { sv[tab[t][0]] }, y[4] = { sv[tab[t][1]] }, z[4] = { sv[tab[t][2]] };
			/* vfmadd132ss xmm0, xmm1, xmm2: xmm0 = xmm0 * xmm2 + xmm1 */
			int v = fma_case(0x99, 0, 0x1F80 | rc << 13, x, z, y);
			kprintf(" %x/%x/%x", v, Y2O[0], MX2O);
		}
		/* the negated forms in round-to-nearest, DAZ, FTZ */
		static const u8 nops[] = { 0x9B, 0x9D, 0x9F };
		for (int q = 0; q < 3; q++) {
			u32 x[4] = { sv[tab[t][0]] }, y[4] = { sv[tab[t][1]] }, z[4] = { sv[tab[t][2]] };
			int v = fma_case(nops[q], 0, 0x1F80 | (q == 1 ? 0x40 : 0) | (q == 2 ? 0x8000 : 0), x, z, y);
			kprintf(" %x/%x/%x", v, Y2O[0], MX2O);
		}
		kputc('\n');
	}
	/* operand order of the three forms: 132, 213, 231 with three distinct NaNs */
	static const u32 n1[4] = { 0x7FC00001, 0x3F800000, 0x7FC00001, 0x40000000 }, n2[4] = { 0x7FC00002, 0x7FC00002, 0x40400000, 0x7FA00002 },
		n3[4] = { 0x7FC00003, 0x7FC00003, 0x7FC00003, 0x7FC00003 };
	kputs("avx2.fma.nanorder:");
	static const u8 forms[] = { 0x98, 0xA8, 0xB8, 0x9C, 0xAE };
	for (int f = 0; f < 5; f++) {
		int v = fma_case(forms[f], 0, 0x1F80, n1, n2, n3);
		kprintf(" %x/%x,%x,%x,%x/%x", v, Y2O[0], Y2O[1], Y2O[2], Y2O[3], MX2O);
	}
	kputc('\n');
	/* binary64: underflow boundary, exact cancellation, a product needing more than 106 bits */
	static const u32 d1[4] = { 0x00000001, 0x3FF00000, 0, 0x80100000 }, d2[4] = { 0, 0x00100000, 0x00000001, 0x3FE00000 },
		d3[4] = { 0xFFFFFFFF, 0x3FEFFFFF, 0, 0x80000000 };
	kputs("avx2.fma.pd:");
	for (int rc = 0; rc < 4; rc++)
		for (int ftz = 0; ftz < 2; ftz++) {
			int v = fma_case(0xA8, 1, 0x1F80 | rc << 13 | ftz << 15, d1, d2, d3);
			kprintf(" %x/%x%x,%x%x/%x", v, Y2O[1], Y2O[0], Y2O[3], Y2O[2], MX2O);
		}
	kputc('\n');
}

/* ---- avx2k: random cases (test/avx2_ref.py) ---- */

/* binary32/binary64 operands for the FMA cases: zeros, denormals, infinities, NaNs, 1.0, operands
   that cancel, values near the overflow and underflow thresholds */
static u32 f32r(void) {
	u32 s = rnd() & 0x80000000, m = rnd() & 0x7FFFFF;
	switch (rnd() % 14) {
	case 0: return s;
	case 1: return s | (m ? m : 1);
	case 2: return s | 0x7F800000;
	case 3: return s | 0x7FC00000 | (m & 0x3FFFFF);
	case 4: return s | 0x7F800000 | ((m & 0x3FFFFF) ? (m & 0x3FFFFF) : 1);
	case 5: return s | 0x3F800000;
	case 6: return s | ((1 + rnd() % 24) << 23) | m;
	case 7: return s | ((230 + rnd() % 24) << 23) | m;
	case 8: return s | ((120 + rnd() % 16) << 23) | (m & 0x7FFFF0);
	default: return s | ((100 + rnd() % 56) << 23) | m;
	}
}
static void f64r(u32 *p) {
	u32 s = rnd() & 0x80000000, h = rnd() & 0xFFFFF, l = rnd();
	switch (rnd() % 14) {
	case 0: p[0] = 0; p[1] = s; break;
	case 1: p[0] = l | 1; p[1] = s | (h & 0xF); break;
	case 2: p[0] = 0; p[1] = s | 0x7FF00000; break;
	case 3: p[0] = l; p[1] = s | 0x7FF80000 | (h & 0x7FFFF); break;
	case 4: p[0] = l | 1; p[1] = s | 0x7FF00000 | (h & 0x7FFFF); break;
	case 5: p[0] = 0; p[1] = s | 0x3FF00000; break;
	case 6: p[0] = l; p[1] = s | ((1 + rnd() % 60) << 20) | h; break;
	case 7: p[0] = l; p[1] = s | ((1990 + rnd() % 56) << 20) | h; break;
	default: p[0] = l; p[1] = s | ((900 + rnd() % 240) << 20) | h; break;
	}
}

struct kop { const char *name; u8 map, pp, op, l, w, flags; };
enum { KV = 1, KI = 2, KM = 4, KR = 8, KS = 16, K4 = 32, KF = 64, KD = 128 };
/* KV: VEX.vvvv = ymm1 source, else 1111b; KI imm8; KM memory only; KR register only; KS store (to
   memory, or the register ModRM.r/m = ymm2); K4 is4 = ymm3; KF/KD FP inputs of all three operands;
   l: 0, 1, 2 = random; w: 0, 1, 2 = random */
static const struct kop kops[] = {
	{ "vfmadd132p", 2, 1, 0x98, 2, 2, KV | KF }, { "vfmadd213p", 2, 1, 0xA8, 2, 2, KV | KF },
	{ "vfmadd231p", 2, 1, 0xB8, 2, 2, KV | KF }, { "vfmsub132p", 2, 1, 0x9A, 2, 2, KV | KF },
	{ "vfnmadd213p", 2, 1, 0xAC, 2, 2, KV | KF }, { "vfnmsub231p", 2, 1, 0xBE, 2, 2, KV | KF },
	{ "vfmaddsub132p", 2, 1, 0x96, 2, 2, KV | KF }, { "vfmsubadd213p", 2, 1, 0xA7, 2, 2, KV | KF },
	{ "vfmadd231s", 2, 1, 0xB9, 0, 2, KV | KF }, { "vfmsub213s", 2, 1, 0xAB, 0, 2, KV | KF },
	{ "vfnmadd132s", 2, 1, 0x9D, 0, 2, KV | KF }, { "vfnmsub213s", 2, 1, 0xAF, 0, 2, KV | KF },
	{ "vcvtph2ps", 2, 1, 0x13, 2, 0, 0 }, { "vcvtps2ph", 3, 1, 0x1D, 2, 0, KI | KS | KF },
	{ "vpermd", 2, 1, 0x36, 1, 0, KV }, { "vpermps", 2, 1, 0x16, 1, 0, KV },
	{ "vpermq", 3, 1, 0x00, 1, 1, KI }, { "vpermpd", 3, 1, 0x01, 1, 1, KI },
	{ "vperm2i128", 3, 1, 0x46, 1, 0, KV | KI }, { "vpblendd", 3, 1, 0x02, 2, 0, KV | KI },
	{ "vpsllv", 2, 1, 0x47, 2, 2, KV }, { "vpsrlv", 2, 1, 0x45, 2, 2, KV }, { "vpsravd", 2, 1, 0x46, 2, 0, KV },
	{ "vpshufb", 2, 1, 0x00, 1, 0, KV }, { "vpalignr", 3, 1, 0x0F, 1, 0, KV | KI },
	{ "vpblendw", 3, 1, 0x0E, 1, 0, KV | KI }, { "vmpsadbw", 3, 1, 0x42, 1, 0, KV | KI },
	{ "vphaddw", 2, 1, 0x01, 1, 0, KV }, { "vpacksswb", 1, 1, 0x63, 1, 0, KV }, { "vpunpcklbw", 1, 1, 0x60, 1, 0, KV },
	{ "vpsllw", 1, 1, 0xF1, 1, 0, KV }, { "vpsrad", 1, 1, 0xE2, 1, 0, KV }, { "vpshufd", 1, 1, 0x70, 1, 0, KI },
	{ "vpbroadcastb", 2, 1, 0x78, 2, 0, 0 }, { "vpbroadcastw", 2, 1, 0x79, 2, 0, 0 },
	{ "vpbroadcastd", 2, 1, 0x58, 2, 0, 0 }, { "vpbroadcastq", 2, 1, 0x59, 2, 0, 0 },
	{ "vbroadcastss", 2, 1, 0x18, 2, 0, KR }, { "vbroadcastsd", 2, 1, 0x19, 1, 0, KR },
	{ "vbroadcasti128", 2, 1, 0x5A, 1, 0, KM }, { "vinserti128", 3, 1, 0x38, 1, 0, KV | KI },
	{ "vextracti128", 3, 1, 0x39, 1, 0, KI | KS }, { "vpmovsxbw", 2, 1, 0x20, 1, 0, 0 },
	{ "vpmovzxbd", 2, 1, 0x31, 1, 0, 0 }, { "vpmovsxdq", 2, 1, 0x25, 1, 0, 0 },
	{ "vpmaskmov_ld", 2, 1, 0x8C, 2, 2, KV | KM }, { "vpmaskmov_st", 2, 1, 0x8E, 2, 2, KV | KM | KS },
	{ "vpblendvb", 3, 1, 0x4C, 1, 0, KV | K4 }, { "vpmovmskb", 1, 1, 0xD7, 1, 0, KR },
	{ "vpslldq", 1, 1, 0x73, 1, 0, KI | KR },
};
#define NKOPS (sizeof kops / sizeof kops[0])

static void k_case(const char *tag, u32 n, const struct kop *o, int f16dn) {
	u8 b[16];
	int L = o->l == 2 ? (int)(rnd() % 2) : o->l;
	int W = o->w == 2 ? (int)(rnd() % 2) : o->w;
	int mem = (o->flags & KM) || (!(o->flags & KR) && rnd() % 3 == 0);
	int vv = (o->flags & KV) ? 1 : 0;
	if (o->op == 0x73 && o->map == 1) vv = 1;                 /* vpslldq: VEX.vvvv is the destination ymm1 */
	int k = vexp(b, o->map, o->pp, L, W, vv);
	u8 imm = rnd();
	if (o->flags & K4) imm = (u8)((imm & 0x0F) | 0x30);
	b[k++] = o->op;
	u8 reg = (o->op == 0x73 && o->map == 1) ? 7 : 0;
	b[k++] = mem ? (u8)(0x06 | reg << 3) : (u8)(0xC2 | reg << 3);
	if ((o->flags & (KI | K4)) || o->map == 3) b[k++] = imm;
	yfill();
	u32 *m = GM + (rnd() % 8);
	for (int w = 0; w < 32; w++) GM[w] = rnd();
	int fp = o->flags & KF, fd = fp && W;
	if (fp) {
		for (int r = 0; r < 3; r++)
			for (int w = 0; w < 8; w += fd ? 2 : 1) {
				u32 *p = Y2I + 8 * r + w;
				if (fd) f64r(p); else p[0] = f32r();
			}
		for (int w = 0; w < 8; w++) {
			if (rnd() % 6 == 0) Y2I[16 + w] = Y2I[w] ^ 0x80000000;      /* cancellation partner */
			m[w] = Y2I[16 + w];
		}
	}
	if (o->op == 0x13 && o->map == 2) {   /* binary16 inputs: every class; no denormals unless f16dn */
		for (int w = 0; w < 8; w++) {
			u16 *h = (u16 *)(Y2I + 16 + w);
			for (int q = 0; q < 2; q++) {
				u16 x = (u16)rnd();
				if (rnd() % 4 == 0) x = (u16)((x & 0x8000) | (rnd() % 2 ? 0x7C00 : 0x7C00 | (x & 0x3FF)));
				if (!f16dn && (x & 0x7C00) == 0 && (x & 0x3FF)) x |= 0x0400;
				h[q] = x;
			}
			m[w] = Y2I[16 + w];
		}
	}
	if ((o->op == 0x47 || o->op == 0x45 || o->op == 0x46) && o->map == 2)   /* small counts mostly */
		for (int w = 0; w < 8; w++) { if (rnd() % 4) Y2I[16 + w] = rnd() % (W ? 70 : 36); if (W && w % 2) Y2I[16 + w] = rnd() % 8 ? 0 : rnd(); m[w] = Y2I[16 + w]; }
	if ((o->op == 0xF1 || o->op == 0xE2) && o->map == 1) {
		Y2I[16] = rnd() % 4 ? rnd() % 40 : rnd(); Y2I[17] = rnd() % 4 ? 0 : rnd(); m[0] = Y2I[16]; m[1] = Y2I[17];
	}
	if (o->op >= 0x8C && o->map == 2)       /* masks: a mix of selected elements */
		for (int w = 0; w < 8; w++) Y2I[8 + w] = rnd() % 2 ? Y2I[8 + w] | 0x80000000 : Y2I[8 + w] & 0x7FFFFFFF;
	u32 mx = 0x1F80;
	if (fp || o->op == 0x13) {
		mx |= (rnd() % 4) << 13;
		if (rnd() % 3 == 0) mx |= 0x40;
		if (rnd() % 3 == 0 && (f16dn || !(o->op == 0x1D && o->map == 3))) mx |= 0x8000;
		if (!f16dn && o->op == 0x13) mx &= ~0x40;
	}
	MX2I = mx;
	u32 min[8], ymi[32];
	memcpy(min, m, 32);
	memcpy(ymi, Y2I, sizeof ymi);
	int v = runy(k, b, m);
	MX2I = 0x1F80;
	kprintf("%s %d %s l=%d w=%d mx=%x", tag, n, o->name, L, W, mx);
	if ((o->flags & (KI | K4)) || o->map == 3) kprintf(" imm=%x", imm);
	py("d", ymi); if (o->flags & KV) py("a", ymi + 8);
	if (mem) py("m", min); else py("b", ymi + 16);
	if (o->flags & K4) py("c", ymi + 24);
	kprintf(" -> vec=%x", v);
	if (v == 0xFFFF) {
		if (o->op == 0x73 && o->map == 1) py("r", Y2O + 8);
		else if (o->op == 0xD7 && o->map == 1) kprintf(" eax=%x", G2O[0]);
		else if (!(o->flags & KS)) py("r", Y2O);
		else if (mem) py("mem", m);
		else py("r2", Y2O + 16);
		kprintf(" mx=%x", MX2O);
	}
	kputc('\n');
}

/* avx2g: random gathers with in-range indices (the memory window GM is a function of the case number) */
static void g_case(u32 n) {
	u8 b[8];
	static const u8 ops[] = { 0x90, 0x91, 0x92, 0x93 };
	int op = ops[rnd() % 4], L = (int)(rnd() % 2), W = (int)(rnd() % 2), scale = (int)(rnd() % 4);
	int disp = (int)(rnd() % 128) - 64;
	int k = gather_bytes(b, op, L, W, 0, 2, 1, scale, disp);
	yfill();
	gfill(n);
	for (int e = 0; e < 8; e++) {
		int ix = (int)(rnd() % 128) - 64;
		if (op & 1) { if (e % 2 == 0) { Y2I[8 + e] = (u32)ix; Y2I[9 + e] = ix < 0 ? ~0u : 0; } }
		else Y2I[8 + e] = (u32)ix;
	}
	u32 yi[24];
	memcpy(yi, Y2I, sizeof yi);
	int v = runy(k, b, (u8 *)GM + 2048);
	kprintf("avx2g %d op=%x l=%d w=%d s=%d disp=%d", n, op, L, W, scale, disp);
	py("d", yi); py("x", yi + 8); py("m", yi + 16);
	kprintf(" -> vec=%x", v); py("r", Y2O); py("mo", Y2O + 16);
	kputc('\n');
}

void test_avx2(void) {
	if (!has_feature(7, 0, 1, 5)) { kputs("avx2: not reported\n"); return; }
	u32 cr0 = RDCR(0), cr4 = RDCR(4);
	rs = fuzz_seed(rs);
	t_ud();
	t_gather();
	t_gather_pf();
	t_maskmov();
	t_fma();
	avx_on();
	u32 nk = param("avx2k", 2000);
	for (u32 k = 0; k < nk; k++) k_case("avx2k", k, &kops[k < NKOPS ? k : rnd() % NKOPS], 0);
	u32 ng = param("avx2g", 300);
	for (u32 k = 0; k < ng; k++) g_case(k);
	MX2I = 0x1F80;
	__asm__ volatile("vzeroall\n ldmxcsr MX2I" ::: "memory");
	WRCR(0, cr0); WRCR(4, cr4);
}

/* ---- MODEL-ONLY ---- */

static u8 ucode[64];
static u8 ustk[256] __attribute__((aligned(16)));
__attribute__((used)) u32 a2_ebx, a2_esp, a2_fl, a2_eip;
/* Run the bytes at CPL 3 with EBX = a2_ebx and EFLAGS = fl; 0x40: completed (INT 0x40) */
static int urun(const u8 *b, int n, u32 fl) {
	for (int k = 0; k < n; k++) ucode[k] = b[k];
	ucode[n] = 0xCD; ucode[n + 1] = 0x40;
	a2_esp = (u32)ustk + sizeof ustk; a2_fl = fl; a2_eip = (u32)ucode;
	return TRY(__asm__ volatile(
		"pushl $0x23\n pushl a2_esp\n pushl a2_fl\n pushl $0x1B\n pushl a2_eip\n"
		"movl $0x23, %%eax\n movl %%eax, %%ds\n movl %%eax, %%es\n movl %%eax, %%fs\n movl %%eax, %%gs\n"
		"movl a2_ebx, %%ebx\n iret" ::: "eax", "ebx", "ecx", "edx", "esi", "edi", "memory"));
}
#define UA(off, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; a2_ebx = (u32)GM + 256 + (off); urun(_b, sizeof _b, 0x40202); })

void test_avx2_model(void) {
	if (!has_feature(7, 0, 1, 5)) return;
	u32 cr0 = RDCR(0), cr4 = RDCR(4);
	avx_on();
	rs = 0x5BE0CD19;
	/* VEX.L = 1 of the scalar FMA forms: bits 255:128 zeroed (TCG keeps them) */
	yfill();
	int a = Y(GM, 0xC4, 0xE2, 0x75, 0x99, 0xC2);        /* vfmadd132ss xmm0, xmm1, xmm2 with VEX.L = 1 */
	u32 r0[8]; memcpy(r0, Y2O, 32);
	int c = Y(GM, 0xC4, 0xE2, 0x71, 0x99, 0xC2);
	kprintf("avx2m.lig: %x/%x same=%d", a, c, Y2O[0] == r0[0] && Y2O[1] == r0[1] && Y2O[2] == r0[2] && Y2O[3] == r0[3]);
	py("y0", r0); kputc('\n');
	/* VCVTPS2PH ignores FTZ; VCVTPH2PS ignores DAZ and reports no DE */
	yfill();
	Y2I[0] = 0x387FC000; Y2I[1] = 0x00000001; Y2I[2] = 0x33800000; Y2I[3] = 0xB3800001;   /* half denormals, a single denormal */
	MX2I = 0x9F80 | 0x40;       /* FTZ, DAZ */
	int f0 = Y(GM, 0xC4, 0xE3, 0x79, 0x1D, 0xC1, 0x00); /* vcvtps2ph xmm1, xmm0, 0 */
	kprintf("avx2m.f16c: ps2ph=%x %x%x mx=%x", f0, Y2O[9], Y2O[8], MX2O);
	MX2I = 0x9F80 | 0x40;
	Y2I[8] = 0x83FF0001; Y2I[9] = 0x0200FC00;
	int f1 = Y(GM, 0xC4, 0xE2, 0x79, 0x13, 0xC1);       /* vcvtph2ps xmm0, xmm1 */
	kprintf(" ph2ps=%x %x,%x,%x,%x mx=%x", f1, Y2O[0], Y2O[1], Y2O[2], Y2O[3], MX2O);
	/* unmasked overflow of VCVTPS2PH to memory: #XM, memory unchanged */
	Y2I[0] = 0x47800000; GM[64] = 0x11111111; GM[65] = 0x22222222;
	MX2I = 0x1F80 & ~0x200 & ~0x400;   /* OM unmasked */
	WRCR(4, RDCR(4) | 0x400);
	int f2 = Y(GM + 64, 0xC4, 0xE3, 0x79, 0x1D, 0x06, 0x00);
	kprintf(" ps2ph_xm=%x mem=%x,%x mx=%x", f2, GM[64], GM[65], MX2O);
	/* unmasked IE of an FMA: #XM, destination unchanged */
	yfill(); Y2I[0] = 0x7F800000; Y2I[16] = 0; Y2I[8] = 0x3F800000;
	MX2I = 0x1F80 & ~0x80;
	int f3 = Y(GM, 0xC4, 0xE2, 0x71, 0x99, 0xC2);
	kprintf(" fma_xm=%x unchanged=%d mx=%x", f3, Y2O[0] == 0x7F800000, MX2O);
	WRCR(4, RDCR(4) & ~0x400);
	int f4 = Y(GM, 0xC4, 0xE2, 0x71, 0x99, 0xC2);
	WRCR(4, RDCR(4) | 0x400);
	MX2I = 0x1F80;
	kprintf(" noxmmexcpt=%x\n", f4);
	/* gathers: a fault after elements with arbitrary mask bits (only the sign selects); unprocessed
	   mask elements are left as they were */
	paging_on();
	u8 *e = (u8 *)(PL + 0x1000);
	u8 b[8];
	int k = gather_bytes(b, 0x90, 1, 0, 0, 2, 1, 2, 0);
	yfill();
	for (int i = 0; i < 8; i++) { Y2I[8 + i] = (u32)i; Y2I[16 + i] = i == 4 ? 0x80000001 : rnd(); }
	Y2I[16 + 0] |= 0x80000000;
	int g0 = runy(k, b, e - 16);
	kprintf("avx2m.gather.pf: vec=%x cr2=%x", g0, last.cr2 - PL); py("r", Y2O); py("mo", Y2O + 16); kputc('\n');
	/* VPMASKMOV loads: masked-out elements on a not-present page do not fault; a store with a selected
	   element there faults and writes nothing */
	yfill();
	for (int i = 0; i < 8; i++) Y2I[8 + i] = i < 3 ? 0x80000000 : 0;
	int m0 = Y(e - 12, 0xC4, 0xE2, 0x75, 0x8C, 0x06);
	kprintf("avx2m.maskmov: load=%x", m0); py("r", Y2O);
	Y2I[8 + 3] = 0x80000000;
	u32 before = ((u32 *)(e - 12))[0];
	int m1 = Y(e - 12, 0xC4, 0xE2, 0x75, 0x8E, 0x06);
	kprintf(" store=%x cr2=%x unchanged=%d", m1, last.cr2 - PL, ((u32 *)(e - 12))[0] == before);
	for (int i = 0; i < 8; i++) Y2I[8 + i] = 0;
	Y2I[9] = 0x80000000;
	int m2 = Y(e - 8, 0xC4, 0xE2, 0xF5, 0x8C, 0x06);    /* vpmaskmovq: element 0 selected (present) */
	kprintf(" q=%x", m2); py("r", Y2O); kputc('\n');
	paging_off();
	/* #AC at CPL 3: gather elements must be aligned to their size, VPMASKMOV operands to 16 bytes (with
	   a selected element) */
	WRCR(0, RDCR(0) | 0x40000);
	int ac[6];
	/* ymm0 = all ones (masks), ymm1 = ymm3 = 0 (an empty mask, zero indices) before each case */
#define ACPREP __asm__ volatile("vpcmpeqd %%ymm0, %%ymm0, %%ymm0\n vpxor %%ymm1, %%ymm1, %%ymm1\n vpxor %%ymm3, %%ymm3, %%ymm3" ::: "memory")
	ACPREP; ac[0] = UA(4, 0xC4, 0xE2, 0x79, 0x8C, 0x13);      /* vpmaskmovd xmm2, xmm0, [ebx]: 4-byte aligned */
	ACPREP; ac[1] = UA(16, 0xC4, 0xE2, 0x79, 0x8C, 0x13);     /* 16-byte aligned */
	ACPREP; ac[2] = UA(4, 0xC4, 0xE2, 0x71, 0x8C, 0x13);      /* mask xmm1 = 0: no element */
	ACPREP; ac[3] = UA(2, 0xC4, 0xE2, 0x79, 0x90, 0x14, 0x1B);   /* vpgatherdd xmm2, [ebx+xmm3], xmm0: misaligned */
	ACPREP; ac[4] = UA(4, 0xC4, 0xE2, 0x79, 0x90, 0x14, 0x1B);   /* dword aligned */
	ACPREP; ac[5] = UA(4, 0xC4, 0xE2, 0xF9, 0x90, 0x14, 0x1B);   /* vpgatherdq: qwords at offset 4 */
	WRCR(0, RDCR(0) & ~0x40000);
	kprintf("avx2m.ac: maskmov_4=%x maskmov_16=%x maskmov_none_4=%x gather_2=%x gather_4=%x gatherq_4=%x\n",
		ac[0], ac[1], ac[2], ac[3], ac[4], ac[5]);
	/* #UD before #NM (QEMU checks VEX.W after CR0.TS); VPERMQ needs VEX.L = 1 (its VEX.W is ignored on the
	   EPYC 7742) */
	cr0set(8);
	kprintf("avx2m.ud_before_nm: permq_l0=%x gather_dm=%x cvtph2ps_w1=%x\n", N(GM, 0xC4, 0xE3, 0xF9, 0x00, 0xC1, 0x1B),
		N(GM, 0xC4, 0xE2, 0x7D, 0x90, 0x04, 0x8E), N(GM, 0xC4, 0xE2, 0xF9, 0x13, 0xC1));
	cr0set(0);
	/* random F16C cases with binary16 denormals, DAZ and FTZ (test/avx2_ref.py) */
	for (u32 i = 0; i < 200; i++) k_case("avx2m", i, &kops[12 + i % 2], 1);
	MX2I = 0x1F80;
	__asm__ volatile("vzeroall\n ldmxcsr MX2I" ::: "memory");
	WRCR(0, cr0); WRCR(4, cr4);
}
