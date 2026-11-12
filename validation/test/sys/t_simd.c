/* MMX/SSE/SSE2 differential fuzzing against QEMU. Each case assembles one instruction (prefix, 0F,
   opcode, ModRM, imm8) into a code buffer, loads XMM0..7 / MM0..7 / MXCSR / EAX / ECX / ESI / EDI from
   memory, runs it, and prints the destination registers, MXCSR, EFLAGS and the memory operand.
   MXCSR always has every exception masked here (TCG does not raise unmasked SIMD exceptions, QEMU
   issue 215); unmasked exceptions are tested in the MODEL-ONLY section (t_simdm.c).

   Extending (EXTENDING.md): `struct sop` also describes 0F 38 / 0F 3A forms (`map`) and VEX forms
   (`vex`, `l`, `w`; VEX.vvvv names XMM2/YMM2), with flags ALLX (print XMM0..7) and YMMD (print the
   YMM upper halves). New rows go into `xops` (run by the `ssex` loop, so the existing `sops` cases
   keep their random sequence); the model implements every Zen 2 form listed in
   test/isa_forms.py. With CPUID reporting XSAVE and AVX, test_simd sets
   CR4.OSXSAVE and XCR0 = 7, and every case also loads YMM0..7[255:128] from YIN and stores them to
   YOUT. */
#include "sys.h"

static u32 rs = 0x6A09E667;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

__attribute__((used, aligned(16))) u32 XIN[32], XOUT[32], YIN[32], YOUT[32];
__attribute__((used, aligned(32))) u32 MEMOP[12];
__attribute__((used, aligned(16))) u32 MMIN[16], MMOUT[16];
__attribute__((used, aligned(16))) u8 FXA[512];
__attribute__((used)) u32 MXIN, MXOUT, FLOUT, GIN, GOUT, ESIIN;
static u8 code[32] __attribute__((aligned(16)));
static int ncode;   /* bytes of the instruction in `code` (a RET follows) */
void (*volatile simd_codep)(void) = (void (*)(void))code;
static int ymm_on;  /* CR4.OSXSAVE and XCR0 = 7 are set (CPUID reports XSAVE and AVX) */

/* vinsertf128 ymmK, ymmK, [eax+16K], 1 and vextractf128 [eax+16K], ymmK, 1, as bytes (this file is
   compiled without AVX) */
#define LDY(k) ".byte 0xc4,0xe3,((~" #k ")&15)*8+5,0x18,0x40+" #k "*8," #k "*16,1\n\t"
#define STY(k) ".byte 0xc4,0xe3,0x7d,0x19,0x40+" #k "*8," #k "*16,1\n\t"
#define ALL8(m) m(0) m(1) m(2) m(3) m(4) m(5) m(6) m(7)

/* Load the register state, run the code buffer, store the state. */
static void run_sse(void) {
	if (ymm_on) __asm__ volatile(ALL8(LDY) :: "a"(YIN) : "memory");
	__asm__ volatile(
		"ldmxcsr MXIN\n"
		"movdqu XIN, %%xmm0\n movdqu XIN+16, %%xmm1\n movdqu XIN+32, %%xmm2\n movdqu XIN+48, %%xmm3\n"
		"movdqu XIN+64, %%xmm4\n movdqu XIN+80, %%xmm5\n movdqu XIN+96, %%xmm6\n movdqu XIN+112, %%xmm7\n"
		"movq MMIN, %%mm0\n movq MMIN+8, %%mm1\n"
		"movl ESIIN, %%esi\n movl %%esi, %%edi\n movl GIN, %%eax\n movl %%eax, %%ecx\n"
		"pushfl\n andl $~0x8D5, (%%esp)\n popfl\n"   /* arithmetic flags 0 before the instruction */
		"call *simd_codep\n"
		"pushfl\n popl FLOUT\n movl %%eax, GOUT\n stmxcsr MXOUT\n"
		"movdqu %%xmm0, XOUT\n movdqu %%xmm1, XOUT+16\n movdqu %%xmm2, XOUT+32\n movdqu %%xmm3, XOUT+48\n"
		"movdqu %%xmm4, XOUT+64\n movdqu %%xmm5, XOUT+80\n movdqu %%xmm6, XOUT+96\n movdqu %%xmm7, XOUT+112\n"
		"movq %%mm0, MMOUT\n movq %%mm1, MMOUT+8\n"
		::: "memory", "eax", "ecx", "esi", "edi", "cc");
	if (ymm_on) __asm__ volatile(ALL8(STY) :: "a"(YOUT) : "memory");
	else memset(YOUT, 0, sizeof YOUT);
}

/* Optional XSAVE-managed state: with CPUID.1:ECX.XSAVE and AVX, set CR4.OSXSAVE and XCR0 = 7
   (x87, SSE, AVX); otherwise leave it off. Nothing is printed, so the transcript does not depend on it. */
static void osxsave_setup(int on) {
	ymm_on = on && has_feature(1, 0, 2, 26) && has_feature(1, 0, 2, 28);
	if (ymm_on) {
		WRCR(4, RDCR(4) | 0x40000);
		__asm__ volatile(".byte 0x0f,0x01,0xd1" :: "a"(7), "d"(0), "c"(0));   /* xsetbv */
	} else if (has_feature(1, 0, 2, 26)) {
		WRCR(4, RDCR(4) & ~0x40000);
	}
}

static u64 rnd64(void) { u64 h = rnd(); return (h << 32) | rnd(); }

/* binary32 operand classes: zeros, denormals, infinities, NaNs, both ends of the exponent range,
   integers, values near rounding ties, ordinary values */
static u32 gen32(int nodenorm) {
	u32 s = rnd() & 0x80000000, m = rnd() & 0x7FFFFF, e;
	switch (rnd() % 16) {
	case 0: return s;
	case 1: if (nodenorm) return s | 0x3F800000; return s | (m ? m : 1);
	case 2: return s | 0x7F800000;
	case 3: return s | 0x7FC00000 | (m & 0x3FFFFF);
	case 4: return s | 0x7F800000 | ((m & 0x3FFFFF) ? (m & 0x3FFFFF) : 1);
	case 5: e = 1 + rnd() % 3; break;
	case 6: e = 251 + rnd() % 2; break;
	case 7: e = 127 + rnd() % 31; m &= ~((1u << (23 - (e - 127 < 23 ? e - 127 : 23))) - 1); break;
	case 8: e = 120 + rnd() % 16; m = (m & 0x7FFF00) | 0x80 | (rnd() & 1); break;
	case 9: e = 100 + rnd() % 60; m &= 0x7F0000; break;
	default: e = 107 + rnd() % 40; break;
	}
	return s | (e << 23) | m;
}

/* Two NaN operands: the SDM returns the first source (vol. 1, table 4-7), TCG applies the x87 rule
   (larger significand, QNaN over SNaN); such lanes are tested in t_simdm.c only. */
static int nan32(u32 v) { return (v & 0x7F800000) == 0x7F800000 && (v & 0x7FFFFF); }
static int nan64(const u32 *p) { return (p[1] & 0x7FF00000) == 0x7FF00000 && ((p[1] & 0xFFFFF) || p[0]); }
static void denan(const u32 *a, u32 *b, int dbl) {
	for (int k = 0; k < 4; k++) {
		if (dbl && k % 2 == 0 && nan64(a + k) && nan64(b + k)) b[k + 1] = 0x3FF00000;
		if (!dbl && nan32(a[k]) && nan32(b[k])) b[k] = 0x3F800000;
	}
}

/* At most `max` NaN lanes among the FP inputs a and b (the extras become 1.0): two NaN inputs of one
   operation follow the first-operand rule on hardware but TCG's larger-significand rule (see denan);
   DPPS/DPPD (max 0) combine all lanes. */
static void onenan(u32 *a, u32 *b, int dbl, int max) {
	int n = 0;
	for (int k = 0; k < 8; k++) {
		u32 *p = k < 4 ? a + k : b + k - 4;
		if (dbl ? (k % 2 == 0 && nan64(p)) : nan32(*p)) {
			if (n++ >= max) { if (dbl) { p[0] = 0; p[1] = 0x3FF00000; } else *p = 0x3F800000; }
		}
	}
}

static u64 gen64(void) {
	u64 s = (u64)(rnd() & 1) << 63, m = rnd64() & 0xFFFFFFFFFFFFFULL, e;
	switch (rnd() % 16) {
	case 0: return s;
	case 1: return s | (m ? m : 1);
	case 2: return s | 0x7FF0000000000000ULL;
	case 3: return s | 0x7FF8000000000000ULL | (m & 0x7FFFFFFFFFFFFULL);
	case 4: return s | 0x7FF0000000000000ULL | ((m & 0x7FFFFFFFFFFFFULL) ? (m & 0x7FFFFFFFFFFFFULL) : 1);
	case 5: e = 1 + rnd() % 3; break;
	case 6: e = 2044 + rnd() % 3; break;
	case 7: e = 896 + rnd() % 3; break;                       /* binary32 underflow range */
	case 8: e = 1150 + rnd() % 6; break;                      /* binary32 overflow range */
	case 9: e = 1023 + rnd() % 40; m &= 0xFFFFFFFF00000000ULL; break; /* int32 range */
	case 10: e = 1010 + rnd() % 20; m = (m & 0xFFFFFE0000000ULL) | 0x10000000ULL | (rnd() & 1); break; /* ties for binary32 */
	default: e = 1003 + rnd() % 40; break;
	}
	return s | (e << 52) | m;
}

static u32 genint(void) {
	u32 v = rnd() >> (rnd() % 32);
	if (rnd() % 8 == 0) v = rnd() % 2 ? 0x80000000 : 0x7FFFFFFF;
	return rnd() & 1 ? -v : v;
}

/* fill 16 bytes with lanes of type t: 0 raw, 1 binary32, 2 binary64, 3 int32, 4 small shift counts */
static void fill(u32 *p, int t, int nodenorm) {
	for (int k = 0; k < 4; k++) p[k] = rnd();
	if (t == 1) for (int k = 0; k < 4; k++) p[k] = gen32(nodenorm);
	if (t == 2) for (int k = 0; k < 2; k++) { u64 v = gen64(); p[2 * k] = (u32)v; p[2 * k + 1] = (u32)(v >> 32); }
	if (t == 3) for (int k = 0; k < 4; k++) p[k] = genint();
	if (t == 4) { p[0] = rnd() % 4 ? rnd() % 70 : rnd(); p[1] = rnd() % 4 ? 0 : rnd(); }
	if (t == 5) for (int k = 0; k < 8; k++) {   /* (Avx2) binary16: no denormals; zeros, infinities, NaNs */
		u16 *h = (u16 *)p + k;
		if ((*h & 0x7C00) == 0 && (*h & 0x3FF)) *h = (u16)(*h & 0x83FF) | (rnd() % 4 ? 0x3C00 : 0);
		if (rnd() % 8 == 0) *h = (u16)((rnd() & 0x8000) | (rnd() % 2 ? 0x7C00 : 0x7E00 | (rnd() & 0x1FF)));
	}
	if (t == 0 && rnd() % 4 == 0) {   /* MMX/integer edge patterns */
		static const u32 pat[] = { 0, 0xFFFFFFFF, 0x80008000, 0x7FFF7FFF, 0x80808080, 0x7F7F7F7F, 0x00FF00FF, 0x80000000 };
		for (int k = 0; k < 4; k++) p[k] = pat[rnd() % 8];
	}
}

static void phex(const u32 *p, int words) { for (int k = words - 1; k >= 0; k--) puthex(p[k]); }

/* Instruction table: prefix (0, 0x66, 0xF3, 0xF2), opcode, flags. */
enum {
	MEM = 1,      /* the E operand may be memory */
	MEMONLY = 2,  /* memory only (stores) */
	IMM = 4,      /* imm8 */
	STORE = 8,    /* writes the memory operand */
	MMXD = 16,    /* prints MM0/MM1 */
	A16 = 32,     /* memory operand must be 16-byte aligned (always aligned here) */
	F32 = 0x100, F64 = 0x200, INT = 0x300, CNT = 0x400, RAW = 0, /* E operand type (bits 8..10) */
	F16 = 0x500,   /* (Avx2) binary16 lanes without denormals (VCVTPH2PS; TCG applies DAZ and reports DE) */
	D32 = 0x800, D64 = 0x1000, DINT = 0x1800,                     /* destination operand type */
	NODN = 0x2000, /* no denormal inputs (RCP/RSQRT), round to nearest */
	NODAZ = 0x4000, /* DAZ clear (MIN/MAX: TCG returns the unflushed denormal) */
	ALLX = 0x40,   /* prints XMM0..7 (not only XMM0/XMM1) */
	YMMD = 0x80,   /* prints the YMM0..7 upper halves (VEX.256 forms) */
	ONENAN = 0x8000 /* at most one NaN among the FP inputs (map 3 rows, DPPS/DPPD: none), see onenan() */
};
/* One instruction form: mandatory prefix (0, 0x66, 0xF3, 0xF2; the VEX.pp of VEX forms), opcode,
   flags; map 0 or 1 = 0F, 2 = 0F 38, 3 = 0F 3A (always an imm8); vex: VEX-encoded, 1 = VEX.vvvv names
   XMM2/YMM2 (a source, or the destination of the shifts by imm8), 2 = VEX.vvvv = 1111b (forms without
   a VEX.vvvv operand: any other value is #UD); l: VEX.L (0, 1, or 2 = random), w: VEX.W. Rows of the
   original table give only the first three. */
struct sop { u8 pfx, op; u16 fl; u8 map, vex, l, w; };
#define FPOPS(o, x) { 0, o, MEM | F32 | D32 | x }, { 0x66, o, MEM | F64 | D64 | x }, { 0xF3, o, MEM | F32 | D32 | x }, { 0xF2, o, MEM | F64 | D64 | x }
static const struct sop sops[] = {
	FPOPS(0x51, 0), FPOPS(0x58, 0), FPOPS(0x59, 0), FPOPS(0x5C, 0), FPOPS(0x5D, NODAZ), FPOPS(0x5E, 0), FPOPS(0x5F, NODAZ),
	FPOPS(0xC2, IMM),
	{ 0, 0x52, MEM | F32 | D32 | NODN }, { 0xF3, 0x52, MEM | F32 | D32 | NODN },
	{ 0, 0x53, MEM | F32 | D32 | NODN }, { 0xF3, 0x53, MEM | F32 | D32 | NODN },
	{ 0, 0x2E, MEM | F32 | D32 }, { 0x66, 0x2E, MEM | F64 | D64 }, { 0, 0x2F, MEM | F32 | D32 }, { 0x66, 0x2F, MEM | F64 | D64 },
	{ 0, 0x2A, MEM | INT | D32 | MMXD }, { 0x66, 0x2A, MEM | INT | D64 | MMXD }, { 0xF3, 0x2A, MEM | INT | D32 }, { 0xF2, 0x2A, MEM | INT | D64 },
	{ 0, 0x2C, MEM | F32 | MMXD }, { 0x66, 0x2C, MEM | F64 | MMXD }, { 0xF3, 0x2C, MEM | F32 }, { 0xF2, 0x2C, MEM | F64 },
	{ 0, 0x2D, MEM | F32 | MMXD }, { 0x66, 0x2D, MEM | F64 | MMXD }, { 0xF3, 0x2D, MEM | F32 }, { 0xF2, 0x2D, MEM | F64 },
	{ 0, 0x5A, MEM | F32 | D64 }, { 0x66, 0x5A, MEM | F64 | D32 }, { 0xF3, 0x5A, MEM | F32 | D64 }, { 0xF2, 0x5A, MEM | F64 | D32 },
	{ 0, 0x5B, MEM | INT }, { 0x66, 0x5B, MEM | F32 }, { 0xF3, 0x5B, MEM | F32 },
	{ 0x66, 0xE6, MEM | F64 }, { 0xF3, 0xE6, MEM | INT }, { 0xF2, 0xE6, MEM | F64 },
	{ 0, 0x10, MEM }, { 0x66, 0x10, MEM }, { 0xF3, 0x10, MEM }, { 0xF2, 0x10, MEM },
	{ 0, 0x11, MEM | STORE }, { 0x66, 0x11, MEM | STORE }, { 0xF3, 0x11, MEM | STORE }, { 0xF2, 0x11, MEM | STORE },
	{ 0, 0x12, MEM }, { 0x66, 0x12, MEMONLY }, { 0, 0x13, MEMONLY | STORE }, { 0x66, 0x13, MEMONLY | STORE },
	{ 0, 0x14, MEM }, { 0x66, 0x14, MEM }, { 0, 0x15, MEM }, { 0x66, 0x15, MEM },
	{ 0, 0x16, MEM }, { 0x66, 0x16, MEMONLY }, { 0, 0x17, MEMONLY | STORE }, { 0x66, 0x17, MEMONLY | STORE },
	{ 0, 0x28, MEM }, { 0x66, 0x28, MEM }, { 0, 0x29, MEM | STORE }, { 0x66, 0x29, MEM | STORE },
	{ 0, 0x2B, MEMONLY | STORE }, { 0x66, 0x2B, MEMONLY | STORE },
	{ 0, 0x50, F32 }, { 0x66, 0x50, F64 },
	{ 0, 0x54, MEM }, { 0x66, 0x54, MEM }, { 0, 0x55, MEM }, { 0x66, 0x55, MEM },
	{ 0, 0x56, MEM }, { 0x66, 0x56, MEM }, { 0, 0x57, MEM }, { 0x66, 0x57, MEM },
	{ 0x66, 0x6E, MEM }, { 0x66, 0x7E, MEM | STORE }, { 0xF3, 0x7E, MEM },
	{ 0x66, 0x6F, MEM }, { 0xF3, 0x6F, MEM }, { 0x66, 0x7F, MEM | STORE }, { 0xF3, 0x7F, MEM | STORE },
	{ 0x66, 0x70, MEM | IMM }, { 0xF3, 0x70, MEM | IMM }, { 0xF2, 0x70, MEM | IMM },
	{ 0x66, 0x71, IMM }, { 0x66, 0x72, IMM }, { 0x66, 0x73, IMM },
	{ 0x66, 0xC4, MEM | IMM }, { 0x66, 0xC5, IMM }, { 0, 0xC6, MEM | IMM }, { 0x66, 0xC6, MEM | IMM },
	{ 0x66, 0xD6, MEM | STORE }, { 0xF3, 0xD6, MMXD }, { 0xF2, 0xD6, MMXD }, { 0x66, 0xD7, 0 },
	{ 0x66, 0x6C, MEM }, { 0x66, 0x6D, MEM },
	{ 0x66, 0xE7, MEMONLY | STORE }, { 0x66, 0xF7, STORE }, { 0, 0xC3, MEMONLY | STORE },
};
/* packed-integer opcodes (MMX without prefix, XMM with 66) */
static const u8 iops[] = {
	0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x74, 0x75, 0x76,
	0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF,
	0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF,
	0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,
};
/* Forms of later ISA extensions (SSE3 .. SSE4.2, AES, AVX, ...), as listed in
   test/isa_forms.py and implemented by the model. Run by the `ssex` loop; the last row is
   a terminator. Example: { 0xF2, 0x7C, MEM | F32 | D32 } (HADDPS), { 0x66, 0x00, MEM, 2 } (PSHUFB),
   { 0x66, 0x58, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 2 } (VADDPD, VEX.128/256). */
static const struct sop xops[] = {
	/* SSE3 (Sse): MOVSLDUP, MOVSHDUP, MOVDDUP, HADDPx, HSUBPx, ADDSUBPx, LDDQU; SSE4a MOVNTSS/SD */
	{ 0xF3, 0x12, MEM | F32 | D32 }, { 0xF3, 0x16, MEM | F32 | D32 }, { 0xF2, 0x12, MEM | F64 | D64 },
	{ 0x66, 0x7C, MEM | F64 | D64 | ONENAN }, { 0xF2, 0x7C, MEM | F32 | D32 | ONENAN },
	{ 0x66, 0x7D, MEM | F64 | D64 | ONENAN }, { 0xF2, 0x7D, MEM | F32 | D32 | ONENAN },
	{ 0x66, 0xD0, MEM | F64 | D64 | ONENAN }, { 0xF2, 0xD0, MEM | F32 | D32 | ONENAN },
	{ 0xF2, 0xF0, MEMONLY }, { 0xF3, 0x2B, MEMONLY | STORE }, { 0xF2, 0x2B, MEMONLY | STORE },
	/* SSE4a register forms EXTRQ/INSERTQ xmm, xmm (the imm8 forms are in t_sse.c) */
	{ 0x66, 0x79, 0 }, { 0xF2, 0x79, 0 },
	/* SSSE3, MMX (no prefix) and XMM (66) forms */
	{ 0, 0x00, MEM | MMXD, 2 }, { 0x66, 0x00, MEM, 2 }, { 0, 0x01, MEM | MMXD, 2 }, { 0x66, 0x01, MEM, 2 },
	{ 0, 0x02, MEM | MMXD, 2 }, { 0x66, 0x02, MEM, 2 }, { 0, 0x03, MEM | MMXD, 2 }, { 0x66, 0x03, MEM, 2 },
	{ 0, 0x04, MEM | MMXD, 2 }, { 0x66, 0x04, MEM, 2 }, { 0, 0x05, MEM | MMXD, 2 }, { 0x66, 0x05, MEM, 2 },
	{ 0, 0x06, MEM | MMXD, 2 }, { 0x66, 0x06, MEM, 2 }, { 0, 0x07, MEM | MMXD, 2 }, { 0x66, 0x07, MEM, 2 },
	{ 0, 0x08, MEM | MMXD, 2 }, { 0x66, 0x08, MEM, 2 }, { 0, 0x09, MEM | MMXD, 2 }, { 0x66, 0x09, MEM, 2 },
	{ 0, 0x0A, MEM | MMXD, 2 }, { 0x66, 0x0A, MEM, 2 }, { 0, 0x0B, MEM | MMXD, 2 }, { 0x66, 0x0B, MEM, 2 },
	{ 0, 0x1C, MEM | MMXD, 2 }, { 0x66, 0x1C, MEM, 2 }, { 0, 0x1D, MEM | MMXD, 2 }, { 0x66, 0x1D, MEM, 2 },
	{ 0, 0x1E, MEM | MMXD, 2 }, { 0x66, 0x1E, MEM, 2 }, { 0, 0x0F, MEM | MMXD, 3 }, { 0x66, 0x0F, MEM, 3 },
	/* SSE4.1 / SSE4.2 (0F 38): PBLENDVB, BLENDVPS/PD, PTEST, PMOVSX/ZX, PMULDQ, PCMPEQQ, MOVNTDQA,
	   PACKUSDW, PCMPGTQ, PMIN/PMAX, PMULLD, PHMINPOSUW */
	{ 0x66, 0x10, MEM, 2 }, { 0x66, 0x14, MEM | F32 | D32, 2 }, { 0x66, 0x15, MEM | F64 | D64, 2 }, { 0x66, 0x17, MEM, 2 },
	{ 0x66, 0x20, MEM, 2 }, { 0x66, 0x21, MEM, 2 }, { 0x66, 0x22, MEM, 2 }, { 0x66, 0x23, MEM, 2 },
	{ 0x66, 0x24, MEM, 2 }, { 0x66, 0x25, MEM, 2 }, { 0x66, 0x28, MEM | INT, 2 }, { 0x66, 0x29, MEM, 2 },
	{ 0x66, 0x2A, MEMONLY, 2 }, { 0x66, 0x2B, MEM | INT | DINT, 2 },
	{ 0x66, 0x30, MEM, 2 }, { 0x66, 0x31, MEM, 2 }, { 0x66, 0x32, MEM, 2 }, { 0x66, 0x33, MEM, 2 },
	{ 0x66, 0x34, MEM, 2 }, { 0x66, 0x35, MEM, 2 }, { 0x66, 0x37, MEM, 2 },
	{ 0x66, 0x38, MEM, 2 }, { 0x66, 0x39, MEM | INT | DINT, 2 }, { 0x66, 0x3A, MEM, 2 }, { 0x66, 0x3B, MEM | INT | DINT, 2 },
	{ 0x66, 0x3C, MEM, 2 }, { 0x66, 0x3D, MEM | INT | DINT, 2 }, { 0x66, 0x3E, MEM, 2 }, { 0x66, 0x3F, MEM | INT | DINT, 2 },
	{ 0x66, 0x40, MEM | INT | DINT, 2 }, { 0x66, 0x41, MEM, 2 },
	/* SSE4.1 (0F 3A): ROUNDPS/PD/SS/SD, BLENDPS/PD, PBLENDW, PEXTRB/W/D and EXTRACTPS to memory (the
	   register forms are in t_sse.c), PINSRB, INSERTPS, PINSRD, DPPS, DPPD, MPSADBW */
	{ 0x66, 0x08, MEM | F32 | D32, 3 }, { 0x66, 0x09, MEM | F64 | D64, 3 },
	{ 0x66, 0x0A, MEM | F32 | D32, 3 }, { 0x66, 0x0B, MEM | F64 | D64, 3 },
	{ 0x66, 0x0C, MEM, 3 }, { 0x66, 0x0D, MEM, 3 }, { 0x66, 0x0E, MEM, 3 },
	{ 0x66, 0x14, MEMONLY | STORE, 3 }, { 0x66, 0x15, MEMONLY | STORE, 3 }, { 0x66, 0x16, MEMONLY | STORE, 3 },
	{ 0x66, 0x17, MEMONLY | STORE, 3 }, { 0x66, 0x20, MEM, 3 }, { 0x66, 0x21, MEM | F32 | D32, 3 }, { 0x66, 0x22, MEM, 3 },
	{ 0x66, 0x40, MEM | F32 | D32 | ONENAN, 3 }, { 0x66, 0x41, MEM | F64 | D64 | ONENAN, 3 }, { 0x66, 0x42, MEM, 3 },
	/* AES-NI, PCLMULQDQ (all imm8), SHA (Crypto) */
	{ 0x66, 0xDB, MEM, 2 }, { 0x66, 0xDC, MEM, 2 }, { 0x66, 0xDD, MEM, 2 }, { 0x66, 0xDE, MEM, 2 },
	{ 0x66, 0xDF, MEM, 2 }, { 0x66, 0xDF, MEM, 3 }, { 0x66, 0x44, MEM, 3 },
	{ 0, 0xC8, MEM, 2 }, { 0, 0xC9, MEM, 2 }, { 0, 0xCA, MEM, 2 }, { 0, 0xCB, MEM, 2 }, { 0, 0xCC, MEM, 2 },
	{ 0, 0xCD, MEM, 2 }, { 0, 0xCC, MEM, 3 },
	/* AVX (Avx): every AVX instruction, VEX.128 and VEX.256 (l = 2: random); scalar forms with VEX.L = 0
	   (they ignore VEX.L, but TCG raises #UD or keeps bits 255:128 for VEX.L = 1; avxm.lig checks it) */
	{ 0x00, 0x10, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0x11, MEM | STORE | ALLX | YMMD, 1, 2, 2 },
	{ 0x00, 0x28, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0x29, MEM | STORE | ALLX | YMMD, 1, 2, 2 },
	{ 0x00, 0x2B, MEMONLY | STORE | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0x14, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x00, 0x15, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x00, 0x13, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0x00, 0x17, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 }, { 0x00, 0x50, F32 | ALLX | YMMD, 1, 2, 2 },
	{ 0x00, 0xC6, MEM | IMM | ALLX | YMMD, 1, 1, 2 }, { 0x00, 0x54, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x00, 0x55, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x00, 0x56, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x00, 0x57, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x66, 0x10, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x11, MEM | STORE | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0x28, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x29, MEM | STORE | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0x2B, MEMONLY | STORE | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x14, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x66, 0x15, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x13, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 }, { 0x66, 0x17, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0x66, 0x50, F64 | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0xC6, MEM | IMM | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x54, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x66, 0x55, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x56, MEM | ALLX | YMMD, 1, 1, 2 }, { 0x66, 0x57, MEM | ALLX | YMMD, 1, 1, 2 },
	{ 0x00, 0x12, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x12, MEMONLY | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x16, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x16, MEMONLY | ALLX | YMMD, 1, 1, 0 },
	{ 0xF3, 0x10, MEMONLY | F32 | D32 | ALLX | YMMD, 1, 2, 0 }, { 0xF3, 0x10, F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF3, 0x11, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 }, { 0xF3, 0x11, F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF3, 0x2A, MEM | INT | D32 | ALLX | YMMD, 1, 1, 0 }, { 0xF3, 0x2C, MEM | F32 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x2D, MEM | F32 | ALLX | YMMD, 1, 2, 2 }, { 0xF2, 0x10, MEMONLY | F64 | D64 | ALLX | YMMD, 1, 2, 0 },
	{ 0xF2, 0x10, F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0xF2, 0x11, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0xF2, 0x11, F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0xF2, 0x2A, MEM | INT | D64 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x2C, MEM | F64 | ALLX | YMMD, 1, 2, 2 }, { 0xF2, 0x2D, MEM | F64 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x12, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 }, { 0xF3, 0x16, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF2, 0x12, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0x2E, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 },
	{ 0x00, 0x2F, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0x2E, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x2F, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0x51, MEM | F32 | D32 | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x51, MEM | F64 | D64 | ALLX | YMMD, 1, 2, 2 }, { 0xF3, 0x51, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x51, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0x00, 0x58, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x58, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 2 }, { 0xF3, 0x58, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x58, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0x00, 0x59, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x59, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 2 }, { 0xF3, 0x59, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x59, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0x00, 0x5C, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x5C, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 2 }, { 0xF3, 0x5C, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x5C, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0x00, 0x5E, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x5E, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 2 }, { 0xF3, 0x5E, MEM | F32 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x5E, MEM | F64 | D64 | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x5D, MEM | F32 | D32 | NODAZ | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x5D, MEM | F64 | D64 | NODAZ | ALLX | YMMD, 1, 1, 2 },
	{ 0xF3, 0x5D, MEM | F32 | D32 | NODAZ | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x5D, MEM | F64 | D64 | NODAZ | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x5F, MEM | F32 | D32 | NODAZ | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x5F, MEM | F64 | D64 | NODAZ | ALLX | YMMD, 1, 1, 2 },
	{ 0xF3, 0x5F, MEM | F32 | D32 | NODAZ | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0x5F, MEM | F64 | D64 | NODAZ | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0xC2, MEM | F32 | D32 | IMM | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0xC2, MEM | F64 | D64 | IMM | ALLX | YMMD, 1, 1, 2 },
	{ 0xF3, 0xC2, MEM | F32 | D32 | IMM | ALLX | YMMD, 1, 1, 0 },
	{ 0xF2, 0xC2, MEM | F64 | D64 | IMM | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x52, MEM | F32 | D32 | NODN | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x52, MEM | F32 | D32 | NODN | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x53, MEM | F32 | D32 | NODN | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x53, MEM | F32 | D32 | NODN | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x5A, MEM | F32 | D64 | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0x5A, MEM | F64 | D32 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x5A, MEM | F32 | D64 | ALLX | YMMD, 1, 1, 0 }, { 0xF2, 0x5A, MEM | F64 | D32 | ALLX | YMMD, 1, 1, 0 },
	{ 0x00, 0x5B, MEM | INT | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0x5B, MEM | F32 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0x5B, MEM | F32 | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0xE6, MEM | F64 | ALLX | YMMD, 1, 2, 2 },
	{ 0xF3, 0xE6, MEM | INT | ALLX | YMMD, 1, 2, 2 }, { 0xF2, 0xE6, MEM | F64 | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x7C, MEM | F64 | D64 | ONENAN | ALLX | YMMD, 1, 1, 2 },
	{ 0xF2, 0x7C, MEM | F32 | D32 | ONENAN | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0x7D, MEM | F64 | D64 | ONENAN | ALLX | YMMD, 1, 1, 2 },
	{ 0xF2, 0x7D, MEM | F32 | D32 | ONENAN | ALLX | YMMD, 1, 1, 2 },
	{ 0x66, 0xD0, MEM | F64 | D64 | ONENAN | ALLX | YMMD, 1, 1, 2 },
	{ 0xF2, 0xD0, MEM | F32 | D32 | ONENAN | ALLX | YMMD, 1, 1, 2 }, { 0x66, 0x60, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x61, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x62, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x63, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x64, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x65, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x66, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x67, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x68, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x69, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x6A, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x6B, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x6C, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x6D, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x74, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x75, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x76, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xD1, MEM | CNT | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xD2, MEM | CNT | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xD3, MEM | CNT | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xD4, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xD5, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xD8, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xD9, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xDA, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xDB, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xDC, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xDD, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xDE, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xDF, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xE0, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xE1, MEM | CNT | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xE2, MEM | CNT | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xE3, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xE4, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xE5, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xE8, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xE9, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xEA, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xEB, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xEC, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xED, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xEE, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xEF, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xF1, MEM | CNT | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xF2, MEM | CNT | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xF3, MEM | CNT | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xF4, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xF5, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xF6, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xF8, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xF9, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xFA, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xFB, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xFC, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xFD, MEM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xFE, MEM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x6E, MEM | ALLX | YMMD, 1, 2, 0 }, { 0x66, 0x7E, MEM | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0xF3, 0x7E, MEM | ALLX | YMMD, 1, 2, 0 }, { 0x66, 0xD6, MEM | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0x66, 0x6F, MEM | ALLX | YMMD, 1, 2, 2 }, { 0xF3, 0x6F, MEM | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x7F, MEM | STORE | ALLX | YMMD, 1, 2, 2 }, { 0xF3, 0x7F, MEM | STORE | ALLX | YMMD, 1, 2, 2 },
	{ 0x66, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 0 }, { 0xF3, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 0 },
	{ 0xF2, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 0 }, { 0x66, 0x71, IMM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0x72, IMM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0x73, IMM | ALLX | YMMD, 1, 1, 0 },
	{ 0x66, 0xC4, MEM | IMM | ALLX | YMMD, 1, 1, 0 }, { 0x66, 0xC5, IMM | ALLX | YMMD, 1, 2, 0 },
	{ 0x66, 0xD7, 0 | ALLX | YMMD, 1, 2, 0 }, { 0x66, 0xE7, MEMONLY | STORE | ALLX | YMMD, 1, 2, 2 },
	{ 0xF2, 0xF0, MEMONLY | ALLX | YMMD, 1, 2, 2 }, { 0x66, 0xF7, STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0x00, 0x77, 0 | ALLX | YMMD, 1, 2, 2 }, { 0x00, 0xAE, MEMONLY | STORE | ALLX | YMMD, 1, 2, 0 },
	{ 0x66, 0x00, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x01, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x02, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x03, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x04, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x05, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x06, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x07, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x08, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x09, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x0A, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x0B, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x1C, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x1D, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x1E, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x0C, MEM | ALLX | YMMD, 2, 1, 2 },
	{ 0x66, 0x0D, MEM | ALLX | YMMD, 2, 1, 2 }, { 0x66, 0x0E, MEM | ALLX | YMMD, 2, 2, 2 },
	{ 0x66, 0x0F, MEM | ALLX | YMMD, 2, 2, 2 }, { 0x66, 0x17, MEM | ALLX | YMMD, 2, 2, 2 },
	{ 0x66, 0x18, MEMONLY | ALLX | YMMD, 2, 2, 2 }, { 0x66, 0x19, MEMONLY | ALLX | YMMD, 2, 2, 1 },
	{ 0x66, 0x1A, MEMONLY | ALLX | YMMD, 2, 2, 1 }, { 0x66, 0x20, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x21, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x22, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x23, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x24, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x25, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x30, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x31, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x32, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x33, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x34, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x35, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x28, MEM | INT | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x29, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x2B, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x37, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x38, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x39, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x3A, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x3B, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x3C, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x3D, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x3E, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x3F, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x40, MEM | INT | DINT | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0x2A, MEMONLY | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0x41, MEM | ALLX | YMMD, 2, 2, 0 },
	{ 0x66, 0x2C, MEMONLY | ALLX | YMMD, 2, 1, 2 }, { 0x66, 0x2D, MEMONLY | ALLX | YMMD, 2, 1, 2 },
	{ 0x66, 0x2E, MEMONLY | STORE | ALLX | YMMD, 2, 1, 2 }, { 0x66, 0x2F, MEMONLY | STORE | ALLX | YMMD, 2, 1, 2 },
	{ 0x66, 0xDB, MEM | ALLX | YMMD, 2, 2, 0 }, { 0x66, 0xDC, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0xDD, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0xDE, MEM | ALLX | YMMD, 2, 1, 0 },
	{ 0x66, 0xDF, MEM | ALLX | YMMD, 2, 1, 0 }, { 0x66, 0x04, MEM | ALLX | YMMD, 3, 2, 2 },
	{ 0x66, 0x05, MEM | ALLX | YMMD, 3, 2, 2 }, { 0x66, 0x06, MEM | ALLX | YMMD, 3, 1, 1 },
	{ 0x66, 0x08, MEM | F32 | D32 | ALLX | YMMD, 3, 2, 2 }, { 0x66, 0x09, MEM | F64 | D64 | ALLX | YMMD, 3, 2, 2 },
	{ 0x66, 0x0A, MEM | F32 | D32 | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x0B, MEM | F64 | D64 | ALLX | YMMD, 3, 1, 0 },
	{ 0x66, 0x0C, MEM | ALLX | YMMD, 3, 1, 2 }, { 0x66, 0x0D, MEM | ALLX | YMMD, 3, 1, 2 },
	{ 0x66, 0x0E, MEM | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x0F, MEM | ALLX | YMMD, 3, 1, 0 },
	{ 0x66, 0x14, MEMONLY | STORE | ALLX | YMMD, 3, 2, 0 }, { 0x66, 0x15, MEMONLY | STORE | ALLX | YMMD, 3, 2, 0 },
	{ 0x66, 0x16, MEMONLY | STORE | ALLX | YMMD, 3, 2, 0 }, { 0x66, 0x17, MEMONLY | STORE | ALLX | YMMD, 3, 2, 0 },
	{ 0x66, 0x18, MEM | ALLX | YMMD, 3, 1, 1 }, { 0x66, 0x19, MEM | STORE | ALLX | YMMD, 3, 2, 1 },
	{ 0x66, 0x20, MEM | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x21, MEM | F32 | D32 | ALLX | YMMD, 3, 1, 0 },
	{ 0x66, 0x22, MEM | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x40, MEM | F32 | D32 | ONENAN | ALLX | YMMD, 3, 1, 2 },
	{ 0x66, 0x41, MEM | F64 | D64 | ONENAN | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x42, MEM | ALLX | YMMD, 3, 1, 0 },
	{ 0x66, 0x44, MEM | ALLX | YMMD, 3, 1, 0 }, { 0x66, 0x4A, MEM | ALLX | YMMD, 3, 1, 2 },
	{ 0x66, 0x4B, MEM | ALLX | YMMD, 3, 1, 2 }, { 0x66, 0x4C, MEM | ALLX | YMMD, 3, 1, 0 },
	{ 0x66, 0x60, MEM | ALLX | YMMD, 3, 2, 0 }, { 0x66, 0x61, MEM | ALLX | YMMD, 3, 2, 0 },
	{ 0x66, 0x62, MEM | ALLX | YMMD, 3, 2, 0 }, { 0x66, 0x63, MEM | ALLX | YMMD, 3, 2, 0 },
	{ 0x66, 0xDF, MEM | ALLX | YMMD, 3, 2, 0 },
	/* AVX2, FMA3, F16C (Avx2): the VEX.256 integer forms, the AVX2-only instructions, every FMA form with
	   VEX.W = 0 and 1 (scalar forms with VEX.L = 0: TCG keeps bits 255:128 for VEX.L = 1, avx2m.lig), F16C
	   (VCVTPH2PS inputs without binary16 denormals, F16; VCVTPS2PH with FTZ = 0, NODN: TCG applies
	   DAZ/FTZ there); the gathers are in t_avx2.c */
	{ 0x66, 0x60, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x61, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x62, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x63, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x64, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x65, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x66, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x67, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x68, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x69, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x6A, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x6B, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x6C, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x6D, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x74, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x75, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x76, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xD1, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xD2, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xD3, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xD4, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xD5, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xD8, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xD9, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xDA, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xDB, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xDC, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xDD, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xDE, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xDF, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xE0, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xE1, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xE2, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xE3, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xE4, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xE5, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xE8, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xE9, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xEA, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xEB, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xEC, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xED, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xEE, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xEF, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xF1, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xF2, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xF3, MEM | CNT | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xF4, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xF5, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xF6, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xF8, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xF9, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xFA, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xFB, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xFC, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xFD, MEM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0xFE, MEM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 1, 0 },
	{ 0xF3, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 1, 0 }, { 0xF2, 0x70, MEM | IMM | ALLX | YMMD, 1, 2, 1, 0 },
	{ 0x66, 0x71, IMM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0x72, IMM | ALLX | YMMD, 1, 1, 1, 0 },
	{ 0x66, 0x73, IMM | ALLX | YMMD, 1, 1, 1, 0 }, { 0x66, 0xD7, 0 | ALLX | YMMD, 1, 2, 1, 0 },
	{ 0x66, 0x00, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x01, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x02, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x03, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x04, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x05, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x06, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x07, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x08, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x09, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x0A, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x0B, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x29, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x37, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x38, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x3A, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x3C, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x3E, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x28, MEM | INT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x2B, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x39, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x3B, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x3D, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x3F, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x40, MEM | INT | DINT | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x1C, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x1D, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x1E, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x20, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x21, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x22, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x23, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x24, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x25, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x30, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x31, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x32, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x33, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x34, MEM | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x35, MEM | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x2A, MEMONLY | ALLX | YMMD, 2, 2, 1, 0 }, { 0x66, 0x13, MEM | F16 | ALLX | YMMD, 2, 2, 2, 0 },
	{ 0x66, 0x16, MEM | ALLX | YMMD, 2, 1, 1, 0 }, { 0x66, 0x36, MEM | ALLX | YMMD, 2, 1, 1, 0 },
	{ 0x66, 0x18, 0 | ALLX | YMMD, 2, 2, 2, 0 }, { 0x66, 0x19, 0 | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x45, MEM | CNT | ALLX | YMMD, 2, 1, 2, 0 }, { 0x66, 0x45, MEM | CNT | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x46, MEM | CNT | ALLX | YMMD, 2, 1, 2, 0 }, { 0x66, 0x47, MEM | CNT | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x47, MEM | CNT | ALLX | YMMD, 2, 1, 2, 1 }, { 0x66, 0x58, MEM | ALLX | YMMD, 2, 2, 2, 0 },
	{ 0x66, 0x59, MEM | ALLX | YMMD, 2, 2, 2, 0 }, { 0x66, 0x78, MEM | ALLX | YMMD, 2, 2, 2, 0 },
	{ 0x66, 0x79, MEM | ALLX | YMMD, 2, 2, 2, 0 }, { 0x66, 0x5A, MEMONLY | ALLX | YMMD, 2, 2, 1, 0 },
	{ 0x66, 0x8C, MEMONLY | ALLX | YMMD, 2, 1, 2, 0 }, { 0x66, 0x8E, MEMONLY | STORE | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x8C, MEMONLY | ALLX | YMMD, 2, 1, 2, 1 }, { 0x66, 0x8E, MEMONLY | STORE | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x96, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x96, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x97, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x97, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x98, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x98, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x99, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0x99, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0x9A, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x9A, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x9B, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0x9B, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0x9C, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x9C, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x9D, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0x9D, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0x9E, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0x9E, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0x9F, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0x9F, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xA6, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xA6, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xA7, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xA7, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xA8, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xA8, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xA9, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xA9, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xAA, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xAA, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xAB, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xAB, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xAC, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xAC, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xAD, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xAD, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xAE, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xAE, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xAF, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xAF, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xB6, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xB6, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xB7, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xB7, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xB8, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xB8, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xB9, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xB9, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xBA, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xBA, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xBB, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xBB, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xBC, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xBC, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xBD, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xBD, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0xBE, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 2, 0 },
	{ 0x66, 0xBE, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 2, 1 },
	{ 0x66, 0xBF, MEM | F32 | D32 | ALLX | YMMD, 2, 1, 0, 0 },
	{ 0x66, 0xBF, MEM | F64 | D64 | ALLX | YMMD, 2, 1, 0, 1 },
	{ 0x66, 0x00, MEM | IMM | ALLX | YMMD, 3, 2, 1, 1 }, { 0x66, 0x01, MEM | IMM | ALLX | YMMD, 3, 2, 1, 1 },
	{ 0x66, 0x02, MEM | IMM | ALLX | YMMD, 3, 1, 2, 0 }, { 0x66, 0x0E, MEM | IMM | ALLX | YMMD, 3, 1, 1, 0 },
	{ 0x66, 0x0F, MEM | IMM | ALLX | YMMD, 3, 1, 1, 0 }, { 0x66, 0x42, MEM | IMM | ALLX | YMMD, 3, 1, 1, 0 },
	{ 0x66, 0x4C, MEM | ALLX | YMMD, 3, 1, 1, 0 },
	{ 0x66, 0x1D, MEM | STORE | D32 | NODN | ALLX | YMMD, 3, 2, 2, 0 },
	{ 0x66, 0x38, MEM | ALLX | YMMD, 3, 1, 1, 0 }, { 0x66, 0x39, MEM | STORE | ALLX | YMMD, 3, 2, 1, 0 },
	{ 0x66, 0x46, MEM | ALLX | YMMD, 3, 1, 1, 0 },
	{ 0, 0, 0xFFFF }
};
#define NXOPS (sizeof xops / sizeof xops[0] - 1)
/* MMX-only data movement: opcode, flags */
static const struct sop mops[] = {
	{ 0, 0x6E, MEM }, { 0, 0x7E, MEM | STORE }, { 0, 0x6F, MEM }, { 0, 0x7F, MEM | STORE },
	{ 0, 0x70, MEM | IMM }, { 0, 0x71, IMM }, { 0, 0x72, IMM }, { 0, 0x73, IMM },
	{ 0, 0xC4, MEM | IMM }, { 0, 0xC5, IMM }, { 0, 0xD7, 0 }, { 0, 0xE7, MEMONLY | STORE }, { 0, 0xF7, STORE },
};

static int isshift(u8 op) { return (op >= 0xD1 && op <= 0xD3) || op == 0xE1 || op == 0xE2 || (op >= 0xF1 && op <= 0xF3); }

static u32 rand_mxcsr(u16 fl) {
	u32 mx = 0x1F80 | ((rnd() % 4) << 13) | (rnd() % 2 ? 0x40 : 0) | (rnd() % 2 ? 0x8000 : 0);
	if (rnd() % 4 == 0) mx |= rnd() & 0x3F;
	if (fl & NODAZ) mx &= ~0x40;
	if (fl & NODN) mx &= ~0xE040;
	return mx;
}

/* Assemble [pfx] 0F [38|3A] op modrm [imm8] ret, or the VEX form (C5 for map 1 with W = 0, else C4;
   vvvv = 2). The ModRM reg field is `reg` (XMM0/MM0/EAX for 0); the E operand is register 1 or [ESI].
   Returns 1 if the memory form was chosen. */
static int assemble_x(const struct sop *o, u8 reg, u8 imm) {
	u16 fl = o->fl;
	int n = 0, mem = (fl & MEMONLY) || ((fl & MEM) && rnd() % 3 == 0);
	int map = o->map ? o->map : 1;
	if (o->vex) {
		u8 pp = o->pfx == 0x66 ? 1 : o->pfx == 0xF3 ? 2 : o->pfx == 0xF2 ? 3 : 0;
		u8 l = o->l == 2 ? rnd() % 2 : o->l;
		u8 vb = (u8)((o->vex == 2 ? 15 : ~2u & 15) << 3 | l << 2 | pp);
		if (map == 1 && !o->w) { code[n++] = 0xC5; code[n++] = 0x80 | vb; }
		else { code[n++] = 0xC4; code[n++] = 0xE0 | map; code[n++] = (u8)(o->w << 7) | vb; }
	} else {
		if (o->pfx) code[n++] = o->pfx;
		code[n++] = 0x0F;
		if (map == 2) code[n++] = 0x38;
		if (map == 3) code[n++] = 0x3A;
	}
	code[n++] = o->op;
	if (o->vex && map == 1 && o->op == 0x77) { ncode = n; code[n++] = 0xC3; return 0; }   /* VZEROUPPER/ALL */
	code[n++] = mem ? (u8)(0x06 | (reg << 3)) : (u8)(0xC1 | (reg << 3));
	if ((fl & IMM) || map == 3) code[n++] = imm;
	ncode = n;
	code[n++] = 0xC3;
	return mem;
}
static int assemble(u8 pfx, u8 op, u16 fl, u8 reg, u8 imm) {
	struct sop o = { pfx, op, fl };
	return assemble_x(&o, reg, imm);
}

static void print_code(void) { for (int k = 0; k < ncode; k++) { kputc("0123456789abcdef"[code[k] >> 4]); kputc("0123456789abcdef"[code[k] & 15]); } }

static void sse_case(u32 n, const struct sop *o) {
	u16 fl = o->fl;
	int et = (fl >> 8) & 7, dt = (fl >> 11) & 3;
	u8 imm = rnd();
	if (o->op == 0xC2) imm &= o->vex ? 31 : 7;           /* VEX: the 32 predicates */
	if (o->vex && o->map == 3 && (o->op == 0x4A || o->op == 0x4B || o->op == 0x4C)) imm &= 0x7F;   /* is4: XMM0..7 (TCG ignores the 32-bit rule for imm8[7]) */
	u8 reg = 0;
	if (o->vex && o->map == 1 && o->op == 0xAE) reg = 3;   /* VSTMXCSR */
	if (o->op == 0x71 || o->op == 0x72) { static const u8 g[] = { 2, 4, 6 }; reg = g[rnd() % 3]; }
	if (o->op == 0x73) { static const u8 g[] = { 2, 3, 6, 7 }; reg = g[rnd() % 4]; }
	if ((o->op >= 0x71 && o->op <= 0x73) && rnd() % 2) imm %= 70;
	int mem = assemble_x(o, reg, imm);
	fill(XIN, dt == 1 ? 1 : dt == 2 ? 2 : dt == 3 ? 3 : 0, fl & NODN);
	fill(XIN + 4, et == 1 ? 1 : et == 2 ? 2 : et == 3 ? 3 : et == 4 ? 4 : et == 5 ? 5 : 0, fl & NODN);
	fill(MEMOP, et == 1 ? 1 : et == 2 ? 2 : et == 3 ? 3 : et == 4 ? 4 : et == 5 ? 5 : 0, fl & NODN);
	if (o->vex) {   /* VEX: the first source is XMM2/YMM2; inputs of bits 255:128 too */
		fill(XIN + 8, dt == 1 ? 1 : dt == 2 ? 2 : dt == 3 ? 3 : 0, fl & NODN);
		fill(YIN, dt == 1 ? 1 : dt == 2 ? 2 : dt == 3 ? 3 : 0, fl & NODN);
		fill(YIN + 8, dt == 1 ? 1 : dt == 2 ? 2 : dt == 3 ? 3 : 0, fl & NODN);
		fill(YIN + 4, et == 1 ? 1 : et == 2 ? 2 : et == 3 ? 3 : et == 4 ? 4 : et == 5 ? 5 : 0, fl & NODN);
		fill(MEMOP + 4, et == 1 ? 1 : et == 2 ? 2 : et == 3 ? 3 : et == 4 ? 4 : et == 5 ? 5 : 0, fl & NODN);
	}
	u32 *a1 = o->vex ? XIN + 8 : XIN;
	if (o->map <= 1 && (o->op == 0x58 || o->op == 0x59 || o->op == 0x5C || o->op == 0x5E)) {
		denan(a1, XIN + 4, et == 2);
		denan(a1, MEMOP, et == 2);
		if (o->vex) { denan(YIN + 8, YIN + 4, et == 2); denan(YIN + 8, MEMOP + 4, et == 2); }
	}
	if (fl & ONENAN) onenan(a1, mem ? MEMOP : XIN + 4, et == 2, o->map == 3 ? 0 : 1);
	if ((fl & ONENAN) && o->vex) onenan(YIN + 8, mem ? MEMOP + 4 : YIN + 4, et == 2, o->map == 3 ? 0 : 1);
	fill(MMIN, et == 3 ? 3 : 0, 0);
	if (et == 3 && rnd() % 2) MMIN[2] = XIN[4], MMIN[3] = XIN[5];
	GIN = et == 3 ? genint() : rnd();
	ESIIN = (u32)MEMOP;
	MXIN = rand_mxcsr(fl);
	run_sse();
	kprintf("sse %d ", n); print_code();
	kprintf(" mx=%x a=", MXIN); phex(XIN, 4); kputs(" b="); phex(mem ? MEMOP : XIN + 4, 4);
	if (fl & MMXD) { kputs(" m="); phex(MMIN, 4); }
	if (o->vex) { kputs(" v="); phex(XIN + 8, 4); }
	kprintf(" g=%x -> ", GIN); phex(XOUT, 4); kputc(' '); phex(XOUT + 4, 4);
	if (fl & ALLX) for (int k = 2; k < 8; k++) { kputc(' '); phex(XOUT + 4 * k, 4); }
	if (fl & YMMD) { kputs(" y="); for (int k = 0; k < 8; k++) { kputc(' '); phex(YOUT + 4 * k, 4); } }
	if (fl & MMXD) { kputs(" m0="); phex(MMOUT, 2); }
	kprintf(" g=%x mx=%x fl=%x", GOUT, MXOUT, FLOUT & 0x8D5);
	if (fl & STORE) { kputs(" mem="); phex(MEMOP, o->vex ? 8 : 4); }
	kputc('\n');
}

/* MMX case: run with x87 state from FNINIT, print MM0/MM1, TOP and the FXSAVE abridged tags. */
static void mmx_case(u32 n, u8 op, u16 fl) {
	u8 imm = rnd(), reg = 0;
	if (op == 0x71 || op == 0x72) { static const u8 g[] = { 2, 4, 6 }; reg = g[rnd() % 3]; }
	if (op == 0x73) { static const u8 g[] = { 2, 6 }; reg = g[rnd() % 2]; }
	if ((op >= 0x71 && op <= 0x73) && rnd() % 2) imm %= 70;
	int mem = assemble(0, op, fl, reg, imm);
	fill(MMIN, 0, 0);
	if (isshift(op)) fill(MMIN + 2, 4, 0);
	fill(MEMOP, isshift(op) ? 4 : 0, 0);
	GIN = rnd();
	ESIIN = (u32)MEMOP;
	__asm__ volatile(
		"fninit\n movq MMIN, %%mm0\n movq MMIN+8, %%mm1\n fnclex\n"
		"movl ESIIN, %%esi\n movl %%esi, %%edi\n movl GIN, %%eax\n movl %%eax, %%ecx\n"
		"call *simd_codep\n"
		"movl %%eax, GOUT\n movq %%mm0, MMOUT\n movq %%mm1, MMOUT+8\n fxsave FXA\n fninit\n"
		::: "memory", "eax", "ecx", "esi", "edi", "cc");
	kprintf("mmx %d ", n); print_code();
	kputs(" a="); phex(MMIN, 2); kputs(" b="); phex(mem ? MEMOP : MMIN + 2, 2);
	kprintf(" g=%x -> ", GIN); phex(MMOUT, 2); kputc(' '); phex(MMOUT + 2, 2);
	kprintf(" g=%x top=%d tags=%x", GOUT, (*(u16 *)(FXA + 2) >> 11) & 7, FXA[4]);
	if (fl & STORE) { kputs(" mem="); phex(MEMOP, 2); }
	kputc('\n');
}

void test_simd(void) {
	WRCR(0, (RDCR(0) & ~0xC) | 0x22);
	WRCR(4, RDCR(4) | 0x600);              /* OSFXSR, OSXMMEXCPT */
	osxsave_setup(1);
	u32 n = 0;
	rs = fuzz_seed(rs);
	u32 nmmx = param("mmx", 1500);
	for (u32 k = 0; k < nmmx; k++) {
		u32 j = rnd() % (sizeof iops + sizeof mops / sizeof mops[0]);
		if (j < sizeof iops) mmx_case(n++, iops[j], MEM);
		else mmx_case(n++, mops[j - sizeof iops].op, mops[j - sizeof iops].fl);
	}
	/* EMMS after MMX use */
	__asm__ volatile("fninit\n movq MMIN, %%mm3\n emms\n fxsave FXA\n fninit" ::: "memory");
	kprintf("mmx.emms: top=%d tags=%x\n", (*(u16 *)(FXA + 2) >> 11) & 7, FXA[4]);
	u32 nsse = param("sse", 5000);
	for (u32 k = 0; k < nsse; k++) {
		u32 j = rnd() % (sizeof sops / sizeof sops[0] + sizeof iops);
		if (j < sizeof sops / sizeof sops[0]) sse_case(n++, &sops[j]);
		else {
			struct sop o = { 0x66, iops[j - sizeof sops / sizeof sops[0]], MEM };
			if (isshift(o.op)) o.fl |= CNT;
			sse_case(n++, &o);
		}
	}
	u32 nx = NXOPS ? param("ssex", 2000) : 0;
	for (u32 k = 0; k < nx; k++) {
		for (int w = 0; w < 32; w++) YIN[w] = rnd();
		for (int w = 8; w < 32; w++) XIN[w] = rnd();   /* XMM2..7 (sse_case fills XMM0/XMM1) */
		sse_case(n++, &xops[k < NXOPS ? k : rnd() % NXOPS]);   /* every row at least once */
	}
	osxsave_setup(0);
	__asm__ volatile("fninit");
}
