/* SSE3, SSSE3, SSE4.1, SSE4.2, SSE4a, FISTTP and MisalignSse (x86_32/X86/Ext/Sse.lean). test_sse is
   compared with QEMU: PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM fuzzing with full control of EAX/EDX/ECX
   (all imm8 modes, embedded zeros, register and unaligned memory operands), EXTRQ/INSERTQ in both
   forms (including AMD's undefined index + length > 64 and length 0 cases), PEXTRB/W/D and EXTRACTPS to a
   general register, PINSR* from one, BLENDV with a separate mask register, FISTTP m16/m32/m64,
   and the #UD/#NM/#GP rules (CR0.EM/TS, CR4.OSFXSR, alignment, memory-only and register-only forms,
   undefined prefixes and ModRM.reg of group 17). test_sse_model runs in the MODEL-ONLY section:
   MisalignSse (TCG lacks it: MXCSR.MM, its alignment rules, #AC, CPUID 8000_0001:ECX[7]),
   unmasked SIMD exceptions (ROUND* precision suppression, DPPS staging), FISTTP stack underflow.
   `sse_ref.py check` recomputes the sstr/sse4a/fisttp lines with an independent reference. */
#include "sys.h"

static u32 rs = 0x3C6EF372;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

static u8 sc[48] __attribute__((aligned(16)));
void (*volatile sse_codep)(void) = (void (*)(void))sc;
__attribute__((used, aligned(16))) u32 QSV[32], QSW[32];   /* XMM0..7 before / after */
__attribute__((used, aligned(16))) u8 QSM[64];            /* memory operand area */
__attribute__((used)) u32 QSG[3], QSGO[3], QSFL, QSMX;       /* EAX, ECX, EDX before / after; EFLAGS; MXCSR */

/* Run the bytes with XMM0..7 = QSV, EAX/ECX/EDX = QSG, ESI = mem, arithmetic flags clear; returns the
   vector (0xFFFF: none); QSW/QSGO/QSFL hold the state after. */
static int runx(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) sc[k] = b[k];
	sc[n] = 0xC3;
	return TRY(__asm__ volatile(
		"movdqu QSV, %%xmm0\n movdqu QSV+16, %%xmm1\n movdqu QSV+32, %%xmm2\n movdqu QSV+48, %%xmm3\n"
		"movdqu QSV+64, %%xmm4\n movdqu QSV+80, %%xmm5\n movdqu QSV+96, %%xmm6\n movdqu QSV+112, %%xmm7\n"
		"movl QSG, %%eax\n movl QSG+4, %%ecx\n movl QSG+8, %%edx\n"
		"pushfl\n andl $~0x8D5, (%%esp)\n popfl\n"
		"call *sse_codep\n"
		"pushfl\n popl QSFL\n movl %%eax, QSGO\n movl %%ecx, QSGO+4\n movl %%edx, QSGO+8\n stmxcsr QSMX\n"
		"movdqu %%xmm0, QSW\n movdqu %%xmm1, QSW+16\n movdqu %%xmm2, QSW+32\n movdqu %%xmm3, QSW+48\n"
		"movdqu %%xmm4, QSW+64\n movdqu %%xmm5, QSW+80\n movdqu %%xmm6, QSW+96\n movdqu %%xmm7, QSW+112\n"
		:: "S"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}
#define R(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runx(sizeof _b, _b, mem); })
/* The same without touching XMM state (for CR0.EM/TS and CR4.OSFXSR = 0) */
static int runn(int n, const u8 *b, void *mem) {
	for (int k = 0; k < n; k++) sc[k] = b[k];
	sc[n] = 0xC3;
	return TRY(__asm__ volatile("xorl %%eax, %%eax\n xorl %%ecx, %%ecx\n call *sse_codep" :: "S"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}
#define N(mem, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runn(sizeof _b, _b, mem); })

static void px(const char *k, const u32 *p) { kprintf(" %s=%x%x%x%x", k, p[3], p[2], p[1], p[0]); }
static void pcode(int n) { for (int k = 0; k < n; k++) { kputc("0123456789abcdef"[sc[k] >> 4]); kputc("0123456789abcdef"[sc[k] & 15]); } }
/* MXCSR and XMM0 after a faulting runx */
static void sync(void) { __asm__ volatile("stmxcsr QSMX\n movdqu %%xmm0, QSW" ::: "memory"); }
static void ldmx(u32 v) { QSMX = v; __asm__ volatile("ldmxcsr QSMX" ::: "memory"); }
static void cr0set(u32 em_ts) { WRCR(0, (RDCR(0) & ~0xC) | 0x22 | em_ts); }
static void cr4sse(int on) { WRCR(4, on ? RDCR(4) | 0x600 : RDCR(4) & ~0x600); }

/* A string operand: characters from a small alphabet (so that matches are frequent), zeros (end of
   an implicit-length string) and signed/unsigned extremes. */
static void gen_str(u8 *p, int words) {
	static const u16 alpha[] = { 'a', 'b', 'c', 'z', 0x7F, 0x80, 0xFF, 0x8000, 0x7FFF, 0xFFFF, 0x0100, 0 };
	int len = rnd() % 4 ? rnd() % 18 : 16;
	int n = words ? 8 : 16;
	for (int k = 0; k < n; k++) {
		u16 v = k < len ? alpha[rnd() % (rnd() % 3 ? 4 : 12)] : (rnd() % 3 ? 0 : rnd());
		if (k < len && v == 0 && rnd() % 2) v = 'a';
		if (rnd() % 16 == 0) v = rnd();
		if (words) { p[2 * k] = (u8)v; p[2 * k + 1] = (u8)(v >> 8); } else p[k] = (u8)v;
	}
}

static u32 gen_len(void) {
	static const u32 l[] = { 0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFF0, 0xFFFFFFF8 };
	return rnd() % 3 ? l[rnd() % 16] : (rnd() % 2 ? rnd() % 40 : -(rnd() % 40));
}

/* PCMPxSTRx: first operand XMM1, second XMM2 or [ESI] (unaligned) */
static void sstr_case(u32 n) {
	u8 op = 0x60 + rnd() % 4, imm = rnd();
	int words = imm & 1, mem = rnd() % 3 == 0;
	for (int k = 0; k < 32; k++) QSV[k] = rnd();
	gen_str((u8 *)(QSV + 4), words);
	gen_str((u8 *)(QSV + 8), words);
	if (rnd() % 3 == 0) {   /* plant (part of) the first string in the second: substring matches */
		int off = rnd() % 16, cnt = rnd() % 8;
		for (int k = 0; k < cnt && off + k < 16; k++) ((u8 *)(QSV + 8))[off + k] = ((u8 *)(QSV + 4))[k];
	}
	u8 *m = QSM + rnd() % 16;
	for (int k = 0; k < 16; k++) m[k] = ((u8 *)(QSV + 8))[k];
	QSG[0] = gen_len(); QSG[1] = rnd(); QSG[2] = gen_len();
	u8 b[6] = { 0x66, 0x0F, 0x3A, op, mem ? 0x0E : 0xCA, imm };
	int v = runx(6, b, m);
	kprintf("sstr %d ", n); pcode(6);
	px("a", QSV + 4); px("b", QSV + 8); kprintf(" eax=%x edx=%x ->", QSG[0], QSG[2]);
	if (v != 0xFFFF) { kprintf(" vec=%x\n", v); return; }
	kprintf(" ecx=%x", QSGO[1]); px("x0", QSW); kprintf(" fl=%x\n", QSFL & 0x8D5);
}

/* EXTRQ/INSERTQ: XMM0 destination, XMM1 source/control; imm8 forms with random fields */
static void sse4a_case(u32 n) {
	int kind = rnd() % 4;
	u8 len = rnd() % 4 ? rnd() % 65 : rnd(), idx = rnd() % 4 ? rnd() % 65 : rnd();
	for (int k = 0; k < 32; k++) QSV[k] = rnd();
	if (rnd() % 2) { QSV[4] = (QSV[4] & ~0x3F3F) | (len & 0x3F) | (idx & 0x3F) << 8; QSV[6] = (QSV[6] & ~0x3F3F) | (len & 0x3F) | (idx & 0x3F) << 8; }
	u8 b[6];
	int nb;
	switch (kind) {
	case 0: b[0] = 0x66; b[1] = 0x0F; b[2] = 0x78; b[3] = 0xC0 | (rnd() % 8); b[4] = len; b[5] = idx; nb = 6; break; /* EXTRQ xmm, ib, ib */
	case 1: b[0] = 0xF2; b[1] = 0x0F; b[2] = 0x78; b[3] = 0xC1; b[4] = len; b[5] = idx; nb = 6; break;            /* INSERTQ xmm0, xmm1, ib, ib */
	case 2: b[0] = 0x66; b[1] = 0x0F; b[2] = 0x79; b[3] = 0xC1; nb = 4; break;                                   /* EXTRQ xmm0, xmm1 */
	default: b[0] = 0xF2; b[1] = 0x0F; b[2] = 0x79; b[3] = 0xC1; nb = 4; break;                                  /* INSERTQ xmm0, xmm1 */
	}
	int v = runx(nb, b, QSM);
	kprintf("sse4a %d ", n); pcode(nb);
	static const char *xn[] = { "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7" };
	for (int k = 0; k < 8; k++) if (k < 2 || (kind == 0 && k == (b[3] & 7))) px(xn[k], QSV + 4 * k);
	kputs(" ->");
	if (v != 0xFFFF) { kprintf(" vec=%x\n", v); return; }
	for (int k = 0; k < 8; k++) if (k < 2 || (kind == 0 && k == (b[3] & 7))) px(xn[k], QSW + 4 * k);
	kputc('\n');
}

/* PEXTRB/W/D, EXTRACTPS r32, xmm1; PINSRB/D xmm1, r32; PEXTRW (0F 3A 15) register form; BLENDVPS/PD,
   PBLENDVB with the mask in XMM0, destination XMM1, source XMM2 */
static void gpr_case(u32 n) {
	static const u8 ops[] = { 0x14, 0x15, 0x16, 0x17, 0x20, 0x22, 0x10, 0x14, 0x15 };
	int j = rnd() % 9;
	for (int k = 0; k < 32; k++) QSV[k] = rnd();
	QSG[0] = rnd(); QSG[1] = rnd(); QSG[2] = rnd();
	u8 b[6] = { 0x66, 0x0F, j < 6 ? 0x3A : 0x38, ops[j], (u8)(0xC0 | 1 << 3 | (j < 6 ? rnd() % 3 : 2)), (u8)rnd() };
	int nb = j < 6 ? 6 : 5;
	int v = runx(nb, b, QSM);
	kprintf("ssex %d ", n); pcode(nb); px("x0", QSV); px("x1", QSV + 4); px("x2", QSV + 8);
	kprintf(" g=%x %x %x ->", QSG[0], QSG[1], QSG[2]);
	if (v != 0xFFFF) { kprintf(" vec=%x\n", v); return; }
	px("x1", QSW + 4); kprintf(" g=%x %x %x\n", QSGO[0], QSGO[1], QSGO[2]);
}

typedef struct { u64 sig; u16 se; } __attribute__((packed)) f80;
__attribute__((used)) f80 QFA;
__attribute__((used)) u64 QFOUT;
__attribute__((used)) u16 QFCW, QFSW;

/* FISTTP m16/m32/m64 of a loaded value (masked exceptions, valid stack) */
static void fisttp_case(u32 n) {
	static const u64 sigs[] = { 0x8000000000000000ULL, 0xC000000000000000ULL, 0xFFFFFFFFFFFFFFFFULL, 0x8000000000000001ULL, 0xA000000000000000ULL };
	u32 cls = rnd() % 8;
	u16 sign = rnd() & 1 ? 0x8000 : 0;
	u64 s = sigs[rnd() % 5];
	u16 e = 16383 + rnd() % 66 - 2;
	if (cls == 0) { s = 0; e = 0; }
	if (cls == 1) { s = (u64)rnd() << 32 | rnd(); s |= 1ULL << 63; e = 16383 - 3 + rnd() % 70; }
	if (cls == 2) { s = 1ULL << 63; e = 0x7FFF; }                          /* infinity */
	if (cls == 3) { s = 3ULL << 62 | rnd(); e = 0x7FFF; }                  /* QNaN */
	if (cls == 4) { s = (u64)rnd() << 32 | rnd(); s |= 1ULL << 63; e = 16383 + 14 + rnd() % 4; }  /* 16-bit boundary */
	if (cls == 5) { s = (u64)rnd() << 32 | rnd(); s |= 1ULL << 63; e = 16383 + 30 + rnd() % 4; }  /* 32-bit boundary */
	if (cls == 6) { s = (u64)rnd() << 32 | rnd(); s |= 1ULL << 63; e = 16383 + 62 + rnd() % 3; }  /* 64-bit boundary */
	QFA.sig = s; QFA.se = sign | e;
	QFCW = 0x37F | (rnd() % 4) << 10;
	QFOUT = 0x5555555555555555ULL;
	int size = rnd() % 3;
	switch (size) {
	case 0: __asm__ volatile("fninit\n fldcw QFCW\n fldt QFA\n .byte 0xdf,0x0d\n .long QFOUT\n fnstsw QFSW\n fninit" ::: "memory"); break;
	case 1: __asm__ volatile("fninit\n fldcw QFCW\n fldt QFA\n .byte 0xdb,0x0d\n .long QFOUT\n fnstsw QFSW\n fninit" ::: "memory"); break;
	default: __asm__ volatile("fninit\n fldcw QFCW\n fldt QFA\n .byte 0xdd,0x0d\n .long QFOUT\n fnstsw QFSW\n fninit" ::: "memory"); break;
	}
	kprintf("fisttp %d size=%d cw=%x a=%x%x%x -> mem=%x%x sw=%x\n", n, 2 << size, QFCW, QFA.se, (u32)(QFA.sig >> 32), (u32)QFA.sig,
		(u32)(QFOUT >> 32), (u32)QFOUT, QFSW & 0xBDFF);   /* C1 (bit 9): QEMU does not model it */
}

static const char *feat(int has, int vec) {
	if (has) return vec == 0xFFFF ? "ok" : "fault";
	return vec == 6 ? "ok" : "ran";
}

void test_sse(void) {
	cr0set(0);
	cr4sse(1);
	__asm__ volatile("fninit");
	ldmx(0x1F80);
	rs = fuzz_seed(rs);
	u32 ns = param("sstr", 1500), na = param("sse4a", 400), ng = param("ssegpr", 300), nf = param("fisttp", 400);
	for (u32 k = 0; k < ns; k++) sstr_case(k);
	for (u32 k = 0; k < na; k++) sse4a_case(k);
	for (u32 k = 0; k < ng; k++) gpr_case(k);
	for (u32 k = 0; k < nf; k++) fisttp_case(k);
	__asm__ volatile("fninit");

	/* CPUID: the features this module implements (8000_0001:ECX[7] MisAlignSse is model-only) */
	kprintf("sse.cpuid: sse3=%d ssse3=%d sse41=%d sse42=%d sse4a=%d\n", has_feature(1, 0, 2, 0), has_feature(1, 0, 2, 9),
		has_feature(1, 0, 2, 19), has_feature(1, 0, 2, 20), has_feature(0x80000001, 0, 2, 6));
	int sse3 = has_feature(1, 0, 2, 0);
	kprintf("sse.feat: fisttp=%s pshufb=%s ptest=%s pcmpestri=%s extrq=%s\n", feat(sse3, R(QSM, 0xDB, 0x0E)),
		feat(has_feature(1, 0, 2, 9), R(QSM, 0x66, 0x0F, 0x38, 0x00, 0xC1)), feat(has_feature(1, 0, 2, 19), R(QSM, 0x66, 0x0F, 0x38, 0x17, 0xC1)),
		feat(has_feature(1, 0, 2, 20), R(QSM, 0x66, 0x0F, 0x3A, 0x61, 0xC1, 0x00)), feat(has_feature(0x80000001, 0, 2, 6), R(QSM, 0x66, 0x0F, 0x79, 0xC1)));
	__asm__ volatile("fninit");

	/* CR4.OSFXSR = 0: XMM forms #UD, MMX forms of SSSE3 run; CR0.EM: #UD; CR0.TS: #NM */
	cr4sse(0);
	kprintf("sse.noosfxsr: haddps=%x pshufb_x=%x pshufb_mm=%x palignr_mm=%x pcmpistri=%x extrq=%x lddqu=%x\n",
		N(QSM, 0xF2, 0x0F, 0x7C, 0xC1), N(QSM, 0x66, 0x0F, 0x38, 0x00, 0xC1), N(QSM, 0x0F, 0x38, 0x00, 0xC1),
		N(QSM, 0x0F, 0x3A, 0x0F, 0xC1, 0x03), N(QSM, 0x66, 0x0F, 0x3A, 0x63, 0xC1, 0x00), N(QSM, 0x66, 0x0F, 0x79, 0xC1), N(QSM, 0xF2, 0x0F, 0xF0, 0x06));
	cr4sse(1);
	__asm__ volatile("fninit");
	cr0set(4);
	kprintf("sse.em: haddps=%x pshufb_x=%x pshufb_mm=%x roundps=%x insertq=%x fisttp=%x\n",
		N(QSM, 0xF2, 0x0F, 0x7C, 0xC1), N(QSM, 0x66, 0x0F, 0x38, 0x00, 0xC1), N(QSM, 0x0F, 0x38, 0x00, 0xC1),
		N(QSM, 0x66, 0x0F, 0x3A, 0x08, 0xC1, 0x00), N(QSM, 0xF2, 0x0F, 0x79, 0xC1), N(QSM, 0xDB, 0x0E));
	cr0set(8);
	kprintf("sse.ts: haddps=%x pshufb_x=%x pshufb_mm=%x pcmpestrm=%x movntss=%x fisttp=%x\n",
		N(QSM, 0xF2, 0x0F, 0x7C, 0xC1), N(QSM, 0x66, 0x0F, 0x38, 0x00, 0xC1), N(QSM, 0x0F, 0x38, 0x00, 0xC1),
		N(QSM, 0x66, 0x0F, 0x3A, 0x60, 0xC1, 0x00), N(QSM, 0xF3, 0x0F, 0x2B, 0x06), N(QSM, 0xDB, 0x0E));
	cr0set(0);
	__asm__ volatile("fninit");

	/* alignment of 128-bit memory operands (ESI = 16-byte aligned + 4) */
	u8 *mis = QSM + 4;
	kprintf("sse.align: haddps=%x addsubpd=%x movsldup=%x movddup=%x lddqu=%x pshufb_x=%x pshufb_mm=%x palignr_x=%x",
		R(mis, 0xF2, 0x0F, 0x7C, 0x06), R(mis, 0x66, 0x0F, 0xD0, 0x06), R(mis, 0xF3, 0x0F, 0x12, 0x06), R(mis, 0xF2, 0x0F, 0x12, 0x06),
		R(mis, 0xF2, 0x0F, 0xF0, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x00, 0x06), R(mis, 0x0F, 0x38, 0x00, 0x06), R(mis, 0x66, 0x0F, 0x3A, 0x0F, 0x06, 0x01));
	kprintf(" ptest=%x pmovsxbw=%x movntdqa=%x roundps=%x roundss=%x insertps=%x dpps=%x pcmpestri=%x pcmpistrm=%x movntsd=%x\n",
		R(mis, 0x66, 0x0F, 0x38, 0x17, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x20, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x2A, 0x06),
		R(mis, 0x66, 0x0F, 0x3A, 0x08, 0x06, 0x00), R(mis, 0x66, 0x0F, 0x3A, 0x0A, 0x06, 0x00), R(mis, 0x66, 0x0F, 0x3A, 0x21, 0x06, 0x00),
		R(mis, 0x66, 0x0F, 0x3A, 0x40, 0x06, 0xFF), R(mis, 0x66, 0x0F, 0x3A, 0x61, 0x06, 0x00), R(mis, 0x66, 0x0F, 0x3A, 0x62, 0x06, 0x00),
		R(mis, 0xF2, 0x0F, 0x2B, 0x06));

	/* memory-only and register-only forms, undefined prefixes, group 17 */
	kprintf("sse.ud: lddqu_reg=%x movntss_reg=%x movntdqa_reg=%x extrq_mem=%x insertq_mem=%x extrqi_mem=%x insertqi_mem=%x extrqi_reg1=%x",
		R(QSM, 0xF2, 0x0F, 0xF0, 0xC1), R(QSM, 0xF3, 0x0F, 0x2B, 0xC1), R(QSM, 0x66, 0x0F, 0x38, 0x2A, 0xC1),
		R(QSM, 0x66, 0x0F, 0x79, 0x06), R(QSM, 0xF2, 0x0F, 0x79, 0x06), R(QSM, 0x66, 0x0F, 0x78, 0x06, 0x04, 0x08),
		R(QSM, 0xF2, 0x0F, 0x78, 0x06, 0x04, 0x08), R(QSM, 0x66, 0x0F, 0x78, 0xC9, 0x04, 0x08));
	kprintf(" f3_pshufb=%x f2_pshufb=%x np_ptest=%x f3_ptest=%x np_roundps=%x f2_palignr=%x f2_0f16=%x f3_haddps=%x np_haddps=%x np_addsub=%x f3_lddqu=%x f3_0f78=%x np_0f79=%x f3_pcmpestri=%x\n",
		R(QSM, 0xF3, 0x0F, 0x38, 0x00, 0xC1), R(QSM, 0xF2, 0x0F, 0x38, 0x00, 0xC1), R(QSM, 0x0F, 0x38, 0x17, 0xC1), R(QSM, 0xF3, 0x0F, 0x38, 0x17, 0xC1),
		R(QSM, 0x0F, 0x3A, 0x08, 0xC1, 0x00), R(QSM, 0xF2, 0x0F, 0x3A, 0x0F, 0xC1, 0x00), R(QSM, 0xF2, 0x0F, 0x16, 0xC1),
		R(QSM, 0xF3, 0x0F, 0x7C, 0xC1), R(QSM, 0x0F, 0x7C, 0xC1), R(QSM, 0x0F, 0xD0, 0xC1), R(QSM, 0xF3, 0x0F, 0xF0, 0x06),
		R(QSM, 0xF3, 0x0F, 0x78, 0xC1), R(QSM, 0x0F, 0x79, 0xC1), R(QSM, 0xF3, 0x0F, 0x3A, 0x61, 0xC1, 0x00));
	ldmx(0x1F80);
	__asm__ volatile("fninit");
}

/* ring-3 snippet: EFLAGS.AC = 1, then ADDPS xmm0, [eax] (u_ac) or MOVUPS xmm0, [eax] (u_ac_u) */
__asm__(".globl u_ac\nu_ac: pushfl\n orl $0x40000, (%esp)\n popfl\n .byte 0x0f,0x58,0x00\n int $0x40\n"
        ".globl u_ac_hadd\nu_ac_hadd: pushfl\n orl $0x40000, (%esp)\n popfl\n .byte 0xf2,0x0f,0x7c,0x00\n int $0x40\n"
        ".globl u_ac_movaps\nu_ac_movaps: pushfl\n orl $0x40000, (%esp)\n popfl\n .byte 0x0f,0x28,0x00\n int $0x40\n");
extern char u_ac[], u_ac_hadd[], u_ac_movaps[];

void test_sse_model(void) {
	cr0set(0);
	cr4sse(1);
	__asm__ volatile("fninit");
	/* CPUID 8000_0001:ECX: SSE4A (6), MisAlignSse (7) */
	kprintf("ssem.cpuid: sse4a=%d misalignsse=%d\n", has_feature(0x80000001, 0, 2, 6), has_feature(0x80000001, 0, 2, 7));

	/* MXCSR.MM (bit 17) is writable, bits 16 and 18 are reserved; FXSAVE reports MXCSR_MASK 0x2FFFF */
	*(u32 *)QSM = 0x21F80;
	int a = R(QSM, 0x0F, 0xAE, 0x16);
	*(u32 *)QSM = 0;
	R(QSM, 0x0F, 0xAE, 0x1E);
	u32 got = *(u32 *)QSM;
	*(u32 *)QSM = 0x41F80;
	int b = R(QSM, 0x0F, 0xAE, 0x16);
	*(u32 *)QSM = 0x11F80;
	int c = R(QSM, 0x0F, 0xAE, 0x16);
	static u8 fx[512] __attribute__((aligned(16)));
	__asm__ volatile("fxsave %0" : "=m"(fx) :: "memory");
	kprintf("ssem.mm.ldmxcsr: ld=%x val=%x bit18=%x bit16=%x fxsave_mxcsr=%x mask=%x\n", a, got, b, c, *(u32 *)(fx + 24), *(u32 *)(fx + 28));

	/* MXCSR.MM = 1: misaligned operands of load/execute instructions are accepted; MOVAPS/MOVAPD,
	   MOVDQA, MOVNTPS, MOVNTDQ, MOVNTDQA and FXSAVE/FXRSTOR still #GP (APM vol. 1, 4.3.2) */
	u8 *mis = QSM + 4;
	for (int k = 0; k < 64; k++) QSM[k] = (u8)(k * 13 + 1);
	for (int k = 0; k < 32; k++) QSV[k] = 0x3F800000;
	ldmx(0x21F80);
	kprintf("ssem.mm: addps=%x haddps=%x pshufb=%x ptest=%x pcmpistri=%x movaps=%x movaps_st=%x movdqa=%x movntps=%x movntdq=%x movntdqa=%x fxsave=%x",
		R(mis, 0x0F, 0x58, 0x06), R(mis, 0xF2, 0x0F, 0x7C, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x00, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x17, 0x06),
		R(mis, 0x66, 0x0F, 0x3A, 0x63, 0x06, 0x00), R(mis, 0x0F, 0x28, 0x06), R(mis, 0x0F, 0x29, 0x06), R(mis, 0x66, 0x0F, 0x6F, 0x06),
		R(mis, 0x0F, 0x2B, 0x06), R(mis, 0x66, 0x0F, 0xE7, 0x06), R(mis, 0x66, 0x0F, 0x38, 0x2A, 0x06), R(fx + 8, 0x0F, 0xAE, 0x06));
	R(mis, 0x66, 0x0F, 0xFE, 0x06);   /* paddd xmm0, [esi+4] */
	px("paddd", QSW); kputc('\n');
	ldmx(0x1F80);
	kprintf("ssem.mm0: addps=%x paddd=%x\n", R(mis, 0x0F, 0x58, 0x06), R(mis, 0x66, 0x0F, 0xFE, 0x06));

	/* with MM = 1, alignment checking (CR0.AM, EFLAGS.AC, CPL 3) turns the misaligned access into #AC(0);
	   MOVAPS keeps #GP; at CPL 0 or with MM = 0 nothing changes */
	WRCR(0, RDCR(0) | 0x40000);
	ldmx(0x21F80);
	int v1 = run_user(u_ac, (u32)mis, 0);
	u32 e1 = last.err;
	int v2 = run_user(u_ac, (u32)QSM, 0);
	int v3 = run_user(u_ac_hadd, (u32)mis, 0);
	int v4 = run_user(u_ac_movaps, (u32)mis, 0);
	ldmx(0x1F80);
	int v5 = run_user(u_ac, (u32)mis, 0);
	WRCR(0, RDCR(0) & ~0x40000);
	ldmx(0x21F80);
	int v6 = run_user(u_ac, (u32)mis, 0);
	ldmx(0x1F80);
	kprintf("ssem.mm.ac: mis=%x err=%x aligned=%x haddps=%x movaps=%x mm0=%x noam=%x\n", v1, e1, v2, v3, v4, v5, v6);

	/* ROUND* imm8[3] suppresses the precision exception, even unmasked: no #XM, PE stays clear */
	QSV[4] = 0x3FC00000; QSV[5] = 0x40200000; QSV[6] = 0; QSV[7] = 0xBF000000;     /* 1.5 2.5 0 -0.5 */
	ldmx(0x0F80);    /* PM unmasked */
	int r1 = R(QSM, 0x66, 0x0F, 0x3A, 0x08, 0xC1, 0x08);
	u32 m1 = QSMX; u32 x1[4]; for (int k = 0; k < 4; k++) x1[k] = QSW[k];
	ldmx(0x0F80);
	int r2 = R(QSM, 0x66, 0x0F, 0x3A, 0x08, 0xC1, 0x00);
	__asm__ volatile("stmxcsr QSMX" ::: "memory");
	kprintf("ssem.round.pe: suppress=%x mxcsr=%x", r1, m1); px("r", x1); kprintf(" unmasked=%x mxcsr=%x\n", r2, QSMX);
	/* ROUNDPS of an SNaN with IM unmasked: #XM, IE; a denormal does not report DE */
	QSV[4] = 0x7F800001; QSV[5] = 0x00000001; QSV[6] = 0x3F800000; QSV[7] = 0x3F800000;
	ldmx(0x1F00);
	int r3 = R(QSM, 0x66, 0x0F, 0x3A, 0x08, 0xC1, 0x04);
	__asm__ volatile("stmxcsr QSMX" ::: "memory");
	u32 m3 = QSMX;
	QSV[4] = 0x00000001;
	ldmx(0x1E80);    /* DM unmasked */
	int r4 = R(QSM, 0x66, 0x0F, 0x3A, 0x0A, 0xC1, 0x0C);
	kprintf("ssem.round.ie: snan=%x mxcsr=%x denormal=%x mxcsr=%x", r3, m3, r4, QSMX); px("r", QSW); kputc('\n');

	/* DPPS: exceptions per stage; an unmasked overflow in the multiplies stops before the additions
	   (no PE from them) and leaves XMM0 unchanged */
	for (int k = 0; k < 4; k++) { QSV[k] = 0x7F000000; QSV[4 + k] = 0x7F000000; }
	QSV[1] = 0x3F800000; QSV[5] = 0x3F800001;    /* lane 1: an exact product */
	ldmx(0x1B80);    /* OM unmasked */
	int d1 = R(QSM, 0x66, 0x0F, 0x3A, 0x40, 0xC1, 0xFF);
	sync();
	u32 md = QSMX, x0[4];
	for (int k = 0; k < 4; k++) x0[k] = QSW[k];
	ldmx(0x1F80);
	int d2 = R(QSM, 0x66, 0x0F, 0x3A, 0x40, 0xC1, 0xFF);
	kprintf("ssem.dpps: om=%x mxcsr=%x", d1, md); px("x0", x0); kprintf(" masked=%x mxcsr=%x", d2, QSMX); px("r", QSW); kputc('\n');
	/* HADDPS with an unmasked invalid operation: #XM, XMM0 kept */
	QSV[0] = 0x7F800000; QSV[1] = 0xFF800000; QSV[2] = 0x3F800000; QSV[3] = 0x3F800000;
	ldmx(0x1F00);
	int h1 = R(QSM, 0xF2, 0x0F, 0x7C, 0xC1);
	sync();
	u32 mh = QSMX;
	for (int k = 0; k < 4; k++) x0[k] = QSW[k];
	cr4sse(0); WRCR(4, RDCR(4) | 0x200);    /* OSFXSR only: #UD */
	ldmx(0x1F00);
	int h2 = R(QSM, 0xF2, 0x0F, 0x7C, 0xC1);
	cr4sse(1);
	ldmx(0x1F80);
	kprintf("ssem.haddps.ie: vec=%x mxcsr=%x", h1, mh); px("x0", x0); kprintf(" noxmmexcpt=%x\n", h2);
	/* HADDPx/HSUBPx with two NaN operands of one operation: the first operand's NaN is returned; for
	   HADD the manuals write the higher element first (SDM "SRC1[63:32] + SRC1[31:0]", AMD APM vol. 4
	   "bits [63:32] and bits [31:0]"), for HSUB the lower (Sse.lean). TCG returns the NaN with the
	   larger significand. Checked by test/sse_ref.py. */
	{
		static const u32 hn[16] = { 0x7FC00001, 0x7FC00002, 0x7F800003, 0x7FC00004,
		                            0xFFC00005, 0x3F800000, 0x7F800006, 0x7F800007,
		                            /* binary64: QNaN, QNaN | SNaN, 1.0 */
		                            0x00000001, 0x7FF80000, 0x00000002, 0x7FF80000,
		                            0x00000003, 0x7FF00000, 0x00000000, 0x3FF00000 };
		static const u8 hops[4][4] = { { 0xF2, 0x0F, 0x7C, 0xC1 }, { 0xF2, 0x0F, 0x7D, 0xC1 },
		                               { 0x66, 0x0F, 0x7C, 0xC1 }, { 0x66, 0x0F, 0x7D, 0xC1 } };
		static const char *hname[4] = { "haddps", "hsubps", "haddpd", "hsubpd" };
		for (int k = 0; k < 4; k++) {
			const u32 *in = hn + (k < 2 ? 0 : 8);
			if (k == 0 || k == 2) { kprintf("ssem.hnan%s: mx=1f80", k ? "pd" : "ps"); px("a", in); px("b", in + 4); }
			for (int j = 0; j < 8; j++) QSV[j] = in[j];
			ldmx(0x1F80);
			int v = runx(4, hops[k], QSM);
			kprintf(" %s=%x", hname[k], v); px("r", QSW); kprintf(" mxo=%x", QSMX);
			if (k == 1 || k == 3) kputc('\n');
		}
		ldmx(0x1F80);
	}

	/* FISTTP with an empty ST(0): stack underflow, masked response stores the integer indefinite */
	QFOUT = 0x5555555555555555ULL;
	__asm__ volatile("fninit\n .byte 0xdb,0x0d\n .long QFOUT\n fnstsw QFSW\n fninit" ::: "memory");
	kprintf("ssem.fisttp.empty: mem=%x%x sw=%x", (u32)(QFOUT >> 32), (u32)QFOUT, QFSW);
	/* rounding up never happens: C1 = 0 after an inexact truncation */
	QFA.sig = 0xC000000000000000ULL; QFA.se = 0xBFFF;   /* -1.5 */
	QFCW = 0x37F;
	__asm__ volatile("fninit\n fldcw QFCW\n fldt QFA\n .byte 0xdb,0x0d\n .long QFOUT\n fnstsw QFSW\n fninit" ::: "memory");
	kprintf(" m15=%x sw=%x\n", (u32)QFOUT, QFSW);
	ldmx(0x1F80);
	__asm__ volatile("fninit");
}
