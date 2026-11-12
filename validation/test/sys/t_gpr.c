/* General-purpose Zen 2 extensions (x86_32/X86/Ext/Gpr.lean): privilege and #UD/#GP rules,
   TSC_AUX with RDTSCP/RDPID, RDRAND/RDSEED flags, MONITOR/MWAIT with an interrupt wake-up,
   WBNOINVD, the cache-line instructions and prefetches. test_gpr is compared with QEMU (rules in
   qemu-deviations.txt where TCG deviates from the APM); test_gpr_model runs in the MODEL-ONLY section:
   what TCG does not implement (CLZERO, MONITORX/MWAITX, RDPRU, MCOMMIT, RDPMC counters, HWCR) or
   gets wrong without a usable rewrite (CLFLUSH/MONITOR page faults and accessed bits, MWAIT
   extensions, reserved TSC_AUX bits, RDPID/RDTSCP with a 66 prefix). */
#include "sys.h"

#define APIC ((volatile u32 *)0xFEE00000)
#define AR(off) APIC[(off) >> 2]

/* Kernel-mode runner: GPRI = eax ecx edx ebx ebp esi edi eflags; GPRO the same after the code. */
__attribute__((used)) u32 GPRI[8], GPRO[8];
static u8 gxc[64];
void (*volatile gpr_codep)(void) = (void (*)(void))gxc;
void gpr_call(void);
__asm__(".globl gpr_call\ngpr_call:\n"
	" pushal\n movl GPRI+28, %eax\n pushl %eax\n popfl\n"
	" movl GPRI, %eax\n movl GPRI+4, %ecx\n movl GPRI+8, %edx\n movl GPRI+12, %ebx\n"
	" movl GPRI+16, %ebp\n movl GPRI+20, %esi\n movl GPRI+24, %edi\n"
	" call *gpr_codep\n"
	" pushfl\n movl %eax, GPRO\n movl %ecx, GPRO+4\n movl %edx, GPRO+8\n movl %ebx, GPRO+12\n"
	" movl %ebp, GPRO+16\n movl %esi, GPRO+20\n movl %edi, GPRO+24\n popl GPRO+28\n"
	" popal\n ret\n");

static int runk(int n, const u8 *b) {
	for (int k = 0; k < n; k++) gxc[k] = b[k];
	gxc[n] = 0xC3;
	for (int k = 0; k < 8; k++) GPRO[k] = 0xDEADBEEF;
	return TRY(gpr_call());
}
#define K(...) ({ static const u8 _b[] = { __VA_ARGS__ }; runk(sizeof _b, _b); })
static void gin(u32 eax, u32 ecx, u32 edx, u32 ebx) {
	GPRI[0] = eax; GPRI[1] = ecx; GPRI[2] = edx; GPRI[3] = ebx; GPRI[4] = 0x55555555; GPRI[5] = 0x66666666;
	GPRI[6] = 0x77777777; GPRI[7] = 0x8D7;   /* all six arithmetic flags set, IF = 0 */
}

/* Ring-3 snippets: the bytes then INT 0x40; EAX/EBX preset by run_user, ECX = EDX = 0. */
static u8 ucode[64];
static int runu(int n, const u8 *b, u32 eax) {
	int k = 0;
	ucode[k++] = 0x31; ucode[k++] = 0xC9;   /* xor ecx, ecx */
	ucode[k++] = 0x31; ucode[k++] = 0xD2;   /* xor edx, edx */
	for (int i = 0; i < n; i++) ucode[k++] = b[i];
	ucode[k++] = 0xCD; ucode[k++] = 0x40;
	return run_user((char *)ucode, eax, 0);
}
#define U(eax, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; runu(sizeof _b, _b, eax); })

static u8 line[256] __attribute__((aligned(64)));
static u32 gpd[1024] __attribute__((aligned(4096)));
static u32 gpt[2048] __attribute__((aligned(4096)));
static u8 gpages[2 * 4096] __attribute__((aligned(4096)));
static volatile u32 hits, hit_eip, hit_vec;
static int gpr_hook(struct frame *f) {
	if (f->vec < 0x50 || f->vec >= 0xF0) return 0;
	hits++; hit_eip = f->eip; hit_vec = f->vec;
	AR(0xB0) = 0;
	return 1;
}
static void apic_on(void) {
	outb(0x21, 0xFF); outb(0xA1, 0xFF);
	AR(0xF0) = 0x1FF; AR(0x80) = 0;
}
static void ipi_self(u32 vec) { AR(0x310) = 0; AR(0x300) = 0x40000 | vec; }

/* MONITOR line; ECX = 0, EDX = 0; then STI; MWAIT (EAX = 0, ECX = 0); CLI: a self-IPI raised while
   IF = 0 wakes the MWAIT and is delivered with the return address after MWAIT */
extern char mw_after[];
static void mwait_wake(void) {
	__asm__ volatile("movl %0, %%eax\n xorl %%ecx, %%ecx\n xorl %%edx, %%edx\n .byte 0x0f,0x01,0xc8\n"
	                 "xorl %%eax, %%eax\n sti\n .byte 0x0f,0x01,0xc9\n .globl mw_after\nmw_after: cli"
	                 :: "r"(line) : "eax", "ecx", "edx", "memory");
}

void test_gpr(void) {
	__asm__ volatile("cli");
	/* MONITOR/MWAIT: #GP for ECX extensions (MONITOR: none, MWAIT ECX[31:1]), #UD at CPL 3 */
	gin((u32)line, 1, 0, 0);
	kprintf("gpr.monitor.ecx: %x", K(0x0F, 0x01, 0xC8));
	gin((u32)line, 0, 0, 0);
	kprintf(" ok=%x", K(0x0F, 0x01, 0xC8));
	gin(0, 2, 0, 0);
	kprintf(" mwait.ecx2=%x", K(0x0F, 0x01, 0xC9));
	kprintf(" cpl3: monitor=%x mwait=%x\n", U((u32)line, 0x0F, 0x01, 0xC8), U(0, 0x0F, 0x01, 0xC9));

	/* MWAIT woken by an interrupt that became pending while IF = 0 */
	apic_on();
	trap_hook = gpr_hook;
	hits = 0;
	ipi_self(0x58);
	mwait_wake();
	kprintf("gpr.mwait.wake: hits=%d vec=%x at_after=%d\n", hits, hit_vec, hit_eip == (u32)mw_after);
	trap_hook = 0;

	/* TSC_AUX, RDTSCP, RDPID */
	wrmsr(0xC0000103, 0x12345678);
	kprintf("gpr.tsc_aux: %x", (u32)rdmsr(0xC0000103));
	gin(0, 0, 0, 0);
	K(0x0F, 0x31);
	u32 t0 = GPRO[0], t0h = GPRO[2];
	K(0x0F, 0x01, 0xF9);
	u32 t1 = GPRO[0], t1h = GPRO[2];
	kprintf(" rdtscp.ecx=%x mono=%d", GPRO[1], t1h > t0h || (t1h == t0h && t1 >= t0));
	gin(0, 0, 0, 0);
	K(0xF3, 0x0F, 0xC7, 0xFB);   /* RDPID ebx */
	kprintf(" rdpid=%x", GPRO[3]);
	kprintf(" f2=%x", K(0xF2, 0x0F, 0xC7, 0xFB));
	kprintf(" cpl3: rdtscp=%x rdpid=%x", U(0, 0x0F, 0x01, 0xF9), U(0, 0xF3, 0x0F, 0xC7, 0xF8));
	WRCR(4, RDCR(4) | 4);   /* CR4.TSD */
	kprintf(" tsd: rdtscp=%x rdpid=%x cpl0=%x\n", U(0, 0x0F, 0x01, 0xF9), U(0, 0xF3, 0x0F, 0xC7, 0xF8),
	        K(0x0F, 0x01, 0xF9));
	WRCR(4, RDCR(4) & ~4);
	wrmsr(0xC0000103, 0);

	/* RDRAND / RDSEED: CF = 1, the other arithmetic flags cleared; 16-bit forms keep bits 31:16 */
	gin(0, 0, 0, 0xABCD0000);
	K(0x0F, 0xC7, 0xF3);
	kprintf("gpr.rdrand: flags=%x", GPRO[7] & 0x8D5);
	gin(0, 0, 0, 0xABCD0000);
	K(0x66, 0x0F, 0xC7, 0xF3);
	kprintf(" r16.flags=%x hi=%x", GPRO[7] & 0x8D5, GPRO[3] >> 16);
	gin(0, 0, 0, 0);
	K(0x0F, 0xC7, 0xFB);
	kprintf(" rdseed.flags=%x", GPRO[7] & 0x8D5);
	kprintf(" ud: mem=%x f3=%x f2=%x lock=%x seed_f2=%x seed_mem=%x\n", K(0x0F, 0xC7, 0x30),
	        K(0xF3, 0x0F, 0xC7, 0xF0), K(0xF2, 0x0F, 0xC7, 0xF0), K(0xF0, 0x0F, 0xC7, 0xF0),
	        K(0xF2, 0x0F, 0xC7, 0xF8), K(0x0F, 0xC7, 0x38));

	/* RDPMC at CPL 3 with CR4.PCE = 0: #GP(0) */
	kprintf("gpr.rdpmc: cpl3=%x err=%x\n", U(0, 0x0F, 0x33), last.err);

	/* WBNOINVD (F3 0F 09) and WBINVD at CPL 0 and 3 */
	gin(0, 0, 0, 0);
	kprintf("gpr.wbnoinvd: cpl0=%x wbinvd=%x cpl3=%x\n", K(0xF3, 0x0F, 0x09), K(0x0F, 0x09),
	        U(0, 0xF3, 0x0F, 0x09));

	/* prefetches: memory forms never fault, register forms of 0F 0D are #UD, of 0F 18 NOPs */
	gin(0x40000000, 0, 0, 0);
	kprintf("gpr.prefetch: far=%x w=%x r5=%x reg=%x regw=%x hint_reg=%x nta=%x\n", K(0x0F, 0x0D, 0x00),
	        K(0x0F, 0x0D, 0x08), K(0x0F, 0x0D, 0x28), K(0x0F, 0x0D, 0xC0), K(0x0F, 0x0D, 0xC8),
	        K(0x0F, 0x18, 0xC0), K(0x0F, 0x18, 0x00));

	/* CLFLUSH / CLFLUSHOPT / CLWB on ordinary memory; register forms #UD; F3/F2 forms #UD */
	gin((u32)line, 0, 0, 0);
	kprintf("gpr.clflush: clflush=%x opt=%x clwb=%x reg=%x f3=%x f2_opt=%x\n", K(0x0F, 0xAE, 0x38),
	        K(0x66, 0x0F, 0xAE, 0x38), K(0x66, 0x0F, 0xAE, 0x30), K(0x66, 0x0F, 0xAE, 0xF8),
	        K(0xF3, 0x0F, 0xAE, 0x38), K(0xF2, 0x0F, 0xAE, 0x38));

	/* MCOMMIT with EFER.MCOMMIT = 0, and RDPRU/CLZERO/MONITORX at CPL 3 are left to the model part */
	gin(0, 0, 0, 0);
	kprintf("gpr.mcommit.off: %x\n", K(0xF3, 0x0F, 0x01, 0xFA));
}

/* MODEL-ONLY: expected values in model-only.expected (derived from the APM, see Gpr.lean). */
static int twr(u32 n, u64 v) { return TRY(wrmsr(n, v)); }

void test_gpr_model(void) {
	__asm__ volatile("cli");
	/* CLZERO: the 64-byte line containing DS:EAX */
	for (int i = 0; i < 256; i++) line[i] = 0xA5;
	gin((u32)line + 64 + 37, 0, 0, 0);
	int v = K(0x0F, 0x01, 0xFC);
	u32 z = 0, a5 = 0;
	for (int i = 0; i < 256; i++) { if (line[i] == 0) z |= 1u << (i / 64); else if (line[i] == 0xA5) a5++; }
	kprintf("gpr.clzero: vec=%x zero_lines=%x a5=%d cpl3=%x\n", v, z, a5, U((u32)line, 0x0F, 0x01, 0xFC));

	/* MCOMMIT: #UD until EFER.MCOMMIT (bit 17), then CF = 1 and OF/SF/ZF/AF/PF = 0 */
	gin(0, 0, 0, 0);
	kprintf("gpr.mcommit: off=%x", K(0xF3, 0x0F, 0x01, 0xFA));
	twr(0xC0000080, 0x20000);
	gin(0, 0, 0, 0);
	v = K(0xF3, 0x0F, 0x01, 0xFA);
	kprintf(" on=%x flags=%x cpl3=%x", v, GPRO[7] & 0x8D5, U(0, 0xF3, 0x0F, 0x01, 0xFA));
	twr(0xC0000080, 0);
	kprintf(" efer=%x\n", (u32)rdmsr(0xC0000080));

	/* RDPRU: MPERF (0) and APERF (1), CF = 1; other ECX 0 with the flags unchanged (EPYC 7742; gin presets
	   them all); #UD at CPL 3 with CR4.TSD */
	twr(0xE7, 0x100000000ull);
	twr(0xE8, 5);
	gin(0, 0, 0, 0);
	K(0x0F, 0x01, 0xFD);
	u32 mp = GPRO[0], mph = GPRO[2], f0 = GPRO[7] & 0x8D5;
	gin(0, 1, 0, 0);
	K(0x0F, 0x01, 0xFD);
	u32 ap = GPRO[0], f1 = GPRO[7] & 0x8D5;
	gin(0, 2, 0, 0);
	K(0x0F, 0x01, 0xFD);
	kprintf("gpr.rdpru: mperf_hi=%x mperf_small=%d aperf_small=%d f0=%x f1=%x ecx2=%x:%x f2=%x", mph,
	        mp < 1000, ap >= 5 && ap < 1000, f0, f1, GPRO[2], GPRO[0], GPRO[7] & 0x8D5);
	kprintf(" cpl3=%x", U(0, 0x0F, 0x01, 0xFD));
	WRCR(4, RDCR(4) | 4);
	kprintf(" tsd.cpl3=%x tsd.cpl0=%x\n", U(0, 0x0F, 0x01, 0xFD), K(0x0F, 0x01, 0xFD));
	WRCR(4, RDCR(4) & ~4);

	/* RDPMC: PerfCtr0..3 (48 bits, C001_0004h..7 alias C001_0201h/3/5/7 only with PerfCtrExtCore),
	   index 4 #GP(0); CR4.PCE lets CPL 3 read them */
	twr(0xC0010004, 0xFFFF123456789ABCull);
	twr(0xC0010007, 7);
	twr(0xC0010000, 0xFFFFFFFFFFFFFFFFull);
	gin(0, 0, 0, 0);
	K(0x0F, 0x33);
	kprintf("gpr.rdpmc: c0=%x:%x", GPRO[2], GPRO[0]);
	gin(0, 3, 0, 0);
	K(0x0F, 0x33);
	kprintf(" c3=%x evtsel0=%x:%x", GPRO[0], (u32)(rdmsr(0xC0010000) >> 32), (u32)rdmsr(0xC0010000));
	gin(0, 4, 0, 0);
	kprintf(" c4=%x", K(0x0F, 0x33));
	WRCR(4, RDCR(4) | 0x100);
	kprintf(" pce.cpl3=%x", U(0, 0x0F, 0x33));
	WRCR(4, RDCR(4) & ~0x100);
	kprintf(" ext=%x\n", TRY(rdmsr(0xC0010201)));
	twr(0xC0010004, 0); twr(0xC0010007, 0); twr(0xC0010000, 0);

	/* HWCR.MonMwaitUserEn lets CPL 3 run MONITOR/MWAIT; TscFreqSel reads 1 */
	u64 hw = 0;
	TRY(hw = rdmsr(0xC0010015));
	kprintf("gpr.hwcr: %x", (u32)hw);
	twr(0xC0010015, 0x400 | 0x200);
	TRY(hw = rdmsr(0xC0010015));
	/* at CPL 3: MONITOR; a store to the line; MWAIT (no wait: the line changed) */
	kprintf(" set=%x monitor.store.mwait=%x", (u32)hw, U((u32)line, 0x0F, 0x01, 0xC8, 0xFE, 0x00, 0x0F, 0x01, 0xC9));
	twr(0xC0010015, 0);
	kprintf(" cleared=%x\n", U((u32)line, 0x0F, 0x01, 0xC8));

	/* TSC_AUX: bits 63:32 reserved (#GP); RDPID and RDTSCP ignore a 66 prefix */
	kprintf("gpr.tsc_aux.rsvd: %x", TRY(wrmsr(0xC0000103, 0x100000000ull)));
	twr(0xC0000103, 0xCAFEF00D);
	gin(0, 0x11111111, 0, 0x22222222);
	K(0x66, 0xF3, 0x0F, 0xC7, 0xFB);
	kprintf(" rdpid66=%x", GPRO[3]);
	gin(0, 0x11111111, 0, 0);
	K(0x66, 0x0F, 0x01, 0xF9);
	kprintf(" rdtscp66.ecx=%x\n", GPRO[1]);
	twr(0xC0000103, 0);

	/* MWAIT extensions: ECX[0] (interrupts wake even with IF = 0): an interrupt already pending ends
	   the wait at once without being delivered; without a MONITOR, MWAIT does not wait */
	apic_on();
	trap_hook = gpr_hook;
	hits = 0;
	ipi_self(0x59);
	gin((u32)line, 0, 0, 0);
	K(0x0F, 0x01, 0xC8);
	gin(0, 1, 0, 0);
	v = K(0x0F, 0x01, 0xC9);
	kprintf("gpr.mwait.ibe: vec=%x hits=%d", v, hits);
	__asm__ volatile("sti; nop; nop; cli");
	kprintf(" after_sti=%d", hits);
	gin(0, 1, 0, 0);
	kprintf(" unarmed=%x", K(0x0F, 0x01, 0xC9));
	/* a store to the monitored line before MWAIT: no wait */
	gin((u32)line, 0, 0, 0);
	K(0x0F, 0x01, 0xC8);
	line[5] ^= 0xFF;
	gin(0, 1, 0, 0);
	kprintf(" stored=%x\n", K(0x0F, 0x01, 0xC9));
	trap_hook = 0;

	/* MONITORX / MWAITX at CPL 3; MWAITX with a timer (ECX[1], EBX TSC ticks) and IF = 0 */
	kprintf("gpr.monitorx: cpl3=%x ecx=%x", U((u32)line, 0x0F, 0x01, 0xFA), ({ gin((u32)line, 1, 0, 0); K(0x0F, 0x01, 0xFA); }));
	gin((u32)line, 0, 0, 0);
	K(0x0F, 0x01, 0xFA);
	gin(0, 0, 0, 0);
	K(0x0F, 0x31);
	u32 s0 = GPRO[0];
	gin(0, 2, 0, 100000);
	v = K(0x0F, 0x01, 0xFB);
	gin(0, 0, 0, 0);
	K(0x0F, 0x31);
	kprintf(" mwaitx.timer=%x waited=%d", v, GPRO[0] - s0 >= 100000 && GPRO[0] - s0 < 101000);
	gin(0, 4, 0, 0);
	kprintf(" ecx4=%x\n", K(0x0F, 0x01, 0xFB));

	/* CLFLUSH: the paging checks of a one-byte read (accessed bit, not-present #PF); prefetches never
	   fault; MONITOR checks like a read; CLZERO like a store */
	for (int i = 0; i < 2048; i++) gpt[i] = (i << 12) | 3;
	gpd[0] = (u32)gpt | 3;
	gpd[1] = (u32)(gpt + 1024) | 3;
	for (int i = 2; i < 1024; i++) gpd[i] = (i << 22) | 0x83;
	u32 L = (u32)gpages;
	gpt[L >> 12] = L | 1;           /* present, read-only, A clear */
	gpt[(L >> 12) + 1] = 0;         /* not present */
	WRCR(4, RDCR(4) | 0x10);
	WRCR(3, (u32)gpd);
	WRCR(0, RDCR(0) | 0x80010000);  /* PG, WP */
	gin(L, 0, 0, 0);
	v = K(0x0F, 0xAE, 0x38);
	kprintf("gpr.clflush.paging: ro=%x a=%d d=%d", v, (gpt[L >> 12] >> 5) & 1, (gpt[L >> 12] >> 6) & 1);
	gin(L + 0x1000, 0, 0, 0);
	v = K(0x66, 0x0F, 0xAE, 0x30);
	kprintf(" np.clwb=%x err=%x cr2_ok=%d", v, last.err, last.cr2 == L + 0x1000);
	gin(L + 0x1000, 0, 0, 0);
	kprintf(" np.prefetchw=%x np.nta=%x np.monitor=%x", K(0x0F, 0x0D, 0x08), K(0x0F, 0x18, 0x00),
	        K(0x0F, 0x01, 0xC8));
	gin(L, 0, 0, 0);
	kprintf(" ro.clzero=%x err=%x\n", K(0x0F, 0x01, 0xFC), last.err);
	WRCR(0, RDCR(0) & ~0x80010000);
	WRCR(4, RDCR(4) & ~0x10);

	/* segment checks: limit of a 4 KiB data segment (CLFLUSH and MONITOR as one-byte reads, CLZERO
	   as a 64-byte store of the line), null segment */
	gdt[30] = seg_desc(0, 0xFFF, 0x92, 0x4);
	u32 r[6];
	/* (the trap handler reloads FS with the kernel's data selector, so set it before each case) */
#define FS(sel) __asm__ volatile("movw %w0, %%fs" :: "r"(sel))
	FS(30 << 3); gin(0xFFF, 0, 0, 0); r[0] = K(0x64, 0x0F, 0xAE, 0x38);
	FS(30 << 3); gin(0x1000, 0, 0, 0); r[1] = K(0x64, 0x0F, 0xAE, 0x38);
	FS(30 << 3); gin(0x1000, 0, 0, 0); r[2] = K(0x64, 0x0F, 0x01, 0xC8);
	FS(30 << 3); gin(0xFC1, 0, 0, 0); r[3] = K(0x64, 0x0F, 0x01, 0xFC);
	FS(0); gin((u32)line, 0, 0, 0); r[4] = K(0x64, 0x0F, 0xAE, 0x38);
	FS(0); gin((u32)line, 0, 0, 0); r[5] = K(0x64, 0x0F, 0x01, 0xFC);
	FS(KDATA);
	kprintf("gpr.clflush.seg: last=%x beyond=%x monitor.beyond=%x clzero.line=%x null=%x null.clzero=%x\n",
	        r[0], r[1], r[2], r[3], r[4], r[5]);
}
