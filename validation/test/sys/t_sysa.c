/* System workstream A (AMD APM vol. 2/3): SYSENTER/SYSEXIT, legacy-mode SYSCALL/SYSRET, CLAC/STAC,
   UMIP, AltMovCr8 (LOCK MOV CR0 = CR8), EFER bits, MSRs (TSC, SYSENTER, STAR, PAT, MTRRs), PSE-36,
   SMEP/SMAP through the TLB and SMAP for implicit supervisor accesses. test_sysa is compared with
   QEMU (EPYC-Rome under TCG; deviations from the APM are rewritten by rules in qemu-deviations.txt);
   test_sysa_model runs in the MODEL-ONLY section: alignment checking (#AC, which TCG does not
   implement), global pages (TLB retention is implementation-defined), and the reserved-bit rules of
   the MSRs that TCG does not model (MCA, PAT/MTRR #GP, LSTAR canonical checks, SPEC_CTRL, ...). */
#include "sys.h"

#define EFER 0xC0000080
#define APIC ((volatile u32 *)0xFEE00000)

/* ---- runners ---- */

static u8 ucode[64] __attribute__((aligned(16)));
static u8 ustk[4096] __attribute__((aligned(16)));
static u8 kcode[64] __attribute__((aligned(16)));
__attribute__((used)) u32 ur_eax, ur_ebx, ur_ecx, ur_edx, ur_esi, ur_edi, ur_esp, ur_fl, ur_eip;
__attribute__((used)) void *kcode_p = kcode;
/* the frame of the INT 0x40 that ends a ring-3 snippet */
static volatile u32 o_cs, o_ss, o_esp, o_fl, o_eax, o_ecx, o_edx;
/* filled by the kernel entry points of SYSENTER / SYSCALL */
__attribute__((used)) volatile u32 sa_k_cs, sa_k_ss, sa_k_esp, sa_k_fl, sa_k_ecx;
__attribute__((used, aligned(16))) u8 abuf[512];
extern char k_sysenter[], k_syscall[];

__asm__(
	".globl k_sysenter\nk_sysenter:\n"
	"movl %esp, sa_k_esp\n pushfl\n popl sa_k_fl\n movw %cs, sa_k_cs\n movw %ss, sa_k_ss\n"
	".byte 0x0f, 0x35\n"            /* SYSEXIT */
	".globl k_syscall\nk_syscall:\n"
	"movl %ecx, sa_k_ecx\n movl %esp, sa_k_esp\n pushfl\n popl sa_k_fl\n movw %cs, sa_k_cs\n movw %ss, sa_k_ss\n"
	".byte 0x0f, 0x07\n");          /* SYSRET */

static u32 sa_cr4, sa_restore;   /* a #PF with SMAP on and AC = 0 in the handler: restore CR4 first */
static int sa_hook(struct frame *f) {
	if (f->vec == 14 && sa_restore) { WRCR(4, sa_cr4); sa_restore = 0; }
	if (f->vec == 0x40) {
		o_cs = f->cs & 0xFFFF; o_ss = f->uss & 0xFFFF; o_esp = f->uesp; o_fl = f->eflags;
		o_eax = f->eax; o_ecx = f->ecx; o_edx = f->edx;
	}
	return 0;
}

/* Run `n` bytes at ring 3 (followed by INT 0x40) with EFLAGS `fl` and ur_* registers; 0x40 = completed. */
static int urun(const u8 *b, int n, u32 fl) {
	for (int k = 0; k < n; k++) ucode[k] = b[k];
	ucode[n] = 0xCD; ucode[n + 1] = 0x40;
	if (!ur_esp) ur_esp = (u32)ustk + sizeof ustk;
	ur_fl = fl; ur_eip = (u32)ucode;
	int v = TRY(__asm__ volatile(
		"pushl $0x23\n pushl ur_esp\n pushl ur_fl\n pushl $0x1B\n pushl ur_eip\n"
		"movl $0x23, %%eax\n movl %%eax, %%ds\n movl %%eax, %%es\n movl %%eax, %%fs\n movl %%eax, %%gs\n"
		"movl ur_eax, %%eax\n movl ur_ebx, %%ebx\n movl ur_ecx, %%ecx\n movl ur_edx, %%edx\n"
		"movl ur_esi, %%esi\n movl ur_edi, %%edi\n iret"
		::: "eax", "ebx", "ecx", "edx", "esi", "edi", "memory"));
	ur_esp = 0;
	return v;
}
#define U(fl, ...) ({ static const u8 _b[] = { __VA_ARGS__ }; urun(_b, sizeof _b, fl); })

/* Run `n` bytes at ring 0 (followed by RET) with EAX..EDX from ur_*; EAX/EDX are stored back. */
static int krun(const u8 *b, int n) {
	for (int k = 0; k < n; k++) kcode[k] = b[k];
	kcode[n] = 0xC3;
	return TRY(__asm__ volatile(
		"movl ur_eax, %%eax\n movl ur_ebx, %%ebx\n movl ur_ecx, %%ecx\n movl ur_edx, %%edx\n"
		"call *kcode_p\n movl %%eax, ur_eax\n movl %%edx, ur_edx"
		::: "eax", "ebx", "ecx", "edx", "memory", "cc"));
}
#define K(...) ({ static const u8 _b[] = { __VA_ARGS__ }; krun(_b, sizeof _b); })

static u32 msr_vec(u32 n, u64 v) { return TRY(wrmsr(n, v)); }
static u64 msr_rd(u32 n, int *vec) { u64 v = 0; *vec = TRY(v = rdmsr(n)); return v; }
static void stac(void) { __asm__ volatile(".byte 0x0f, 0x01, 0xcb" ::: "memory", "cc"); }
static void clac(void) { __asm__ volatile(".byte 0x0f, 0x01, 0xca" ::: "memory", "cc"); }

/* ---- 4 KiB identity paging of 0..64 MiB (32-bit), page attributes set per test ---- */

static u32 *ipd, *ipt;
static void ident(u32 attr) {
	if (!ipd) { ipd = page_alloc(1); ipt = page_alloc(16); }
	for (u32 a = 0; a < 0x4000000; a += 0x1000) ipt[a >> 12] = a | attr;
	for (u32 i = 0; i < 1024; i++) ipd[i] = i < 16 ? ((u32)ipt + i * 0x1000) | 7 : 0;
}
static void pg_on(void) { WRCR(3, (u32)ipd); WRCR(0, RDCR(0) | 0x80010000); }
static void pg_off(void) { WRCR(0, RDCR(0) & ~0x80000000); }
static u32 *pte(u32 lin) { return &ipt[lin >> 12]; }

/* ---- QEMU-compared ---- */

static void t_sysenter(void) {
	wrmsr(0x174, KCODE); wrmsr(0x175, (u32)page_alloc(1) + 4096); wrmsr(0x176, (u32)k_sysenter);
	u32 ret = (u32)ucode + 9;
	u8 b[9] = { 0x89, 0xE1, 0xBA, (u8)ret, (u8)(ret >> 8), (u8)(ret >> 16), (u8)(ret >> 24), 0x0F, 0x34 };
	sa_k_cs = sa_k_ss = 0;
	int v = urun(b, 9, 0x202);
	kprintf("sysa.sysenter: vec=%x k: cs=%x ss=%x esp_ok=%d fl=%x u: cs=%x ss=%x esp_ok=%d fl=%x\n", v,
	        sa_k_cs & 0xFFFF, sa_k_ss & 0xFFFF, sa_k_esp == (u32)rdmsr(0x175), sa_k_fl,
	        o_cs, o_ss, o_esp == (u32)ustk + sizeof ustk, o_fl);
	kprintf("sysa.sysenter.msrs: cs=%x eip_ok=%d\n", (u32)rdmsr(0x174), (u32)rdmsr(0x176) == (u32)k_sysenter);
	wrmsr(0x174, 0);
	int v0 = urun(b, 9, 0x202);
	u32 e0 = last.err;
	int x3 = U(0x202, 0x0F, 0x35);
	u32 e3 = last.err;
	int x0 = K(0x0F, 0x35);
	kprintf("sysa.sysenter.null: %x/%x sysexit.cpl3: %x/%x sysexit.null: %x/%x\n", v0, e0, x3, e3, x0, last.err);
	/* SYSENTER_CS/ESP/EIP keep bits 15:0 / 31:0 */
	wrmsr(0x174, 0x123456789ABCDEF0ULL); wrmsr(0x175, 0x1111222233334444ULL); wrmsr(0x176, 0x5555666677778888ULL);
	kprintf("sysa.sysenter.width: %x %x %x %x %x %x\n", (u32)(rdmsr(0x174) >> 32), (u32)rdmsr(0x174),
	        (u32)(rdmsr(0x175) >> 32), (u32)rdmsr(0x175), (u32)(rdmsr(0x176) >> 32), (u32)rdmsr(0x176));
	wrmsr(0x174, 0); wrmsr(0x175, 0); wrmsr(0x176, 0);
}

static void t_syscall(void) {
	wrmsr(EFER, 0);
	int u3 = U(0x202, 0x0F, 0x05), u0 = K(0x0F, 0x05), r0 = K(0x0F, 0x07);
	kprintf("sysa.syscall.nosce: syscall3=%x syscall0=%x sysret0=%x\n", u3, u0, r0);
	wrmsr(EFER, 1);
	/* STAR: SYSRET CS 0x1B (SS 0x23), SYSCALL CS 0x08 (SS 0x10), target k_syscall */
	static const u16 sel[][2] = { { 0x1B, 0x08 }, { 0x18, 0x08 }, { 0x1B, 0x0B } };
	for (int k = 0; k < 3; k++) {
		wrmsr(0xC0000081, ((u64)sel[k][0] << 48) | ((u64)sel[k][1] << 32) | (u32)k_syscall);
		sa_k_cs = sa_k_ss = sa_k_ecx = 0;
		int v = U(0x202, 0x0F, 0x05);
		kprintf("sysa.syscall %d: vec=%x k: cs=%x ss=%x ecx_ok=%d esp_ok=%d fl=%x u: cs=%x ss=%x fl=%x\n", k, v,
		        sa_k_cs & 0xFFFF, sa_k_ss & 0xFFFF, sa_k_ecx == (u32)ucode + 2, sa_k_esp == (u32)ustk + sizeof ustk,
		        sa_k_fl, o_cs, o_ss, o_fl);
	}
	int s3 = U(0x202, 0x0F, 0x07);
	kprintf("sysa.sysret.cpl3: %x/%x star=%x\n", s3, last.err, (u32)(rdmsr(0xC0000081) >> 32));
	wrmsr(0xC0000081, 0);
	wrmsr(EFER, 0);
}

static void t_clac(void) {
	u32 f0, f1;
	stac(); f0 = rdflags(); clac(); f1 = rdflags();
	int c3 = U(0x202, 0x0F, 0x01, 0xCA), s3 = U(0x202, 0x0F, 0x01, 0xCB);
	kprintf("sysa.clac: stac=%x clac=%x clac3=%x stac3=%x\n", f0 & 0x40000, f1 & 0x40000, c3, s3);
}

static void t_umip(void) {
	u32 cr4 = RDCR(4);
	int v = TRY(WRCR(4, cr4 | 0x800));
	ur_ebx = (u32)abuf;
	int sg = U(0x202, 0x0F, 0x01, 0x03), si = U(0x202, 0x0F, 0x01, 0x0B), sl = U(0x202, 0x0F, 0x00, 0xC0),
	    st = U(0x202, 0x0F, 0x00, 0xC8), sm = U(0x202, 0x0F, 0x01, 0xE0), smm = U(0x202, 0x0F, 0x01, 0x23);
	u32 err = last.err;
	int k0 = K(0x0F, 0x01, 0xE0);
	kprintf("sysa.umip: cr4=%x sgdt=%x sidt=%x sldt=%x str=%x smsw=%x smsw_m=%x/%x ring0=%x\n", v, sg, si, sl, st,
	        sm, smm, err, k0);
	WRCR(4, cr4);
	kprintf("sysa.umip.off: sgdt=%x smsw=%x\n", U(0x202, 0x0F, 0x01, 0x03), U(0x202, 0x0F, 0x01, 0xE0));
}

static void t_cr8(void) {
	APIC[0x80 >> 2] = 0;
	ur_eax = 5;
	int w = K(0xF0, 0x0F, 0x22, 0xC0);            /* LOCK MOV CR0, EAX = MOV CR8, EAX */
	u32 tpr = APIC[0x80 >> 2];
	ur_eax = 0;
	int r = K(0xF0, 0x0F, 0x20, 0xC0);            /* LOCK MOV EAX, CR0 = MOV EAX, CR8 */
	kprintf("sysa.cr8: write=%x tpr=%x read=%x eax=%x\n", w, tpr, r, ur_eax);
	APIC[0x80 >> 2] = 0x90;
	r = K(0xF0, 0x0F, 0x20, 0xC0);
	kprintf("sysa.cr8.tpr: read=%x eax=%x\n", r, ur_eax);
	ur_eax = 0x15;
	w = K(0xF0, 0x0F, 0x22, 0xC0);
	kprintf("sysa.cr8.rsvd: write=%x tpr=%x\n", w, APIC[0x80 >> 2]);
	int c2 = K(0xF0, 0x0F, 0x22, 0xD0);           /* LOCK MOV CR2: no CR10 */
	int u3 = U(0x202, 0xF0, 0x0F, 0x20, 0xC0);
	kprintf("sysa.cr8.other: lock_cr2=%x ring3=%x/%x\n", c2, u3, last.err);
	APIC[0x80 >> 2] = 0;
}

static void t_efer(void) {
	static const struct { const char *n; u32 bit; } b[] = {
		{ "sce", 1 }, { "rsvd1", 2 }, { "nxe", 0x800 }, { "lmsle", 0x2000 }, { "ffxsr", 0x4000 }, { "tce", 0x8000 },
		{ "intwb", 0x40000 }, { "rsvd16", 0x10000 }, { "rsvd19", 0x80000 } };
	for (u32 k = 0; k < sizeof b / sizeof b[0]; k++) {
		int v = msr_vec(EFER, b[k].bit);
		kprintf("sysa.efer.%s: vec=%x efer=%x\n", b[k].n, v, (u32)rdmsr(EFER));
		wrmsr(EFER, 0);
	}
}

static void t_msr(void) {
	int v;
	/* STAR keeps 64 bits */
	wrmsr(0xC0000081, 0x0123456789ABCDEFULL);
	kprintf("sysa.star: %x_%x\n", (u32)(rdmsr(0xC0000081) >> 32), (u32)rdmsr(0xC0000081));
	wrmsr(0xC0000081, 0);
	/* PAT: reset value, a valid value, an unsupported type (2) and a reserved bit (#GP(0) on AMD) */
	u64 pat = rdmsr(0x277);
	v = msr_vec(0x277, 0x0001040506070001ULL);
	kprintf("sysa.pat: reset=%x_%x valid=%x %x_%x\n", (u32)(pat >> 32), (u32)pat, v, (u32)(rdmsr(0x277) >> 32),
	        (u32)rdmsr(0x277));
	v = msr_vec(0x277, 0x0007040600070402ULL);
	kprintf("sysa.pat.type2: vec=%x pat=%x\n", v, (u32)rdmsr(0x277));
	wrmsr(0x277, pat);
	v = msr_vec(0x277, 0x0007040600070416ULL);
	kprintf("sysa.pat.rsvd: vec=%x pat=%x\n", v, (u32)rdmsr(0x277));
	wrmsr(0x277, pat);
	/* MTRRs */
	kprintf("sysa.mtrrcap: %x\n", (u32)rdmsr(0xFE));
	u64 dt = rdmsr(0x2FF), b0 = rdmsr(0x200), m0 = rdmsr(0x201);
	wrmsr(0x2FF, 0xC06); wrmsr(0x200, 0x12345006ULL); wrmsr(0x201, 0xFFF000800ULL);
	kprintf("sysa.mtrr: deftype=%x base0=%x mask0=%x_%x\n", (u32)rdmsr(0x2FF), (u32)rdmsr(0x200),
	        (u32)(rdmsr(0x201) >> 32), (u32)rdmsr(0x201));
	v = msr_vec(0x2FF, 0x1C06);
	kprintf("sysa.mtrr.deftype.rsvd: vec=%x deftype=%x\n", v, (u32)rdmsr(0x2FF));
	wrmsr(0x2FF, dt); wrmsr(0x200, b0); wrmsr(0x201, m0);
}

/* PSE-36: 4 MiB PDE bits 20:13 are physical-address bits 39:32 (no fault, the access reaches memory
   above 4 GiB); bit 21 is reserved. Only vectors, error codes and the accessed flag are printed. */
static void t_pse36(void) {
	ident(7);
	u32 cr4 = RDCR(4);
	WRCR(4, cr4 | 0x10);
	pg_on();
	kputs("sysa.pse36:");
	for (u32 b = 13; b <= 21; b++) {
		pg_off();
		ipd[0x100] = 0x00400000 | 0x87 | (1u << b);    /* 4 MiB page at 0x40000000 */
		pg_on();
		int r = TRY((void)*(volatile u32 *)0x40000000);
		u32 e = r == 14 ? last.err : 0;
		kprintf(" %d:%x/%x a=%d", b, r, e, (ipd[0x100] >> 5) & 1);
	}
	kputc('\n');
	pg_off();
	ipd[0x100] = 0;
	WRCR(4, cr4);
}

/* SMEP/SMAP with a translation cached before CR4 changes, and SMAP for an implicit supervisor access
   (an LDT on a user page, loaded with EFLAGS.AC = 1: APM vol. 2, 5.6.6 checks it regardless of AC). */
static void t_smx(void) {
	u32 cr4 = RDCR(4);
	ident(3);                                      /* supervisor identity map */
	u8 *upage = page_alloc(1);
	upage[0] = 0xC3;                                /* RET */
	*(u32 *)(upage + 16) = 0x5A5A1234;
	*pte((u32)upage) |= 4;                          /* one user page */
	pg_on();
	void (*volatile fn)(void) = (void (*)(void))upage;
	volatile u32 *p = (u32 *)(upage + 16);
	u32 val = 0;
	int f0 = TRY(fn()), r0 = TRY(val = *p);         /* fills the TLB */
	int c = TRY(WRCR(4, cr4 | 0x300000));
	int f1 = TRY(fn());
	u32 ef = last.err;
	int r1 = TRY(val = *p);
	u32 er = last.err;
	stac();
	int r2 = TRY(val = *p);
	int w2 = TRY(*p = 0x77);
	clac();
	int w3 = TRY(*p = 0x88);
	u32 ew = last.err;
	WRCR(4, cr4);
	kprintf("sysa.smx.tlb: before=%x/%x cr4=%x smep_fetch=%x/%x smap_read=%x/%x stac_read=%x stac_write=%x clac_write=%x/%x val=%x\n",
	        f0, r0, c, f1, ef, r1, er, r2, w2, w3, ew, *(volatile u32 *)(upage + 16) + (val & 0));
	pg_off();

	/* implicit: user identity map except the GDT and IDT pages; SMAP on, AC = 1 */
	ident(7);
	*pte((u32)gdt) &= ~4u; *pte((u32)gdt + sizeof gdt - 1) &= ~4u;
	*pte((u32)idt) &= ~4u; *pte((u32)idt + sizeof idt - 1) &= ~4u;
	u64 *ldt = page_alloc(1);
	ldt[0] = seg_desc(0, 0xFFFFF, 0xF2, 0xC);       /* data, DPL 3: selector 0x07 */
	gdt[30] = seg_desc((u32)ldt, 0xFF, 0x82, 0);
	__asm__ volatile("lldt %0" :: "r"((u16)0xF0));
	pg_on();
	sa_cr4 = cr4; sa_restore = 1;
	WRCR(4, cr4 | 0x200000);
	stac();
	u32 fs = 0;
	int li = TRY(__asm__ volatile("movl %1, %%eax\n movl %%eax, %%fs\n movl %%fs, %0" : "=r"(fs) : "i"(7) : "eax"));
	u32 el = last.err, cl = last.cr2;
	sa_restore = 0;
	clac();
	WRCR(4, cr4);
	__asm__ volatile("movl %0, %%fs" :: "r"((u32)KDATA));
	kprintf("sysa.smap.implicit: vec=%x err=%x cr2_ok=%d fs=%x\n", li, li == 14 ? el : 0, li == 14 && cl == (u32)ldt, fs);
	pg_off();
	__asm__ volatile("lldt %0" :: "r"((u16)0));
	gdt[30] = 0;
}

void test_sysa(void) {
	trap_hook = sa_hook;
	t_sysenter();
	t_syscall();
	t_clac();
	t_umip();
	t_cr8();
	t_efer();
	t_msr();
	t_pse36();
	t_smx();
	trap_hook = 0;
}

/* ---- MODEL-ONLY ---- */

/* #AC: CR0.AM = 1, EFLAGS.AC = 1, CPL 3; the APM's table 8-7 alignments (expected values in
   model-only.expected; QEMU's TCG does not implement alignment checking). */
static void t_ac(void) {
	u32 cr0 = RDCR(0), cr4 = RDCR(4);
	WRCR(0, (cr0 | 0x40000) & ~0xC);
	WRCR(4, cr4 | 0x600);
	__asm__ volatile("fninit");
	const u32 AC = 0x40202;
	u32 B = (u32)abuf;
	memset(abuf, 0, sizeof abuf);
#define AT(off) (ur_ebx = B + (off), ur_esi = B + (off), ur_edi = B + (off))
	kputs("sysa.ac:");
	AT(1); kprintf(" w1=%x", U(AC, 0x66, 0x8B, 0x03));
	AT(2); kprintf(" w2=%x", U(AC, 0x66, 0x8B, 0x03));
	AT(2); kprintf(" d2=%x", U(AC, 0x8B, 0x03));
	AT(4); kprintf(" d4=%x", U(AC, 0x8B, 0x03));
	AT(3); kprintf(" b3=%x", U(AC, 0x8A, 0x03));
	AT(2); kprintf(" noac=%x", U(0x202, 0x8B, 0x03));
	AT(1); kprintf(" err=%x", (U(AC, 0x89, 0x03), last.err));
	AT(1); kprintf(" rmw=%x", U(AC, 0x01, 0x03));
	AT(2); kprintf(" push=%x", U(AC, 0x89, 0xDC, 0x50));         /* mov esp, ebx; push eax */
	AT(4); kprintf(" push4=%x", U(AC, 0x89, 0xDC, 0x50));
	AT(1); kprintf(" movsw=%x", U(AC, 0x66, 0xA5));
	AT(2); kprintf(" bt=%x", U(AC, 0x0F, 0xA3, 0x03));           /* bt [ebx], eax (eax = 0) */
	AT(4); kprintf(" bt4=%x", U(AC, 0x0F, 0xA3, 0x03));
	kputc('\n');
	kputs("sysa.ac.multi:");
	AT(4); kprintf(" cx8_4=%x", U(AC, 0x0F, 0xC7, 0x0B));
	AT(8); kprintf(" cx8_8=%x", U(AC, 0x0F, 0xC7, 0x0B));
	AT(2); kprintf(" les_2=%x", U(AC, 0xC4, 0x03));               /* 48-bit far pointer: 4 */
	AT(4); kprintf(" les_4=%x", U(AC, 0xC4, 0x03));
	AT(2); kprintf(" les16_2=%x", U(AC, 0x66, 0xC4, 0x03));       /* 32-bit far pointer: 2 */
	AT(2); kprintf(" sgdt_2=%x", U(AC, 0x0F, 0x01, 0x03));        /* word then dword: mod 4 = 2 */
	AT(4); kprintf(" sgdt_4=%x", U(AC, 0x0F, 0x01, 0x03));
	AT(1); kprintf(" movsreg=%x", U(AC, 0x8C, 0x1B));             /* mov [ebx], ds */
	kputc('\n');
	kputs("sysa.ac.fp:");
	AT(4); kprintf(" fld32_4=%x", U(AC, 0xD9, 0x03));
	AT(2); kprintf(" fld32_2=%x", U(AC, 0xD9, 0x03));
	AT(4); kprintf(" fld64_4=%x", U(AC, 0xDD, 0x03));
	AT(8); kprintf(" fld64_8=%x", U(AC, 0xDD, 0x03));
	AT(4); kprintf(" fld80_4=%x", U(AC, 0xDB, 0x2B));
	AT(8); kprintf(" fld80_8=%x", U(AC, 0xDB, 0x2B));
	AT(4); kprintf(" fistp64_4=%x", U(AC, 0xDF, 0x3B));
	AT(1); kprintf(" fnstcw_1=%x", U(AC, 0xD9, 0x3B));
	AT(2); kprintf(" fnstenv_2=%x", U(AC, 0xD9, 0x33));
	AT(4); kprintf(" fnstenv_4=%x", U(AC, 0xD9, 0x33));
	AT(2); kprintf(" fnstenv16_2=%x", U(AC, 0x66, 0xD9, 0x33));
	AT(2); kprintf(" fnsave16_2=%x", U(AC, 0x66, 0xDD, 0x33));
	AT(4); kprintf(" fnsave_4=%x", U(AC, 0xDD, 0x33));
	AT(2); kprintf(" frstor_2=%x", U(AC, 0xDD, 0x23));
	__asm__ volatile("fninit");
	kputc('\n');
	kputs("sysa.ac.simd:");
	AT(8); kprintf(" movups_8=%x", U(AC, 0x0F, 0x10, 0x03));
	AT(16); kprintf(" movups_16=%x", U(AC, 0x0F, 0x10, 0x03));
	AT(8); kprintf(" movaps_8=%x", U(AC, 0x0F, 0x28, 0x03));
	AT(4); kprintf(" movq_4=%x", U(AC, 0x0F, 0x6F, 0x03));
	AT(8); kprintf(" movq_8=%x", U(AC, 0x0F, 0x6F, 0x03));
	AT(2); kprintf(" movss_2=%x", U(AC, 0xF3, 0x0F, 0x10, 0x03));
	AT(4); kprintf(" movss_4=%x", U(AC, 0xF3, 0x0F, 0x10, 0x03));
	AT(4); kprintf(" movsd_4=%x", U(AC, 0xF2, 0x0F, 0x10, 0x03));
	AT(2); kprintf(" stmxcsr_2=%x", U(AC, 0x0F, 0xAE, 0x1B));
	AT(4); kprintf(" maskmovq_4=%x", U(AC, 0x0F, 0xF7, 0xC1));    /* MASKMOVQ mm0, mm1 at DS:EDI */
	AT(8); kprintf(" fxsave_8=%x", U(AC, 0x0F, 0xAE, 0x03));
	__asm__ volatile("emms");
	kputc('\n');
	/* not checked: AC = 0, CR0.AM = 0, CPL 0, implicit accesses (a GDT at an odd address) */
	AT(1);
	int r0 = TRY(__asm__ volatile("pushfl\n orl $0x40000, (%%esp)\n popfl\n movl 1(%0), %%eax\n pushfl\n"
	                              "andl $~0x40000, (%%esp)\n popfl" :: "r"(abuf) : "eax", "memory", "cc"));
	WRCR(0, (cr0 & ~0x40000) & ~0xC);
	AT(1); int am0 = U(AC, 0x8B, 0x03);
	WRCR(0, (cr0 | 0x40000) & ~0xC);
	memcpy(abuf + 1, gdt, 8 * 8);
	struct { u16 lim; u32 base; } __attribute__((packed)) g1 = { 8 * 8 - 1, B + 1 }, g0 = { sizeof gdt - 1, (u32)gdt };
	__asm__ volatile("lgdt %0" :: "m"(g1));
	ur_eax = UDATA;
	int imp = U(AC, 0x8E, 0xD8);                                   /* mov ds, eax: GDT read at B+1+0x20 */
	__asm__ volatile("lgdt %0" :: "m"(g0));
	kprintf("sysa.ac.exempt: cpl0=%x am0=%x implicit=%x\n", r0, am0, imp);
	/* #AC is checked before paging: a misaligned read of a not-present page */
	ident(7);
	u32 L = (u32)page_alloc(1);
	*pte(L) = 0;
	pg_on();
	ur_ebx = L + 1;
	int npf = U(AC, 0x8B, 0x03);
	ur_ebx = L + 4;
	int npa = U(AC, 0x8B, 0x03);
	pg_off();
	*pte(L) = L | 7;
	kprintf("sysa.ac.pf: misaligned=%x aligned=%x\n", npf, npa);
	WRCR(0, cr0);
	WRCR(4, cr4);
#undef AT
}

/* Global pages: with CR4.PGE a G=1 translation survives MOV CR3 (APM vol. 2, 5.5.2) until INVLPG or a
   change of CR4.PGE; caching is permitted, not required, so this checks the model's TLB policy. */
static void t_global(void) {
	u32 cr4 = RDCR(4);
	ident(7);
	u32 *f = page_alloc(4);
	f[0] = 0xA; f[1024] = 0xB; f[2048] = 0xC; f[3072] = 0xD;
	u32 L = 0x40000000;
	ipd[L >> 22] = (u32)page_alloc(1) | 7;
	u32 *pt = (u32 *)(ipd[L >> 22] & ~0xFFF);
	pt[0] = (u32)f | 0x107;                         /* G = 1 */
	pt[1] = ((u32)f + 0x1000) | 7;                  /* G = 0 */
	WRCR(4, cr4 | 0x80);
	pg_on();
	volatile u32 *g = (u32 *)L, *n = (u32 *)(L + 0x1000);
	u32 a = *g + *n;
	pt[0] = ((u32)f + 0x2000) | 0x107;
	pt[1] = ((u32)f + 0x3000) | 7;
	WRCR(3, RDCR(3));
	u32 g1 = *g, n1 = *n;
	invlpg(L);
	u32 g2 = *g;
	pt[0] = (u32)f | 0x107;
	WRCR(3, RDCR(3));
	u32 g3 = *g;
	WRCR(4, cr4);                                   /* PGE 1 -> 0 flushes global entries */
	u32 g4 = *g;
	pt[0] = ((u32)f + 0x2000) | 0x107;
	WRCR(3, RDCR(3));
	u32 g5 = *g;                                    /* PGE = 0: G is ignored */
	kprintf("sysa.global: %x cr3=%x/%x invlpg=%x cr3=%x pge_off=%x nopge_cr3=%x\n", a, g1, n1, g2, g3, g4, g5);
	pg_off();
	ipd[L >> 22] = 0;
	WRCR(4, cr4);
}

static void t_msr_model(void) {
	int v, w;
	u64 x;
	/* TSC: WRMSR 0x10 sets the counter (TCG ignores WRMSR/RDMSR of MSR 0x10) */
	wrmsr(0x10, 0x1234500000000ULL);
	u32 lo, hi;
	__asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
	kprintf("sysa.tsc: hi=%x msr_hi=%x\n", hi, (u32)(rdmsr(0x10) >> 32));
	kputs("sysa.msr:");
	x = msr_rd(0x179, &v); kprintf(" mcg_cap=%x/%x", v, (u32)x);
	kprintf(" mcg_cap_wr=%x", msr_vec(0x179, 0));
	w = msr_vec(0x17A, 0xFF); x = msr_rd(0x17A, &v); kprintf(" mcg_status=%x/%x", w, (u32)x);
	w = msr_vec(0x17B, ~0ULL); x = msr_rd(0x17B, &v); kprintf(" mcg_ctl=%x/%x", w, (u32)x);
	kprintf(" mc0_status_wr=%x mc0_status_0=%x", msr_vec(0x401, 1), msr_vec(0x401, 0));
	u64 hw = rdmsr(0xC0010015);
	wrmsr(0xC0010015, hw | 0x40000);
	kprintf(" mcstatuswren=%x", msr_vec(0x401, 0x8000000000000001ULL));
	x = rdmsr(0x401); kprintf("/%x_%x", (u32)(x >> 32), (u32)x);
	wrmsr(0x401, 0); wrmsr(0xC0010015, hw);
	x = msr_rd(0x400 + 4 * 23, &v); kprintf(" mc23=%x", v);
	kputc('\n');
	kputs("sysa.msr.mtrr:");
	kprintf(" cap_wr=%x", msr_vec(0xFE, 0x508));
	kprintf(" type2=%x type7=%x", msr_vec(0x2FF, 0x802), msr_vec(0x2FF, 0x807));
	kprintf(" base_rsvd=%x mask_rsvd=%x base_hi=%x", msr_vec(0x200, 0x100), msr_vec(0x201, 0x400),
	        msr_vec(0x200, 1ULL << 48));
	kprintf(" fix_rsvd=%x fix_type3=%x", msr_vec(0x250, 0x20), msr_vec(0x250, 0x0300000000000000ULL));
	/* RdMem/WrMem: hidden while SYSCFG.MtrrFixDramModEn = 0 */
	u64 sc = rdmsr(0xC0010010);
	wrmsr(0x250, 0x1E1E1E1E1E1E1E1EULL);
	u64 h = rdmsr(0x250);
	wrmsr(0xC0010010, sc | 0x80000);
	u64 m1 = rdmsr(0x250);
	wrmsr(0x250, 0x1E1E1E1E1E1E1E1EULL);
	u64 m2 = rdmsr(0x250);
	wrmsr(0xC0010010, sc);
	u64 m3 = rdmsr(0x250);
	kprintf(" fix_hidden=%x fix_moden=%x/%x fix_after=%x", (u32)h, (u32)m1, (u32)m2, (u32)m3);
	wrmsr(0xC0010010, sc | 0x80000); wrmsr(0x250, 0); wrmsr(0xC0010010, sc);
	kputc('\n');
	kputs("sysa.msr.amd:");
	x = msr_rd(0xC0010010, &v); kprintf(" syscfg=%x/%x rsvd=%x", v, (u32)x, msr_vec(0xC0010010, 1ULL << 27));
	x = msr_rd(0xC0010015, &v); kprintf(" hwcr=%x/%x", v, (u32)x);
	x = msr_rd(0xC001001A, &v); kprintf(" top_mem=%x/%x rsvd=%x", v, (u32)x, msr_vec(0xC001001A, 0x1000));
	x = msr_rd(0xC0010140, &v); kprintf(" osvw_len=%x/%x", v, (u32)x);
	x = msr_rd(0xC0011004, &v); kprintf(" cpuid1=%x/%x_%x", v, (u32)(x >> 32), (u32)x);
	x = msr_rd(0xC001011F, &v); kprintf(" virt_spec_ctrl=%x", v);
	kputc('\n');
	kputs("sysa.msr.spec:");
	kprintf(" spec_ctrl=%x", msr_vec(0x48, 7));
	x = msr_rd(0x48, &v); kprintf("/%x", (u32)x);
	kprintf(" spec_rsvd=%x", msr_vec(0x48, 8));
	wrmsr(0x48, 0);
	kprintf(" ibpb=%x pred_rsvd=%x", msr_vec(0x49, 1), msr_vec(0x49, 2));
	x = msr_rd(0x49, &v); kprintf(" pred_rd=%x", v);
	kprintf(" lstar=%x lstar_nc=%x cstar_nc=%x", msr_vec(0xC0000082, 0xFFFF800000000000ULL),
	        msr_vec(0xC0000082, 0x0000800000000000ULL), msr_vec(0xC0000083, 0x1000000000000000ULL));
	x = msr_rd(0xC0000082, &v); kprintf(" lstar_rd=%x_%x", (u32)(x >> 32), (u32)x);
	wrmsr(0xC0000084, 0xFFFFFFFF00004700ULL);
	x = msr_rd(0xC0000084, &v); kprintf(" sfmask=%x_%x", (u32)(x >> 32), (u32)x);
	u64 a0 = rdmsr(0xE8), a1 = rdmsr(0xE8);
	kprintf(" aperf_runs=%d", a1 > a0);
	kputc('\n');
	/* SYSENTER with a null selector whose RPL is not 0 (APM: "MSR_SYSENTER_CS was a null selector") */
	wrmsr(0x174, 3);
	u8 b[2] = { 0x0F, 0x34 };
	int s = urun(b, 2, 0x202);
	kprintf("sysa.sysenter.null3: %x/%x\n", s, last.err);
	wrmsr(0x174, 0);
}

void test_sysa_model(void) {
	trap_hook = sa_hook;
	t_ac();
	t_global();
	t_msr_model();
	trap_hook = 0;
}
