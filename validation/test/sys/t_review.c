/* Regression tests for review findings on the merged EPYC model.
   test_review (compared with QEMU):
   * rv.int.*: INT n reads the TSS interrupt-redirection bitmap only in virtual-8086 mode with
     CR4.VME = 1 (AMD APM vol. 2, 8.10.1, table 8-11; vol. 3 INT). With a TSS whose limit is that of
     a 16-bit TSS (2Bh), or whose I/O map base lies beyond the limit, INT n in protected mode (CPL 0
     and CPL 3), in virtual-8086 mode without VME and in real mode (inside SMM) is delivered normally.
   * rv.v86pg.*: interrupts and exceptions from virtual-8086 mode push their frame onto the ring-0
     stack as supervisor accesses (SDM vol. 3, INT pseudocode INTERRUPT-FROM-VIRTUAL-8086-MODE:
     "VM ← 0 ... CPL ← 0" before the pushes; 4.6: accesses made while CPL < 3 are supervisor
     accesses): under paging with a supervisor-only ring-0 stack page they succeed (a user access
     would be #PF, then #DF and a triple fault); with CR0.AM, EFLAGS.AC and a misaligned ring-0 ESP
     they raise no #AC (alignment checking applies at CPL 3 only).
   test_review_model (MODEL-ONLY, TCG has no VME): the same supervisor-stack check with CR4.VME = 1
   (INT n through the IDT with the IRB bit set; #GP from INT n with IOPL < 3; a redirected INT n,
   which pushes on the virtual-8086 stack as user accesses). */
#include "sys.h"

#define RV_CS 0x0800      /* virtual-8086 code copied to linear 8000h */
#define TSS_RV 0xD8       /* scratch TSS descriptor (TSS_SSR of t_sysb.c, saved and restored) */

__asm__(
	".code16\n.globl rv86_base\nrv86_base:\n"
	"rv86_int: int $0x41\n hlt\n"
	"rv86_div: xorw %bx, %bx\n movw $1, %ax\n xorw %dx, %dx\n divw %bx\n hlt\n"
	"rv86_int3: int3\n hlt\n"
	".globl rv86_end\nrv86_end:\n.code32\n"
	".globl rv_u41\nrv_u41: int $0x41\n"
	/* SMM handler (16-bit, at SMBASE + 8000h): INT 21h through a real-mode IVT at 6300h (IDTR image
	   at 6280h); the INT 21h handler counts at 6200h, a #GP counts at 6204h and leaves SMM */
	".code16\n.globl rv_smh\nrv_smh:\n"
	" movl $0x6200, %ebx\n movl $0x7000, %esp\n lidtl 0x6280\n int $0x21\n rsm\n"
	".globl rv_sm21\nrv_sm21: incl (%ebx)\n iretw\n"
	".globl rv_smgp\nrv_smgp: incl 4(%ebx)\n rsm\n"
	".globl rv_smh_end\nrv_smh_end:\n.code32\n");
extern char rv86_base[], rv86_end[], rv86_int[], rv86_div[], rv86_int3[], rv_u41[];
extern char rv_smh[], rv_sm21[], rv_smgp[], rv_smh_end[];

static struct frame rvf;
static int rv_hook(struct frame *f) { rvf = *f; return 0; }

static void rv_enter_v86(u32 ip, u32 eflags) {
	__asm__ volatile(
		"pushl $0\n pushl $0\n pushl $0x0900\n pushl $0x0900\n"   /* GS FS DS ES */
		"pushl $0x0700\n pushl $0xFFFE\n pushl %1\n pushl %2\n pushl %0\n iret"
		:: "r"(ip), "r"(eflags), "i"(RV_CS) : "memory");
}

static int rv_v86(char *code, u32 eflags) {
	memset(&rvf, 0, sizeof rvf);
	return TRY(rv_enter_v86(code - rv86_base, eflags));
}

static void rv_show(const char *name, int v) {
	kprintf("%s: vec=%x err=%x ip=%x cs=%x efl=%x sp=%x ss=%x ds=%x\n", name, v, rvf.err, rvf.eip,
	        rvf.cs & 0xFFFF, rvf.eflags, rvf.uesp, rvf.uss & 0xFFFF, rvf.v86ds & 0xFFFF);
}

/* A TSS with room for an interrupt-redirection bitmap and an I/O map */
static struct { struct tss32 t; u8 irb[32]; u8 io[8]; } __attribute__((packed, aligned(128))) rvtss;
static u8 rv_r0[2048] __attribute__((aligned(16)));
static u64 rv_old;

/* Load TR with the scratch TSS: access byte `acc` (0x89 32-bit, 0x81 16-bit), limit, I/O map base */
static void rv_tr(u32 acc, u32 limit, u16 iomap) {
	memset(&rvtss, 0, sizeof rvtss);
	rvtss.t.ss0 = KDATA; rvtss.t.esp0 = (u32)rv_r0 + sizeof rv_r0; rvtss.t.iomap = iomap;
	memset(rvtss.io, 0xFF, sizeof rvtss.io);
	if (acc == 0x81) {   /* 16-bit TSS: SP0 at 2, SS0 at 4 (the stack is not used by these cases) */
		u16 *t16 = (u16 *)&rvtss;
		t16[1] = (u16)(u32)(rv_r0 + sizeof rv_r0); t16[2] = KDATA;
	}
	rv_old = gdt[TSS_RV >> 3];
	gdt[TSS_RV >> 3] = seg_desc((u32)&rvtss, limit, acc, 0);
	ltr(TSS_RV);
}
static void rv_tr_restore(void) {
	reload_tr(TSS_MAIN);
	gdt[TSS_RV >> 3] = rv_old;
}

static void pci_w8(u32 dev, u32 reg, u8 v) { outl(0xCF8, 0x80000000 | dev | (reg & 0xFC)); outb(0xCFC + (reg & 3), v); }

/* INT 21h in real mode (inside SMM) with the current TR */
static void rv_int_real(const char *name) {
	volatile u32 *r = (volatile u32 *)0x6200;
	r[0] = 0; r[1] = 0;
	__asm__ volatile("outb %%al, $0xb2" ::: "eax", "memory");
	kprintf("%s: int21=%d gp=%d\n", name, r[0], r[1]);
}

static char rv_name[48];
static const char *rv_cat(const char *a, const char *b) {
	int k = 0;
	for (; *a; ) rv_name[k++] = *a++;
	for (; *b; ) rv_name[k++] = *b++;
	rv_name[k] = 0;
	return rv_name;
}

/* INT n at CPL 0, at CPL 3 (to ring 0 through the DPL-3 gate 41h) and in real mode */
static void rv_int_cases(const char *tag) {
	report(rv_cat(tag, ".pm0"), TRY(__asm__ volatile("int $0x20" ::: "memory")));
	report(rv_cat(tag, ".pm3"), run_user(rv_u41, 0, 0));
	rv_int_real(rv_cat(tag, ".real"));
}

void test_review(void) {
	/* ---- INT n and the interrupt-redirection bitmap ---- */
	pci_w8(0x0000, 0x72, 0x4A);                         /* i440FX: open SMRAM (as t_smm.c) */
	memcpy((void *)0xA8000, rv_smh, rv_smh_end - rv_smh);
	pci_w8(0x0000, 0x72, 0x0A);
	*(volatile u16 *)0x6280 = 0x3FF; *(volatile u32 *)0x6282 = 0x6300;
	*(volatile u16 *)(0x6300 + 4 * 0x21) = (u16)(0x8000 + (rv_sm21 - rv_smh)); *(volatile u16 *)(0x6302 + 4 * 0x21) = 0xA000;
	*(volatile u16 *)(0x6300 + 4 * 0x0D) = (u16)(0x8000 + (rv_smgp - rv_smh)); *(volatile u16 *)(0x6302 + 4 * 0x0D) = 0xA000;
	rv_int_real("rv.int.real.main");
	/* 32-bit TSS with the limit of a 16-bit TSS (the IRB pointer at 66h is beyond it) */
	rv_tr(0x89, 0x2B, 0);
	rv_int_cases("rv.int.lim2b");
	rv_tr_restore();
	/* 16-bit TSS (limit 2Bh) */
	rv_tr(0x81, 0x2B, 0);
	report("rv.int.tss16.pm0", TRY(__asm__ volatile("int $0x20" ::: "memory")));
	rv_int_real("rv.int.tss16.real");
	rv_tr_restore();
	/* 32-bit TSS, I/O map base beyond the limit */
	rv_tr(0x89, 0x67, 0x1000);
	rv_int_cases("rv.int.iomap");
	rv_tr_restore();

	/* virtual-8086 mode without VME (CR4 = 0), IOPL 3: INT n goes through the IDT */
	memcpy((void *)0x8000, rv86_base, rv86_end - rv86_base);
	trap_hook = rv_hook;
	rv_tr(0x89, 0x2B, 0);
	rv_show("rv.int.lim2b.v86", rv_v86(rv86_int, 0x23002));
	rv_tr_restore();
	rv_tr(0x89, 0x67, 0x1000);
	rv_show("rv.int.iomap.v86", rv_v86(rv86_int, 0x23002));
	rv_show("rv.int.iomap.v86.iopl0", rv_v86(rv86_int, 0x20002));
	rv_tr_restore();

	/* ---- virtual-8086 mode under paging with a supervisor-only ring-0 stack ---- */
	u32 *pd = page_alloc(1);
	for (u32 t = 0; t < 16; t++) {
		u32 *pt = page_alloc(1);
		for (u32 k = 0; k < 1024; k++) pt[k] = ((t << 22) + (k << 12)) | 7;
		pd[t] = (u32)pt | 7;
	}
	u8 *sstk = page_alloc(1);
	u32 *spte = &((u32 *)(pd[(u32)sstk >> 22] & ~0xFFF))[((u32)sstk >> 12) & 0x3FF];
	*spte = (u32)sstk | 3;                          /* supervisor, writable */
	u32 esp0 = tss_main.esp0;
	tss_main.esp0 = (u32)sstk + 4096;
	WRCR(3, (u32)pd);
	WRCR(0, RDCR(0) | 0x80000000);
	rv_show("rv.v86pg.int", rv_v86(rv86_int, 0x23002));
	rv_show("rv.v86pg.int.iopl0", rv_v86(rv86_int, 0x20002));
	rv_show("rv.v86pg.div", rv_v86(rv86_div, 0x23002));
	rv_show("rv.v86pg.int3", rv_v86(rv86_int3, 0x20002));
	report("rv.v86pg.pm3", run_user(rv_u41, 0, 0));
	/* CR0.AM, EFLAGS.AC and a misaligned ring-0 stack: the pushes are not alignment-checked */
	tss_main.esp0 = (u32)sstk + 4096 - 2;
	WRCR(0, RDCR(0) | 0x40000);
	rv_show("rv.v86pg.ac", rv_v86(rv86_int, 0x63002));
	WRCR(0, RDCR(0) & ~0x40000);
	tss_main.esp0 = (u32)sstk + 4096;
	WRCR(0, RDCR(0) & ~0x80000000);
	tss_main.esp0 = esp0;
	trap_hook = 0;
}

/* MODEL-ONLY: the same with CR4.VME = 1 */
void test_review_model(void) {
	memcpy((void *)0x8000, rv86_base, rv86_end - rv86_base);
	/* IVT entry 41h = 0900:0041h, a HLT there (linear 9041h) */
	u32 z = 0;
	__asm__ volatile("" : "+r"(z));
	volatile u16 *ivt = (volatile u16 *)z;
	u16 ivt41[2] = { ivt[0x82], ivt[0x83] };
	ivt[0x82] = 0x41; ivt[0x83] = 0x0900;
	*(volatile u8 *)0x9041 = 0xF4;
	u32 *pd = page_alloc(1);
	for (u32 t = 0; t < 16; t++) {
		u32 *pt = page_alloc(1);
		for (u32 k = 0; k < 1024; k++) pt[k] = ((t << 22) + (k << 12)) | 7;
		pd[t] = (u32)pt | 7;
	}
	u8 *sstk = page_alloc(1);
	((u32 *)(pd[(u32)sstk >> 22] & ~0xFFF))[((u32)sstk >> 12) & 0x3FF] = (u32)sstk | 3;
	rv_tr(0x89, 0x88, 0x88);
	rvtss.t.esp0 = (u32)sstk + 4096;
	memset(rvtss.irb, 0xFF, sizeof rvtss.irb);      /* every vector through the IDT */
	trap_hook = rv_hook;
	WRCR(3, (u32)pd);
	WRCR(4, RDCR(4) | 1);
	WRCR(0, RDCR(0) | 0x80000000);
	rv_show("rv.vme.pg.int", rv_v86(rv86_int, 0x23002));
	rv_show("rv.vme.pg.int.iopl0", rv_v86(rv86_int, 0x20002));
	rv_show("rv.vme.pg.div", rv_v86(rv86_div, 0x20002));
	rvtss.irb[0x41 >> 3] &= ~(1 << (0x41 & 7));      /* 41h redirected to the 8086 handler */
	rv_show("rv.vme.pg.redir", rv_v86(rv86_int, 0x20002));
	WRCR(0, RDCR(0) & ~0x80000000);
	WRCR(4, RDCR(4) & ~1);
	trap_hook = 0;
	rv_tr_restore();
	ivt[0x82] = ivt41[0]; ivt[0x83] = ivt41[1];
}
