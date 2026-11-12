/* System workstream B: exception classes and double faults (compared with QEMU), NMI and IRPerf
   (model-only).

   dfc.*: every pair (class of the event being delivered, class of a fault raised while delivering it)
   that can be provoked. The first event is an exception of each class raised in ring 0 or ring 3, a
   software interrupt or an external interrupt (an APIC self-IPI); the second is a contributory fault
   of the IDT gate (#NP: not present, #GP: bad gate type, #TS: task gate to a TSS with a short limit)
   or of the ring-0 stack of a ring-3 event (#TS: bad SS0, #SS: SS0 not present, #PF: ESP0 on a
   not-present page). AMD APM vol. 2, 8.2.9: contributory + contributory and page fault + contributory
   or page fault give #DF (error code 0); everything else is handled serially (the second exception is
   delivered). The EXT bit of the second exception's error code is set when the first event is an
   exception or an external interrupt, clear for INT n / INT3 (SDM vol. 3, 6.13).
   #DF, and #TS, #SS and #PF when they cannot use the ring-0 stack, are taken through task gates to
   recording tasks that resume the kernel. */
#include "smp.h"

#define TSS_DFR 0xC8      /* recording tasks: #DF, #TS, #SS, #PF */
#define TSS_TSR 0xD0
#define TSS_SSR 0xD8
#define TSS_PFR 0xE0
#define TSS_BAD 0xE8      /* 32-bit TSS descriptor with limit 0x60 (< 0x67): #TS */
#define SEG_NP 0xF8       /* writable data, DPL 0, not present */
#define APIC ((volatile u32 *)0xFEE00000)
#define AR(off) APIC[(off) >> 2]

static struct tss32 rt[4] __attribute__((aligned(128)));
static struct tss32 tbad __attribute__((aligned(128)));
static u8 rstk[4][1024] __attribute__((aligned(16)));
static u8 recstk[2048] __attribute__((aligned(16)));
static u8 ustk[4096] __attribute__((aligned(4096)));
volatile u32 dfc_vec, dfc_err, dfc_cr2;
static u32 *dfc_pd;
u32 dfc_hole;

/* recording task: pop the error code, record, make the kernel resume at dfc_recover, IRET (NT) */
#define REC(v) ".globl dfc_t" #v "\ndfc_t" #v ": popl dfc_err\n movl $" #v ", dfc_vec\n call dfc_fix\n iret\n jmp dfc_t" #v "\n"
__asm__(REC(8) REC(10) REC(12) REC(14)
	/* ring-0 sources */
	".globl dfc_de\ndfc_de: xorl %ecx, %ecx\n divl %ecx\n ret\n"
	".globl dfc_ud\ndfc_ud: ud2\n ret\n"
	".globl dfc_gp\ndfc_gp: movl $0x2B, %eax\n movl %eax, %ds\n ret\n"
	".globl dfc_np\ndfc_np: movl $0xF8, %eax\n movl %eax, %fs\n ret\n"
	".globl dfc_ss\ndfc_ss: movl $0xF8, %eax\n movl %eax, %ss\n ret\n"
	".globl dfc_ts\ndfc_ts: ljmp $0xE8, $0\n ret\n"
	".globl dfc_pf\ndfc_pf: movl dfc_hole, %eax\n movl (%eax), %eax\n ret\n"
	".globl dfc_br\ndfc_br: movl $5, %eax\n .byte 0x62, 0x05\n .long dfc_bounds\n ret\n"   /* BOUND EAX, dfc_bounds */
	".globl dfc_nm\ndfc_nm: .byte 0xD9, 0xD0\n ret\n"     /* FNOP with CR0.TS = 1 */
	".globl dfc_db\ndfc_db: pushfl\n orl $0x100, (%esp)\n popfl\n nop\n ret\n"
	".globl dfc_int3\ndfc_int3: int3\n ret\n"
	".globl dfc_intn\ndfc_intn: int $0x41\n ret\n"
	".globl dfc_intr\ndfc_intr: sti\n nop\n nop\n cli\n ret\n"
	/* ring-3 sources (end with INT 0x40 if they complete) */
	".globl dfc_u_ud\ndfc_u_ud: ud2\n"
	".globl dfc_u_gp\ndfc_u_gp: cli\n int $0x40\n"
	".globl dfc_u_de\ndfc_u_de: xorl %ecx, %ecx\n divl %ecx\n int $0x40\n"
	".globl dfc_u_pf\ndfc_u_pf: movl dfc_hole, %eax\n movl 0x2000(%eax), %eax\n int $0x40\n"
	".globl dfc_u_int\ndfc_u_int: int $0x41\n int $0x40\n"
	".globl dfc_u_intr\ndfc_u_intr: nop\n nop\n int $0x40\n");
extern char dfc_t8[], dfc_t10[], dfc_t12[], dfc_t14[], dfc_de[], dfc_ud[], dfc_gp[], dfc_np[], dfc_ss[],
	dfc_ts[], dfc_pf[], dfc_br[], dfc_nm[], dfc_db[], dfc_int3[], dfc_intn[], dfc_intr[], dfc_u_ud[],
	dfc_u_gp[], dfc_u_de[], dfc_u_pf[], dfc_u_int[], dfc_u_intr[];
u32 dfc_bounds[2] = { 0, 1 };

static void dfc_recover(void) {
	last.vec = dfc_vec; last.err = dfc_err; last.cr2 = dfc_cr2;
	fault_armed = 0;
	klongjmp(&fault_jb, 1);
}

/* runs in a recording task: the interrupted kernel (or ring-3 code) resumes in dfc_recover */
void dfc_fix(void) {
	dfc_cr2 = RDCR(2);
	tss_main.eip = (u32)dfc_recover; tss_main.eflags = 2;
	tss_main.cs = KCODE; tss_main.ss = tss_main.ds = tss_main.es = tss_main.fs = tss_main.gs = KDATA;
	tss_main.esp = (u32)recstk + sizeof recstk;
	tss_main.cr3 = RDCR(3);
}

static void mkrec(struct tss32 *t, char *eip, u8 *stk) {
	memset(t, 0, sizeof *t);
	t->cr3 = RDCR(3); t->eip = (u32)eip; t->eflags = 2;
	t->esp = (u32)stk + 1024;
	t->cs = KCODE; t->ss = t->ds = t->es = t->fs = t->gs = KDATA;
	t->iomap = sizeof *t;
}

static void tgate(int vec, u16 sel) { idt[vec] = gate_desc(sel, 0, 0x85); }

static void enter3(char *code, u32 eflags) {
	__asm__ volatile(
		"movl %0, %%ecx\n movl %%ecx, %%ds\n movl %%ecx, %%es\n movl %%ecx, %%fs\n movl %%ecx, %%gs\n"
		"pushl %0\n pushl %1\n pushl %2\n pushl %3\n pushl %4\n iret"
		:: "i"(UDATA), "r"((u32)ustk + sizeof ustk), "r"(eflags), "i"(UCODE), "r"((u32)code)
		: "ecx", "memory");
}

static void show(const char *name, int v) {
	kprintf("dfc.%s: vec=%x err=%x", name, v, last.err);
	if (v == 14) kprintf(" cr2=%x", last.cr2 - dfc_hole);
	kputc('\n');
}

static void call0(char *f) { ((void (*)(void))f)(); }

/* IDT entry of `vec`: 0 not present, 1 bad type (present, type 0), 2 task gate to the short TSS */
static void spoil(int vec, int how) {
	if (how == 0) idt[vec] &= ~((u64)0x80 << 40);
	else if (how == 1) idt[vec] = (idt[vec] & ~((u64)0x1F << 40)) | ((u64)0x00 << 40);
	else tgate(vec, TSS_BAD);
}

static const char *const how_name[3] = { "np", "gp", "ts" };

static void ring0(const char *name, char *f, int vec, int how) {
	u64 saved = idt[vec];
	spoil(vec, how);
	char buf[40]; int n = 0;
	for (const char *p = name; *p; p++) buf[n++] = *p;
	buf[n++] = '.';
	for (const char *p = how_name[how]; *p; p++) buf[n++] = *p;
	buf[n] = 0;
	if (f == dfc_nm) WRCR(0, RDCR(0) | 8);
	int v = TRY(call0(f));
	idt[vec] = saved;
	__asm__ volatile("clts");
	show(buf, v);
	reload_tr(TSS_MAIN);
}

/* ring-3 source with a broken ring-0 stack: 0 SS0 not present, 1 SS0 with RPL 1, 2 ESP0 on a
   not-present page */
static const char *const stk_name[3] = { "ss", "ts", "pf" };
static void ring3(const char *name, char *code, int stk, u32 eflags) {
	u32 ss0 = tss_main.ss0, esp0 = tss_main.esp0;
	if (stk == 0) tss_main.ss0 = SEG_NP;
	else if (stk == 1) tss_main.ss0 = KDATA | 1;
	else tss_main.esp0 = dfc_hole + 0x1000;
	char buf[40]; int n = 0;
	for (const char *p = name; *p; p++) buf[n++] = *p;
	buf[n++] = '.';
	for (const char *p = stk_name[stk]; *p; p++) buf[n++] = *p;
	buf[n] = 0;
	int v = TRY(enter3(code, eflags));
	tss_main.ss0 = ss0; tss_main.esp0 = esp0;
	show(buf, v);
	reload_tr(TSS_MAIN);
	__asm__ volatile("movl %0, %%ds\n movl %0, %%es\n movl %0, %%fs\n movl %0, %%gs" :: "r"((u32)KDATA));
}

static void ipi_self(u32 vec) { AR(0x310) = 0; AR(0x300) = 0x40000 | vec; }

void test_sysb(void) {
	/* paging: 4 MiB identity pages (user accessible) except the 4 MiB region of the hole page, which
	   has a page table; the hole and the page 2 pages above it are not present */
	dfc_pd = page_alloc(1);
	u32 *pt = page_alloc(1);
	dfc_hole = (u32)page_alloc(4);
	for (u32 i = 0; i < 1024; i++) dfc_pd[i] = (i << 22) | 0x87;
	u32 base = dfc_hole & ~0x3FFFFF;
	for (u32 i = 0; i < 1024; i++) pt[i] = (base + (i << 12)) | 7;
	pt[(dfc_hole >> 12) & 0x3FF] = 0;
	pt[((dfc_hole >> 12) + 2) & 0x3FF] = 0;
	dfc_pd[dfc_hole >> 22] = (u32)pt | 7;
	WRCR(4, RDCR(4) | 0x10);
	WRCR(3, (u32)dfc_pd);
	WRCR(0, RDCR(0) | 0x80000000);

	char *rec[4] = { dfc_t8, dfc_t10, dfc_t12, dfc_t14 };
	for (int k = 0; k < 4; k++) {
		mkrec(&rt[k], rec[k], rstk[k]);
		gdt[(TSS_DFR >> 3) + k] = seg_desc((u32)&rt[k], 0x67, 0x89, 0);
	}
	memset(&tbad, 0, sizeof tbad);
	gdt[TSS_BAD >> 3] = seg_desc((u32)&tbad, 0x60, 0x89, 0);
	gdt[SEG_NP >> 3] = seg_desc(0, 0xFFFFF, 0x12, 0xC);   /* P = 0 */
	u64 idt8 = idt[8];
	tgate(8, TSS_DFR);

	/* APIC on, for the external-interrupt sources */
	AR(0xF0) = 0x1FF; AR(0x80) = 0;

	/* ring 0: the first event's gate is broken */
	for (int how = 0; how < 3; how++) {
		ring0("de", dfc_de, 0, how);
		ring0("ud", dfc_ud, 6, how);
		ring0("gp", dfc_gp, 13, how);
		ring0("np", dfc_np, 11, how);
		ring0("ss", dfc_ss, 12, how);
		ring0("ts", dfc_ts, 10, how);
		ring0("pf", dfc_pf, 14, how);
		ring0("br", dfc_br, 5, how);
		ring0("nm", dfc_nm, 7, how);
		ring0("db", dfc_db, 1, how);
		ring0("int3", dfc_int3, 3, how);
		ring0("intn", dfc_intn, 0x41, how);
		ipi_self(0x60);
		ring0("intr", dfc_intr, 0x60, how);
		AR(0xB0) = 0;
	}

	/* ring 3: the ring-0 stack is broken; #TS, #SS and #PF use recording tasks */
	u64 i10 = idt[10], i12 = idt[12], i14 = idt[14];
	tgate(10, TSS_TSR); tgate(12, TSS_SSR); tgate(14, TSS_PFR);
	for (int stk = 0; stk < 3; stk++) {
		ring3("ud", dfc_u_ud, stk, 2);
		ring3("gp", dfc_u_gp, stk, 2);
		ring3("de", dfc_u_de, stk, 2);
		idt[14] = i14;   /* the first #PF through its interrupt gate: it needs the ring-0 stack */
		ring3("pf", dfc_u_pf, stk, 2);
		tgate(14, TSS_PFR);
		ring3("intn", dfc_u_int, stk, 2);
		ipi_self(0x61);
		ring3("intr", dfc_u_intr, stk, 0x202);
		AR(0xB0) = 0;
	}
	idt[10] = i10; idt[12] = i12; idt[14] = i14;
	idt[8] = idt8;

	WRCR(0, RDCR(0) & ~0x80000000);
	WRCR(4, RDCR(4) & ~0x10);
	for (int k = 0; k < 4; k++) gdt[(TSS_DFR >> 3) + k] = 0;
	gdt[TSS_BAD >> 3] = 0; gdt[SEG_NP >> 3] = 0;
	__asm__ volatile("clts");
}

/* ---------------------------------------------------------------------------------------------
   NMI: latch, blocking until IRET, HLT, SMM, gates, priority.

   QEMU-compared (`nmiq.*`): the NMIs come from the local APIC, as on hardware: a self-IPI with
   delivery mode NMI (ICR 400h to the own APIC ID) and an I/O APIC entry in NMI mode on the PIT's pin.
   TCG may take an interrupt request a few instructions after the APIC write, so these lines print
   counts, flags and orders, not the exact interrupted EIP (except where the CPU waits in HLT).

   Model-only (`nmi.*`): what the APIC cannot express. The model has a test hook, MSR 0x4E4D4931
   ("NMI1"), present only when the runner enables it (x86sys does): WRMSR with EAX = n latches an NMI
   that becomes deliverable after n more instruction boundaries, so that it can arrive at a chosen
   boundary (the MOV SS and STI shadows, an SMI at the same boundary); RDMSR returns bit 0 latched,
   bit 1 blocked. Without the hook the model-only tests print "nmi: no hook". */
#define NMI_MSR 0x4E4D4931
#define SMMS ((volatile u32 *)0x6000)   /* SMM handler results: 0 count, 1 NMIs taken in SMM, 2 mode */

static volatile u32 nmi_n, nmi_eip[8], nmi_efl[8], nmi_st[8], nmi_if[8], nmi_smm[8];
static volatile u32 seq[8], nseq, act, inner_n, inner_st, nested_n, gp_seen;
static volatile int use_hook;
static struct tss32 nmi_tss __attribute__((aligned(128)));
static u8 nmi_tstk[1024] __attribute__((aligned(16)));
volatile u32 nmi_task_n, nmi_task_st;

static u32 nst(void) { return use_hook ? (u32)rdmsr(NMI_MSR) : 0; }
/* an NMI now: the hook (model-only tests) or a self-IPI with delivery mode NMI */
static void nmi_send(void) {
	if (use_hook) wrmsr(NMI_MSR, 0);
	else { AR(0x310) = 0; AR(0x300) = 0x400; }
}
static void settle(void) { for (volatile int i = 0; i < 64; i++) {} }

static int nmi_hook(struct frame *f) {
	if (nseq < 8) seq[nseq++] = f->vec;
	if (f->vec == 0x41) return 1;                 /* plain IRET */
	if (f->vec == 0x62) { AR(0xB0) = 0; return 1; }
	if (f->vec != 2) return 0;
	u32 k = nmi_n++;
	if (k < 8) { nmi_eip[k] = f->eip; nmi_efl[k] = f->eflags; nmi_st[k] = nst(); nmi_if[k] = rdflags() & 0x200; nmi_smm[k] = SMMS[0]; }
	u32 a = act; act = 0;
	if (a == 1) {            /* another NMI while blocked: held until the IRET */
		nmi_send();
		settle();
		inner_n = nmi_n; inner_st = nst();
	} else if (a == 2) {     /* two more: the latch holds one */
		nmi_send(); settle(); nmi_send();
		settle();
		inner_n = nmi_n;
	} else if (a == 3) {     /* an IRET of another handler unblocks: the NMI nests here */
		nmi_send();
		settle();
		__asm__ volatile("int $0x41" ::: "memory");
		settle();
		nested_n = nmi_n;
	} else if (a == 4) {     /* a faulting IRET does not unblock (AMD APM vol. 2, 8.1.4) */
		nmi_send();
		settle();
		int v = TRY(__asm__ volatile("pushl $0\n pushl $0\n pushl $0\n iret" ::: "memory"));
		settle();
		gp_seen = v;
		nested_n = nmi_n;
	} else if (a == 5) {     /* an INTR and an NMI pending when the IRET sets IF again: NMI first */
		ipi_self(0x62);
		nmi_send();
		settle();
		inner_n = nmi_n;
	} else if (a == 6) {     /* an SMI while NMIs are blocked: RSM keeps them blocked */
		nmi_send();
		settle();
		__asm__ volatile("outb %%al, $0xb2" :: "a"(0) : "memory");
		settle();
		inner_n = nmi_n;
	}
	return 1;
}

static void reset_nmi(void) { nmi_n = 0; nseq = 0; act = 0; inner_n = inner_st = nested_n = gp_seen = 0; }

__asm__(
	".globl nmi_basic_go\nnmi_basic_go: movl $0x4E4D4931, %ecx\n xorl %eax, %eax\n xorl %edx, %edx\n wrmsr\n.globl nmi_l_basic\nnmi_l_basic: ret\n"
	".globl nmi_hlt_go\nnmi_hlt_go: cli\n hlt\n.globl nmi_l_hlt\nnmi_l_hlt: ret\n"
	".globl nmi_movss_go\nnmi_movss_go: pushl %ebx\n movl %ss, %ebx\n movl $0x4E4D4931, %ecx\n movl $1, %eax\n xorl %edx, %edx\n wrmsr\n movl %ebx, %ss\n"
	".globl nmi_l_movss1\nnmi_l_movss1: nop\n.globl nmi_l_movss2\nnmi_l_movss2: popl %ebx\n ret\n"
	".globl nmi_sti_go\nnmi_sti_go: movl $0x4E4D4931, %ecx\n movl $1, %eax\n xorl %edx, %edx\n wrmsr\n sti\n"
	".globl nmi_l_sti1\nnmi_l_sti1: nop\n.globl nmi_l_sti2\nnmi_l_sti2: cli\n ret\n"
	".globl nmi_smi_go\nnmi_smi_go: movl $0x4E4D4931, %ecx\n movl $1, %eax\n xorl %edx, %edx\n wrmsr\n outb %al, $0xb2\n.globl nmi_l_smi\nnmi_l_smi: ret\n"
	".globl smi_only_go\nsmi_only_go: outb %al, $0xb2\n.globl nmi_l_smi2\nnmi_l_smi2: ret\n"
	".globl nmi_task\nnmi_task: incl nmi_task_n\n iret\n jmp nmi_task\n"
	/* SMM handler (16-bit, at SMBASE + 8000h): count; mode 1: an NMI self-IPI (local APIC ICR, 32-bit
	   addresses); mode 2: the same, then load a real-mode IVT at 6100h (IDTR image at 6080h) and IRET to
	   itself, which unblocks NMIs in SMM: the NMI is taken in SMM through IVT[2] (smmb_nmi counts it) */
	".code16\n.globl smmb_h\nsmmb_h:\n"
	" movl $0x6000, %ebx\n incl (%ebx)\n movl $0x7000, %esp\n"
	" movl 8(%ebx), %eax\n testl %eax, %eax\n jz 2f\n"
	" movl $0xFEE00310, %ecx\n movl $0, (%ecx)\n movl $0xFEE00300, %ecx\n movl $0x400, (%ecx)\n"
	" movl $64, %ecx\n 3: loop 3b\n"
	" movl 8(%ebx), %eax\n cmpl $2, %eax\n jne 2f\n"
	" lidtl 0x6080\n pushfw\n pushw %cs\n pushw $(1f - smmb_h + 0x8000)\n iretw\n"
	"1: movl $64, %ecx\n 4: loop 4b\n"
	"2: rsm\n"
	".globl smmb_nmi\nsmmb_nmi: incl 4(%ebx)\n iretw\n"
	".globl smmb_end\nsmmb_end:\n.code32\n");
extern char nmi_l_basic[], nmi_l_hlt[], nmi_l_movss1[], nmi_l_movss2[], nmi_l_sti1[], nmi_l_sti2[],
	nmi_l_smi[], nmi_l_smi2[], nmi_task[], smmb_h[], smmb_nmi[], smmb_end[];
extern void nmi_basic_go(void), nmi_hlt_go(void), nmi_movss_go(void), nmi_sti_go(void),
	nmi_smi_go(void), smi_only_go(void);

static const char *where(u32 eip) {
	if (eip == (u32)nmi_l_basic) return "after_wrmsr";
	if (eip == (u32)nmi_l_hlt) return "after_hlt";
	if (eip == (u32)nmi_l_movss1) return "after_movss";
	if (eip == (u32)nmi_l_movss2) return "after_movss_next";
	if (eip == (u32)nmi_l_sti1) return "after_sti";
	if (eip == (u32)nmi_l_sti2) return "after_sti_next";
	if (eip == (u32)nmi_l_smi || eip == (u32)nmi_l_smi2) return "after_out";
	if (eip == (u32)isr_base + 16 * 13) return "gp_handler_entry";
	return "elsewhere";
}
/* model-only lines: where each NMI was taken and the hook's latch/blocked state in its handler */
static void showw(const char *what) {
	kprintf("%s: n=%d", what, nmi_n);
	for (u32 i = 0; i < nmi_n && i < 4; i++)
		kprintf(" [%s if=%x st=%x hif=%x smm=%d]", where(nmi_eip[i]), nmi_efl[i] & 0x200, nmi_st[i], nmi_if[i], nmi_smm[i]);
	kprintf(" after=%x\n", nst());
}
/* QEMU-compared lines: counts, the IF image and the handler's IF */
static void showq(const char *what) {
	kprintf("%s: n=%d", what, nmi_n);
	for (u32 i = 0; i < nmi_n && i < 4; i++) kprintf(" [if=%x hif=%x smm=%d]", nmi_efl[i] & 0x200, nmi_if[i], nmi_smm[i]);
	kputc('\n');
}

static void smm_setup(void) {
	/* QEMU: open SMRAM (i440FX D_OPEN) to install the handler, then close it (as t_smm.c); the model
	   has no chipset and ignores the configuration cycles */
	outl(0xCF8, 0x80000000 | 0x72); outb(0xCFE, 0x4A);
	memcpy((void *)0xA8000, smmb_h, smmb_end - smmb_h);
	outl(0xCF8, 0x80000000 | 0x72); outb(0xCFE, 0x0A);
	*(volatile u16 *)0x6080 = 0x3FF; *(volatile u32 *)0x6082 = 0x6100;
	*(volatile u16 *)0x6108 = (u16)(0x8000 + (smmb_nmi - smmb_h)); *(volatile u16 *)0x610A = 0xA000;
	SMMS[0] = 0; SMMS[1] = 0; SMMS[2] = 0;
}

/* QEMU-compared NMI tests (local APIC sources) */
void test_sysb_nmi(void) {
	use_hook = 0;
	trap_hook = nmi_hook;
	u64 idt2 = idt[2];
	AR(0xF0) = 0x1FF; AR(0x80) = 0;
	SMMS[0] = 0;

	reset_nmi(); nmi_send(); settle(); showq("nmiq.basic");
	reset_nmi(); __asm__ volatile("sti"); nmi_send(); settle(); __asm__ volatile("cli"); showq("nmiq.if1");
	reset_nmi(); act = 1; nmi_send(); settle();
	showq("nmiq.blocked"); kprintf("nmiq.blocked.inside: n=%d\n", inner_n);
	reset_nmi(); act = 2; nmi_send(); settle();
	showq("nmiq.latch_one"); kprintf("nmiq.latch_one.inside: n=%d\n", inner_n);
	reset_nmi(); act = 3; nmi_send(); settle();
	kprintf("nmiq.iret.other: n=%d nested=%d seq=%x,%x,%x,%x\n", nmi_n, nested_n, seq[0], seq[1], seq[2], seq[3]);
	reset_nmi(); act = 4; nmi_send(); settle();
	kprintf("nmiq.iret.fault: n=%d nested=%d gp=%x\n", nmi_n, nested_n, gp_seen);
	/* NMI and INTR both pending when the NMI handler's IRET sets IF again: the NMI first */
	reset_nmi(); act = 5; __asm__ volatile("sti"); nmi_send(); settle(); __asm__ volatile("cli");
	kprintf("nmiq.prio.intr: seq=%x,%x,%x n=%d inside=%d\n", seq[0], seq[1], seq[2], nmi_n, inner_n);
	/* HLT with IF = 0 is woken by an NMI from an I/O APIC entry in NMI mode (pin 2, the PIT) */
	ioapic_entry(2, 0x400, 0);
	reset_nmi(); pit_oneshot(500); nmi_hlt_go();
	ioapic_entry(2, 0x10000, 0);
	kprintf("nmiq.hlt: n=%d at=%s\n", nmi_n, where(nmi_eip[0]));
	/* trap gate: IF stays set in the handler */
	idt[2] = gate_desc(KCODE, (u32)isr_base + 16 * 2, 0x8F);
	reset_nmi(); __asm__ volatile("sti"); nmi_send(); settle(); __asm__ volatile("cli"); showq("nmiq.trapgate");
	idt[2] = idt2;
	/* task gate: the NMI handler is a task; its IRET (NT) unblocks */
	memset(&nmi_tss, 0, sizeof nmi_tss);
	nmi_tss.eip = (u32)nmi_task; nmi_tss.eflags = 2; nmi_tss.esp = (u32)nmi_tstk + sizeof nmi_tstk;
	nmi_tss.cs = KCODE; nmi_tss.ss = nmi_tss.ds = nmi_tss.es = nmi_tss.fs = nmi_tss.gs = KDATA;
	nmi_tss.iomap = sizeof nmi_tss;
	gdt[TSS_DFR >> 3] = seg_desc((u32)&nmi_tss, 0x67, 0x89, 0);
	idt[2] = gate_desc(TSS_DFR, 0, 0x85);
	reset_nmi(); nmi_task_n = 0;
	nmi_send(); settle(); nmi_send(); settle();
	__asm__ volatile("clts");
	kprintf("nmiq.taskgate: tasks=%d hook=%d\n", nmi_task_n, nmi_n);
	idt[2] = idt2; gdt[TSS_DFR >> 3] = 0;

	/* SMM (with CR4.OSFXSR, OSXMMEXCPT and OSXSAVE set: RSM must accept every CR4 bit MOV CR4 does) */
	smm_setup();
	u32 cr4 = RDCR(4);
	WRCR(4, cr4 | 0x40600);
	SMMS[0] = 0; SMMS[2] = 0;
	smi_only_go();
	kprintf("nmiq.smm.cr4: count=%d cr4=%x\n", SMMS[0], RDCR(4) & 0x40600);
	/* an NMI raised in SMM waits for RSM */
	SMMS[0] = 0; SMMS[1] = 0; SMMS[2] = 1;
	reset_nmi(); smi_only_go(); settle(); showq("nmiq.smi.latched"); kprintf("nmiq.smi.latched.smm: count=%d in_smm=%d\n", SMMS[0], SMMS[1]);
	/* an IRET in SMM unblocks NMIs: the NMI is taken in SMM */
	SMMS[0] = 0; SMMS[1] = 0; SMMS[2] = 2;
	reset_nmi(); smi_only_go(); settle(); showq("nmiq.smi.iret"); kprintf("nmiq.smi.iret.smm: count=%d in_smm=%d\n", SMMS[0], SMMS[1]);
	/* an SMI in an NMI handler: RSM restores the blocking, the second NMI waits for the handler's IRET */
	SMMS[0] = 0; SMMS[1] = 0; SMMS[2] = 0;
	reset_nmi(); act = 6; nmi_send(); settle();
	kprintf("nmiq.smi.restore: n=%d inside=%d smm=%d\n", nmi_n, inner_n, SMMS[0]);
	SMMS[2] = 0;
	WRCR(4, cr4);

	idt[2] = idt2;
	trap_hook = 0;
}

/* Model-only NMI tests (the test hook) */
static void test_nmi(void) {
	if (TRY(rdmsr(NMI_MSR)) != 0xFFFF) { kputs("nmi: no hook\n"); return; }
	use_hook = 1;
	trap_hook = nmi_hook;
	SMMS[0] = 0;

	reset_nmi(); nmi_basic_go(); showw("nmi.basic");
	reset_nmi(); act = 1; nmi_basic_go();
	showw("nmi.blocked"); kprintf("nmi.blocked.inside: n=%d st=%x\n", inner_n, inner_st);
	reset_nmi(); act = 4; nmi_basic_go();
	kprintf("nmi.iret.fault: n=%d nested=%d gp=%x second=%s\n", nmi_n, nested_n, gp_seen, where(nmi_eip[1]));
	reset_nmi(); nmi_movss_go(); showw("nmi.movss");
	reset_nmi(); nmi_sti_go(); showw("nmi.sti");
	/* an SMI and an NMI at the same boundary: the SMI first, the NMI after RSM */
	smm_setup();
	reset_nmi(); nmi_smi_go(); showw("nmi.smi.both"); kprintf("nmi.smi.both.smm: count=%d in_smm=%d\n", SMMS[0], SMMS[1]);
	use_hook = 0;
	trap_hook = 0;
}

/* IRPerf: instructions retired (MSR C000_00E9h with HWCR[30]) */
u8 irp_src[8192], irp_dst[8192];
volatile u32 irp_a, irp_cnt;
static u32 irp_straight(void) {
	u32 d;
	__asm__ volatile("movl $0xC00000E9, %%ecx\n rdmsr\n movl %%eax, %%esi\n nop\n nop\n nop\n nop\n nop\n rdmsr\n subl %%esi, %%eax"
	                 : "=a"(d) :: "ecx", "edx", "esi", "memory");
	return d;
}
static u32 irp_rep(u32 n) {
	u32 d;
	irp_cnt = n;
	__asm__ volatile("movl $0xC00000E9, %%ecx\n rdmsr\n movl %%eax, irp_a\n movl $irp_src, %%esi\n movl $irp_dst, %%edi\n movl irp_cnt, %%ecx\n cld\n"
	                 " rep movsb\n movl $0xC00000E9, %%ecx\n rdmsr\n subl irp_a, %%eax"
	                 : "=a"(d) :: "ecx", "edx", "esi", "edi", "memory");
	return d;
}
static u32 irp_write(u32 v) {
	u32 r;
	__asm__ volatile("movl $0xC00000E9, %%ecx\n xorl %%edx, %%edx\n wrmsr\n rdmsr" : "=a"(r) : "a"(v) : "ecx", "edx", "memory");
	return r;
}
static u32 irp_enable(u32 lo, u32 hi) {
	u32 r;
	__asm__ volatile("movl $0xC0010015, %%ecx\n wrmsr\n movl $0xC00000E9, %%ecx\n rdmsr" : "=a"(r) : "a"(lo), "d"(hi) : "ecx", "memory");
	return r;
}

static void test_irperf(void) {
	u32 r[4];
	cpuid(0x80000008, 0, r);
	u64 hw = rdmsr(0xC0010015);
	kprintf("irperf.cpuid: %d hwcr30=%d\n", (r[1] >> 1) & 1, (u32)(hw >> 30) & 1);
	wrmsr(0xC0010015, hw | (1ULL << 30));
	u32 s = irp_straight(), r64 = irp_rep(64), r5k = irp_rep(5000), r0 = irp_rep(0);
	kprintf("irperf.on: hwcr=%x straight=%d rep64=%d rep5000=%d rep0=%d\n", (u32)rdmsr(0xC0010015) & 0x40040000, s, r64, r5k, r0);
	kprintf("irperf.write: %d\n", irp_write(1000));
	wrmsr(0xC0010015, hw & ~(1ULL << 30));
	u64 a = rdmsr(0xC00000E9);
	__asm__ volatile("nop\n nop\n nop");
	u64 b = rdmsr(0xC00000E9);
	u32 so = irp_straight(), wo = irp_write(500);
	kprintf("irperf.off: frozen=%d straight=%d write=%d\n", a == b, so, wo);
	kprintf("irperf.enable: %d\n", irp_enable((u32)(hw | (1ULL << 30)), (u32)(hw >> 32)));
	wrmsr(0xC00000E9, ~0ULL);
	__asm__ volatile("nop");
	u64 w = rdmsr(0xC00000E9);
	kprintf("irperf.wrap: hi=%x small=%d\n", (u32)(w >> 32), w < 100);   /* 64-bit counter (OSRR 56255) wraps to 0 */
	wrmsr(0xC0010015, hw);
	/* MSR 8Bh: PATCH_LEVEL with the AMD identity, read-only (WRMSR #GP(0); theorems patchLevel_amd_wr,
	   coreMsr_patchLevel); the former Intel identity kept IA32_BIOS_SIGN_ID, which is writable */
	kprintf("msr8b.amd: wr=%x\n", TRY(wrmsr(0x8B, 0)));
	/* Intel's IA32_PLATFORM_ID, IA32_PMC0/1, IA32_PERFEVTSEL0/1 are not AMD MSRs (AMD APM vol. 2, appendix A):
	   #GP(0) with the AMD identity; DebugCtl (1D9h) exists */
	kprintf("msr.intel: 17=%x c1=%x c2=%x 186=%x 187=%x 1d9=%x\n", TRY((void)rdmsr(0x17)), TRY((void)rdmsr(0xC1)),
	        TRY((void)rdmsr(0xC2)), TRY((void)rdmsr(0x186)), TRY(wrmsr(0x187, 0)), TRY((void)rdmsr(0x1D9)));
}

void test_sysb_model(void) {
	test_nmi();
	test_irperf();
}
