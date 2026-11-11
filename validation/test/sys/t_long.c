/* Long mode (AMD APM vol. 2 ch. 4, 5, 8, 14): activation rules, compatibility-mode execution with
   4-level paging, and the transfers into 64-bit code.

   Runs only with the kernel command line "long=1" (test/sys/run.sh runs it as a second pass under
   qemu-system-x86_64, whose CPU has long mode; the main pass uses qemu-system-i386).

   Every interrupt and exception in long mode goes to a 64-bit handler, and far transfers, IRET, RETF
   and SYSCALL can enter 64-bit code. The 64-bit targets are tiny hand-assembled stubs (built at run
   time into `stubs`): each pushes an error-code placeholder (if the CPU pushed none) and an entry
   number, then the common part stores RAX, RBX, RCX, R11 and copies 7 quadwords from the stack (entry
   number, error code and the CPU's frame) into `lmrec`, and returns with IRETQ to the 32-bit
   compatibility-mode routine `lm_recover` (CS = KCODE, SS = KDATA, a stack of its own), which turns
   the record into `last` and longjmps back into the TRY that was running. On QEMU the stub really
   executes; the Lean model stops before the first 64-bit instruction (`Fault.unsupported "64-bit
   mode"`), and the test runner `x86sys` (validation/LongStub.lean) recognises the stub's exact bytes at
   RIP and applies their effect, so that both transcripts show the architectural state at the boundary
   (the frame the CPU pushed, RCX/R11 after SYSCALL, CR2) and continue. */
#include "sys.h"

#define EFER 0xC0000080
#define LME 0x100
#define LMA 0x400
#define NXE 0x800

/* GDT: the kernel's first 32 entries, then these */
#define NG 64
#define KC64 0x100      /* 64-bit code, DPL 0 */
#define UC64 0x108      /* 64-bit code, DPL 3 */
#define KC16 0x110      /* 16-bit code, DPL 0, based at code16 */
#define RSVDC 0x118     /* code with L = 1 and D = 1 (reserved in long mode) */
#define TSS64 0x120     /* 64-bit TSS (8-byte descriptor read in compatibility mode; next entry zero) */
#define CG3 0x130       /* 64-bit call gate, DPL 3, to KC64:stub(0xF1) */
#define CG0 0x140       /* 64-bit call gate, DPL 0, to KC64:stub(0xF2) */
#define CG16 0x150      /* 16-bit call gate (illegal in long mode) */
#define TGATE 0x158     /* task gate (illegal) */
#define TSS16 0x160     /* available 16-bit TSS (illegal in long mode) */
#define CGBAD 0x168     /* 64-bit call gate whose upper half has type bits set */
#define CG32T 0x178     /* 64-bit call gate to 32-bit code (KCODE) */
#define LDTD 0x188      /* LDT descriptor */
#define TSSEND 0x1F8    /* TSS descriptor in the last GDT entry: only 8 bytes within the limit */

static u64 lgdt_[NG] __attribute__((aligned(16)));
static u64 idt64[512] __attribute__((aligned(4096)));
static u8 stubs[8192] __attribute__((aligned(4096)));
static u32 stub_at[256];
static volatile u64 lmrec[11];
static u8 rstack[4096] __attribute__((aligned(16)));     /* lm_recover's stack */
static u8 kstack64[8192] __attribute__((aligned(4096))); /* RSP0 */
static u8 iststack[4096] __attribute__((aligned(4096))); /* IST1 */
static u32 tss64[26] __attribute__((aligned(128)));
static u64 ldt_[4] __attribute__((aligned(8)));
static u8 code16[64] __attribute__((aligned(16)));
static u64 *pml4, *pdpt, *pd0, *pdw, *ptw;
static u8 *data;                 /* 4 window pages */
static u32 big2m;                /* a 2 MiB aligned physical region */

struct dtr { u16 lim; u32 base; } __attribute__((packed));
static struct dtr old_gdt, old_idt;

static void show(const char *n, u64 e) { kprintf("%s: %x_%x\n", n, (u32)(e >> 32), (u32)e); }

/* ---- 64-bit stubs ---- */
static u8 *sp_;
static void b(u8 x) { *sp_++ = x; }
static void d32(u32 x) { b(x); b(x >> 8); b(x >> 16); b(x >> 24); }
extern char lm_recover_entry[];

static void build_stubs(void) {
	sp_ = stubs + 4096;                     /* the common part */
	u8 *common = sp_;
	b(0x48); b(0x89); b(0x04); b(0x25); d32((u32)&lmrec[9]);    /* mov [rec+72], rax */
	b(0x48); b(0x89); b(0x1C); b(0x25); d32((u32)&lmrec[10]);   /* mov [rec+80], rbx */
	b(0x48); b(0x89); b(0x0C); b(0x25); d32((u32)&lmrec[7]);    /* mov [rec+56], rcx */
	b(0x4C); b(0x89); b(0x1C); b(0x25); d32((u32)&lmrec[8]);    /* mov [rec+64], r11 */
	b(0x48); b(0x89); b(0xE6);                                  /* mov rsi, rsp */
	b(0xBF); d32((u32)&lmrec[0]);                               /* mov edi, rec */
	b(0xB9); d32(7);                                            /* mov ecx, 7 */
	b(0xF3); b(0x48); b(0xA5);                                  /* rep movsq */
	b(0x6A); b(KDATA);                                          /* push KDATA (SS) */
	b(0x68); d32((u32)rstack + sizeof rstack);                  /* push RSP */
	b(0x6A); b(0x02);                                           /* push 2 (RFLAGS) */
	b(0x6A); b(KCODE);                                          /* push KCODE */
	b(0x68); d32((u32)lm_recover_entry);                        /* push RIP */
	b(0x48); b(0xCF);                                           /* iretq */
	sp_ = stubs;
	for (u32 v = 0; v < 256; v++) {
		stub_at[v] = (u32)sp_;
		int err = v == 8 || (v >= 10 && v <= 14) || v == 17 || v == 21 || v == 29 || v == 30;
		if (!err) { b(0x6A); b(0x00); }                         /* push 0 */
		b(0x68); d32(v);                                        /* push v */
		b(0xE9); d32((u32)common - ((u32)sp_ + 4));             /* jmp common */
	}
}

/* lm_recover: entered by the stubs' IRETQ in compatibility mode at CPL 0 */
__asm__(".globl lm_recover_entry\nlm_recover_entry:\n movl $0x10, %eax\n movl %eax, %ds\n movl %eax, %es\n"
        " movl %eax, %fs\n movl %eax, %gs\n call lm_recover_c\n1: hlt\n jmp 1b\n");
void lm_recover_c(void) {
	last.vec = (u32)lmrec[0]; last.err = (u32)lmrec[1]; last.eip = (u32)lmrec[2]; last.cs = (u32)lmrec[3];
	last.eflags = (u32)lmrec[4]; last.esp = (u32)lmrec[5]; last.cr2 = RDCR(2); last.dr6 = 0;
	if (fault_armed) { fault_armed = 0; klongjmp(&fault_jb, 1); }
	kprintf("UNEXPECTED64 vec=%x err=%x rip=%x_%x cs=%x\n", (u32)lmrec[0], (u32)lmrec[1], (u32)(lmrec[2] >> 32),
	        (u32)lmrec[2], (u32)lmrec[3]);
	kputs("END\n");
	outl(0xF4, 0);
	for (;;) __asm__ volatile("cli; hlt");
}

/* The full record of the last 64-bit entry: entry number, error code, the five frame slots, RCX, R11 */
static void showrec(const char *n, int vec) {
	kprintf("%s: vec=%x", n, vec);
	if (vec == 0xFFFF) { kputc('\n'); return; }
	kprintf(" err=%x rip=%x_%x cs=%x fl=%x rsp=%x_%x ss=%x cr2=%x\n", (u32)lmrec[1], (u32)(lmrec[2] >> 32),
	        (u32)lmrec[2], (u32)lmrec[3], (u32)lmrec[4], (u32)(lmrec[5] >> 32), (u32)lmrec[5], (u32)lmrec[6],
	        RDCR(2));
}

/* ---- descriptors ---- */
static u64 gate64lo(u16 sel, u64 off, u32 access, u32 ist) {
	u32 lo = ((u32)off & 0xFFFF) | ((u32)sel << 16);
	u32 hi = ((u32)off & 0xFFFF0000) | (access << 8) | ist;
	return ((u64)hi << 32) | lo;
}
static void idt_set(int v, u16 sel, u64 off, u32 access, u32 ist) {
	idt64[2 * v] = gate64lo(sel, off, access, ist);
	idt64[2 * v + 1] = off >> 32;
}
static void gdt_gate(u16 sel, u16 tsel, u64 off, u32 access, u32 uptype) {
	lgdt_[sel >> 3] = gate64lo(tsel, off, access, 0);
	lgdt_[(sel >> 3) + 1] = (off >> 32) | ((u64)(uptype << 8) << 32);
}

static void build_tables(void) {
	for (int i = 0; i < 32; i++) lgdt_[i] = gdt[i];
	lgdt_[KC64 >> 3] = seg_desc(0, 0xFFFFF, 0x9A, 0xA);
	lgdt_[UC64 >> 3] = seg_desc(0, 0xFFFFF, 0xFA, 0xA);
	lgdt_[KC16 >> 3] = seg_desc((u32)code16, 0xFFFF, 0x9A, 0x0);
	lgdt_[RSVDC >> 3] = seg_desc(0, 0xFFFFF, 0x9A, 0xE);
	lgdt_[TSS64 >> 3] = seg_desc((u32)tss64, 0x67, 0x89, 0);
	lgdt_[(TSS64 >> 3) + 1] = 0;
	gdt_gate(CG3, KC64, stub_at[0xF1], 0xEC, 0);
	gdt_gate(CG0, KC64, stub_at[0xF2], 0x8C, 0);
	lgdt_[CG16 >> 3] = gate_desc(KCODE, stub_at[0xF3], 0x84);
	lgdt_[TGATE >> 3] = gate_desc(TSS_MAIN, 0, 0x85);
	lgdt_[TSS16 >> 3] = seg_desc((u32)tss64, 0x67, 0x81, 0);
	gdt_gate(CGBAD, KC64, stub_at[0xF4], 0x8C, 0x0C);
	gdt_gate(CG32T, KCODE, stub_at[0xF5], 0x8C, 0);
	lgdt_[LDTD >> 3] = seg_desc((u32)ldt_, sizeof ldt_ - 1, 0x82, 0);
	lgdt_[TSSEND >> 3] = seg_desc((u32)tss64, 0x67, 0x89, 0);
	ldt_[1] = seg_desc(0, 0xFFFFF, 0x92, 0xC);
	/* 64-bit TSS: RSP0 at +4, IST1 at +0x24, I/O map base beyond the limit */
	*(u64 *)((u8 *)tss64 + 4) = (u32)kstack64 + sizeof kstack64;
	*(u64 *)((u8 *)tss64 + 0x24) = (u32)iststack + sizeof iststack - 8;   /* misaligned: aligned by the CPU */
	*(u16 *)((u8 *)tss64 + 0x66) = 0x68;
	for (int v = 0; v < 256; v++)
		idt_set(v, KC64, stub_at[v], (v >= 0x40 && v < 0x50) || v == 0x55 ? 0xEE : 0x8E, 0);
	idt_set(0x50, KC64, stub_at[0x50], 0x8E, 1);               /* IST1 */
	idt64[2 * 0x51] = gate_desc(TSS_MAIN, 0, 0x85);            /* task gate */
	idt64[2 * 0x52] = gate_desc(KC64, stub_at[0x52], 0x86);    /* 16-bit interrupt gate */
	idt_set(0x53, KC64, stub_at[0x53], 0x0E, 0);               /* not present */
	idt_set(0x54, KCODE, stub_at[0x54], 0x8E, 0);              /* target is 32-bit code */
	idt_set(0x55, KC64, stub_at[0x55], 0xEF, 0);               /* trap gate, DPL 3 */
	idt_set(0x56, RSVDC, stub_at[0x56], 0x8E, 0);              /* target with L = D = 1 */
	idt_set(0x57, KC64, stub_at[0x57] | 0x0000800000000000ULL, 0x8E, 0);   /* non-canonical offset */
}

/* ---- paging ---- */
static void build_paging(void) {
	pml4 = page_alloc(1); pdpt = page_alloc(1); pd0 = page_alloc(1); pdw = page_alloc(1); ptw = page_alloc(1);
	data = page_alloc(4);
	u8 *bigarea = page_alloc(1024);
	big2m = ((u32)bigarea + 0x1FFFFF) & ~0x1FFFFF;
	for (u32 i = 0; i < 32; i++) pd0[i] = ((u64)i << 21) | 0x87;     /* identity 0..64 MiB, user, RW */
	pml4[0] = (u32)pdpt | 7;
	pdpt[0] = (u32)pd0 | 7;
	pdpt[1] = (u32)pdw | 7;                                         /* window at 0x40000000 */
	pdw[0] = (u32)ptw | 7;
	pdw[1] = big2m | 0x87;                                          /* 2 MiB page at 0x40200000 */
	pdw[2] = big2m | 0x87 | 0x2000;                                 /* reserved bit 13 */
	pdpt[2] = 0x87;                                                 /* 1 GiB page: 0x80000000 -> 0 */
	pdpt[3] = 0x87 | 0x40000000 | 0x2000;                           /* 1 GiB page, reserved bit 13 */
	ptw[0] = (u32)data | 3;
	ptw[1] = ((u32)data + 0x1000) | 1;
	ptw[2] = ((u32)data + 0x2000) | 7 | (1ULL << 55);               /* bits 62:52: available */
	ptw[3] = ((u32)data + 0x2000) | 7 | (1ULL << 49);               /* reserved (MAXPHYADDR 48) */
	ptw[4] = ((u32)data + 0x2000) | 7 | (1ULL << 40);               /* address bit 40 (7742) */
	ptw[5] = ((u32)data + 0x3000) | 7 | (1ULL << 63);               /* NX */
	ptw[6] = ((u32)data + 0x3000) | 7;                              /* user, executable */
	((u32 *)data)[0] = 0x600DF00D;
	((u32 *)data)[0x800] = 0xC0FFEE;
	data[0x3000] = 0xC3;                                            /* RET */
	*(u32 *)(big2m + 0x5000) = 0xB16B16;
}

static void lm_on(void) {
	WRCR(4, RDCR(4) | 0x20);
	WRCR(3, (u32)pml4);
	wrmsr(EFER, rdmsr(EFER) | LME | NXE);
	struct dtr id = { sizeof idt64 - 1, (u32)idt64 };
	__asm__ volatile("lidt %0" :: "m"(id));
	WRCR(0, RDCR(0) | 0x80000000);
	__asm__ volatile("jmp 1f\n1:");
}
static void lm_off(void) {
	WRCR(0, RDCR(0) & ~0x80000000);
	__asm__ volatile("lidt %0" :: "m"(old_idt));
	wrmsr(EFER, rdmsr(EFER) & ~(u64)(LME | NXE));
	WRCR(4, RDCR(4) & ~0x20);
}

/* far transfers to selector:offset */
static void ljmp(u16 sel, u32 off) {
	struct { u32 off; u16 sel; } __attribute__((packed)) p = { off, sel };
	__asm__ volatile("ljmp *%0" :: "m"(p) : "memory");
}
static void lcall(u16 sel, u32 off) {
	struct { u32 off; u16 sel; } __attribute__((packed)) p = { off, sel };
	__asm__ volatile("lcall *%0" :: "m"(p) : "memory");
}

static u32 lar(u16 sel, u32 *zf) {
	u32 v = 0xDEAD, f;
	__asm__ volatile("larl %2, %0\n pushfl\n popl %1" : "+r"(v), "=r"(f) : "r"((u32)sel) : "cc");
	*zf = (f >> 6) & 1;
	return v;
}
static u32 lsl(u16 sel, u32 *zf) {
	u32 v = 0xDEAD, f;
	__asm__ volatile("lsll %2, %0\n pushfl\n popl %1" : "+r"(v), "=r"(f) : "r"((u32)sel) : "cc");
	*zf = (f >> 6) & 1;
	return v;
}

static int msr_vec(u32 n, u64 v) { return TRY(wrmsr(n, v)); }

static void entries(const char *n) {
	kprintf("%s: pml4e=%x pdpe=%x pde=%x pte=%x\n", n, (u32)pml4[0] & 0x60, (u32)pdpt[1] & 0x60, (u32)pdw[0] & 0x60,
	        (u32)ptw[0] & 0x60);
}

/* 16-bit code for KC16 (offsets relative to code16): mov eax, imm32; far jmp back */
__asm__(".globl lm16_back\nlm16_back: ret\n");
extern char lm16_back[];


/* ---- 4-level paging fuzzer (lmf): t_pgfuzz.c's dimensions for long-mode paging ----
   Random PDPE (directory or 1 GiB page), PDEs (tables or 2 MiB pages) and PTEs for an 8-page window
   at W64 that crosses a PDE boundary, random harmless PML4E bits (A, PWT, PCD, AVL, bits 62:52; P,
   R/W, U/S stay set: the PML4E also maps the kernel), reserved bits (51:48 = above MAXPHYADDR 48;
   bit 63 without NXE; 2 MiB bits 20:13; 1 GiB bits 29:13), NX at every level, CR0.WP, EFER.NXE,
   CR4.PGE with G bits, and in half of the cases (with SMEP/SMAP) a supervisor-only identity map with
   CR4.SMEP/SMAP and EFLAGS.AC at random for ring-0 accesses (ring-3 accesses only otherwise).
   Physical-address bits 47:40 are not used: TCG has 40 (t_pae.c, lm.pg.maxphy40 check them). */
#define W64 0x43BFA000u           /* PDPT[1], PDE 29 (6 pages) and PDE 30 (2 pages) */
#define WOFF 0x3BFA000u           /* the window's offset in the 1 GiB page: physical with a 1 GiB leaf */
extern char lmf_r1[], lmf_r2[], lmf_w1[], lmf_w2[];
static u32 frs = 0x2545F491;
static u32 frnd(void) { frs ^= frs << 13; frs ^= frs >> 17; frs ^= frs << 5; return frs; }
static u64 *pdF, *ptA, *ptB;
static u32 fframes[8];
static u64 lmf_rsvd(int nxe) {
	if (frnd() % 24) return 0;
	if (!nxe && frnd() % 4 == 0) return 1ULL << 63;
	return 1ULL << (48 + frnd() % 4);
}
static u64 lmf_attr(void) {
	u32 r = frnd();
	u64 e = (r & 7) ? 1 : 0;
	if ((r >> 3) % 4) e |= 2;
	if ((r >> 5) % 4) e |= 4;
	e |= ((r >> 7) & 0xF) << 3;          /* PWT, PCD, A, D */
	e |= ((r >> 11) & 0xF) << 8;         /* G, AVL */
	if (frnd() % 8 == 0) e |= (u64)(frnd() & 0x7FF) << 52;   /* available bits 62:52 */
	return e;
}
static u64 lmf_nx(int nxe, int n) { return nxe && frnd() % n == 0 ? 1ULL << 63 : 0; }
static u64 lmf_dir(u64 *t, int nxe) { return (lmf_attr() & ~0x180ULL) | (u32)t | lmf_rsvd(nxe) | lmf_nx(nxe, 6); }
static u64 lmf_leaf4k(int nxe) {
	return lmf_attr() | (frnd() & 0x80) | fframes[frnd() % 8] | lmf_rsvd(nxe) | lmf_nx(nxe, 4);
}
/* physical address of `lin` in the window (ignoring permissions and reserved bits), ~0 if not present */
static u32 lmf_phys(u32 lin) {
	u64 e = pdpt[1];
	if (!(e & 1)) return ~0u;
	if (e & 0x80) return lin - 0x40000000;
	e = pdF[(lin >> 21) & 0x1FF];
	if (!(e & 1)) return ~0u;
	if (e & 0x80) return ((u32)e & 0xFFE00000) | (lin & 0x1FFFFF);
	e = ((u64 *)(u32)(e & 0xFFFFF000))[(lin >> 12) & 0x1FF];
	if (!(e & 1)) return ~0u;
	return ((u32)e & 0xFFFFF000) | (lin & 0xFFF);
}
static void show64(u64 e) { kprintf(" %x_%x", (u32)(e >> 32), (u32)e); }
static const char *const fkind[] = { "rd", "wr", "x" };

static void lm_fuzz(void) {
	u32 n = param("lmf", 300);
	frs = fuzz_seed(frs);
	pdF = page_alloc(1); ptA = page_alloc(1); ptB = page_alloc(1);
	for (int i = 0; i < 8; i++) {
		u32 *f = page_alloc(1);
		fframes[i] = (u32)f;
		for (int k = 0; k < 1024; k++) f[k] = 0x01010101u * (u32)(i * 16 + 1) + (u32)k * 0x04030201u;
	}
	for (u32 k = 0; k < 0x2000; k++) ((u32 *)WOFF)[k] = 0x3C000000u + k;       /* behind the 1 GiB page */
	for (u32 k = 0; k < 0x800; k++) ((u32 *)big2m)[k] = 0x2D000000u + k;
	int smx_ok = has_feature(7, 0, 1, 7) && has_feature(7, 0, 1, 20);
	u64 pml4e0 = pml4[0], pdpt1 = pdpt[1];
	u32 cr0 = RDCR(0) & ~0x10000u, cr4 = RDCR(4) & ~0x300080u;
	for (u32 c = 0; c < n; c++) {
		int nxe = frnd() % 2, wp = frnd() % 2, smx = smx_ok && frnd() % 2;
		int smep = smx && frnd() % 2, smap = smx && frnd() % 2, pge = frnd() % 2;
		wrmsr(EFER, LME | LMA | (nxe ? NXE : 0));
		WRCR(4, cr4);
		for (int i = 0; i < 512; i++) pdF[i] = ptA[i] = ptB[i] = 0;
		for (int i = 0; i < 32; i++) pd0[i] = ((u64)i << 21) | (smx ? 0x83 : 0x87);
		u64 e4 = pml4e0 | (lmf_attr() & 0x0E38ULL);                   /* PWT, PCD, A, AVL */
		u64 e3 = frnd() % 5 == 0 ? (lmf_attr() | 0x80 | (frnd() & 0x1000) | lmf_rsvd(nxe) | lmf_nx(nxe, 4) |
		                            (frnd() % 24 == 0 ? 1u << (13 + frnd() % 17) : 0))
		                         : lmf_dir(pdF, nxe);
		u64 eA = lmf_dir(ptA, nxe);
		u64 eB = frnd() % 3 == 0 ? (lmf_attr() | 0x80 | (frnd() & 0x1000) | big2m | lmf_rsvd(nxe) | lmf_nx(nxe, 4) |
		                            (frnd() % 24 == 0 ? 1u << (13 + frnd() % 8) : 0))
		                         : lmf_dir(ptB, nxe);
		for (u32 i = 0; i < 6; i++) ptA[0x1FA + i] = lmf_leaf4k(nxe);
		for (u32 i = 0; i < 2; i++) ptB[i] = lmf_leaf4k(nxe);
		pml4[0] = e4; pdpt[1] = e3; pdF[29] = eA; pdF[30] = eB;
		kprintf("lmf %d: wp=%d nxe=%d smx=%d smep=%d smap=%d pge=%d pml4e", c, wp, nxe, smx, smep, smap, pge);
		show64(e4); kputs(" pdpe"); show64(e3);
		if (!(e3 & 0x80)) {
			kputs(" pde"); show64(eA); show64(eB);
			kputs(" pte");
			for (u32 i = 0; i < 6; i++) show64(ptA[0x1FA + i]);
			if (!(eB & 0x80)) for (u32 i = 0; i < 2; i++) show64(ptB[i]);
		}
		kputc('\n');
		WRCR(4, cr4 | (smep ? 0x100000 : 0) | (smap ? 0x200000 : 0) | (pge ? 0x80 : 0));
		WRCR(3, (u32)pml4);
		WRCR(0, cr0 | (wp ? 0x10000 : 0));
		u32 na = 3 + frnd() % 6;
		int okany = 0;
		for (u32 a = 0; a < na; a++) {
			u32 kind = frnd() % 5;
			kind = kind < 2 ? 0 : kind < 4 ? 1 : 2;
			u32 size = kind == 2 ? 6 : (1u << (frnd() % 3));
			u32 user = !smx && frnd() % 2;
			u32 off = frnd() % 3 ? 0x1000 - 1 - frnd() % 8 : frnd() % 0x1000;
			u32 lin = W64 + (frnd() % 8) * 0x1000 + off;
			u32 v = frnd(), got = 0;
			int vec;
			int ac = !user && kind != 2 && frnd() % 2;
			if (kind == 2) {
				u8 code[6] = { 0xB8, (u8)v, (u8)(v >> 8), (u8)(v >> 16), (u8)(v >> 24), 0xC3 };
				for (u32 k = 0; k < 6; k++) { u32 p = lmf_phys(lin + k); if (p != ~0u) *(volatile u8 *)p = code[k]; }
				if (user) { vec = run_user(u_call, lin, 0); got = (u32)lmrec[9]; }
				else { u32 (*volatile fn)(void) = (u32 (*)(void))lin; vec = TRY(got = fn()); }
			} else if (kind == 0) {
				if (user) {
					vec = run_user(size == 4 ? u_read : size == 2 ? lmf_r2 : lmf_r1, lin, 0);
					got = (u32)lmrec[10];
				} else {
					if (ac) __asm__ volatile("stac");
					if (size == 1) vec = TRY(got = *(volatile u8 *)lin);
					else if (size == 2) vec = TRY(got = *(volatile u16 *)lin);
					else vec = TRY(got = *(volatile u32 *)lin);
					__asm__ volatile("clac");
				}
			} else {
				if (user) vec = run_user(size == 4 ? u_write : size == 2 ? lmf_w2 : lmf_w1, lin, v);
				else {
					if (ac) __asm__ volatile("stac");
					if (size == 1) vec = TRY(*(volatile u8 *)lin = (u8)v);
					else if (size == 2) vec = TRY(*(volatile u16 *)lin = (u16)v);
					else vec = TRY(*(volatile u32 *)lin = v);
					__asm__ volatile("clac");
				}
				for (u32 k = 0; k < size; k++) {
					u32 p = lmf_phys(lin + k);
					got |= (p == ~0u ? 0xEEu : *(volatile u8 *)p) << (8 * k);
				}
			}
			if (vec == 0x40) vec = 0xFFFF;
			if (vec == 0xFFFF) okany = 1;
			int pf = vec == 14;
			kprintf("lmf %d.%d: %s%d r%d%s %x vec=%x err=%x cr2=%x val=%x\n", c, a, fkind[kind], size, user ? 3 : 0,
			        ac ? "ac" : "", lin, vec, pf || vec == 13 ? last.err : 0, pf ? last.cr2 : 0, vec == 0xFFFF ? got : 0);
		}
		WRCR(0, cr0);
		WRCR(4, cr4);
		/* a large leaf with a reserved bit is marked 'r' (whether its A flag is set is unspecified) */
		u64 hi = 0x000F000000000000ULL | (nxe ? 0 : 1ULL << 63);
		int r3 = (e3 & 0x80) && (e3 & (hi | 0x3FFFE000)), rB = !(e3 & 0x80) && (eB & 0x80) && (eB & (hi | 0x1FE000));
		/* a 1 GiB leaf through which no access succeeded is marked 'p' (TCG sets its A flag on a fault) */
		if (r3 || ((e3 & 0x80) && !okany))   /* marker, 'a' if the A flag became set, then D */
			kprintf("lmf %d ad: %d%s%s%d", c, (int)(pml4[0] >> 5) & 3, r3 ? "r" : "p",
			        (pdpt[1] & ~e3 & 0x20) ? "a" : "-", (int)(pdpt[1] >> 6) & 1);
		else kprintf("lmf %d ad: %d%d", c, (int)(pml4[0] >> 5) & 3, (int)(pdpt[1] >> 5) & 3);
		if (!(e3 & 0x80)) {
			if (rB) kprintf(" %dr%s%d ", (int)(pdF[29] >> 5) & 3, (pdF[30] & ~eB & 0x20) ? "a" : "-", (int)(pdF[30] >> 6) & 1);
			else kprintf(" %d%d ", (int)(pdF[29] >> 5) & 3, (int)(pdF[30] >> 5) & 3);
			for (u32 i = 0; i < 6; i++) kputc('0' + ((ptA[0x1FA + i] >> 5) & 3));
			if (!(eB & 0x80)) for (u32 i = 0; i < 2; i++) kputc('0' + ((ptB[i] >> 5) & 3));
		}
		kputc('\n');
	}
	pml4[0] = pml4e0; pdpt[1] = pdpt1;
	for (int i = 0; i < 32; i++) pd0[i] = ((u64)i << 21) | 0x87;
	WRCR(3, (u32)pml4);
	wrmsr(EFER, LME | LMA | NXE);
}

__asm__(
	".globl lmf_r1\nlmf_r1: movzbl (%eax), %ebx\n int $0x40\n"
	".globl lmf_r2\nlmf_r2: movzwl (%eax), %ebx\n int $0x40\n"
	".globl lmf_w1\nlmf_w1: movb %bl, (%eax)\n int $0x40\n"
	".globl lmf_w2\nlmf_w2: movw %bx, (%eax)\n int $0x40\n");
void test_long(void) {
	__asm__ volatile("sgdt %0" : "=m"(old_gdt));
	__asm__ volatile("sidt %0" : "=m"(old_idt));
	build_stubs();
	build_tables();
	build_paging();
	struct dtr gd = { sizeof lgdt_ - 1, (u32)lgdt_ };
	__asm__ volatile("lgdt %0" :: "m"(gd));
	u32 r[4];

	/* CPUID: LM, Page1GB, NX, RDTSCP (8000_0001:EDX), LahfSahf (ECX), FSGSBASE (7:EBX) */
	cpuid(0x80000001, 0, r);
	kprintf("lm.cpuid: lm=%d page1gb=%d nx=%d lahf=%d fsgsbase=%d\n", (r[3] >> 29) & 1, (r[3] >> 26) & 1,
	        (r[3] >> 20) & 1, r[2] & 1, has_feature(7, 0, 1, 0));

	/* activation rules, from legacy mode (APM vol. 2, table 14-5) */
	report("lm.efer.lme", msr_vec(EFER, LME));
	kprintf("lm.efer: %x\n", (u32)rdmsr(EFER));
	WRCR(3, (u32)pml4);
	u32 cr0 = RDCR(0);
	int v = TRY(WRCR(0, cr0 | 0x80000000));               /* PAE = 0 */
	kprintf("lm.pg.nopae: vec=%x cr0=%x efer=%x\n", v, RDCR(0), (u32)rdmsr(EFER));
	WRCR(0, cr0);
	kprintf("lm.efer.lma.set: vec=%x\n", msr_vec(EFER, LME | LMA));   /* LMA differs from the processor's */
	kprintf("lm.efer2: %x\n", (u32)rdmsr(EFER));
	wrmsr(EFER, 0);

	/* activate */
	lm_on();
	kprintf("lm.active: efer=%x cr0=%x cr4=%x\n", (u32)rdmsr(EFER), RDCR(0), RDCR(4));
	entries("lm.ad.after_on");
	kprintf("lm.efer.lme.clear: vec=%x\n", msr_vec(EFER, LMA | NXE));    /* LME cannot change while PG = 1 */
	kprintf("lm.efer.lma.clear: vec=%x\n", msr_vec(EFER, LME | NXE));    /* LMA must be written as read */
	report("lm.efer.same", msr_vec(EFER, LME | LMA | NXE));
	kprintf("lm.efer3: %x\n", (u32)rdmsr(EFER));
	cpuid(0, 0, r);
	kprintf("lm.compat.cpuid: max=%x\n", r[0]);

	/* LTR in compatibility mode: 8-byte descriptors; a 16-bit TSS is illegal */
	report("lm.ltr.tss16", TRY(ltr(TSS16)));
	report("lm.ltr", TRY(ltr(TSS64)));
	kprintf("lm.ltr.end8: vec=%x\n", TRY(ltr(TSSEND)));    /* only 8 bytes within the GDT limit */
	u32 zf, x;
	x = lar(TSS16, &zf); kprintf("lm.lar.tss16: zf=%d\n", zf);
	x = lar(TGATE, &zf); kprintf("lm.lar.tgate: zf=%d\n", zf);
	x = lar(CG0, &zf); kprintf("lm.lar.cg64: zf=%d v=%x\n", zf, zf ? x : 0);
	x = lar(CGBAD, &zf); kprintf("lm.lar.cgbad: zf=%d\n", zf);
	x = lar(CG16, &zf); kprintf("lm.lar.cg16: zf=%d\n", zf);
	x = lsl(TSS64, &zf); kprintf("lm.lsl.tss64: zf=%d v=%x\n", zf, zf ? x : 0);
	x = lsl(TSS16, &zf); kprintf("lm.lsl.tss16: zf=%d\n", zf);
	report("lm.lldt", TRY(__asm__ volatile("lldt %0" :: "r"((u16)LDTD))));
	report("lm.ldt.load", TRY(__asm__ volatile("movl $0x0C, %%eax\n movl %%eax, %%fs\n movl $0x10, %%eax\n movl %%eax, %%fs" ::: "eax")));
	__asm__ volatile("lldt %0" :: "r"((u16)0));

	/* 4-level paging from compatibility mode */
	volatile u32 *L = (volatile u32 *)0x40000000;
	u32 val = 0;
	v = TRY(val = L[0]); kprintf("lm.pg.read: vec=%x val=%x\n", v, val);
	entries("lm.ad.read");
	report("lm.pg.write", TRY(L[1] = 5));
	entries("lm.ad.write");
	showrec("lm.pg.write.ro", TRY(L[0x400] = 1));
	v = TRY(val = L[0x800]); kprintf("lm.pg.avl55: vec=%x val=%x\n", v, val);
	showrec("lm.pg.rsvd49", TRY(val = L[0xC00]));
	kprintf("lm.pg.maxphy40: vec=%x\n", TRY(val = L[0x1000]));
	void (*volatile fn)(void) = (void (*)(void))0x40005000;
	showrec("lm.pg.nx.fetch", TRY(fn()));
	fn = (void (*)(void))0x40006000;
	report("lm.pg.x.fetch", TRY(fn()));
	pdw[0] |= 1ULL << 63; WRCR(3, (u32)pml4);
	showrec("lm.pg.nx.pde", TRY(fn()));
	pdw[0] &= ~(1ULL << 63); pdpt[1] |= 1ULL << 63; WRCR(3, (u32)pml4);
	showrec("lm.pg.nx.pdpe", TRY(fn()));
	pdpt[1] &= ~(1ULL << 63); WRCR(3, (u32)pml4);
	v = TRY(val = *(volatile u32 *)0x40205000); kprintf("lm.pg.2m: vec=%x val=%x\n", v, val);
	showrec("lm.pg.2m.rsvd13", TRY(val = *(volatile u32 *)0x40400000));
	v = TRY(val = *(volatile u32 *)(0x80000000 + (u32)data)); kprintf("lm.pg.1g: vec=%x val=%x\n", v, val);
	report("lm.pg.1g.write", TRY(*(volatile u32 *)(0x80000000 + (u32)data + 8) = 0x1234));
	kprintf("lm.pg.1g.pdpe: %x data2=%x\n", (u32)pdpt[2], ((u32 *)data)[2]);
	showrec("lm.pg.1g.rsvd13", TRY(val = *(volatile u32 *)0xC0000000));
	/* INVLPG of one address of a 1 GiB page drops every cached slice of it (APM vol. 2, 5.5.2) */
	pdpt[2] = 0;
	invlpg(0x80000000);
	showrec("lm.pg.1g.invlpg", TRY(val = *(volatile u32 *)(0x80000000 + (u32)data)));
	pdpt[2] = 0x87;
	pdpt[3] = 0;
	WRCR(3, (u32)pml4);
	showrec("lm.pg.pdpe.np", TRY(val = *(volatile u32 *)0xC0000000));
	pdpt[3] = (u32)pdw | 7 | (1ULL << 48); WRCR(3, (u32)pml4);
	showrec("lm.pg.pdpe.rsvd48", TRY(val = *(volatile u32 *)0xC0000000));
	pdpt[3] = 0; WRCR(3, (u32)pml4);
	/* U/S and R/W at the PDPE and PDE level, WP */
	pdpt[1] &= ~4ULL; WRCR(3, (u32)pml4);
	showrec("lm.pg.user.pdpe", run_user(u_read, 0x40000000, 0));
	pdpt[1] |= 4; pdw[0] &= ~2ULL; WRCR(3, (u32)pml4);
	report("lm.pg.super.write.nowp", TRY(L[2] = 7));
	WRCR(0, RDCR(0) | 0x10000);
	showrec("lm.pg.super.write.wp", TRY(L[3] = 7));
	WRCR(0, RDCR(0) & ~0x10000);
	pdw[0] |= 2; WRCR(3, (u32)pml4);
	/* SMEP and SMAP: the window is user at every level */
	if (has_feature(7, 0, 1, 7) && has_feature(7, 0, 1, 20)) {
		/* the identity map (kernel code, data, stacks, stubs, page tables) becomes supervisor-only */
		for (int i = 0; i < 32; i++) pd0[i] &= ~4ULL;
		WRCR(3, (u32)pml4);
		WRCR(4, RDCR(4) | 0x300000);
		showrec("lm.pg.smep", TRY(fn()));
		showrec("lm.pg.smap", TRY(val = L[0x1800]));              /* user page at every level */
		__asm__ volatile("stac");
		v = TRY(val = L[0x1800]); kprintf("lm.pg.smap.ac: vec=%x val=%x\n", v, val);
		__asm__ volatile("clac");
		ptw[6] &= ~4ULL; invlpg(0x40006000);
		report("lm.pg.smep.super", TRY(fn()));
		ptw[6] |= 4; invlpg(0x40006000);
		WRCR(4, RDCR(4) & ~0x300000);
		for (int i = 0; i < 32; i++) pd0[i] |= 4;
		WRCR(3, (u32)pml4);
	}
	/* NX without EFER.NXE is a reserved bit */
	wrmsr(EFER, LME | LMA);
	showrec("lm.pg.nx.nonxe", TRY(val = *(volatile u32 *)0x40005000));
	wrmsr(EFER, LME | LMA | NXE);

	/* interrupts and exceptions through the 64-bit IDT */
	showrec("lm.ud2", TRY(__asm__ volatile("ud2")));
	showrec("lm.int3", TRY(__asm__ volatile("int3")));
	showrec("lm.int40", TRY(__asm__ volatile("int $0x40")));
	showrec("lm.int.ist", TRY(__asm__ volatile("int $0x50")));
	showrec("lm.int.taskgate", TRY(__asm__ volatile("int $0x51")));
	showrec("lm.int.gate16", TRY(__asm__ volatile("int $0x52")));
	showrec("lm.int.np", TRY(__asm__ volatile("int $0x53")));
	showrec("lm.int.cs32", TRY(__asm__ volatile("int $0x54")));
	showrec("lm.int.trap", TRY(__asm__ volatile("sti\n int $0x55\n cli")));
	showrec("lm.int.cs.ld", TRY(__asm__ volatile("int $0x56")));
	showrec("lm.into", TRY(__asm__ volatile("movl $0x7FFFFFFF, %%eax\n addl $1, %%eax\n into" ::: "eax", "cc")));
	showrec("lm.div0", TRY(__asm__ volatile("xorl %%ecx, %%ecx\n divl %%ecx" ::: "eax", "edx", "ecx", "cc")));
	showrec("lm.user.int40", run_user(u_read, (u32)data, 0));
	kprintf("lm.user.int40.rbx: %x\n", (u32)lmrec[10]);
	showrec("lm.user.int3", run_user((char *)"\xCC", 0, 0));
	showrec("lm.user.gp", run_user((char *)"\xFA", 0, 0));          /* CLI at CPL 3 */
	showrec("lm.user.int.dpl0", run_user((char *)"\xCD\x41", 0, 0)); /* INT 0x41: gate DPL 3: ok */
	showrec("lm.user.int.dpl0b", run_user((char *)"\xCD\x30", 0, 0)); /* gate DPL 0: #GP */

	/* instructions that differ in long mode */
	showrec("lm.sysenter", TRY(__asm__ volatile(".byte 0x0F, 0x34")));
	showrec("lm.sysexit", TRY(__asm__ volatile(".byte 0x0F, 0x35")));
	showrec("lm.swapgs", TRY(__asm__ volatile(".byte 0x0F, 0x01, 0xF8")));
	showrec("lm.rdfsbase", TRY(__asm__ volatile(".byte 0xF3, 0x0F, 0xAE, 0xC0" ::: "eax")));
	WRCR(4, RDCR(4) | 0x10000);
	showrec("lm.rdfsbase.cr4", TRY(__asm__ volatile(".byte 0xF3, 0x0F, 0xAE, 0xC0" ::: "eax")));
	WRCR(4, RDCR(4) & ~0x10000);
	showrec("lm.iret.nt", TRY(__asm__ volatile("pushfl\n orl $0x4000, (%%esp)\n popfl\n pushfl\n pushl %%cs\n pushl $1f\n iret\n1:" ::: "memory", "cc")));

	/* FS/GS base MSRs */
	report("lm.fsbase.wr", msr_vec(0xC0000100, 0x100000000ULL | (u32)data));
	u64 fb = rdmsr(0xC0000100);
	__asm__ volatile("movl %%fs:0, %0" : "=r"(val));
	kprintf("lm.fsbase: %x_%x fs0=%x\n", (u32)(fb >> 32), (u32)fb, val);
	__asm__ volatile("movl %0, %%fs" :: "r"((u32)KDATA));
	fb = rdmsr(0xC0000100);
	kprintf("lm.fsbase.reload: %x_%x\n", (u32)(fb >> 32), (u32)fb);
	kprintf("lm.fsbase.noncanon: vec=%x\n", msr_vec(0xC0000100, 0x0000800000000000ULL));
	report("lm.kgsbase.wr", msr_vec(0xC0000102, 0xFFFF800012345678ULL));
	fb = rdmsr(0xC0000102);
	kprintf("lm.kgsbase: %x_%x\n", (u32)(fb >> 32), (u32)fb);
	kprintf("lm.kgsbase.noncanon: vec=%x\n", msr_vec(0xC0000102, 0x1234567812345678ULL));
	wrmsr(0xC0000102, 0);

	/* far transfers: task switches and illegal gates */
	showrec("lm.jmp.tss16", TRY(ljmp(TSS16, 0)));
	showrec("lm.jmp.tgate", TRY(ljmp(TGATE, 0)));
	showrec("lm.call.tss", TRY(lcall(TSS_MAIN, 0)));
	showrec("lm.call.cg16", TRY(lcall(CG16, 0)));
	showrec("lm.call.cgbad", TRY(lcall(CGBAD, 0)));
	showrec("lm.call.cg32t", TRY(lcall(CG32T, 0)));
	/* 16-bit compatibility-mode code: mov eax, imm32; far jmp ptr16:32 back to KCODE */
	{
		/* mov eax, imm32; add ax, 1 (16-bit operand size); retf with 32-bit operand size */
		static const u8 c16[] = { 0x66, 0xB8, 0x16, 0x16, 0x16, 0x16, 0x05, 0xF0, 0x0F, 0x66, 0xCB };
		for (u32 i = 0; i < sizeof c16; i++) code16[i] = c16[i];
		u32 got = 0;
		__asm__ volatile("lcall %1, $0" : "=a"(got) : "i"(KC16) : "memory", "cc");
		kprintf("lm.code16: %x\n", got);
	}

	/* transfers into 64-bit code: the stubs record and return */
	showrec("lm.jmp.64", TRY(ljmp(KC64, stub_at[0xF7])));
	showrec("lm.call.64", TRY(lcall(KC64, stub_at[0xF8])));
	showrec("lm.call.cg0", TRY(lcall(CG0, 0)));
	showrec("lm.jmp.cg0", TRY(ljmp(CG0, 0)));
	showrec("lm.retf.64", TRY(__asm__ volatile("pushl %0\n pushl %1\n lret" :: "i"(KC64), "r"(stub_at[0xF9]) : "memory")));
	showrec("lm.iret.64", TRY(__asm__ volatile("pushfl\n pushl %0\n pushl %1\n iret" :: "i"(KC64), "r"(stub_at[0xFA]) : "memory")));
	{
		/* ring 3 -> 64-bit call gate DPL 3 (inner stack RSP0, null SS) */
		static u8 snip[8] = { 0x9A, 0, 0, 0, 0, (u8)CG3, (u8)(CG3 >> 8), 0xCC };   /* call far CG3:0 */
		showrec("lm.user.call.cg3", run_user((char *)snip, 0, 0));
		static u8 snip2[8] = { 0x9A, 0, 0, 0, 0, (u8)CG0, (u8)(CG0 >> 8), 0xCC };  /* gate DPL 0 */
		showrec("lm.user.call.cg0", run_user((char *)snip2, 0, 0));
	}
	/* SYSCALL from compatibility mode: 64-bit at CSTAR, RCX = next RIP, R11 = RFLAGS */
	wrmsr(EFER, LME | LMA | NXE | 1);
	wrmsr(0xC0000081, (u64)KC64 << 32);
	wrmsr(0xC0000083, stub_at[0xFB]);
	wrmsr(0xC0000084, 0x200);
	showrec("lm.syscall", TRY(__asm__ volatile("pushfl\n orl $0x200, (%%esp)\n popfl\n .byte 0x0F, 0x05" ::: "ecx", "memory")));
	kprintf("lm.syscall.regs: rcx=%x_%x r11=%x_%x\n", (u32)(lmrec[7] >> 32), (u32)lmrec[7], (u32)(lmrec[8] >> 32),
	        (u32)lmrec[8]);
	wrmsr(EFER, LME | LMA | NXE);
	wrmsr(0xC0000081, 0); wrmsr(0xC0000083, 0); wrmsr(0xC0000084, 0);
	/* a code segment with L = 1 and D = 1 (reserved) as a far JMP target: last, since TCG enters it
	   and the stub's copy of the stack then differs */
	v = TRY(ljmp(RSVDC, stub_at[0xF6]));
	kprintf("lm.jmp.rsvdcode: vec=%x err=%x\n", v, v == 13 ? last.err : 0);

	lm_fuzz();

	/* deactivation: clear PG (LMA = 0), then LME */
	lm_off();
	kprintf("lm.off: efer=%x cr0=%x\n", (u32)rdmsr(EFER), RDCR(0));
	__asm__ volatile("lgdt %0" :: "m"(old_gdt));
	reload_tr(TSS_MAIN);
	kprintf("lm.legacy.again: vec=%x\n", TRY(__asm__ volatile("int $0x41")));
}

/* Model-only: behaviour where TCG is known to differ in a way that cannot be compared line by line. */
void test_long_model(void) {
	__asm__ volatile("sgdt %0" : "=m"(old_gdt));
	struct dtr gd = { sizeof lgdt_ - 1, (u32)lgdt_ };
	__asm__ volatile("lgdt %0" :: "m"(gd));
	/* PML4E bits 8:7 are MBZ (figure 5-20): checked here only through the ring-3 view of a separate
	   PML4 would be needed on QEMU; the model's walk is exercised through PDPT/PD/PT by lmf */
	/* enabling paging with EFER.LME = 1 while CS.L = 1 (legacy mode ignores L): #GP(0). TCG would
	   activate long mode and run the following 32-bit code as 64-bit code. */
	lgdt_[RSVDC >> 3] = seg_desc(0, 0xFFFFF, 0x9A, 0xE);
	WRCR(4, RDCR(4) | 0x20);
	WRCR(3, (u32)pml4);
	wrmsr(EFER, LME);
	u32 vec, cr0b = RDCR(0);
	__asm__ volatile("ljmp %0, $1f\n1:" :: "i"(RSVDC));
	vec = TRY(WRCR(0, cr0b | 0x80000000));
	__asm__ volatile("ljmp %0, $1f\n1:" :: "i"(KCODE));
	kprintf("lmm.pg.csl: vec=%x efer=%x cr0=%x\n", vec, (u32)rdmsr(EFER), RDCR(0));
	wrmsr(EFER, 0);
	WRCR(4, RDCR(4) & ~0x20);
	/* MOV CR4 cannot clear PAE while long mode is active (table 14-5). TCG accepts it (and then walks
	   the 4-level tables as 32-bit ones), so this comes last. */
	lm_on();
	vec = TRY(WRCR(4, RDCR(4) & ~0x20));
	kprintf("lmm.cr4.pae.clear: vec=%x cr4=%x\n", vec, RDCR(4));
	lm_off();
	__asm__ volatile("lgdt %0" :: "m"(old_gdt));
}
