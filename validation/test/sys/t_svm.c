/* SVM (AMD APM vol. 2, chapter 15): a small hypervisor in the test kernel. It enables EFER.SVME,
   builds VMCBs and runs guests in the identity-mapped test kernel's memory (guest physical = host
   physical without nested paging), with intercepts, event injection and nested paging, and prints
   the #VMEXIT information (EXITCODE, EXITINFO1/2, EXITINTINFO) and the guest state saved in the VMCB.
   The QEMU part covers what TCG implements as the APM describes; the MODEL-ONLY part (test_svm_model)
   what TCG lacks or does differently (NRIPS, decode assists, PAUSE filter, TSC ratio, VM_CR/SVM_KEY,
   SKINIT, several consistency checks, EV of event injection, ...), checked against
   model-only.expected and, for the tables, test/sys/svmref.py; test_svm_smp the smp=2 pass (a guest
   on the AP). */
#include "sys.h"
#include "smp.h"

#define EFER_MSR 0xC0000080
#define VM_CR 0xC0010114
#define VM_HSAVE 0xC0010117
#define SVME (1u << 12)

/* VMCB control area (table B-1) */
#define C_CR 0x000
#define C_DR 0x004
#define C_EXC 0x008
#define C_I3 0x00C
#define C_I4 0x010
#define C_I5 0x014
#define C_PTHR 0x03C
#define C_PCNT 0x03E
#define C_IOPM 0x040
#define C_MSRPM 0x048
#define C_TSCOFF 0x050
#define C_ASID 0x058
#define C_TLBCTL 0x05C
#define C_VINT 0x060
#define C_VVEC 0x064
#define C_INTST 0x068
#define C_CODE 0x070
#define C_INFO1 0x078
#define C_INFO2 0x080
#define C_EII 0x088
#define C_NP 0x090
#define C_INJ 0x0A8
#define C_NCR3 0x0B0
#define C_VIRT 0x0B8
#define C_CLEAN 0x0C0
#define C_NRIP 0x0C8
#define C_BYTES 0x0D0
/* state-save area (table B-2) */
#define S_ES 0x400
#define S_CS 0x410
#define S_SS 0x420
#define S_DS 0x430
#define S_FS 0x440
#define S_GS 0x450
#define S_GDTR 0x460
#define S_LDTR 0x470
#define S_IDTR 0x480
#define S_TR 0x490
#define S_CPL 0x4CB
#define S_EFER 0x4D0
#define S_CR4 0x548
#define S_CR3 0x550
#define S_CR0 0x558
#define S_DR7 0x560
#define S_DR6 0x568
#define S_RFLAGS 0x570
#define S_RIP 0x578
#define S_RSP 0x5D8
#define S_RAX 0x5F8
#define S_STAR 0x600
#define S_SCS 0x628
#define S_SESP 0x630
#define S_SEIP 0x638
#define S_CR2 0x640
#define S_GPAT 0x668

/* intercept bit numbers of vector 3 (00Ch) and 4 (010h) */
enum { I_INTR, I_NMI, I_SMI, I_INIT, I_VINTR, I_CR0SEL, I_IDTRR, I_GDTRR, I_LDTRR, I_TRR, I_IDTRW, I_GDTRW,
       I_LDTRW, I_TRW, I_RDTSC, I_RDPMC, I_PUSHF, I_POPF, I_CPUID, I_RSM, I_IRET, I_INTN, I_INVD, I_PAUSE,
       I_HLT, I_INVLPG, I_INVLPGA, I_IOIO, I_MSR, I_TASK, I_FERR, I_SHUTDOWN };
enum { I4_VMRUN, I4_VMMCALL, I4_VMLOAD, I4_VMSAVE, I4_STGI, I4_CLGI, I4_SKINIT, I4_RDTSCP, I4_ICEBP,
       I4_WBINVD, I4_MONITOR, I4_MWAIT, I4_MWAITC, I4_XSETBV, I4_RDPRU };

static u8 *vmcb, *vmcb2, *iopm, *msrpm, *gidt, *gcode, *gstack, *gdata;
u32 svm_vmcb_pa;
u32 svm_g[8];   /* guest GPRs other than EAX/ESP: EBX ECX EDX ESI EDI EBP (indices 3 1 2 6 7 5) */

#define VM8(o) (*(volatile u8 *)(vmcb + (o)))
#define VM16(o) (*(volatile u16 *)(vmcb + (o)))
#define VM32(o) (*(volatile u32 *)(vmcb + (o)))
#define VM64(o) (*(volatile u64 *)(vmcb + (o)))

/* VMRUN with the guest GPRs of svm_g; afterwards svm_g holds the guest's. The host's GPRs are kept
   on its stack (VMRUN saves only RAX, RSP and RIP of them). */
__asm__(
	".globl svm_vmrun_raw\nsvm_vmrun_raw:\n"
	" pushal\n"
	" movl svm_g+12, %ebx\n movl svm_g+4, %ecx\n movl svm_g+8, %edx\n"
	" movl svm_g+24, %esi\n movl svm_g+28, %edi\n movl svm_g+20, %ebp\n"
	" movl svm_vmcb_pa, %eax\n"
	" .byte 0x0f, 0x01, 0xd8\n"          /* VMRUN */
	" movl %ebx, svm_g+12\n movl %ecx, svm_g+4\n movl %edx, svm_g+8\n"
	" movl %esi, svm_g+24\n movl %edi, svm_g+28\n movl %ebp, svm_g+20\n"
	" popal\n ret\n"
	/* guest exception/interrupt stubs (guest IDT): EAX = vector, then VMMCALL */
	" .p2align 4\n.globl svm_gisr\nsvm_gisr:\n"
	" .set v, 0\n .rept 256\n .p2align 4\n movl $v, %eax\n .byte 0x0f, 0x01, 0xd9\n hlt\n .set v, v + 1\n .endr\n");
extern char svm_gisr[];
void svm_vmrun_raw(void);

static inline void clgi(void) { __asm__ volatile(".byte 0x0f, 0x01, 0xdd" ::: "memory"); }
static inline void stgi(void) { __asm__ volatile(".byte 0x0f, 0x01, 0xdc" ::: "memory"); }

/* One VMRUN with GIF cleared around it (the usual hypervisor sequence); GIF is set again after. */
static void run(void) {
	svm_vmcb_pa = (u32)vmcb;
	clgi();
	svm_vmrun_raw();
	stgi();
}

static void seg(u32 off, u16 sel, u16 attr, u32 limit, u32 base) {
	VM16(off) = sel; VM16(off + 2) = attr; VM32(off + 4) = limit; VM64(off + 8) = base;
}

/* A flat 32-bit ring-0 guest at `rip` (no paging), the guest IDT, VMRUN and VMMCALL intercepted,
   every exception intercepted unless `exc` clears bits. */
static void vmcb_flat(u32 rip) {
	memset(vmcb, 0, 4096);
	VM32(C_I4) = (1 << I4_VMRUN) | (1 << I4_VMMCALL);
	VM32(C_ASID) = 1;
	VM64(C_IOPM) = (u32)iopm;
	VM64(C_MSRPM) = (u32)msrpm;
	seg(S_CS, KCODE, 0xC9B, 0xFFFFFFFF, 0);
	seg(S_SS, KDATA, 0xC93, 0xFFFFFFFF, 0);
	seg(S_DS, KDATA, 0xC93, 0xFFFFFFFF, 0);
	seg(S_ES, KDATA, 0xC93, 0xFFFFFFFF, 0);
	VM32(S_GDTR + 4) = sizeof gdt - 1; VM64(S_GDTR + 8) = (u32)gdt;
	VM32(S_IDTR + 4) = 0x7FF; VM64(S_IDTR + 8) = (u32)gidt;
	VM8(S_CPL) = 0;
	VM64(S_EFER) = SVME;
	VM64(S_CR0) = 0x11;
	VM64(S_DR7) = 0x400; VM64(S_DR6) = 0xFFFF0FF0;
	VM64(S_RFLAGS) = 2;
	VM64(S_RIP) = rip;
	VM64(S_RSP) = (u32)gstack + 4096 - 16;
	VM64(S_RAX) = 0;
	for (int k = 0; k < 8; k++) svm_g[k] = 0;
}

/* Guest code: `n` bytes, then VMMCALL and HLT. */
static u32 gput(const u8 *b, int n) {
	for (int k = 0; k < n; k++) gcode[k] = b[k];
	gcode[n] = 0x0f; gcode[n + 1] = 0x01; gcode[n + 2] = 0xd9; gcode[n + 3] = 0xf4;
	return (u32)gcode;
}
#define G(...) ({ static const u8 _b[] = { __VA_ARGS__ }; gput(_b, sizeof _b); })

static void x64(const char *k, u64 v) { kprintf(" %s=%x:%x", k, (u32)(v >> 32), (u32)v); }

/* The common exit report: EXITCODE, EXITINFO1/2, EXITINTINFO and the guest's RIP/RSP/RAX/RFLAGS. */
static void show(const char *name) {
	kprintf("%s:", name);
	x64("code", VM64(C_CODE)); x64("i1", VM64(C_INFO1)); x64("i2", VM64(C_INFO2)); x64("ii", VM64(C_EII));
	kprintf(" rip=%x rsp=%x rax=%x fl=%x\n", (u32)VM64(S_RIP), (u32)VM64(S_RSP), (u32)VM64(S_RAX),
	        (u32)VM64(S_RFLAGS));
}

/* guest IDT: every vector to its stub, DPL 3 interrupt gates */
static void gidt_init(void) {
	u64 *t = (u64 *)gidt;
	for (int v = 0; v < 256; v++) t[v] = gate_desc(KCODE, (u32)svm_gisr + 16 * v, 0xEE);
}

static void svm_setup(void) {
	vmcb = page_alloc(1); vmcb2 = page_alloc(1); iopm = page_alloc(3); msrpm = page_alloc(2);
	gidt = page_alloc(1); gcode = page_alloc(1); gstack = page_alloc(1); gdata = page_alloc(1);
	gidt_init();
}

/* ---------------- enabling, #UD/#GP rules ---------------- */

static void t_enable(void) {
	u32 r[4];
	cpuid(0x80000001, 0, r);
	kprintf("svm.cpuid: svm=%d\n", (r[2] >> 2) & 1);
	u32 efer = (u32)rdmsr(EFER_MSR);
	wrmsr(EFER_MSR, efer & ~SVME);
	/* every SVM instruction but STGI/SKINIT is #UD without EFER.SVME (vol. 3) */
	static const char *nm[] = { "vmrun", "vmmcall", "vmload", "vmsave", "clgi", "invlpga" };
	int v[6];
	u32 a = (u32)vmcb;
	v[0] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xd8" :: "a"(a) : "memory"));
	v[1] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xd9" ::: "memory"));
	v[2] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xda" :: "a"(a) : "memory"));
	v[3] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xdb" :: "a"(a) : "memory"));
	v[4] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xdd" ::: "memory"));
	v[5] = TRY(__asm__ volatile(".byte 0x0f,0x01,0xdf" :: "a"(0), "c"(0) : "memory"));
	for (int k = 0; k < 6; k++) kprintf("svm.nosvme.%s: vec=%x\n", nm[k], v[k]);
	wrmsr(EFER_MSR, efer | SVME);
	kprintf("svm.efer: %x\n", (u32)rdmsr(EFER_MSR) & SVME);
	/* VM_HSAVE_PA: bits 11:0 must be zero */
	kprintf("svm.hsave.lowbits: vec=%x\n", TRY(wrmsr(VM_HSAVE, 0x10000123)));
	wrmsr(VM_HSAVE, (u32)vmcb2);
	kprintf("svm.hsave: %x\n", (u32)rdmsr(VM_HSAVE) == (u32)vmcb2);
	/* VMRUN/VMLOAD/VMSAVE: rAX must be 4 KiB aligned (#GP(0)) */
	kprintf("svm.vmrun.misaligned: vec=%x err=%x\n",
	        TRY(__asm__ volatile(".byte 0x0f,0x01,0xd8" :: "a"(a + 0x10) : "memory")), last.err);
	kprintf("svm.vmload.misaligned: vec=%x\n", TRY(__asm__ volatile(".byte 0x0f,0x01,0xda" :: "a"(a + 8) : "memory")));
	kprintf("svm.vmsave.misaligned: vec=%x\n", TRY(__asm__ volatile(".byte 0x0f,0x01,0xdb" :: "a"(a + 8) : "memory")));
	/* VMMCALL outside a guest: #UD */
	kprintf("svm.vmmcall.host: vec=%x\n", TRY(__asm__ volatile(".byte 0x0f,0x01,0xd9" ::: "memory")));
}

/* CPL 3: VMRUN, VMLOAD, VMSAVE, STGI, CLGI, INVLPGA #GP(0); VMMCALL #UD */
__asm__(".globl svm_u_vmrun\nsvm_u_vmrun: .byte 0x0f,0x01,0xd8\n int $0x40\n"
        ".globl svm_u_vmmcall\nsvm_u_vmmcall: .byte 0x0f,0x01,0xd9\n int $0x40\n"
        ".globl svm_u_vmload\nsvm_u_vmload: .byte 0x0f,0x01,0xda\n int $0x40\n"
        ".globl svm_u_vmsave\nsvm_u_vmsave: .byte 0x0f,0x01,0xdb\n int $0x40\n"
        ".globl svm_u_stgi\nsvm_u_stgi: .byte 0x0f,0x01,0xdc\n int $0x40\n"
        ".globl svm_u_clgi\nsvm_u_clgi: .byte 0x0f,0x01,0xdd\n int $0x40\n"
        ".globl svm_u_invlpga\nsvm_u_invlpga: .byte 0x0f,0x01,0xdf\n int $0x40\n");
extern char svm_u_vmrun[], svm_u_vmmcall[], svm_u_vmload[], svm_u_vmsave[], svm_u_stgi[], svm_u_clgi[], svm_u_invlpga[];

static void t_cpl3(void) {
	char *c[] = { svm_u_vmrun, svm_u_vmmcall, svm_u_vmload, svm_u_vmsave, svm_u_stgi, svm_u_clgi, svm_u_invlpga };
	static const char *nm[] = { "vmrun", "vmmcall", "vmload", "vmsave", "stgi", "clgi", "invlpga" };
	for (int k = 0; k < 7; k++) {
		int v = run_user(c[k], (u32)vmcb, 0);
		kprintf("svm.cpl3.%s: vec=%x err=%x\n", nm[k], v, v == 0x40 ? 0 : last.err);
	}
}

/* ---------------- a first guest ---------------- */

static void t_basic(void) {
	vmcb_flat(G(0xbb, 0x34, 0x12, 0, 0, 0xb8, 0x78, 0x56, 0, 0));   /* mov $0x1234,%ebx; mov $0x5678,%eax */
	svm_g[1] = 0x11; svm_g[2] = 0x22; svm_g[6] = 0x66; svm_g[7] = 0x77; svm_g[5] = 0x55;
	run();
	show("svm.basic");
	kprintf("svm.basic.regs: ebx=%x ecx=%x edx=%x esi=%x edi=%x ebp=%x cpl=%x cs=%x/%x ss=%x/%x\n",
	        svm_g[3], svm_g[1], svm_g[2], svm_g[6], svm_g[7], svm_g[5], VM8(S_CPL), VM16(S_CS), VM16(S_CS + 2),
	        VM16(S_SS), VM16(S_SS + 2));
	/* the host state is back */
	u32 cr0 = RDCR(0), cr4 = RDCR(4), dr7 = RDDR(7);
	u16 cs, ss, ds;
	__asm__ volatile("movw %%cs, %0\n movw %%ss, %1\n movw %%ds, %2" : "=r"(cs), "=r"(ss), "=r"(ds));
	kprintf("svm.basic.host: cr0=%x cr4=%x dr7=%x cs=%x ss=%x ds=%x\n", cr0, cr4, dr7, cs, ss, ds);
}

/* ---------------- intercepts ---------------- */

static int streq(const char *a, const char *b) { while (*a && *a == *b) { a++; b++; } return *a == *b; }

static char nmbuf[64];
static const char *nm3(const char *a, const char *b, const char *c) {
	int i = 0;
	while (*a) nmbuf[i++] = *a++;
	while (*b) nmbuf[i++] = *b++;
	while (*c) nmbuf[i++] = *c++;
	nmbuf[i] = 0;
	return nmbuf;
}

/* flags of a case */
#define OFF 1      /* also run without the intercept (the instruction completes or faults) */
#define RAX0 2     /* the guest's EAX is 0 (else the VMCB address) */

struct icase { const char *name; int vec; int bit; int flags; u8 code[12]; int n; u32 eax, ecx, edx, esi, edi; };

/* Instruction intercepts: vector 0 (CR read 0-15, write 16-31), 1 (DR), 3 (00Ch), 4 (010h); the
   instruction under test, then VMMCALL. The decode-assist EXITINFO1 of MOV CRx/DRx, INTn, INVLPG and
   the nRIP are printed in the model-only part (TCG has neither). */
static const struct icase icases[] = {
	{ "rdtsc", 3, I_RDTSC, OFF, { 0x0f, 0x31 }, 2 },
	{ "rdpmc", 3, I_RDPMC, 0, { 0x0f, 0x33 }, 2 },
	{ "pushf", 3, I_PUSHF, OFF, { 0x9c, 0x58 }, 2 },
	{ "popf", 3, I_POPF, OFF, { 0x6a, 0x02, 0x9d }, 3 },
	{ "cpuid", 3, I_CPUID, OFF, { 0x0f, 0xa2 }, 2 },
	{ "intn", 3, I_INTN, OFF, { 0xcd, 0x41 }, 2 },
	{ "invd", 3, I_INVD, OFF, { 0x0f, 0x08 }, 2 },
	{ "pause", 3, I_PAUSE, OFF, { 0xf3, 0x90 }, 2 },
	{ "hlt", 3, I_HLT, 0, { 0xf4 }, 1 },
	{ "invlpg", 3, I_INVLPG, OFF, { 0x0f, 0x01, 0x38 }, 3, 0x123456 },
	{ "invlpga", 3, I_INVLPGA, OFF, { 0x0f, 0x01, 0xdf }, 3, 0x5000, 1 },
	{ "sidt", 3, I_IDTRR, OFF, { 0x0f, 0x01, 0x0e }, 3, 0, 0, 0, 0x40C000 },
	{ "sgdt", 3, I_GDTRR, OFF, { 0x0f, 0x01, 0x06 }, 3, 0, 0, 0, 0x40C000 },
	{ "sldt", 3, I_LDTRR, OFF, { 0x0f, 0x00, 0xc0 }, 3 },
	{ "str", 3, I_TRR, OFF, { 0x0f, 0x00, 0xc8 }, 3 },
	{ "lidt", 3, I_IDTRW, 0, { 0x0f, 0x01, 0x1e }, 3, 0, 0, 0, 0x40C000 },
	{ "lgdt", 3, I_GDTRW, 0, { 0x0f, 0x01, 0x16 }, 3, 0, 0, 0, 0x40C000 },
	{ "lldt", 3, I_LDTRW, OFF | RAX0, { 0x0f, 0x00, 0xd0 }, 3, 0 },
	{ "ltr", 3, I_TRW, 0, { 0x0f, 0x00, 0xd8 }, 3, TSS_MAIN },
	{ "iret", 3, I_IRET, 0, { 0xcf }, 1 },
	{ "rsm", 3, I_RSM, OFF, { 0x0f, 0xaa }, 2 },
	{ "vmmcall", 4, I4_VMMCALL, 0, { 0x90 }, 1 },
	{ "vmload", 4, I4_VMLOAD, 0, { 0x0f, 0x01, 0xda }, 3 },
	{ "vmsave", 4, I4_VMSAVE, 0, { 0x0f, 0x01, 0xdb }, 3 },
	{ "stgi", 4, I4_STGI, OFF, { 0x0f, 0x01, 0xdc }, 3 },
	{ "clgi", 4, I4_CLGI, OFF, { 0x0f, 0x01, 0xdd }, 3 },
	{ "vmrun", 4, I4_VMRUN, 0, { 0x0f, 0x01, 0xd8 }, 3 },
	{ "wbinvd", 4, I4_WBINVD, OFF, { 0x0f, 0x09 }, 2 },
	{ "icebp", 4, I4_ICEBP, 0, { 0xf1 }, 1 },
	{ "rdtscp", 4, I4_RDTSCP, OFF, { 0x0f, 0x01, 0xf9 }, 3 },
	{ "monitor", 4, I4_MONITOR, OFF, { 0x0f, 0x01, 0xc8 }, 3, 0x40C000, 0, 0 },
	{ "mwait", 4, I4_MWAIT, 0, { 0x0f, 0x01, 0xc9 }, 3, 0, 0 },
	{ "xsetbv", 4, I4_XSETBV, OFF, { 0x0f, 0x01, 0xd1 }, 3, 1, 0, 0 },
	{ "rdcr0", 0, 0, OFF, { 0x0f, 0x20, 0xc0 }, 3 },
	{ "rdcr2", 0, 2, OFF, { 0x0f, 0x20, 0xd1 }, 3 },
	{ "rdcr3", 0, 3, OFF, { 0x0f, 0x20, 0xda }, 3 },
	{ "rdcr4", 0, 4, OFF, { 0x0f, 0x20, 0xe6 }, 3 },
	{ "rdcr8", 0, 8, OFF, { 0xf0, 0x0f, 0x20, 0xc7 }, 4 },
	{ "wrcr0", 0, 16, OFF, { 0x0f, 0x22, 0xc0 }, 3, 0x11 },
	{ "wrcr2", 0, 18, OFF, { 0x0f, 0x22, 0xd3 }, 3 },
	{ "wrcr3", 0, 19, OFF | RAX0, { 0x0f, 0x22, 0xd8 }, 3, 0 },
	{ "wrcr4", 0, 20, OFF | RAX0, { 0x0f, 0x22, 0xe0 }, 3, 0 },
	{ "wrcr8", 0, 24, OFF | RAX0, { 0xf0, 0x0f, 0x22, 0xc0 }, 4, 0 },
	{ "clts", 0, 16, OFF, { 0x0f, 0x06 }, 2 },
	{ "lmsw", 0, 16, OFF, { 0x0f, 0x01, 0xf6 }, 3, 0, 0, 0, 0x1 },
	{ "smsw", 0, 0, OFF, { 0x0f, 0x01, 0xe0 }, 3 },
	{ "rddr0", 1, 0, OFF, { 0x0f, 0x21, 0xc0 }, 3 },
	{ "rddr7", 1, 7, OFF, { 0x0f, 0x21, 0xfa }, 3 },
	{ "wrdr1", 1, 17, OFF, { 0x0f, 0x23, 0xcb }, 3 },
	{ "wrdr6", 1, 22, OFF | RAX0, { 0x0f, 0x23, 0xf0 }, 3, 0 },
	{ "wrdr7", 1, 23, OFF, { 0x0f, 0x23, 0xf8 }, 3, 0x400 },
};

static void set_icpt(const struct icase *c, int on) {
	u32 b = 1u << c->bit;
	switch (c->vec) {
	case 0: if (on) VM32(C_CR) |= b; break;
	case 1: if (on) VM32(C_DR) |= b; break;
	case 3: if (on) VM32(C_I3) |= b; break;
	default:
		if (on) VM32(C_I4) |= b;
		else if (c->bit != I4_VMRUN && c->bit != I4_VMMCALL) VM32(C_I4) &= ~b;
	}
}

static void prep_case(const struct icase *c, int on) {
	u32 rip = gput(c->code, c->n);
	vmcb_flat(rip);
	VM32(C_EXC) = 0xFFFFFFFF;   /* every exception intercepted */
	set_icpt(c, on);
	VM64(S_RAX) = (c->eax || (c->flags & RAX0)) ? c->eax : (u32)vmcb2;
	svm_g[1] = c->ecx; svm_g[2] = c->edx; svm_g[6] = c->esi; svm_g[7] = c->edi;
}

static void t_intercepts(void) {
	for (u32 k = 0; k < sizeof icases / sizeof icases[0]; k++) {
		const struct icase *c = &icases[k];
		for (int on = 1; on >= 0; on--) {
			if (!on && !(c->flags & OFF)) continue;
			prep_case(c, on);
			run();
			kprintf("%s: code=%x rip=%x\n", nm3("svm.icpt.", c->name, on ? ".on" : ".off"),
			        (u32)VM64(C_CODE), (u32)VM64(S_RIP) - (u32)gcode);
		}
	}
}

/* CR0 selective write intercept (VMCB 00Ch bit 5): MOV CR0 changing only TS/MP does not exit, another
   bit does (65h); the CR0 write intercept takes priority; CLTS does not check it. */
static void t_cr0sel(void) {
	static const struct { const char *n; u32 v; u8 code[4]; int len; int gen; } k[] = {
		{ "ts", 0x19, { 0x0f, 0x22, 0xc0 }, 3, 0 },
		{ "mp", 0x13, { 0x0f, 0x22, 0xc0 }, 3, 0 },
		{ "em", 0x15, { 0x0f, 0x22, 0xc0 }, 3, 0 },
		{ "wp", 0x10011, { 0x0f, 0x22, 0xc0 }, 3, 0 },
		{ "both", 0x15, { 0x0f, 0x22, 0xc0 }, 3, 1 },
		{ "clts", 0, { 0x0f, 0x06 }, 2, 0 },
		{ "lmsw.em", 0x5, { 0x0f, 0x01, 0xf6 }, 3, 0 },
	};
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		vmcb_flat(gput(k[i].code, k[i].len));
		VM32(C_EXC) = 0xFFFFFFFF;
		VM32(C_I3) |= 1 << I_CR0SEL;
		if (k[i].gen) VM32(C_CR) |= 1 << 16;
		VM64(S_RAX) = k[i].v;
		svm_g[6] = k[i].v;
		if (streq(k[i].n, "clts")) VM64(S_CR0) = 0x19;
		run();
		kprintf("%s: code=%x rip=%x cr0=%x\n", nm3("svm.cr0sel.", k[i].n, ""), (u32)VM64(C_CODE),
		        (u32)VM64(S_RIP) - (u32)gcode, (u32)VM64(S_CR0));
	}
}

/* IOIO intercepts (15.10): the IOPM bit of every byte of the access; EXITINFO1 = port, size, STR,
   type (address size and segment: model-only, TCG leaves them 0); EXITINFO2 = the next RIP. */
static void t_ioio(void) {
	static const struct { const char *n; u8 code[4]; int len; u32 edx, ecx; } k[] = {
		{ "inb", { 0xe4, 0x80 }, 2, 0, 0 },
		{ "outb", { 0xe6, 0x80 }, 2, 0, 0 },
		{ "inw.dx", { 0x66, 0xed }, 2, 0x7F, 0 },
		{ "outl.dx", { 0xef }, 1, 0x7E, 0 },
		{ "outl.dx.miss", { 0xef }, 1, 0x84, 0 },
		{ "insb", { 0x6c }, 1, 0x80, 0 },
		{ "repoutsw", { 0xf3, 0x66, 0x6f }, 3, 0x80, 2 },
	};
	iopm[0x80 >> 3] = 1 << (0x80 & 7);   /* port 80h only */
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		u32 rip = gput(k[i].code, k[i].len);
		vmcb_flat(rip);
		VM32(C_EXC) = 0xFFFFFFFF;
		VM32(C_I3) |= 1u << I_IOIO;
		svm_g[2] = k[i].edx; svm_g[1] = k[i].ecx; svm_g[6] = (u32)gdata; svm_g[7] = (u32)gdata;
		run();
		kprintf("%s: code=%x i1=%x i2=%x rip=%x\n", nm3("svm.ioio.", k[i].n, ""), (u32)VM64(C_CODE),
		        (u32)VM64(C_INFO1) & ~0x1F80u, (u32)VM64(C_INFO2) - rip, (u32)VM64(S_RIP) - rip);
	}
	iopm[0x80 >> 3] = 0;
}

/* MSR intercepts (15.11): the MSRPM read/write bits; MSRs outside the map always exit. */
static void t_msr(void) {
	static const struct { const char *n; u8 w; u32 msr; u32 pos; } k[] = {
		{ "rd.tsc", 0, 0x10, 0x10 * 2 },
		{ "rd.tsc.wbit", 0, 0x10, 0x10 * 2 + 1 },
		{ "wr.sysenter", 1, 0x174, 0x174 * 2 + 1 },
		{ "wr.sysenter.rbit", 1, 0x174, 0x174 * 2 },
		{ "rd.star", 0, 0xC0000081, 0x4000 + 0x81 * 2 },
		{ "rd.hsave", 0, 0xC0010117, 0x8000 + 0x117 * 2 },
		{ "rd.outside", 0, 0x40000000, 0xFFFFFFFF },
	};
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		memset(msrpm, 0, 8192);
		if (k[i].pos != 0xFFFFFFFF) msrpm[k[i].pos >> 3] |= 1 << (k[i].pos & 7);
		u32 rip = k[i].w ? G(0x0f, 0x30) : G(0x0f, 0x32);
		vmcb_flat(rip);
		VM32(C_EXC) = 0xFFFFFFFF;
		VM32(C_I3) |= 1u << I_MSR;
		svm_g[1] = k[i].msr; svm_g[2] = 0;
		VM64(S_RAX) = 0x8;
		run();
		kprintf("%s: code=%x i1=%x rip=%x\n", nm3("svm.msr.", k[i].n, ""), (u32)VM64(C_CODE),
		        (u32)VM64(C_INFO1), (u32)VM64(S_RIP) - rip);
	}
	memset(msrpm, 0, 8192);
}

/* Exception intercepts (15.12): EXITINFO1 the error code (#NP, #SS, #GP); the rIP of the faulting
   instruction, of the next one for a trap; DR6 written before the #DB intercept. */
static void t_exc(void) {
	gdt[31] = seg_desc(0, 0xFFFFF, 0x12, 0xC);   /* a not-present data segment, selector F8h */
	u32 *bnd = (u32 *)gdata;
	bnd[0] = 10; bnd[1] = 20;
	static const struct { const char *n; u8 code[16]; int len; u32 eax, ecx, fl, cr0, cr4; } k[] = {
		{ "de", { 0x31, 0xc9, 0xf7, 0xf1 }, 4 },
		{ "db.tf", { 0x90, 0x90 }, 2, 0, 0, 0x102 },
		{ "bp", { 0xcc }, 1 },
		{ "of", { 0xb0, 0x7f, 0x04, 0x01, 0xce }, 5 },
		{ "br", { 0x62, 0x01 }, 2, 30, 0 },
		{ "ud", { 0x0f, 0x0b }, 2 },
		{ "nm", { 0xdb, 0xe3 }, 2, 0, 0, 2, 0x19 },
		{ "np", { 0x8e, 0xd8 }, 2, 0xF8 },
		{ "ss", { 0x8e, 0xd0 }, 2, 0xF8 },
		{ "gp", { 0x8e, 0xd8 }, 2, 0x1234 },
		{ "gp.cr4", { 0x0f, 0x22, 0xe0 }, 3, 0x80000000 },
		{ "mf", { 0xdb, 0xe3, 0xd9, 0x29, 0xd9, 0xe8, 0xd9, 0xee, 0xde, 0xf9, 0x9b }, 11, 0, 0, 2, 0x31 },
	};
	*(u16 *)(gdata + 0x20) = 0x37B;    /* x87 control word with ZM clear */
	*(u32 *)(gdata + 0x10) = 0x1F00;   /* MXCSR with IM clear */
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		u32 rip = gput(k[i].code, k[i].len);
		vmcb_flat(rip);
		VM32(C_EXC) = 0xFFFFFFFF;
		VM64(S_RAX) = k[i].eax;
		svm_g[1] = k[i].ecx;
		if (streq(k[i].n, "br")) svm_g[1] = (u32)gdata;
		if (streq(k[i].n, "mf")) svm_g[1] = (u32)gdata + 0x20;
		if (k[i].fl) VM64(S_RFLAGS) = k[i].fl;
		if (k[i].cr0) VM64(S_CR0) = k[i].cr0;
		if (k[i].cr4) VM64(S_CR4) = k[i].cr4;
		run();
		kprintf("%s: code=%x i1=%x rip=%x dr6=%x\n", nm3("svm.exc.", k[i].n, ""), (u32)VM64(C_CODE),
		        (u32)VM64(C_INFO1), (u32)VM64(S_RIP) - rip, (u32)VM64(S_DR6));
	}
	gdt[31] = 0;
}

/* #DF and its intercept (15.12.9, 15.7.2): a guest IDT with limit 0 makes every delivery #GP; with
   only #DF intercepted the #UD -> #GP -> #DF chain exits with the #GP in EXITINTINFO; with #GP
   intercepted the first #GP exits with the #UD in EXITINTINFO; with neither, the shutdown intercept
   (15.14.3). */
/* c = 0 (the #DF intercept of a double fault from combining exceptions) is model-only: TCG shuts
   down instead (m_df0) */
static void t_df_case(int c, const char *pfx) {
	vmcb_flat(G(0x0f, 0x0b));
	VM32(S_IDTR + 4) = 0;
	VM32(C_EXC) = c == 0 ? (1 << 8) : c == 1 ? (1 << 13) : 0;
	if (c == 2) VM32(C_I3) |= 1u << I_SHUTDOWN;
	run();
	kprintf("%s.%d: code=%x i1=%x", pfx, c, (u32)VM64(C_CODE), c == 1 ? (u32)VM64(C_INFO1) : 0);
	x64("ii", c == 2 ? 0 : VM64(C_EII));
	kputc('\n');
}
static void t_df(void) {
	for (int c = 1; c < 3; c++) t_df_case(c, "svm.df");
}

/* Priority of instruction intercepts and exceptions (table 15-7) in a CPL-3 guest with every
   exception intercepted. */
static const struct icase pcases[] = {
	{ "hlt", 3, I_HLT, 0, { 0xf4 }, 1 },
	{ "invd", 3, I_INVD, 0, { 0x0f, 0x08 }, 2 },
	{ "rdcr0", 0, 0, 0, { 0x0f, 0x20, 0xc0 }, 3 },
	{ "wrcr0", 0, 16, 0, { 0x0f, 0x22, 0xc0 }, 3 },
	{ "rdmsr", 3, I_MSR, 0, { 0x0f, 0x32 }, 2 },
	{ "stgi", 4, I4_STGI, 0, { 0x0f, 0x01, 0xdc }, 3 },
	{ "clgi", 4, I4_CLGI, 0, { 0x0f, 0x01, 0xdd }, 3 },
	{ "vmload", 4, I4_VMLOAD, 0, { 0x0f, 0x01, 0xda }, 3 },
	{ "invlpg", 3, I_INVLPG, 0, { 0x0f, 0x01, 0x38 }, 3 },
	{ "rdtsc.tsd", 3, I_RDTSC, 0, { 0x0f, 0x31 }, 2 },
	{ "lgdt", 3, I_GDTRW, 0, { 0x0f, 0x01, 0x16 }, 3 },
	{ "pushf", 3, I_PUSHF, 0, { 0x9c }, 1 },
	{ "popf", 3, I_POPF, 0, { 0x9d }, 1 },
	{ "iret", 3, I_IRET, 0, { 0xcf }, 1 },
	{ "intn", 3, I_INTN, 0, { 0xcd, 0x05 }, 2 },
	{ "cpuid", 3, I_CPUID, 0, { 0x0f, 0xa2 }, 2 },
	{ "vmmcall", 4, I4_VMMCALL, 0, { 0x90 }, 1 },
	{ "xsetbv", 4, I4_XSETBV, 0, { 0x0f, 0x01, 0xd1 }, 3 },
	{ "in.iopl", 3, I_IOIO, 0, { 0xe4, 0x80 }, 2 },
	{ "rsm", 3, I_RSM, 0, { 0x0f, 0xaa }, 2 },
};

static void ring3(void) {
	seg(S_CS, UCODE, 0xCFB, 0xFFFFFFFF, 0);
	seg(S_SS, UDATA, 0xCF3, 0xFFFFFFFF, 0);
	seg(S_DS, UDATA, 0xCF3, 0xFFFFFFFF, 0);
	seg(S_ES, UDATA, 0xCF3, 0xFFFFFFFF, 0);
	VM8(S_CPL) = 3;
}

static void t_prio(void) {
	u64 *gi = (u64 *)gidt;
	u64 save5 = gi[5];
	gi[5] = gate_desc(KCODE, (u32)svm_gisr + 16 * 5, 0x8E);   /* DPL 0: INT 5 from CPL 3 is #GP */
	iopm[0x80 >> 3] = 1 << (0x80 & 7);
	for (u32 i = 0; i < sizeof pcases / sizeof pcases[0]; i++) {
		const struct icase *c = &pcases[i];
		prep_case(c, 1);
		ring3();
		if (streq(c->name, "rdtsc.tsd")) VM64(S_CR4) = 4;
		run();
		kprintf("%s: code=%x i1=%x rip=%x\n", nm3("svm.prio.", c->name, ""), (u32)VM64(C_CODE),
		        VM64(C_CODE) == 0x75 ? 0 : (u32)VM64(C_INFO1), (u32)VM64(S_RIP) - (u32)gcode);
	}
	iopm[0x80 >> 3] = 0;
	gi[5] = save5;
}

/* Event injection (15.20): each type, delivered through the guest IDT before the first guest
   instruction (the stubs report the vector in EAX), the frame the handler finds; illegal EVENTINJ
   values end VMRUN with VMEXIT_INVALID. Software interrupts and #BP get nRIP = RIP (the return
   address TCG pushes, as it has no nRIP). */
static void t_inject(void) {
	static const struct { const char *n; u32 ev; u32 err; } k[] = {
		{ "intr", 0x80000030, 0 },
		{ "nmi", 0x80000202, 0 },
		{ "gp", 0x80000B0D, 0x1234 },
		{ "ud", 0x80000306, 0 },
		{ "pf", 0x80000B0E, 0x5 },
		{ "soft", 0x80000441, 0 },
		{ "bp", 0x80000303, 0 },
		{ "de", 0x80000300, 0 },
		{ "inv.type1", 0x80000130, 0 },
		{ "inv.type5", 0x80000530, 0 },
		{ "inv.nmivec", 0x80000302, 0 },
		{ "inv.vec32", 0x80000320, 0 },
		{ "notvalid", 0x00000306, 0 },
	};
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		u32 rip = G(0x90);
		vmcb_flat(rip);
		VM32(C_INJ) = k[i].ev; VM32(C_INJ + 4) = k[i].err;
		VM64(C_NRIP) = rip;
		u32 top = (u32)gstack + 4096 - 16;
		run();
		u32 sp = (u32)VM64(S_RSP);
		u32 depth = top - sp;
		kprintf("%s: code=%x rax=%x depth=%x", nm3("svm.inject.", k[i].n, ""), (u32)VM64(C_CODE),
		        (u32)VM64(S_RAX), depth);
		if (depth >= 12 && depth <= 16 && VM64(C_CODE) == 0x81) {
			u32 *f = (u32 *)sp;
			int e = depth == 16;
			kprintf(" err=%x eip=%x cs=%x", e ? f[0] : 0, f[e] - rip, f[e + 1]);
		}
		kputc('\n');
	}
}

/* Consistency checks of VMRUN (15.5.1): each illegal state ends VMRUN with VMEXIT_INVALID (-1) and
   the host continues after it. */
static void t_consist(void) {
	static const char *n[] = { "efer.nosvme", "efer.rsvd", "cr0.hi", "cr0.nwcd", "cr4.rsvd", "novmrun",
	                           "asid0", "msrpm.max", "iopm.max", "ok" };
	for (int c = 0; c < 10; c++) {
		vmcb_flat(G(0x90));
		switch (c) {
		case 0: VM64(S_EFER) = 0; break;
		case 1: VM64(S_EFER) = SVME | 0x2000000; break;
		case 2: VM64(S_CR0) = 0x100000011ULL; break;
		case 3: VM64(S_CR0) = 0x20000011; break;
		case 4: VM64(S_CR4) = 0x80000000; break;
		case 5: VM32(C_I4) &= ~1u; break;
		case 6: VM32(C_ASID) = 0; break;
		case 7: VM64(C_MSRPM) = 0xFFFFFFFFF000ULL; break;
		case 8: VM64(C_IOPM) = 0xFFFFFFFFE000ULL; break;
		}
		run();
		kprintf("%s: code=%x\n", nm3("svm.consist.", n[c], ""), (u32)VM64(C_CODE));
	}
}

/* VMSAVE and VMLOAD (15.5.2): FS, GS, TR, LDTR with their hidden state, STAR and SYSENTER_CS/ESP/EIP
   (KernelGsBase, LSTAR, CSTAR and SFMASK: model-only, qemu-system-i386 does not have them). */
static void t_vmloadsave(void) {
	memset(vmcb2, 0, 4096);
	u32 a = (u32)vmcb2;
	__asm__ volatile(".byte 0x0f,0x01,0xdb" :: "a"(a) : "memory");   /* VMSAVE */
	volatile u8 *v = vmcb2;
	kprintf("svm.vmsave: fs=%x/%x/%x/%x gs=%x/%x tr=%x/%x/%x/%x ldtr=%x/%x star=%x:%x scs=%x\n",
	        *(u16 *)(v + S_FS), *(u16 *)(v + S_FS + 2), *(u32 *)(v + S_FS + 4), *(u32 *)(v + S_FS + 8),
	        *(u16 *)(v + S_GS), *(u16 *)(v + S_GS + 2),
	        *(u16 *)(v + S_TR), *(u16 *)(v + S_TR + 2), *(u32 *)(v + S_TR + 4), *(u32 *)(v + S_TR + 8) == (u32)&tss_main,
	        *(u16 *)(v + S_LDTR), *(u16 *)(v + S_LDTR + 2), *(u32 *)(v + S_STAR + 4), *(u32 *)(v + S_STAR),
	        *(u32 *)(v + S_SCS));
	u8 *w = (u8 *)vmcb2;
	*(u16 *)(w + S_FS) = 0x10; *(u16 *)(w + S_FS + 2) = 0x493; *(u32 *)(w + S_FS + 4) = 0x1FFF; *(u64 *)(w + S_FS + 8) = (u32)gdata + 0x800;
	*(u16 *)(w + S_GS) = 0x23; *(u16 *)(w + S_GS + 2) = 0xCF3; *(u32 *)(w + S_GS + 4) = 0xFFFFFFFF; *(u64 *)(w + S_GS + 8) = 0x800;
	*(u64 *)(w + S_STAR) = 0x0023001000001234ULL;
	*(u64 *)(w + S_SCS) = 0x08; *(u64 *)(w + S_SESP) = 0x9000; *(u64 *)(w + S_SEIP) = 0x7777;
	__asm__ volatile(".byte 0x0f,0x01,0xda" :: "a"(a) : "memory");   /* VMLOAD */
	u16 fs, gs;
	__asm__ volatile("movw %%fs, %0\n movw %%gs, %1" : "=r"(fs), "=r"(gs));
	*(u32 *)(gdata + 0x800) = 0xCAFEF00D;
	u32 x;
	__asm__ volatile("movl %%fs:0, %0" : "=r"(x));
	memset(vmcb2, 0, 4096);
	__asm__ volatile(".byte 0x0f,0x01,0xdb" :: "a"(a) : "memory");   /* VMSAVE */
	kprintf("svm.vmload: fs=%x gs=%x fsattr=%x fslim=%x fsbase=%x gsbase=%x star=%x:%x sesp=%x seip=%x fsread=%x\n",
	        fs, gs, *(u16 *)(v + S_FS + 2), *(u32 *)(v + S_FS + 4), *(u32 *)(v + S_FS + 8) - (u32)gdata, *(u32 *)(v + S_GS + 8),
	        *(u32 *)(v + S_STAR + 4), *(u32 *)(v + S_STAR), *(u32 *)(v + S_SESP), *(u32 *)(v + S_SEIP), x);
	__asm__ volatile("movw %0, %%fs\n movw %0, %%gs" :: "r"((u16)KDATA));
	wrmsr(0x174, 0); wrmsr(0x175, 0); wrmsr(0x176, 0); wrmsr(0xC0000081, 0);
}

/* ---------------- GIF, physical and virtual interrupts ---------------- */

static volatile u32 h_intr, h_nmi, h_vec;
static int svm_hook(struct frame *f) {
	if (f->vec == 0x50 || f->vec == 0x51) { h_intr++; h_vec = f->vec; LR(0xB0) = 0; return 1; }
	if (f->vec == 2) { h_nmi++; return 1; }
	return 0;
}
static void self_ipi(u32 v) { LR(0x310) = 0; LR(0x300) = v; }
static void settle(void) { for (volatile int k = 0; k < 64; k++) {} }

/* GIF (15.17, table 15-10): with GIF = 0 an INTR or NMI is held pending, STGI lets it in. */
static void t_gif(void) {
	h_intr = h_nmi = 0;
	clgi();
	__asm__ volatile("sti");
	self_ipi(0x50);
	settle();
	u32 a = h_intr;
	stgi();
	settle();
	__asm__ volatile("cli");
	kprintf("svm.gif.intr: gif0=%d after_stgi=%d\n", a, h_intr);
	clgi();
	self_ipi(0x400);
	settle();
	a = h_nmi;
	stgi();
	settle();
	kprintf("svm.gif.nmi: gif0=%d after_stgi=%d\n", a, h_nmi);
}

/* Interrupts in guest mode (15.13, 15.21): the INTR and NMI intercepts leave the event pending (the
   host takes it after STGI); without the intercept it is delivered through the guest's IDT; with
   V_INTR_MASKING the host's IF masks physical interrupts, the guest's only virtual ones; a virtual
   interrupt (V_IRQ) is taken when its priority is above V_TPR (or V_IGN_TPR) and the guest's IF is
   set, or causes the VINTR intercept. */
static void irq_run(const char *name, u32 hostif, u32 ipi) {
	h_intr = h_nmi = 0;
	clgi();
	if (hostif) __asm__ volatile("sti");
	if (ipi) self_ipi(ipi);
	settle();
	svm_vmcb_pa = (u32)vmcb;
	svm_vmrun_raw();
	u32 hi = h_intr, hn = h_nmi;
	stgi();
	settle();
	__asm__ volatile("cli");
	LR(0xB0) = 0;   /* EOI of a vector the guest took */
	kprintf("%s: code=%x rax=%x vint=%x:%x host_intr=%d/%d host_nmi=%d/%d\n", name, (u32)VM64(C_CODE),
	        (u32)VM64(S_RAX), VM32(C_VINT + 4), VM32(C_VINT) & 0xFFF, hi, h_intr, hn, h_nmi);
}

static void t_irq(void) {
	/* a loop of NOPs, then VMMCALL */
	u8 nops[32];
	for (int k = 0; k < 32; k++) nops[k] = 0x90;
	u32 rip = gput(nops, 32);
	/* physical INTR, intercepted (guest IF = 0, V_INTR_MASKING: the host's IF counts) */
	vmcb_flat(rip); VM32(C_I3) |= 1 << I_INTR; VM32(C_VINT) = 1 << 24;
	irq_run("svm.irq.intr.icpt", 1, 0x50);
	/* intercepted but masked by the host's IF = 0: runs to VMMCALL */
	vmcb_flat(rip); VM32(C_I3) |= 1 << I_INTR; VM32(C_VINT) = 1 << 24;
	irq_run("svm.irq.intr.hostif0", 0, 0x50);
	/* not intercepted, no V_INTR_MASKING: the guest's IF = 1 lets it in through the guest IDT */
	vmcb_flat(rip); VM64(S_RFLAGS) = 0x202;
	irq_run("svm.irq.intr.guest", 0, 0x50);
	/* not intercepted, guest IF = 0: masked */
	vmcb_flat(rip);
	irq_run("svm.irq.intr.guestif0", 1, 0x50);
	/* NMI intercepted: pending, taken by the host after STGI */
	vmcb_flat(rip); VM32(C_I3) |= 1 << I_NMI;
	irq_run("svm.irq.nmi.icpt", 0, 0x400);
	/* NMI not intercepted: delivered through the guest's IDT (vector 2) */
	vmcb_flat(rip);
	irq_run("svm.irq.nmi.guest", 0, 0x400);
	/* virtual interrupts: V_IRQ, V_INTR_PRIO, V_TPR, V_IGN_TPR, V_INTR_VECTOR (060h) */
	static const struct { const char *n; u32 vint, fl, icpt; } k[] = {
		{ "svm.virq.take", 0x00030100, 0x202, 0 },          /* prio 3 > tpr 0 */
		{ "svm.virq.tpr", 0x00030105, 0x202, 0 },           /* prio 3 < tpr 5: not taken */
		{ "svm.virq.igntpr", 0x00130105, 0x202, 0 },        /* V_IGN_TPR */
		{ "svm.virq.if0", 0x00030100, 0x002, 0 },           /* guest IF = 0 */
		{ "svm.virq.icpt", 0x00030100, 0x202, 1 },          /* VINTR intercept: V_IRQ stays */
		{ "svm.virq.masking", 0x01030100, 0x202, 0 },       /* with V_INTR_MASKING */
	};
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		vmcb_flat(rip);
		VM32(C_VINT) = k[i].vint; VM32(C_VINT + 4) = 0x51;
		VM64(S_RFLAGS) = k[i].fl;
		if (k[i].icpt) VM32(C_I3) |= 1 << I_VINTR;
		irq_run(k[i].n, 0, 0);
	}
	/* CR8 in a guest (15.21.2): with V_INTR_MASKING reads give V_TPR and writes set only V_TPR;
	   without it writes also set the APIC's TPR */
	for (int vm = 0; vm < 2; vm++) {
		vmcb_flat(G(0xf0, 0x0f, 0x20, 0xc3, 0xb8, 0x07, 0, 0, 0, 0xf0, 0x0f, 0x22, 0xc0));   /* mov cr8,ebx; mov $7,eax; mov eax,cr8 */
		VM32(C_VINT) = (vm ? 1 << 24 : 0) | 0x4;
		LR(0x80) = 0x20;
		run();
		u32 tpr = LR(0x80);
		LR(0x80) = 0;
		kprintf("svm.cr8.%s: code=%x ebx=%x vtpr=%x apic_tpr=%x\n", vm ? "masking" : "plain", (u32)VM64(C_CODE),
		        svm_g[3], VM32(C_VINT) & 0xF, tpr);
	}
}

/* ---------------- guest modes ---------------- */

#define RMBASE 0x20000   /* real-mode / virtual-8086 guests: code at 2000:0000, stack 2000:F000 */

/* Real-mode guest (CR0.PE = 0; CPL forced to 0): 16-bit code, INT n through its IVT (IDTR base) with
   and without the INTn intercept, an exception through the IVT, segment loads. */
static void t_real(void) {
	u8 *c = (u8 *)RMBASE;
	u16 *ivt = (u16 *)(RMBASE + 0x8000);
	/* mov ax,1234h; mov bx,ds; int 10h; mov si,ax; vmmcall */
	static const u8 code[] = { 0xb8, 0x34, 0x12, 0x8c, 0xdb, 0xcd, 0x10, 0x89, 0xc6, 0x0f, 0x01, 0xd9, 0xf4 };
	for (u32 k = 0; k < sizeof code; k++) c[k] = code[k];
	/* INT 10h handler at 2000:0100: mov ax,5678h; iret */
	static const u8 h[] = { 0xb8, 0x78, 0x56, 0xcf };
	for (u32 k = 0; k < sizeof h; k++) c[0x100 + k] = h[k];
	ivt[0x10 * 2] = 0x100; ivt[0x10 * 2 + 1] = 0x2000;
	for (int icpt = 0; icpt < 2; icpt++) {
		vmcb_flat(0);
		VM64(S_CR0) = 0x10;
		seg(S_CS, 0x2000, 0x09B, 0xFFFF, RMBASE);
		seg(S_SS, 0x2000, 0x093, 0xFFFF, RMBASE);
		seg(S_DS, 0x2000, 0x093, 0xFFFF, RMBASE);
		seg(S_ES, 0x2000, 0x093, 0xFFFF, RMBASE);
		VM32(S_IDTR + 4) = 0x3FF; VM64(S_IDTR + 8) = RMBASE + 0x8000;
		VM64(S_RSP) = 0xF000;
		VM8(S_CPL) = 3;   /* ignored in real mode: CPL 0 */
		if (icpt) VM32(C_I3) |= 1u << I_INTN;
		run();
		kprintf("svm.real.%s: code=%x rip=%x rax=%x esi=%x ebx=%x rsp=%x cpl=%x cs=%x/%x\n", icpt ? "icpt" : "int",
		        (u32)VM64(C_CODE), (u32)VM64(S_RIP), (u32)VM64(S_RAX) & 0xFFFF, svm_g[6] & 0xFFFF, svm_g[3] & 0xFFFF,
		        (u32)VM64(S_RSP), VM8(S_CPL), VM16(S_CS), VM16(S_CS + 2));
	}
}

/* Virtual-8086 guest (EFLAGS.VM = 1; CPL forced to 3): IOPL-sensitive CLI raises #GP (intercepted);
   INT n is intercepted before its IOPL check; IN with IOPL < 3 is #GP before the IOIO intercept. */
static void t_vm86(void) {
	static const struct { const char *n; u8 code[4]; int len; int bit; } k[] = {
		{ "cli", { 0xfa }, 1, -1 },
		{ "intn", { 0xcd, 0x10 }, 2, I_INTN },
		{ "in", { 0xe4, 0x80 }, 2, I_IOIO },
		{ "pushf", { 0x9c }, 1, I_PUSHF },
		{ "mov", { 0xb8, 0x22, 0x11 }, 3, -1 },
	};
	iopm[0x80 >> 3] = 1 << (0x80 & 7);
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		u8 *c = (u8 *)RMBASE;
		for (int b = 0; b < k[i].len; b++) c[b] = k[i].code[b];
		c[k[i].len] = 0x0f; c[k[i].len + 1] = 0x01; c[k[i].len + 2] = 0xd9;
		vmcb_flat(0);
		VM32(C_EXC) = 0xFFFFFFFF;
		VM64(S_RFLAGS) = 0x20002;
		seg(S_CS, 0x2000, 0x0F3, 0xFFFF, RMBASE);
		seg(S_SS, 0x2000, 0x0F3, 0xFFFF, RMBASE);
		seg(S_DS, 0x2000, 0x0F3, 0xFFFF, RMBASE);
		seg(S_ES, 0x2000, 0x0F3, 0xFFFF, RMBASE);
		VM64(S_RSP) = 0xF000;
		if (k[i].bit >= 0) VM32(C_I3) |= 1u << k[i].bit;
		run();
		kprintf("%s: code=%x i1=%x rip=%x rax=%x cpl=%x fl=%x\n", nm3("svm.vm86.", k[i].n, ""), (u32)VM64(C_CODE),
		        VM64(C_CODE) == 0x7B ? 0 : (u32)VM64(C_INFO1), (u32)VM64(S_RIP), (u32)VM64(S_RAX) & 0xFFFF, VM8(S_CPL),
		        (u32)VM64(S_RFLAGS));
	}
	iopm[0x80 >> 3] = 0;
}

/* 16-bit protected-mode guest (CS.D = 0): operand size 16 by default. */
static void t_pm16(void) {
	static const u8 code[] = { 0xb8, 0x34, 0x12, 0x66, 0xbb, 0x78, 0x56, 0x34, 0x12, 0x0f, 0x01, 0xd9 };
	for (u32 k = 0; k < sizeof code; k++) ((u8 *)RMBASE)[k] = code[k];   /* mov ax,1234h; mov ebx,12345678h */
	vmcb_flat(0);
	seg(S_CS, KCODE, 0x09B, 0xFFFF, RMBASE);
	VM64(S_RAX) = 0xAAAA0000;
	run();
	kprintf("svm.pm16: code=%x rip=%x rax=%x ebx=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RIP),
	        (u32)VM64(S_RAX), svm_g[3]);
}

/* Paged guests without nested paging (the guest's CR3 holds host-physical addresses, as with shadow
   paging): legacy 2-level (4 MiB identity pages plus a 4 KiB table), PAE, and paged real mode
   (CR0.PE = 0, PG = 1, 15.19). A not-present page gives a #PF, caught by the #PF intercept: EXITINFO1
   the error code, EXITINFO2 the address, CR2 unchanged (15.12.15). The accessed/dirty bits the walk
   set are printed. */
static u32 *gpd, *gpt;
static u64 *gpdpt, *gpd64, *gpt64;
#define GWIN 0x40000000   /* the guest's 4 KiB window: page 0 -> gdata, page 1 not present, page 2 read-only */

static void build_gpt32(void) {
	for (int k = 0; k < 1024; k++) gpd[k] = (k << 22) | 0x87;   /* 4 MiB identity, user, writable */
	gpd[GWIN >> 22] = (u32)gpt | 0x07;
	for (int k = 0; k < 1024; k++) gpt[k] = 0;
	gpt[0] = (u32)gdata | 0x07;
	gpt[2] = (u32)gdata | 0x05;
}
static void build_gpt64(void) {
	for (int k = 0; k < 4; k++) gpdpt[k] = 0;
	gpdpt[0] = (u32)gpd64 | 1;
	gpdpt[1] = (u32)(gpd64 + 512) | 1;
	for (int k = 0; k < 1024; k++) gpd64[k] = ((u64)k << 21) | 0x87;
	gpd64[512] = (u32)gpt64 | 0x07;    /* 40000000h: through the second PD */
	for (int k = 0; k < 512; k++) gpt64[k] = 0;
	gpt64[0] = (u32)gdata | 0x07;
	gpt64[2] = (u32)gdata | 0x05;
}

static void t_paged(void) {
	gpd = page_alloc(1); gpt = page_alloc(1); gpdpt = page_alloc(1); gpd64 = page_alloc(2); gpt64 = page_alloc(1);
	static const struct { const char *n; u32 addr; int write; } acc[] = {
		{ "rd0", GWIN, 0 }, { "wr0", GWIN + 4, 1 }, { "rd1", GWIN + 0x1000, 0 }, { "wr2", GWIN + 0x2008, 1 },
	};
	for (int mode = 0; mode < 3; mode++) {
		for (u32 a = 0; a < 4; a++) {
			build_gpt32(); build_gpt64();
			*(u32 *)gdata = 0x600DF00D;
			/* mov eax,[ecx] / mov [ecx],eax */
			vmcb_flat(acc[a].write ? G(0x89, 0x01) : G(0x8b, 0x01));
			VM32(C_EXC) = 1 << 14;
			svm_g[1] = acc[a].addr;
			VM64(S_RAX) = 0x11223344;
			VM64(S_CR2) = 0xC2C2C2C2;
			if (mode == 0) { VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd; }
			else if (mode == 1) { VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x20; VM64(S_CR3) = (u32)gpdpt; }
			else {   /* paged real mode with 32-bit segments ("big real mode"): CS = 0, base 0 */
				VM64(S_CR0) = 0x80000010; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd;
				seg(S_CS, 0, 0xC9B, 0xFFFFFFFF, 0); seg(S_DS, 0, 0xC93, 0xFFFFFFFF, 0);
				seg(S_SS, 0, 0xC93, 0xFFFFFFFF, 0); seg(S_ES, 0, 0xC93, 0xFFFFFFFF, 0);
			}
			run();
			u32 pte = mode == 1 ? (u32)gpt64[(acc[a].addr >> 12) & 0x1FF] : gpt[(acc[a].addr >> 12) & 0x3FF];
			u32 pde = mode == 1 ? (u32)gpd64[512] : gpd[GWIN >> 22];
			kprintf("svm.paged.%s.%s: code=%x", mode == 0 ? "leg" : mode == 1 ? "pae" : "realpg", acc[a].n,
			        (u32)VM64(C_CODE));
			x64("i1", VM64(C_INFO1)); x64("i2", VM64(C_INFO2));
			kprintf(" cr2=%x rax=%x mem=%x pde=%x pte=%x\n", (u32)VM64(S_CR2),
			        VM64(C_CODE) == 0x81 ? (u32)VM64(S_RAX) : 0, *(u32 *)gdata, pde & 0x60, pte & 0x60);
		}
	}
}

/* ---------------- nested paging ---------------- */

/* Host paging for the nested-paging tests: identity maps of 0..4 GiB, 4 MiB pages (32-bit, CR4.PSE)
   or 2 MiB pages (PAE, with EFER.NXE). The nested tables use the host's paging mode (15.25.3). */
static u32 *hpd32;
static u64 *hpdpt, *hpd64;
static void host_paging(int mode) {
	if (!hpd32) { hpd32 = page_alloc(1); hpdpt = page_alloc(1); hpd64 = page_alloc(4); }
	if (mode == 0) {
		WRCR(0, RDCR(0) & ~0x80000000u);
		WRCR(4, RDCR(4) & ~0x30u);
		wrmsr(EFER_MSR, rdmsr(EFER_MSR) & ~0x800ULL);
		return;
	}
	if (mode == 1) {
		for (u32 k = 0; k < 1024; k++) hpd32[k] = (k << 22) | 0x83 | (k >= 0x3F8 ? 0x18 : 0);
		WRCR(4, (RDCR(4) & ~0x20u) | 0x10);
		WRCR(3, (u32)hpd32);
	} else {
		for (u32 k = 0; k < 4; k++) hpdpt[k] = (u32)(hpd64 + 512 * k) | 1;
		for (u32 k = 0; k < 2048; k++) hpd64[k] = ((u64)k << 21) | 0x83 | (k >= 0x7F0 ? 0x18 : 0);
		wrmsr(EFER_MSR, rdmsr(EFER_MSR) | 0x800);
		WRCR(4, RDCR(4) | 0x20);
		WRCR(3, (u32)hpdpt);
	}
	WRCR(0, RDCR(0) | 0x80000000u);
}

#define GPA0 0x10000000u   /* guest-physical window: pages k = 0..15 backed by npages */
static u8 *npages;
static u32 *npd32, *npt32;
static u64 *npdpt, *npd64, *npt64;

/* Nested permissions of the window pages (k): 0 RW data, 1 not present, 2 read-only, 3 guest PD,
   4 guest PT, 5 guest PDPT, 6 not present (a guest page table there faults at the nested level),
   7 no-execute code, 8/9 guest PAE PDs, 10 guest PAE PT, 11 a reserved bit in the nested entry. */
static u64 nperm(int k, int pae) {
	switch (k) {
	case 1: case 6: return 0;
	case 2: return 0x5;
	case 7: return pae ? 0x8000000000000007ULL : 0x7;
	case 11: return pae ? 0x0010000000000007ULL : 0x7;
	default: return 0x7;
	}
}

static void build_nested(int pae) {
	if (!npages) {
		npages = page_alloc(16); npd32 = page_alloc(1); npt32 = page_alloc(1);
		npdpt = page_alloc(1); npd64 = page_alloc(4); npt64 = page_alloc(1);
	}
	if (!pae) {
		for (u32 k = 0; k < 1024; k++) npd32[k] = (k << 22) | 0x87;   /* identity, user, writable, 4 MiB */
		npd32[GPA0 >> 22] = (u32)npt32 | 0x07;
		npd32[(GPA0 >> 22) + 1] = (GPA0 + 0x400000) | 0x87 | 0x200000;   /* reserved bit 21 of a 4 MiB PDE */
		for (u32 k = 0; k < 1024; k++) npt32[k] = 0;
		for (int k = 0; k < 16; k++) npt32[k] = nperm(k, 0) ? ((u32)npages + 0x1000 * k) | (u32)nperm(k, 0) : 0;
	} else {
		for (u32 k = 0; k < 4; k++) npdpt[k] = (u32)(npd64 + 512 * k) | 1;
		for (u32 k = 0; k < 2048; k++) npd64[k] = ((u64)k << 21) | 0x87;
		npd64[GPA0 >> 21] = (u32)npt64 | 0x07;
		npd64[(GPA0 >> 21) + 1] = (GPA0 + 0x200000) | 0x87 | 0x2000;   /* reserved bit 13 of a 2 MiB PDE */
		for (u32 k = 0; k < 512; k++) npt64[k] = 0;
		for (int k = 0; k < 16; k++) npt64[k] = nperm(k, 1) ? ((u32)npages + 0x1000 * k) | nperm(k, 1) : 0;
	}
	memset(npages, 0, 16 * 4096);
	*(u32 *)npages = 0x600DF00D;
	*(u32 *)(npages + 0x2000) = 0x5EADBEEF;
	u8 *code = npages + 0x7000;   /* mov eax,7777h; vmmcall */
	code[0] = 0xb8; code[1] = 0x77; code[2] = 0x77; code[3] = 0; code[4] = 0; code[5] = 0x0f; code[6] = 0x01; code[7] = 0xd9;
}

#define NWIN 0x40000000u   /* the guest's linear window under guest paging */
/* Guest page tables in guest-physical memory: legacy (PD at page 3, PT at page 4) and PAE (PDPT at
   page 5, PD0 at 8 identity, PD1 at 9 for NWIN, PT at 10). The window: page 0 -> GPA0 (data), 1 ->
   GPA0+1000h (nested not present), 2 -> GPA0+2000h (nested read-only), 3 guest not present,
   4 -> GPA0+7000h (code, nested NX), 5 -> GPA0+0B000h (nested reserved bit); NWIN + 4 MiB/2 MiB:
   through a guest page table at GPA0+6000h, which is not present at the nested level. */
static void build_guest_tables(void) {
	u32 *pd = (u32 *)(npages + 0x3000), *pt = (u32 *)(npages + 0x4000);
	for (u32 k = 0; k < 1024; k++) pd[k] = (k << 22) | 0x87;
	pd[NWIN >> 22] = (GPA0 + 0x4000) | 0x07;
	pd[(NWIN >> 22) + 1] = (GPA0 + 0x6000) | 0x07;
	u32 map[6] = { GPA0 | 7, (GPA0 + 0x1000) | 7, (GPA0 + 0x2000) | 7, 0, (GPA0 + 0x7000) | 7, (GPA0 + 0xB000) | 7 };
	for (int k = 0; k < 6; k++) pt[k] = map[k];
	u64 *pdpt = (u64 *)(npages + 0x5000), *pd0 = (u64 *)(npages + 0x8000), *pd1 = (u64 *)(npages + 0x9000),
	    *pt64 = (u64 *)(npages + 0xA000);
	pdpt[0] = (GPA0 + 0x8000) | 1; pdpt[1] = (GPA0 + 0x9000) | 1; pdpt[2] = pdpt[3] = 0;
	for (u32 k = 0; k < 512; k++) pd0[k] = ((u64)k << 21) | 0x87;
	pd1[0] = (GPA0 + 0xA000) | 7;
	pd1[1] = (GPA0 + 0x6000) | 7;
	for (int k = 0; k < 6; k++) pt64[k] = map[k];
}

/* The accesses: guest-physical with guest paging off, linear through the window otherwise. */
static const struct { const char *n; u32 off; u8 kind; } nacc[] = {
	{ "rd", 0, 0 }, { "wr", 4, 1 }, { "rd.np", 0x1000, 0 }, { "wr.ro", 0x2008, 1 }, { "rd.ro", 0x2000, 0 },
	{ "rd.gnp", 0x3000, 0 }, { "exec.nx", 0x4000, 2 }, { "rd.rsvd", 0x5000, 0 }, { "rd.gtable", 0x400000, 0 },
};

static void t_np_one(int hmode, int gmode) {
	static const char *hn[] = { "", "h32", "hpae" };
	static const char *gn[] = { "goff", "gleg", "gpae" };
	for (u32 a = 0; a < sizeof nacc / sizeof nacc[0]; a++) {
		if (gmode == 0 && (nacc[a].off == 0x3000 || nacc[a].off == 0x400000)) continue;
		if (gmode == 2 && nacc[a].off == 0x400000) continue;   /* PAE: the second PDE is +2 MiB */
		build_nested(hmode == 2);
		build_guest_tables();
		u32 addr;
		if (gmode == 0) {
			static const u32 gpa[] = { 0, 4, 0x1000, 0x2008, 0x2000, 0, 0x7000, 0xB000 };
			addr = GPA0 + gpa[a];
			if (hmode == 1 && nacc[a].off == 0x5000) addr = GPA0 + 0x400000;   /* the reserved-bit 4 MiB PDE */
			if (hmode == 2 && nacc[a].off == 0x5000) addr = GPA0 + 0x200000;   /* the reserved-bit 2 MiB PDE */
		} else addr = NWIN + nacc[a].off;
		if (gmode == 2 && nacc[a].off == 0x400000) addr = NWIN + 0x200000;
		u32 rip = nacc[a].kind == 1 ? G(0x89, 0x01) : nacc[a].kind == 0 ? G(0x8b, 0x01) : G(0xff, 0xd1);
		vmcb_flat(rip);
		VM32(C_EXC) = 1 << 14;
		VM64(C_NP) = 1;
		VM64(C_NCR3) = hmode == 2 ? (u32)npdpt : (u32)npd32;
		VM64(S_GPAT) = 0x0007040600070406ULL;
		svm_g[1] = addr;
		VM64(S_RAX) = 0x11223344;
		if (gmode == 1) { VM64(S_CR0) = 0x80010011; VM64(S_CR4) = 0x10; VM64(S_CR3) = GPA0 + 0x3000; }
		if (gmode == 2) { VM64(S_CR0) = 0x80010011; VM64(S_CR4) = 0x20; VM64(S_CR3) = GPA0 + 0x5000;
		                  VM64(S_EFER) = SVME | 0x800; }
		run();
		/* accessed/dirty bits (2 bits each) of the nested PTEs of window pages 0, 2, 3, 4, 5, 8, 9, 10 and of
		   the guest PTEs of window pages 0, 1, 2, 4 */
		u32 nad = 0, gad = 0;
		static const int nk[] = { 0, 2, 3, 4, 5, 8, 9, 10 };
		for (int j = 0; j < 8; j++) {
			u32 e = hmode == 2 ? (u32)npt64[nk[j]] : npt32[nk[j]];
			nad = (nad << 2) | ((e >> 5) & 3);
		}
		static const int gk[] = { 0, 1, 2, 4 };
		for (int j = 0; j < 4; j++) {
			u32 e = gmode == 2 ? (u32)((u64 *)(npages + 0xA000))[gk[j]] : ((u32 *)(npages + 0x4000))[gk[j]];
			gad = (gad << 2) | ((e >> 5) & 3);
		}
		kprintf("svm.np.%s.%s.%s: code=%x", hn[hmode], gn[gmode], nacc[a].n, (u32)VM64(C_CODE));
		x64("i1", VM64(C_CODE) == 0x81 ? 0 : VM64(C_INFO1)); x64("i2", VM64(C_CODE) == 0x81 ? 0 : VM64(C_INFO2));
		kprintf(" rax=%x d0=%x nad=%x gad=%x\n", VM64(C_CODE) == 0x81 ? (u32)VM64(S_RAX) : 0,
		        *(u32 *)(npages + 4), nad, gad);
	}
}

/* Host modes: 1 32-bit paging (model-only: TCG walks no nested tables for a host without PAE, it
   treats them as an identity map), 2 PAE. */
static void t_np(int h) {
	host_paging(h);
	for (int g = 0; g < 3; g++) t_np_one(h, g);
	host_paging(0);
}

/* NP_ENABLE with the host's paging disabled: VMEXIT_INVALID (15.25.3) (model-only: TCG does not
   check it) */
static void t_np_hostpg0(void) {
	build_nested(0);
	vmcb_flat(G(0x90));
	VM64(C_NP) = 1; VM64(C_NCR3) = (u32)npd32; VM64(S_GPAT) = 0x0007040600070406ULL;
	run();
	kprintf("svm.np.hostpg0: code=%x\n", (u32)VM64(C_CODE));
}

/* ---------------- fuzzers ---------------- */

static u32 fs_s;
static u32 frnd(void) { fs_s ^= fs_s << 13; fs_s ^= fs_s >> 17; fs_s ^= fs_s << 5; return fs_s; }

/* The SVM fuzzer's instruction pool (the instruction, then VMMCALL). `need` restricts a case: bit 0
   the instruction's own intercept must be set (it would hang or TCG executes it differently), bit 1
   CPL 0 only. `cr`/`dr`: the CR/DR intercept bit it checks (-1 none), `v3`/`v4`: its vector 3/4 bit. */
typedef signed char s8;
struct fcase { const char *n; u8 code[8]; u8 len; u8 need; s8 v3, v4, crb, exb; };
static const struct fcase fpool[] = {
	{ "nop", { 0x90 }, 1, 0, -1, -1, -1, -1 },
	{ "pushf", { 0x9c }, 1, 0, I_PUSHF, -1, -1, -1 },
	{ "popf", { 0x9d }, 1, 0, I_POPF, -1, -1, -1 },
	{ "int41", { 0xcd, 0x41 }, 2, 0, I_INTN, -1, -1, -1 },
	{ "invd", { 0x0f, 0x08 }, 2, 2, I_INVD, -1, -1, -1 },
	{ "pause", { 0xf3, 0x90 }, 2, 0, I_PAUSE, -1, -1, -1 },
	{ "hlt", { 0xf4 }, 1, 1, I_HLT, -1, -1, -1 },
	{ "invlpg", { 0x0f, 0x01, 0x39 }, 3, 0, I_INVLPG, -1, -1, -1 },
	{ "sidt", { 0x0f, 0x01, 0x0e }, 3, 0, I_IDTRR, -1, -1, -1 },
	{ "sgdt", { 0x0f, 0x01, 0x06 }, 3, 0, I_GDTRR, -1, -1, -1 },
	{ "sldt", { 0x0f, 0x00, 0xc0 }, 3, 0, I_LDTRR, -1, -1, -1 },
	{ "str", { 0x0f, 0x00, 0xc8 }, 3, 0, I_TRR, -1, -1, -1 },
	{ "rdcr0", { 0x0f, 0x20, 0xc2 }, 3, 0, -1, -1, 0, -1 },
	{ "wrcr0", { 0x0f, 0x22, 0xc0 }, 3, 0, -1, -1, 16, -1 },
	{ "clts", { 0x0f, 0x06 }, 2, 0, -1, -1, 16, -1 },
	{ "smsw", { 0x0f, 0x01, 0xe2 }, 3, 0, -1, -1, 0, -1 },
	{ "wrcr3", { 0x0f, 0x22, 0xdf }, 3, 0, -1, -1, 19, -1 },
	{ "wrcr2", { 0x0f, 0x22, 0xd3 }, 3, 0, -1, -1, 18, -1 },
	{ "rddr0", { 0x0f, 0x21, 0xc2 }, 3, 0, -1, -1, 32, -1 },
	{ "wrdr1", { 0x0f, 0x23, 0xcb }, 3, 0, -1, -1, 49, -1 },
	{ "rddr7", { 0x0f, 0x21, 0xfa }, 3, 0, -1, -1, 39, -1 },
	{ "in80", { 0xe4, 0x80 }, 2, 0, I_IOIO, -1, -1, -1 },
	{ "out80", { 0xe6, 0x80 }, 2, 0, I_IOIO, -1, -1, -1 },
	{ "inwdx", { 0x66, 0xed }, 2, 0, I_IOIO, -1, -1, -1 },
	{ "outldx", { 0xef }, 1, 0, I_IOIO, -1, -1, -1 },
	{ "rdmsr", { 0x0f, 0x32 }, 2, 0, I_MSR, -1, -1, -1 },
	{ "wrmsr", { 0x0f, 0x30 }, 2, 0, I_MSR, -1, -1, -1 },
	{ "wbinvd", { 0x0f, 0x09 }, 2, 2, -1, I4_WBINVD, -1, -1 },
	{ "stgi", { 0x0f, 0x01, 0xdc }, 3, 0, -1, I4_STGI, -1, -1 },
	{ "clgi", { 0x0f, 0x01, 0xdd }, 3, 0, -1, I4_CLGI, -1, -1 },
	{ "vmload", { 0x0f, 0x01, 0xda }, 3, 1, -1, I4_VMLOAD, -1, -1 },
	{ "vmsave", { 0x0f, 0x01, 0xdb }, 3, 1, -1, I4_VMSAVE, -1, -1 },
	{ "invlpga", { 0x0f, 0x01, 0xdf }, 3, 0, I_INVLPGA, -1, -1, -1 },
	{ "vmmcall", { 0x0f, 0x01, 0xd9 }, 3, 0, -1, I4_VMMCALL, -1, -1 },
	{ "rsm", { 0x0f, 0xaa }, 2, 0, I_RSM, -1, -1, -1 },
	{ "iret", { 0xcf }, 1, 1, I_IRET, -1, -1, -1 },
	{ "xsetbv", { 0x0f, 0x01, 0xd1 }, 3, 0, -1, I4_XSETBV, -1, -1 },
	{ "ud2", { 0x0f, 0x0b }, 2, 0, -1, -1, -1, 6 },
	{ "div0", { 0xf7, 0xf6 }, 2, 0, -1, -1, -1, 0 },
	{ "movds", { 0x8e, 0xd8 }, 2, 0, -1, -1, -1, 13 },
	{ "int3", { 0xcc }, 1, 4, -1, -1, -1, 3 },
	{ "lmsw", { 0x0f, 0x01, 0xf3 }, 3, 8, -1, -1, 16, -1 },
	{ "vmrun", { 0x0f, 0x01, 0xd8 }, 3, 0, -1, I4_VMRUN, -1, -1 },
	{ "lldt", { 0x0f, 0x00, 0xd0 }, 3, 0, I_LDTRW, -1, -1, -1 },
};
#define NFPOOL (sizeof fpool / sizeof fpool[0])

/* One case: intercept vectors, guest state and the instruction from the seed. `qemu`: keep to what TCG
   does as the APM describes (flags 4: not with the #BP intercept (TCG never checks it for INT3);
   8: not with the selective CR0 intercept (TCG checks LMSW like MOV CR0)). Returns the pool index. */
static u32 fz_case(u32 seed, int qemu) {
	fs_s = seed ? seed : 1;
	u32 k = frnd() % NFPOOL;
	const struct fcase *f = &fpool[k];
	u32 rip = gput(f->code, f->len);
	vmcb_flat(rip);
	int cpl3 = !(f->need & 2) && frnd() % 3 == 0;
	if (cpl3) ring3();
	VM32(C_I3) = frnd() & frnd() & ~((1u << I_INTR) | (1u << I_NMI) | (1u << I_SMI) | (1u << I_INIT) | (1u << I_VINTR) |
	                                (1u << I_FERR) | (1u << I_SHUTDOWN) | (1u << I_TASK));
	VM32(C_I4) = ((frnd() & frnd()) & 0x3FF & ~((1u << I4_SKINIT) | (1u << I4_RDTSCP) | (1u << I4_ICEBP))) |
	             (1u << I4_VMRUN) | (1u << I4_VMMCALL);
	VM32(C_CR) = frnd() & 0x00190009;   /* CR0, CR3, CR4 writes and CR0 reads (TCG checks no other reads) */
	VM32(C_DR) = frnd() & 0x00FF00FF;
	VM32(C_EXC) = frnd() | (1u << 8);   /* #DF always: no triple faults */
	/* TCG checks neither the #BP intercept for INT3 nor ... it checks the INTn intercept for it */
	if (qemu) VM32(C_EXC) &= ~((1u << 3) | (1u << 4));
	if (qemu && (f->need & 4)) VM32(C_I3) &= ~(1u << I_INTN);
	if (f->need & 1) { if (f->v3 >= 0) VM32(C_I3) |= 1u << f->v3; if (f->v4 >= 0) VM32(C_I4) |= 1u << f->v4; }
	if (qemu && (f->need & 8)) VM32(C_I3) &= ~(1u << I_CR0SEL);
	/* the IOPM and MSRPM bits of the I/O ports and MSRs the pool uses */
	iopm[0x80 >> 3] = frnd() & 0xFF;
	iopm[0x88 >> 3] = frnd() & 0xFF;
	memset(msrpm, 0, 0x1800);
	u32 msrs[4] = { 0x174, 0xC0000081, 0x40000000, 0x175 };
	u32 msr = msrs[frnd() % 4];
	if (msr == 0x174 || msr == 0x175) msrpm[(msr * 2) >> 3] = frnd() & 0xFF;
	if (msr == 0xC0000081) msrpm[0x800 + ((0x81 * 2) >> 3)] = frnd() & 0xFF;
	/* TCG lets RDMSR/WRMSR of an MSR it does not have pass (#GP on hardware and in the model): only
	   with MSR_PROT, which intercepts every MSR outside the map */
	if (qemu && msr == 0x40000000) VM32(C_I3) |= 1u << I_MSR;
	/* TCG raises #GP for XSETBV with CR4.OSXSAVE = 0 (#UD, APM vol. 3 XSETBV): only intercepted */
	if (qemu && f->v4 == I4_XSETBV) VM32(C_I4) |= 1u << I4_XSETBV;
	/* guest state: GPRs, arithmetic flags and DF, CR0.TS/MP/EM/WP/NE, CR4.TSD/DE/PCE */
	static const u32 sels[] = { 0, KDATA, KCODE, UDATA, 0x1234, 0xF8, 0x13 };
	svm_g[1] = msr; svm_g[2] = 0x7E + frnd() % 12;
	svm_g[3] = frnd(); svm_g[5] = frnd();
	svm_g[6] = (u32)gdata + (frnd() & 0x3F0); svm_g[7] = (u32)gdata + (frnd() & 0x3F0);
	u32 cr0v = 0x11 | (frnd() & 0x1002E);
	VM64(S_CR0) = cr0v;
	VM64(S_RAX) = frnd() % 2 ? cr0v ^ (frnd() & 0x2E) : sels[frnd() % 7];
	if (f->code[0] == 0xf7) svm_g[6] = 0;   /* div esi: #DE */
	if (f->code[1] == 0x22 && f->code[2] == 0xdf) svm_g[7] = 0;    /* CR3 = 0 */
	if (f->code[0] == 0x0f && f->code[1] == 0x01 && f->code[2] == 0xf3) svm_g[3] = cr0v ^ (frnd() & 0xE);
	VM64(S_CR4) = frnd() & 0x10C;
	VM64(S_RFLAGS) = 2 | (frnd() & 0x8D5);
	VM64(S_DR7) = 0x400 | (frnd() & 0x2000 & 0);
	gdt[31] = seg_desc(0, 0xFFFFF, 0x12, 0xC);
	/* the QEMU-compared fuzzer also varies the interrupt shadow and RFLAGS.RF the guest starts with
	   (saved as of the moment an intercept triggers, 15.7.1, 15.21.5); drawn last, so the model-only
	   replay of svmref.py (qemu = 0) is unchanged */
	if (qemu) {
		VM32(C_INTST) = frnd() % 4 == 0;
		/* not for VMMCALL itself: TCG's VMMCALL exit saves RF = 0 */
		if (frnd() % 4 == 0 && !streq(f->n, "vmmcall")) VM64(S_RFLAGS) |= 0x10000;
	}
	return k;
}

static void fz_show(const char *tag, u32 n, u32 k, u32 rip, int qemu) {
	u32 code = (u32)VM64(C_CODE);
	u32 i1 = (u32)VM64(C_INFO1);
	/* decode-assist EXITINFO1 (MOV CR/DR, INTn, INVLPG) and the IOIO address-size/segment fields:
	   TCG has neither */
	if (qemu && (code < 0x40 || code == 0x75 || code == 0x79)) i1 = 0;
	if (qemu && code == 0x7B) i1 &= ~0x1F80u;
	/* the value an IN instruction read from an unassigned port is the device's (TCG emulates the
	   PC's DMA page registers at 81h..8Fh) */
	u32 rax = (u32)VM64(S_RAX);
	if (code == 0x81 && fpool[k].code[0] != 0x0f && (fpool[k].code[0] == 0xe4 || fpool[k].code[1] == 0xed)) rax = 0;
	u32 i2 = (code == 0x7B) ? (u32)VM64(C_INFO2) - rip : (code == 0x4E || code == 0x400) ? (u32)VM64(C_INFO2) : 0;
	kprintf("%s %d %s cpl=%d: code=%x i1=%x i2=%x rip=%x rax=%x rsp=%x fl=%x ebx=%x esi=%x edi=%x sh=%d\n", tag, n,
	        fpool[k].n, VM8(S_CPL), code, i1, i2, (u32)VM64(S_RIP) - (code == 0x81 && (u32)VM64(S_RIP) >= (u32)svm_gisr &&
	        (u32)VM64(S_RIP) < (u32)svm_gisr + 4096 ? (u32)svm_gisr : rip), rax,
	        (u32)VM64(S_RSP) - (u32)gstack, (u32)VM64(S_RFLAGS), svm_g[3], svm_g[6] - (u32)gdata, svm_g[7] - (u32)gdata,
	        VM32(C_INTST) & 1);
}

/* SVM fuzzer (QEMU-compared): `svf` cases (default 300) of random intercept vectors, guest state and
   an instruction from the pool. */
static void t_fuzz(void) {
	u32 n = param("svf", 300);
	u32 base = fuzz_seed(0x5A17C0DE);
	for (u32 c = 0; c < n; c++) {
		u32 seed = base + c * 0x9E3779B9u;
		u32 k = fz_case(seed, 1);
		u32 rip = (u32)gcode;
		run();
		fz_show("svf", c, k, rip, 1);
	}
	iopm[0x80 >> 3] = iopm[0x88 >> 3] = 0;
	memset(msrpm, 0, 0x2000);
	gdt[31] = 0;
}

/* ---------------- nested-paging fuzzer ---------------- */

/* A case of the two-dimensional walk: the host's paging mode (1 32-bit, 2 PAE: the nested format),
   the guest's (0 off, 1 32-bit with PSE, 2 PAE), CR0.WP, EFER.NXE of the guest (PAE), CPL, the access
   (0 read, 1 write, 2 fetch) to window page `pg` (offset 0 data, 100h code), the attribute bits of the
   nested PDE covering the window and of the nested PTEs of window pages 0..7 (bit 0 P, 1 R/W, 2 U/S,
   3 NX, 4 A, 5 D, 6 a reserved bit), and of the guest PDE and PTEs for window pages 0..7. Window page
   k is guest-physical GPA0 + 1000h * k; the guest's tables are in window pages 8 (PD / PDPT and PDs:
   8, 9, 10) and 11 (PT), mapped by the nested PTEs 8..11 (attributes `ntab`). */
#define NPCODE 0x21000
struct npc { u8 hmode, gmode, wp, nxe, cpl, acc, pg, ntab, npde, gpde; u8 npte[8], gpte[8]; };

static u64 attr_bits(u8 a, int pae) {
	u64 e = 0;
	if (a & 1) e |= 1;
	if (a & 2) e |= 2;
	if (a & 4) e |= 4;
	if ((a & 8) && pae) e |= 0x8000000000000000ULL;
	if (a & 0x10) e |= 0x20;
	if (a & 0x20) e |= 0x40;
	if (a & 0x40) e |= pae ? 0x0010000000000000ULL : 0;   /* PAE: bit 52 (reserved); 32-bit PTEs have none */
	return e;
}

/* Build the case's tables (the identity part of the nested tables as in build_nested) and run it. */
static void npc_run(const struct npc *c) {
	int hp = c->hmode == 2;
	build_nested(hp);
	u64 pde = attr_bits(c->npde, hp);
	if (hp) {
		npd64[GPA0 >> 21] = (u32)npt64 | (u32)(pde & 0xFFF) | (pde & 0xFFF0000000000000ULL);
		for (int k = 0; k < 16; k++) npt64[k] = 0;
		for (int k = 0; k < 8; k++) npt64[k] = ((u32)npages + 0x1000 * k) | attr_bits(c->npte[k], 1);
		for (int k = 8; k < 12; k++) npt64[k] = ((u32)npages + 0x1000 * k) | attr_bits(c->ntab, 1);
	} else {
		npd32[GPA0 >> 22] = (u32)npt32 | (u32)(pde & 0xFFF);
		for (int k = 0; k < 16; k++) npt32[k] = 0;
		for (int k = 0; k < 8; k++) npt32[k] = ((u32)npages + 0x1000 * k) | (u32)attr_bits(c->npte[k], 0);
		for (int k = 8; k < 12; k++) npt32[k] = ((u32)npages + 0x1000 * k) | (u32)attr_bits(c->ntab, 0);
	}
	for (int k = 0; k < 8; k++) {
		*(u32 *)(npages + 0x1000 * k) = 0xD0000000 | k;
		u8 *code = npages + 0x1000 * k + 0x100;   /* mov eax, 0C0DE000k; vmmcall */
		code[0] = 0xb8; *(u32 *)(code + 1) = 0xC0DE0000 | k; code[5] = 0x0f; code[6] = 0x01; code[7] = 0xd9;
	}
	/* guest tables: 32-bit PD in page 8, PT in 11; PAE PDPT in 8, PD0 (identity) in 9, PD1 (window) in 10, PT in 11 */
	u32 gpde = (u32)attr_bits(c->gpde, 0) & 0x67;
	if (c->gmode == 1) {
		u32 *pd = (u32 *)(npages + 0x8000), *pt = (u32 *)(npages + 0xB000);
		for (u32 k = 0; k < 1024; k++) pd[k] = (k << 22) | 0x87;
		pd[NWIN >> 22] = (GPA0 + 0xB000) | gpde;
		for (int k = 0; k < 8; k++) pt[k] = (GPA0 + 0x1000 * k) | ((u32)attr_bits(c->gpte[k], 0) & 0x67);
	} else if (c->gmode == 2) {
		u64 *pdpt = (u64 *)(npages + 0x8000), *pd0 = (u64 *)(npages + 0x9000), *pd1 = (u64 *)(npages + 0xA000),
		    *pt = (u64 *)(npages + 0xB000);
		pdpt[0] = (GPA0 + 0x9000) | 1; pdpt[1] = (GPA0 + 0xA000) | 1; pdpt[2] = pdpt[3] = 0;
		for (u32 k = 0; k < 512; k++) pd0[k] = ((u64)k << 21) | 0x87;
		pd1[0] = (GPA0 + 0xB000) | (attr_bits(c->gpde, 1) & 0x8000000000000067ULL);
		for (int k = 0; k < 8; k++) pt[k] = (GPA0 + 0x1000 * k) | (attr_bits(c->gpte[k], 1) & 0x8000000000000067ULL);
	}
	u32 off = c->acc == 2 ? 0x100 : 0;
	u32 addr = (c->gmode ? NWIN : GPA0) + 0x1000 * c->pg + off;
	/* the instruction at a fixed address (NPCODE: guest PDE 0, which svmref.py walks first) */
	u8 *ic = (u8 *)NPCODE;
	ic[0] = c->acc == 1 ? 0x89 : c->acc == 0 ? 0x8b : 0xff; ic[1] = c->acc == 2 ? 0xd1 : 0x01;
	ic[2] = 0x0f; ic[3] = 0x01; ic[4] = 0xd9; ic[5] = 0xf4;
	vmcb_flat(NPCODE);
	if (c->cpl) ring3();
	VM32(C_EXC) = 1 << 14;
	VM64(C_NP) = 1;
	VM64(C_NCR3) = hp ? (u32)npdpt : (u32)npd32;
	VM64(S_GPAT) = 0x0007040600070406ULL;
	svm_g[1] = addr;
	VM64(S_RAX) = 0xA5A5A5A5;
	u32 wp = c->wp ? 0x10000 : 0;
	if (c->gmode == 1) { VM64(S_CR0) = 0x80000011 | wp; VM64(S_CR4) = 0x10; VM64(S_CR3) = GPA0 + 0x8000; }
	if (c->gmode == 2) { VM64(S_CR0) = 0x80000011 | wp; VM64(S_CR4) = 0x20; VM64(S_CR3) = GPA0 + 0x8000;
	                     VM64(S_EFER) = SVME | (c->nxe ? 0x800 : 0); }
	run();
}

/* The outcome: EXITCODE (81h: completed; 4Eh: the guest's #PF; 400h: NPF), EXITINFO1/2, the value
   loaded (or the code's EAX), and the accessed/dirty bits of the guest and nested PTEs of the page. */
static void npc_out(const struct npc *c, u32 *o) {
	u32 code = (u32)VM64(C_CODE);
	o[0] = code;
	o[1] = code == 0x81 ? 0 : (u32)VM64(C_INFO1);
	o[2] = code == 0x81 ? 0 : (u32)(VM64(C_INFO1) >> 32);
	o[3] = code == 0x81 ? 0 : (u32)VM64(C_INFO2);
	o[4] = code == 0x81 && c->acc != 1 ? (u32)VM64(S_RAX) : 0;
	o[5] = *(u32 *)(npages + 0x1000 * c->pg);
	u32 ne = c->hmode == 2 ? (u32)npt64[c->pg] : npt32[c->pg];
	u32 ge = c->gmode == 2 ? (u32)((u64 *)(npages + 0xB000))[c->pg] : c->gmode == 1 ? ((u32 *)(npages + 0xB000))[c->pg] : 0;
	o[6] = ((ne >> 5) & 3) | (((ge >> 5) & 3) << 2);
}

static void npc_rand(struct npc *c, int qemu) {
	c->hmode = qemu ? 2 : 1 + frnd() % 2;
	c->gmode = frnd() % 3;
	c->wp = frnd() % 2; c->nxe = frnd() % 2; c->cpl = frnd() % 4 == 0; c->acc = frnd() % 3;
	c->pg = frnd() % 8;
	/* mostly present, writable, user; sometimes NX, A, D; rarely reserved */
	#define RA() ((u8)(((frnd() % 8) ? 1 : 0) | ((frnd() % 4) ? 2 : 0) | ((frnd() % 4) ? 4 : 0) | \
	                   ((frnd() % 4) ? 0 : 8) | ((frnd() % 2) ? 0x10 : 0) | ((frnd() % 2) ? 0x20 : 0) | ((frnd() % 16) ? 0 : 0x40)))
	c->npde = RA() | 1; c->ntab = RA() | 1; c->gpde = RA() | 1;
	if (frnd() % 8 == 0) c->npde &= ~1; if (frnd() % 8 == 0) c->ntab &= ~2;
	c->npde &= ~0x40; c->gpde &= ~0x40;
	for (int k = 0; k < 8; k++) { c->npte[k] = RA(); c->gpte[k] = RA(); }
	#undef RA
}

/* Nested-paging fuzzer (QEMU-compared, PAE host): `npf` random cases (default 300). */
static void t_npfuzz(void) {
	u32 n = param("npf", 300);
	fs_s = fuzz_seed(0x2DFA11E5);
	host_paging(2);
	for (u32 i = 0; i < n; i++) {
		struct npc c;
		npc_rand(&c, 1);
		u32 s = fs_s;
		npc_run(&c);
		fs_s = s;
		u32 o[7];
		npc_out(&c, o);
		kprintf("npf %d h%d g%d wp%d nx%d c%d a%d p%d: code=%x i1=%x:%x i2=%x v=%x m=%x ad=%x\n", i, c.hmode, c.gmode, c.wp, c.nxe,
		        c.cpl, c.acc, c.pg, o[0], o[2], o[1], o[3], o[4], o[5], o[6]);
	}
	host_paging(0);
}

/* ---------------- model-only: the reference tables of svmref.py ---------------- */

#include "svm_cases.h"

/* The SVM fuzzer without the TCG restrictions, each case against svmref.py: EXITCODE, EXITINFO1,
   nRIP - rIP (FFFFFFFFh: nRIP 0) and, for an exception delivered to the guest, its vector. */
static void m_svfx(void) {
	u64 save[25];
	for (int k = 6; k <= 30; k++) { save[k - 6] = gdt[k]; gdt[k] = 0; }
	u32 bad = 0, n = sizeof svfx / sizeof svfx[0];
	for (u32 i = 0; i < n; i++) {
		const struct svfx *x = &svfx[i];
		u32 k = fz_case(x->seed, 0);
		run();
		u32 code = (u32)VM64(C_CODE);
		u64 i1 = VM64(C_INFO1);
		u32 nrip = VM64(C_NRIP) ? (u32)VM64(C_NRIP) - (u32)VM64(S_RIP) : 0xFFFFFFFF;
		u32 rip = (u32)VM64(S_RIP);
		u32 vec = code == 0x81 && rip >= (u32)svm_gisr && rip < (u32)svm_gisr + 4096 ? (u32)VM64(S_RAX) : 0xFFFF;
		/* EXITINFO1 is compared only where the APM defines it */
		int i1def = code < 0x40 || code == 0x75 || code == 0x79 || code == 0x7B || code == 0x7C ||
		            code == 0x4A || code == 0x4B || code == 0x4C || code == 0x4D || code == 0x4E;
		if (code != x->code || (i1def && i1 != x->info1) || nrip != x->nrip || vec != x->vec) {
			bad++;
			kprintf("svfx %d %s: code=%x/%x i1=%x:%x/%x:%x nrip=%x/%x vec=%x/%x\n", i, fpool[k].n, code, x->code,
			        (u32)(i1 >> 32), (u32)i1, (u32)(x->info1 >> 32), (u32)x->info1, nrip, x->nrip, vec, x->vec);
		}
	}
	for (int k = 6; k <= 30; k++) gdt[k] = save[k - 6];
	iopm[0x80 >> 3] = iopm[0x88 >> 3] = 0;
	memset(msrpm, 0, 0x2000);
	kprintf("svmm.svfx: %d cases, %d differ from svmref.py\n", n, bad);
}

/* Nested-paging cases (32-bit and PAE hosts, every guest mode) against svmref.py's 2D walk. */
static void m_npx(void) {
	u32 bad = 0, n = sizeof npx / sizeof npx[0], open = 0;
	for (u32 i = 0; i < n; i++) {
		const struct npx *x = &npx[i];
		open += x->open;
		host_paging(x->c.hmode);
		npc_run(&x->c);
		u32 o[7];
		npc_out(&x->c, o);
		host_paging(0);
		int diff = 0;
		for (int j = 0; j < 7; j++) diff |= o[j] != x->o[j];
		if (diff) {
			bad++;
			kprintf("npx %d h%d g%d wp%d nx%d c%d a%d p%d: model", i, x->c.hmode, x->c.gmode, x->c.wp, x->c.nxe,
			        x->c.cpl, x->c.acc, x->c.pg);
			for (int j = 0; j < 7; j++) kprintf(" %x", o[j]);
			kputs(" ref");
			for (int j = 0; j < 7; j++) kprintf(" %x", x->o[j]);
			kputc('\n');
		}
	}
	/* `open`: cases whose outcome depends on a point the APM leaves open (svmref.py's documentation);
	   for them the check is consistency with the documented reading, not with the APM */
	kprintf("svmm.npx: %d cases, %d differ from svmref.py, %d depend on a reading the APM leaves open\n", n, bad, open);
}

/* ---------------- two CPUs (smp=2) ---------------- */

/* The application processor runs a guest (its own VMCB, its own SVM state) while the boot processor
   sends it IPIs: a fixed interrupt (the AP's INTR intercept: #VMEXIT 60h, taken by the AP's host
   after STGI), an NMI (61h) and an INIT (the INIT intercept, 63h, INIT pending until STGI, then the
   AP resets and waits for STARTUP). The guest counts in shared memory, so the BSP knows it runs; only
   the BSP prints. The AP starts from its own trampoline at 7000h. */
#define SAP_TRAMP 0x7000
__asm__(
	".code16\n.globl sap_tramp\nsap_tramp:\n"
	" cli\n movw %cs, %ax\n movw %ax, %ds\n"
	" lgdtl sap_gdtr - sap_tramp\n"
	" movl %cr0, %eax\n orl $1, %eax\n movl %eax, %cr0\n"
	" ljmpl $0x08, $sap_entry32\n"
	" .p2align 2\n.globl sap_gdtr\nsap_gdtr: .word 0\n .long 0\n"
	".globl sap_tramp_end\nsap_tramp_end:\n"
	".code32\nsap_entry32:\n"
	" movl $0x10, %eax\n movl %eax, %ds\n movl %eax, %es\n movl %eax, %fs\n movl %eax, %gs\n movl %eax, %ss\n"
	" movl sap_stack_top, %esp\n call svm_ap_main\n"
	"1: cli\n hlt\n jmp 1b\n");
extern char sap_tramp[], sap_tramp_end[], sap_gdtr[];
static u8 sap_stack[8192] __attribute__((aligned(16)));
u32 sap_stack_top;
static volatile u32 sap_started, sap_phase, sap_code[4], sap_intr, sap_nmi, sap_got;
static u8 *ap_vmcb, *ap_hsave, *ap_gcode, *ap_gstack;
static volatile u32 *gcount;

static int sap_hook(struct frame *f) {
	if (f->vec == 0x58) { sap_intr++; LR(0xB0) = 0; return 1; }
	if (f->vec == 2) { sap_nmi++; return 1; }
	return 0;
}

/* AP guest: inc dword [ecx]; pause; jmp back */
static void ap_guest_vmcb(void) {
	u8 *v = ap_vmcb;
	memset(v, 0, 4096);
	*(u32 *)(v + C_I3) = (1u << I_INTR) | (1u << I_NMI) | (1u << I_INIT);
	*(u32 *)(v + C_I4) = 3;
	*(u32 *)(v + C_ASID) = 2;
	*(u64 *)(v + C_IOPM) = (u32)iopm; *(u64 *)(v + C_MSRPM) = (u32)msrpm;
	*(u32 *)(v + C_VINT) = 1 << 24;   /* V_INTR_MASKING: the host's IF masks physical interrupts */
	u16 attr[4] = { 0xC93, 0xC9B, 0xC93, 0xC93 };
	u16 sel[4] = { KDATA, KCODE, KDATA, KDATA };
	for (int k = 0; k < 4; k++) {
		*(u16 *)(v + S_ES + 16 * k) = sel[k]; *(u16 *)(v + S_ES + 16 * k + 2) = attr[k];
		*(u32 *)(v + S_ES + 16 * k + 4) = 0xFFFFFFFF;
	}
	*(u32 *)(v + S_GDTR + 4) = sizeof gdt - 1; *(u64 *)(v + S_GDTR + 8) = (u32)gdt;
	*(u32 *)(v + S_IDTR + 4) = 0x7FF; *(u64 *)(v + S_IDTR + 8) = (u32)gidt;
	*(u64 *)(v + S_EFER) = SVME; *(u64 *)(v + S_CR0) = 0x11;
	*(u64 *)(v + S_DR7) = 0x400; *(u64 *)(v + S_DR6) = 0xFFFF0FF0; *(u64 *)(v + S_RFLAGS) = 2;
	*(u64 *)(v + S_RIP) = (u32)ap_gcode; *(u64 *)(v + S_RSP) = (u32)ap_gstack + 4080;
}

static void ap_vmrun(void) {
	__asm__ volatile("pushal\n movl %0, %%ecx\n movl %1, %%eax\n .byte 0x0f,0x01,0xd8\n popal"
	                 :: "m"(gcount), "m"(ap_vmcb) : "memory");
}

static volatile u32 sap_mode, sap_res[6];
static void svm_ap_np(void);
void svm_ap_main(void) {
	struct { u16 lim; u32 base; } __attribute__((packed)) id = { sizeof idt - 1, (u32)idt };
	__asm__ volatile("lidt %0" :: "m"(id));
	LR(0xF0) = 0x1FF; LR(0x80) = 0;
	if (sap_mode == 3) {   /* after the INIT of svm_ap_np: what INIT left */
		u64 pat = rdmsr(0x277);
		sap_res[0] = (u32)pat; sap_res[1] = (u32)(pat >> 32); sap_res[2] = (u32)rdmsr(0x48);
		sap_res[3] = (u32)rdmsr(EFER_MSR); sap_res[4] = RDCR(0);
		sap_res[5] = 1;
		return;
	}
	wrmsr(EFER_MSR, rdmsr(EFER_MSR) | SVME);
	wrmsr(VM_HSAVE, (u32)ap_hsave);
	if (sap_mode == 2) { svm_ap_np(); return; }
	sap_started = 1;
	for (int k = 0; k < 3; k++) {
		ap_guest_vmcb();
		__asm__ volatile(".byte 0x0f,0x01,0xdd\n sti" ::: "memory");   /* CLGI; host IF = 1 */
		sap_phase = k + 1;
		ap_vmrun();
		sap_code[k] = *(u32 *)(ap_vmcb + C_CODE);
		sap_got = k + 1;
		__asm__ volatile(".byte 0x0f,0x01,0xdc" ::: "memory");   /* STGI: the pending event is taken here */
		for (volatile int d = 0; d < 200; d++) {}
		__asm__ volatile("cli");
		sap_phase = 10 + k;
	}
}

static void sap_wait(volatile u32 *p, u32 v) { for (u32 k = 0; k < 20000000 && *p != v; k++) cpu_relax(); }

void test_svm_smp(void) {
	if (!has_feature(0x80000001, 0, 2, 2)) { kputs("svm: not available\n"); return; }
	svm_setup();
	ap_vmcb = page_alloc(1); ap_hsave = page_alloc(1); ap_gcode = page_alloc(1); ap_gstack = page_alloc(1);
	gcount = (volatile u32 *)page_alloc(1);
	static const u8 gc[] = { 0xff, 0x01, 0xf3, 0x90, 0xeb, 0xfa };   /* 1: inc dword [ecx]; pause; jmp 1b */
	for (u32 k = 0; k < sizeof gc; k++) ap_gcode[k] = gc[k];
	int (*old_hook)(struct frame *) = trap_hook;
	trap_hook = sap_hook;
	sap_stack_top = (u32)sap_stack + sizeof sap_stack;
	memcpy((void *)SAP_TRAMP, sap_tramp, sap_tramp_end - sap_tramp);
	*(volatile u16 *)(SAP_TRAMP + (sap_gdtr - sap_tramp)) = sizeof gdt - 1;
	*(volatile u32 *)(SAP_TRAMP + (sap_gdtr - sap_tramp) + 2) = (u32)gdt;
	LR(0xF0) = 0x1FF;
	ipi(1, 0xC500); for (volatile int d = 0; d < 1000; d++) {}
	ipi(1, 0x8500); for (volatile int d = 0; d < 1000; d++) {}
	ipi(1, 0x600 | (SAP_TRAMP >> 12));
	sap_wait(&sap_started, 1);
	static const u32 ev[3] = { 0x4058, 0x4400, 0x4500 };   /* fixed vector 58h, NMI, INIT */
	for (int k = 0; k < 3; k++) {
		sap_wait(&sap_phase, k + 1);
		*gcount = 0;
		sap_wait(gcount, 1);   /* the guest runs (its counter moves) */
		for (u32 n = 0; n < 20000000 && *gcount < 50; n++) cpu_relax();
		ipi(1, ev[k]);
		if (k < 2) sap_wait(&sap_phase, 10 + k);
		else for (volatile int d = 0; d < 200000; d++) {}
	}
	sap_wait(&sap_got, 3);   /* the AP has stored the INIT exit code (then takes the INIT at STGI) */
	/* the INIT exit (sap_code[2]) is model-only (test_svm_smp_model): TCG resets the CPU in guest mode */
	kprintf("svm.smp: started=%d intr_exit=%x nmi_exit=%x ap_intr=%d ap_nmi=%d phase=%d\n", sap_started,
	        sap_code[0], sap_code[1], sap_intr, sap_nmi, sap_phase);
	/* the INIT was taken after the AP's STGI: hand the AP back to t_smp.c's AP loop, which the
	   model-only SMP tests use */
	trap_hook = old_hook;
	smp_restart_ap();
}

/* ---------------- model-only: what TCG lacks ---------------- */

#define VM_CR_LOCK 8
#define VM_CR_SVMDIS 0x10
#define SVM_KEY 0xC0010118
#define TSC_RATIO 0xC0000104

static int try_wr(u32 n, u64 v) { return TRY(wrmsr(n, v)); }

/* CPUID (APM vol. 3, E.4.9): SVM revision 1, 8000h ASIDs, the implemented feature bits */
static void m_cpuid(void) {
	u32 r[4];
	cpuid(0x80000001, 0, r);
	kprintf("svmm.cpuid.80000001: svm=%d skinit=%d\n", (r[2] >> 2) & 1, (r[2] >> 12) & 1);
	cpuid(0x8000000A, 0, r);
	kprintf("svmm.cpuid.8000000a: %x %x %x %x\n", r[0], r[1], r[2], r[3]);
}

/* VM_CR, SVM_KEY (15.30.1, 15.31): reserved bits #GP; SVMDIS makes EFER.SVME MBZ and cannot be set
   while SVME = 1; LOCK freezes LOCK and SVMDIS until the key is written. STGI executes with
   SVME = 0 (SVM-Lock and SKINIT are supported). */
static void m_vmcr(void) {
	u64 efer = rdmsr(EFER_MSR);
	kprintf("svmm.vmcr: reset=%x rsvd=%x\n", (u32)rdmsr(VM_CR), try_wr(VM_CR, 0x20));
	kprintf("svmm.vmcr.svmdis.svme1: %x\n", try_wr(VM_CR, VM_CR_SVMDIS));
	wrmsr(EFER_MSR, efer & ~(u64)SVME);
	int stgi_v = TRY(stgi());
	wrmsr(SVM_KEY, 0x1234);
	kprintf("svmm.svmkey.read: %x\n", (u32)rdmsr(SVM_KEY));
	wrmsr(VM_CR, VM_CR_SVMDIS | VM_CR_LOCK);
	int e1 = try_wr(EFER_MSR, efer | SVME);
	wrmsr(VM_CR, 0);   /* ignored for LOCK/SVMDIS while locked */
	u32 a = (u32)rdmsr(VM_CR);
	wrmsr(SVM_KEY, 0x9999);   /* wrong key: ignored */
	u32 b = (u32)rdmsr(VM_CR);
	wrmsr(SVM_KEY, 0x1234);   /* the key: LOCK clears */
	u32 c = (u32)rdmsr(VM_CR);
	wrmsr(VM_CR, 0);
	int e2 = try_wr(EFER_MSR, efer | SVME);
	kprintf("svmm.vmcr.lock: efer_gp=%x locked=%x wrongkey=%x unlocked=%x efer_ok=%x stgi_nosvme=%x\n", e1, a, b, c, e2, stgi_v);
	/* IGNNE, SMM_CTL (write-only), TSC_RATIO reset and reserved bits, HSAVE above MAXPHYADDR */
	u64 v;
	int r1 = TRY(v = rdmsr(0xC0010116));
	kprintf("svmm.msrs: ignne=%x ignne_rsvd=%x smmctl_rd=%x tscratio=%x:%x tscratio_rsvd=%x hsave_max=%x\n",
	        (u32)rdmsr(0xC0010115), try_wr(0xC0010115, 2), r1, (u32)(rdmsr(TSC_RATIO) >> 32), (u32)rdmsr(TSC_RATIO),
	        try_wr(TSC_RATIO, 1ULL << 40), try_wr(VM_HSAVE, 1ULL << 48));
	(void)v;
}

/* nRIP (15.7.1) and decode assists (15.8) for the intercepts of icases (and the IOIO address size
   and segment fields): EXITINFO1 and nRIP - rIP. */
static void m_nrip(void) {
	for (u32 k = 0; k < sizeof icases / sizeof icases[0]; k++) {
		const struct icase *c = &icases[k];
		prep_case(c, 1);
		run();
		kprintf("%s: code=%x i1=%x:%x nrip=%x\n", nm3("svmm.nrip.", c->name, ""), (u32)VM64(C_CODE),
		        (u32)(VM64(C_INFO1) >> 32), (u32)VM64(C_INFO1), (u32)VM64(C_NRIP) - (u32)VM64(S_RIP));
	}
	/* IOIO: address size (16-bit with 67h) and the segment of OUTS (FS override) */
	iopm[0x80 >> 3] = 1;
	static const struct { const char *n; u8 code[4]; int len; } io[] = {
		{ "in.a16", { 0x67, 0xe4, 0x80 }, 3 }, { "outs.fs", { 0x64, 0x6e }, 2 }, { "ins.a16", { 0x67, 0x6c }, 2 },
		{ "repins", { 0xf3, 0x6d }, 2 },
	};
	for (u32 k = 0; k < sizeof io / sizeof io[0]; k++) {
		vmcb_flat(gput(io[k].code, io[k].len));
		VM32(C_I3) |= 1u << I_IOIO; svm_g[2] = 0x80; svm_g[1] = 1; svm_g[6] = svm_g[7] = (u32)gdata;
		run();
		kprintf("%s: code=%x i1=%x nrip=%x\n", nm3("svmm.ioio.", io[k].n, ""), (u32)VM64(C_CODE), (u32)VM64(C_INFO1),
		        (u32)VM64(C_NRIP) - (u32)VM64(S_RIP));
	}
	iopm[0x80 >> 3] = 0;
	/* exceptions: nRIP only for INT3, INTO, BOUND (15.7.1) */
	static const struct { const char *n; u8 code[6]; int len; u32 ecx; } ex[] = {
		{ "bp", { 0xcc }, 1, 0 }, { "of", { 0xb0, 0x7f, 0x04, 0x01, 0xce }, 5, 0 }, { "br", { 0x62, 0x01 }, 2, 1 },
		{ "ud", { 0x0f, 0x0b }, 2, 0 },
	};
	*(u32 *)gdata = 10; *(u32 *)(gdata + 4) = 20;
	for (u32 k = 0; k < sizeof ex / sizeof ex[0]; k++) {
		vmcb_flat(gput(ex[k].code, ex[k].len));
		VM32(C_EXC) = 0xFFFFFFFF; VM64(S_RAX) = 30; svm_g[1] = ex[k].ecx ? (u32)gdata : 0;
		run();
		kprintf("%s: code=%x nrip=%x\n", nm3("svmm.excnrip.", ex[k].n, ""), (u32)VM64(C_CODE),
		        VM64(C_NRIP) ? (u32)VM64(C_NRIP) - (u32)gcode : 0xFFFFFFFF);
	}
}

/* Decode assist of a data #PF / NPF (15.8.4): the guest instruction bytes at CS:rIP; none for an
   instruction-fetch fault. */
static void m_bytes(void) {
	gpd = gpd ? gpd : page_alloc(1);
	build_gpt32();
	vmcb_flat(G(0x8b, 0x81, 0x00, 0x10, 0x00, 0x00));   /* mov eax,[ecx+1000h] */
	VM32(C_EXC) = 1 << 14; svm_g[1] = GWIN;
	VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd;
	run();
	kprintf("svmm.bytes.pf: code=%x b0=%x:%x b1=%x:%x\n", (u32)VM64(C_CODE), VM32(C_BYTES + 4), VM32(C_BYTES),
	        VM32(C_BYTES + 12), VM32(C_BYTES + 8));
	vmcb_flat(G(0xff, 0xd1));   /* call ecx -> fetch from the not-present page */
	VM32(C_EXC) = 1 << 14; svm_g[1] = GWIN + 0x1000;
	VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd;
	VM32(C_BYTES) = 0xAAAAAAAA;
	run();
	kprintf("svmm.bytes.fetch: code=%x i1=%x count=%x\n", (u32)VM64(C_CODE), (u32)VM64(C_INFO1), VM8(C_BYTES));
}

/* PAUSE filter (15.14.4): count 3 lets three PAUSEs through and intercepts the fourth; count 0
   intercepts the first; the threshold reloads the count after a long gap. */
static void m_pause(void) {
	u8 code[32];
	for (int c = 0; c < 3; c++) {
		/* c 0, 1: back-to-back PAUSEs; c 2: PAUSE, NOP, NOP (3 cycles apart, above the threshold 1) */
		int st = c == 2 ? 4 : 2;
		for (int k = 0; k < 8; k++) { code[st * k] = 0xf3; code[st * k + 1] = 0x90; code[st * k + 2] = 0x90; code[st * k + 3] = 0x90; }
		vmcb_flat(gput(code, 8 * st));
		VM32(C_I3) |= 1u << I_PAUSE;
		VM16(C_PCNT) = c == 0 ? 3 : c == 1 ? 0 : 3;
		if (c == 2) { VM16(C_PTHR) = 1; }   /* every PAUSE more than 1 cycle after the previous one reloads */
		run();
		kprintf("svmm.pause.%d: code=%x rip=%x\n", c, (u32)VM64(C_CODE), (u32)VM64(S_RIP) - (u32)gcode);
	}
}

/* (a * r) >> 32 for the 8.32 fixed-point ratio r */
static u64 mulr(u64 a, u64 r) {
	u64 ah = a >> 32, al = (u32)a, rh = r >> 32, rl = (u32)r;
	return ((ah * rh) << 32) + ah * rl + al * rh + ((al * rl) >> 32);
}

/* TSC_OFFSET and TSC_RATIO (15.5.1, 15.30.5): RDTSC in the guest reads ratio * host TSC + offset. */
static void m_tsc(void) {
	u64 ratios[3] = { 0x100000000ULL, 0x200000000ULL, 0x080000000ULL };
	for (int k = 0; k < 3; k++) {
		wrmsr(TSC_RATIO, ratios[k]);
		vmcb_flat(G(0x0f, 0x31));
		VM64(C_TSCOFF) = 0x100000000ULL;
		u32 lo, hi;
		__asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
		u64 h0 = ((u64)hi << 32) | lo;
		run();
		__asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
		u64 h1 = ((u64)hi << 32) | lo;
		u64 g = ((u64)svm_g[2] << 32) | (u32)VM64(S_RAX);
		u64 lo_b = mulr(h0, ratios[k]) + 0x100000000ULL;
		u64 hi_b = mulr(h1, ratios[k]) + 0x100000000ULL;
		kprintf("svmm.tsc.%d: in_range=%d host_after_unchanged=%d\n", k, g >= lo_b && g <= hi_b, h1 > h0 && h1 - h0 < 0x100000);
	}
	wrmsr(TSC_RATIO, 0x100000000ULL);
}

/* Virtual GIF (15.33.2): with V_GIF_ENABLE the guest's CLGI/STGI change VGIF, which masks only virtual
   interrupts. */
static void m_vgif(void) {
	for (int c = 0; c < 3; c++) {
		/* c 0: CLGI then a pending virtual interrupt is masked; 1: CLGI, STGI: taken; 2: without
		   V_GIF_ENABLE CLGI clears the real GIF (the virtual interrupt waits) */
		vmcb_flat(c == 1 ? G(0x0f, 0x01, 0xdd, 0x0f, 0x01, 0xdc, 0x90) : G(0x0f, 0x01, 0xdd, 0x90, 0x90));
		VM32(C_VINT) = 0x00030100 | (c < 2 ? (1 << 25) | (1 << 9) : 0); VM32(C_VINT + 4) = 0x52;
		VM64(S_RFLAGS) = 0x202;
		VM32(C_VINT) &= ~0x100u;   /* V_IRQ raised by the second instruction: set it in the VMCB now, taken
		                              only after the CLGI because the first boundary has the shadow */
		VM32(C_VINT) |= 0x100;
		VM32(C_INTST) = 1;   /* interrupt shadow on the first instruction (the CLGI) */
		run();
		kprintf("svmm.vgif.%d: code=%x rax=%x vint=%x\n", c, (u32)VM64(C_CODE), (u32)VM64(S_RAX), VM32(C_VINT) & 0x3FF);
	}
}

/* Event injection details TCG does not have: EV decides the error code (15.20), injected #BP and soft
   INT check the gate DPL and push nRIP, vector 31 is an exception vector. */
static void m_inject(void) {
	static const struct { const char *n; u32 ev; u32 err; int cpl3; u32 nrip_add; } k[] = {
		{ "gp.noev", 0x8000030D, 0x1234, 0, 0 },
		{ "ud.ev", 0x80000B06, 0x55, 0, 0 },
		{ "soft.nrip", 0x80000441, 0, 0, 2 },
		{ "bp.dpl0", 0x80000303, 0, 1, 1 },
		{ "soft.dpl0", 0x80000405, 0, 1, 2 },
		{ "vec31", 0x8000031F, 0, 0, 0 },
		{ "intr.notpresent", 0x80000060, 0, 0, 0 },
	};
	u64 *gi = (u64 *)gidt;
	u64 s3 = gi[3], s5 = gi[5], s60 = gi[0x60];
	gi[3] = gate_desc(KCODE, (u32)svm_gisr + 16 * 3, 0x8E);
	gi[5] = gate_desc(KCODE, (u32)svm_gisr + 16 * 5, 0x8E);
	gi[0x60] = gate_desc(KCODE, (u32)svm_gisr + 16 * 0x60, 0x0E);   /* not present */
	for (u32 i = 0; i < sizeof k / sizeof k[0]; i++) {
		u32 rip = G(0x90, 0x90);
		vmcb_flat(rip);
		VM32(C_EXC) = 0xFFFFFFFF & ~(1u << 13) & ~(1u << 11);
		if (streq(k[i].n, "intr.notpresent")) VM32(C_EXC) = 1u << 11;
		if (k[i].cpl3) ring3();
		VM32(C_INJ) = k[i].ev; VM32(C_INJ + 4) = k[i].err;
		VM64(C_NRIP) = rip + k[i].nrip_add;
		u32 top = (u32)gstack + 4096 - 16;
		run();
		/* the depth on the guest stack (a CPL-3 guest's #GP is taken on the ring-0 stack: 0 here) */
		u32 sp = (u32)VM64(S_RSP), depth = k[i].cpl3 ? 0 : top - sp;
		kprintf("%s: code=%x rax=%x depth=%x", nm3("svmm.inject.", k[i].n, ""), (u32)VM64(C_CODE), (u32)VM64(S_RAX), depth);
		if (VM64(C_CODE) == 0x81 && !k[i].cpl3 && (depth == 12 || depth == 16)) {
			u32 *f = (u32 *)sp;
			int e = depth == 16;
			kprintf(" err=%x eip=%x", e ? f[0] : 0, f[e] - rip);
		} else if (VM64(C_CODE) == 0x81 && k[i].cpl3) {
			u32 *f = (u32 *)sp;   /* the #GP frame on the ring-0 stack: error code, EIP, CS */
			kprintf(" err=%x eip=%x cs=%x", f[0], f[1] - rip, f[2]);
		}
		x64("i1", VM64(C_INFO1)); x64("ii", VM64(C_EII));
		kputc('\n');
	}
	gi[3] = s3; gi[5] = s5; gi[0x60] = s60;
}

/* Consistency checks TCG does not make (15.5.1, 15.25.4) */
static void m_consist(void) {
	static const char *n[] = { "dr6.hi", "dr7.hi", "tlbctl.rsvd", "tlbctl.flushasid", "pae.pdpte.rsvd", "np.ncr3.mbz",
	                           "np.gpat", "np.ok", "cr3.long.mbz" };
	gpdpt = gpdpt ? gpdpt : page_alloc(1);
	for (int c = 0; c < 9; c++) {
		vmcb_flat(G(0x90));
		switch (c) {
		case 0: VM64(S_DR6) = 0x1FFFF0FF0ULL; break;
		case 1: VM64(S_DR7) = 0x100000400ULL; break;
		case 2: VM8(C_TLBCTL) = 2; break;
		case 3: VM8(C_TLBCTL) = 3; break;
		case 4: gpdpt[0] = 0x1 | 0x4; gpdpt[1] = gpdpt[2] = gpdpt[3] = 0;
		        VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x20; VM64(S_CR3) = (u32)gpdpt; break;
		case 5: case 6: case 7:
			VM64(C_NP) = 1; VM64(C_NCR3) = c == 5 ? 0x1000000000000ULL : (u32)npdpt;
			VM64(S_GPAT) = c == 6 ? 0x0007040600070402ULL : 0x0007040600070406ULL;
			break;
		case 8: VM64(S_EFER) = SVME | 0x100; VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x20;
		        VM64(S_CR3) = 0x1000000000000ULL; break;
		}
		if (c >= 5 && c <= 7) { host_paging(2); build_nested(1); }
		run();
		if (c >= 5 && c <= 7) host_paging(0);
		kprintf("%s: code=%x\n", nm3("svmm.consist.", n[c], ""), (u32)VM64(C_CODE));
	}
}

/* VMSAVE/VMLOAD of KernelGsBase, LSTAR, CSTAR and SFMASK; VMLOAD in a guest without the intercept
   works on the system-physical rAX; with VMSAVE/VMLOAD virtualization enabled (never recognized
   outside a 64-bit host) it exits with its code (15.33.1). */
static void m_vmload(void) {
	u8 *w = vmcb2;
	memset(w, 0, 4096);
	*(u64 *)(w + 0x620) = 0xFFFF800012345678ULL;   /* KernelGsBase */
	*(u64 *)(w + 0x608) = 0x1111222233334444ULL;   /* LSTAR */
	*(u64 *)(w + 0x610) = 0x5555666677778888ULL;   /* CSTAR */
	*(u64 *)(w + 0x618) = 0x0000000000047700ULL;   /* SFMASK */
	*(u16 *)(w + S_FS) = KDATA; *(u16 *)(w + S_FS + 2) = 0xC93; *(u32 *)(w + S_FS + 4) = 0xFFFFFFFF;
	*(u16 *)(w + S_GS) = KDATA; *(u16 *)(w + S_GS + 2) = 0xC93; *(u32 *)(w + S_GS + 4) = 0xFFFFFFFF;
	*(u16 *)(w + S_TR) = TSS_MAIN; *(u16 *)(w + S_TR + 2) = 0x8B; *(u32 *)(w + S_TR + 4) = sizeof(struct tss32) - 1;
	*(u64 *)(w + S_TR + 8) = (u32)&tss_main;
	*(u16 *)(w + S_LDTR + 2) = 0x82;
	u32 a = (u32)w;
	__asm__ volatile(".byte 0x0f,0x01,0xda" :: "a"(a) : "memory");
	kprintf("svmm.vmload.msrs: kgs=%x:%x lstar=%x:%x cstar=%x:%x sfmask=%x\n", (u32)(rdmsr(0xC0000102) >> 32),
	        (u32)rdmsr(0xC0000102), (u32)(rdmsr(0xC0000082) >> 32), (u32)rdmsr(0xC0000082),
	        (u32)(rdmsr(0xC0000083) >> 32), (u32)rdmsr(0xC0000083), (u32)rdmsr(0xC0000084));
	wrmsr(0xC0000102, 0); wrmsr(0xC0000082, 0); wrmsr(0xC0000083, 0); wrmsr(0xC0000084, 0);
	for (int c = 0; c < 2; c++) {
		memset(gdata, 0, 4096);
		vmcb_flat(G(0x0f, 0x01, 0xdb));   /* VMSAVE in the guest, not intercepted */
		VM32(C_I4) &= ~(1u << I4_VMSAVE);
		if (c) VM32(C_VIRT) = 2;
		VM64(S_RAX) = (u32)gdata;
		run();
		kprintf("svmm.vmsave.guest.%d: code=%x saved_tr=%x\n", c, (u32)VM64(C_CODE), *(u16 *)(gdata + S_TR));
	}
}

/* Host TLB entries survive a VMRUN/#VMEXIT pair (the guest runs in its own ASID); TLB_CONTROL 01h
   flushes them; INVLPGA with ASID 0 invalidates a host translation (15.16). The host maps a page,
   changes the PTE without INVLPG, and reads it again after a guest has run. */
static void m_tlb(void) {
	static u32 *pd, *pt;
	if (!pd) { pd = page_alloc(1); pt = page_alloc(1); }
	for (u32 k = 0; k < 1024; k++) pd[k] = (k << 22) | 0x83;
	pd[GWIN >> 22] = (u32)pt | 3;
	u8 *p0 = page_alloc(1), *p1 = page_alloc(1);
	*(u32 *)p0 = 0xAAAA0000; *(u32 *)p1 = 0xBBBB1111;
	WRCR(4, RDCR(4) | 0x10);
	WRCR(3, (u32)pd);
	WRCR(0, RDCR(0) | 0x80000000);
	/* the last page of the window: a TLB slot (1024 entries, direct mapped by page number) that no
	   other page this code touches shares */
	u32 lin = GWIN + 0x3FF000;
	for (int c = 0; c < 4; c++) {
		pt[0x3FF] = (u32)p0 | 3;
		invlpg(lin);
		u32 before = *(volatile u32 *)lin;
		pt[0x3FF] = (u32)p1 | 3;   /* no INVLPG: the stale translation stays */
		vmcb_flat(G(0x90));
		if (c == 1) VM8(C_TLBCTL) = 1;
		if (c < 3) run();      /* c 3: no guest at all */
		if (c == 2) __asm__ volatile(".byte 0x0f,0x01,0xdf" :: "a"(lin), "c"(0) : "memory");   /* INVLPGA ASID 0 */
		u32 after = *(volatile u32 *)lin;
		kprintf("svmm.tlb.%d: before=%x after=%x\n", c, before, after);
	}
	WRCR(0, RDCR(0) & ~0x80000000u);
}

/* INIT (15.21.8, 15.28): held while GIF = 0; the INIT intercept leaves it pending (#VMEXIT 63h);
   with VM_CR.R_INIT it becomes #SX (vector 30, error code 1), in the host or, unintercepted, in the
   guest (where the #SX intercept catches it). */
volatile u32 sx_n, sx_err;
/* #SX pushes an error code, which the generic stubs do not expect for vector 30 */
__asm__(".globl sx_isr\nsx_isr: incl sx_n\n popl sx_err\n iret\n");
extern char sx_isr[];
static void m_init(void) {
	u64 save30 = idt[30];
	set_idt(30, (u32)sx_isr, 0x8E);
	wrmsr(VM_CR, 2);   /* R_INIT */
	sx_n = 0;
	clgi();
	LR(0x310) = 0; LR(0x300) = 0x4500;   /* INIT to APIC ID 0 (this CPU) */
	settle();
	u32 held = sx_n;
	stgi();
	settle();
	kprintf("svmm.init.host: gif0=%d after_stgi=%d err=%x\n", held, sx_n, sx_err);
	/* guest with the INIT intercept: #VMEXIT(INIT), INIT pending; STGI in the host: #SX */
	sx_n = 0;
	vmcb_flat(G(0x90, 0x90, 0x90));
	VM32(C_I3) |= 1u << I_INIT;
	clgi();
	LR(0x310) = 0; LR(0x300) = 0x4500;
	settle();
	svm_vmcb_pa = (u32)vmcb; svm_vmrun_raw();
	u32 code = (u32)VM64(C_CODE), n0 = sx_n;
	stgi();
	settle();
	kprintf("svmm.init.icpt: code=%x sx_before_stgi=%d sx=%d\n", code, n0, sx_n);
	/* guest without the intercept: #SX in the guest, intercepted */
	sx_n = 0;
	vmcb_flat(G(0x90, 0x90, 0x90));
	VM32(C_EXC) = 1u << 30;
	clgi();
	LR(0x310) = 0; LR(0x300) = 0x4500;
	settle();
	svm_vmcb_pa = (u32)vmcb; svm_vmrun_raw();
	stgi();
	kprintf("svmm.init.guest: code=%x i1=%x host_sx=%d\n", (u32)VM64(C_CODE), (u32)VM64(C_INFO1), sx_n);
	wrmsr(VM_CR, 0);
	idt[30] = save30;
}

/* SMI (15.22, table 15-14): held while GIF = 0; the SMI intercept exits (62h, EXITINFO1 bit 0 = 1)
   with the SMI still pending, taken by the host after STGI. The SMM handler counts and returns. */
static void m_smi(void) {
	u8 *h = (u8 *)0xA8000;
	static const u8 smh[] = { 0x66, 0xff, 0x06, 0x00, 0x61, 0x0f, 0xaa };   /* inc dword [6100h]; rsm */
	for (u32 k = 0; k < sizeof smh; k++) h[k] = smh[k];
	volatile u32 *cnt = (volatile u32 *)0x6100;
	*cnt = 0;
	clgi();
	outb(0xB2, 0);
	u32 held = *cnt;
	stgi();
	settle();
	kprintf("svmm.smi.host: gif0=%d after_stgi=%d\n", held, *cnt);
	*cnt = 0;
	vmcb_flat(G(0xe6, 0xb2, 0x90, 0x90));   /* out 0b2h,al: an SMI at the next boundary */
	VM32(C_I3) |= 1u << I_SMI;
	clgi();
	svm_vmcb_pa = (u32)vmcb; svm_vmrun_raw();
	u32 code = (u32)VM64(C_CODE), i1 = (u32)VM64(C_INFO1), n0 = *cnt;
	stgi();
	settle();
	kprintf("svmm.smi.icpt: code=%x i1=%x rip=%x smm_before_stgi=%d smm=%d\n", code, i1, (u32)VM64(S_RIP) - (u32)gcode, n0, *cnt);
	*cnt = 0;
	vmcb_flat(G(0xe6, 0xb2, 0x90, 0x90));
	VM32(C_VINT) = 0x00030005; VM32(C_VVEC) = 0x41;   /* V_TPR 5, V_INTR_PRIO 3 (no V_IRQ) */
	run();
	kprintf("svmm.smi.guest: code=%x smm=%d\n", (u32)VM64(C_CODE), *cnt);
	/* the SVM fields of the AMD64 state-save map (SMBASE A0000h; APM vol. 2, table 10-1, 15.22): SVM
	   Guest, VMCB address, virtual interrupt, and the nested-paging context (guest PAT, host EFER, CR4,
	   nCR3, CR0), 0 outside guest mode; SMM entry and RSM keep EFER.SVME */
#define SV(o) (*(volatile u32 *)(0xA0000 + (o)))
	kprintf("svmm.smi.save.guest: guest=%x:%x vmcb_ok=%d vint=%x:%x efer=%x hefer=%x hcr0=%x hcr4=%x gpat=%x hcr3_ok=%d\n",
	        SV(0xFED8), SV(0xFEDC), SV(0xFEE0) == (u32)vmcb && SV(0xFEE4) == 0, SV(0xFEE8), SV(0xFEEC), SV(0xFED0),
	        SV(0xFF28), SV(0xFF40), SV(0xFF30), SV(0xFF20), SV(0xFF38) == RDCR(3) && SV(0xFF3C) == 0);
	*cnt = 0;
	clgi();
	outb(0xB2, 0);
	stgi();
	settle();
	kprintf("svmm.smi.save.host: smm=%d guest=%x vmcb=%x hefer=%x efer_svme=%x\n", *cnt, SV(0xFED8), SV(0xFEE0),
	        SV(0xFF28), (u32)rdmsr(EFER_MSR) & SVME);
	/* nested paging (host 32-bit paging, identity nested tables): the SMM handler runs on physical
	   addresses (nested paging is off in SMM) and RSM resumes the guest under nested paging */
	*cnt = 0;
	host_paging(1);
	build_nested(0);
	vmcb_flat(G(0xe6, 0xb2, 0x90, 0x90));
	VM64(C_NP) = 1; VM64(C_NCR3) = (u32)npd32; VM64(S_GPAT) = 0x0007040600070406ULL;
	run();
	u32 hcr4 = RDCR(4), hcr3 = RDCR(3);
	host_paging(0);
	/* FF38h is the host's CR3 ("SVM Host CR3", table 10-1), not nCR3 */
	kprintf("svmm.smi.save.np: code=%x smm=%d guest=%x gpat=%x:%x hcr3_ok=%d hefer=%x hcr0=%x hcr4_ok=%d\n",
	        (u32)VM64(C_CODE), *cnt, SV(0xFED8), SV(0xFF20), SV(0xFF24), SV(0xFF38) == hcr3 && SV(0xFF3C) == 0,
	        SV(0xFF28), SV(0xFF40), SV(0xFF30) == hcr4);
#undef SV
}

/* SKINIT (15.27.6): the INIT-like state, EAX = SLB base, EDX = signature, ESP = SLB + 64 KiB, EFER = 0,
   VM_CR.DPD/R_INIT/DIS_A20M, GIF = 0, the jump to SLB + entry; the SL stub records the state and
   returns to the kernel (no TPM: nothing else happens). */
#define SLB 0x30000
static volatile u32 skres[12];
static struct jmpbuf skjb;
static struct { u16 lim; u32 base; } __attribute__((packed)) sk_gdtr, sk_idtr;
__asm__(
	".globl sk_stub\nsk_stub: movl $sk_cont, %ecx\n jmp *%ecx\n.globl sk_stub_end\nsk_stub_end:\n"
	"sk_cont:\n"
	" movl %eax, %ss:skres\n movl %edx, %ss:skres+4\n movl %esp, %ss:skres+8\n"
	" pushfl\n popl %ecx\n movl %ecx, %ss:skres+12\n"
	" movl %cr0, %ecx\n movl %ecx, %ss:skres+16\n movl %cr4, %ecx\n movl %ecx, %ss:skres+20\n"
	" movl $0xC0000080, %ecx\n rdmsr\n movl %eax, %ss:skres+24\n"
	" movl $0xC0010114, %ecx\n rdmsr\n movl %eax, %ss:skres+28\n"
	" movw %cs, %ax\n movw %ax, %ss:skres+32\n movw %ss, %ax\n movw %ax, %ss:skres+36\n"
	" movl %ebx, %ss:skres+40\n movl %esi, %ss:skres+44\n"
	" lgdt %ss:sk_gdtr\n lidt %ss:sk_idtr\n"
	" ljmp $0x08, $1f\n"
	"1: movl $0x10, %eax\n movl %eax, %ds\n movl %eax, %es\n movl %eax, %fs\n movl %eax, %gs\n movl %eax, %ss\n"
	" pushl $1\n pushl $skjb\n call klongjmp\n");
extern char sk_stub[], sk_stub_end[];
static void m_skinit(void) {
	memcpy((void *)(SLB + 0x100), sk_stub, sk_stub_end - sk_stub);
	*(u16 *)SLB = 0x100; *(u16 *)(SLB + 2) = 0x200;
	__asm__ volatile("sgdt %0\n sidt %1" : "=m"(sk_gdtr), "=m"(sk_idtr));
	u32 cr4 = RDCR(4);
	u64 efer = rdmsr(EFER_MSR);
	if (ksetjmp(&skjb) == 0) {
		__asm__ volatile("movl $0x12345678, %%ebx\n movl $0x87654321, %%esi\n .byte 0x0f,0x01,0xde"
		                 :: "a"(SLB + 0x1234) : "ebx", "esi", "memory");
	}
	reload_tr(TSS_MAIN);
	WRCR(4, cr4);
	wrmsr(EFER_MSR, efer);
	wrmsr(VM_CR, 0);
	stgi();
	kprintf("svmm.skinit: eax=%x edx_sig=%d esp=%x fl=%x cr0=%x cr4=%x efer=%x vmcr=%x cs=%x ss=%x ebx=%x esi=%x\n",
	        skres[0], skres[1] == 0x619 || skres[1] == 0x830F10, skres[2], skres[3], skres[4], skres[5], skres[6], skres[7],
	        skres[8] & 0xFFFF, skres[9] & 0xFFFF, skres[10], skres[11]);
	/* CPL 3: #GP; a guest with the SKINIT intercept: exit 86h */
	vmcb_flat(G(0x0f, 0x01, 0xde));
	VM32(C_I4) |= 1u << I4_SKINIT;
	run();
	kprintf("svmm.skinit.icpt: code=%x\n", (u32)VM64(C_CODE));
}

/* Guest state TCG does not keep: SPEC_CTRL (VMCB 2E0h) is the guest's in the guest, the host's after
   #VMEXIT; with nested paging the PAT register is G_PAT in the guest (15.25.4). */
static void m_swap(void) {
	wrmsr(0x48, 1);   /* host SPEC_CTRL: IBRS */
	vmcb_flat(G(0xb9, 0x48, 0, 0, 0, 0x0f, 0x32, 0x89, 0xc3, 0xb9, 0x77, 0x02, 0, 0, 0x0f, 0x32));   /* rdmsr 48h; ebx = eax; rdmsr 277h */
	VM64(0x6E0) = 4;   /* guest SSBD */
	host_paging(2); build_nested(1);
	VM64(C_NP) = 1; VM64(C_NCR3) = (u32)npdpt; VM64(S_GPAT) = 0x0606060606060606ULL;
	run();
	host_paging(0);
	kprintf("svmm.swap: code=%x guest_spec=%x guest_pat=%x host_spec=%x host_pat=%x:%x vmcb_spec=%x\n", (u32)VM64(C_CODE),
	        svm_g[3], (u32)VM64(S_RAX), (u32)rdmsr(0x48), (u32)(rdmsr(0x277) >> 32), (u32)rdmsr(0x277), (u32)VM64(0x6E0));
	wrmsr(0x48, 0);
}

/* GIF = 0 discards data-breakpoint #DB traps, not single-step traps (table 15-10). */
static volatile u32 db_n, db_dr6;
static int db_hook(struct frame *f) {
	if (f->vec == 1) { db_n++; db_dr6 = RDDR(6); f->eflags &= ~0x100u; return 1; }
	return 0;
}
static void m_gifdb(void) {
	trap_hook = db_hook;
	static volatile u32 var;
	WRDR(0, (u32)&var); WRDR(6, 0); WRDR(7, 0x30001);   /* DR0: write, 4 bytes, L0 */
	db_n = 0; clgi(); var = 1; stgi();
	u32 a = db_n;
	db_n = 0; var = 2;
	u32 b = db_n;
	WRDR(7, 0x400);
	db_n = 0;
	clgi();
	__asm__ volatile("pushfl\n orl $0x100, (%%esp)\n popfl\n nop\n" ::: "memory");
	stgi();
	kprintf("svmm.gif.db: data_gif0=%d data_gif1=%d step_gif0=%d dr6=%x\n", a, b, db_n, db_dr6 & 0x4000);
	trap_hook = 0;
}

/* What TCG does not intercept or check: the conditional MWAIT intercept after MONITOR, RDPRU,
   MCOMMIT (EFER.MCOMMIT), SVM instructions in virtual-8086 mode (#UD), #XM. */
static void m_misc(void) {
	vmcb_flat(G(0x0f, 0x01, 0xc8, 0x0f, 0x01, 0xc9));   /* monitor; mwait */
	VM32(C_I4) |= (1u << I4_MWAITC) | (1u << I4_MWAIT);
	VM64(S_RAX) = (u32)gdata;
	run();
	kprintf("svmm.mwait.cond: code=%x rip=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RIP) - (u32)gcode);
	vmcb_flat(G(0x0f, 0x01, 0xfd));
	VM32(C_I4) |= 1u << I4_RDPRU;
	run();
	kprintf("svmm.rdpru: code=%x\n", (u32)VM64(C_CODE));
	vmcb_flat(G(0xf3, 0x0f, 0x01, 0xfa));
	VM32(C_I5) |= 1u << 3;
	VM64(S_EFER) = SVME | 0x20000;
	run();
	kprintf("svmm.mcommit: code=%x\n", (u32)VM64(C_CODE));
	vmcb_flat(G(0x0f, 0x33));
	VM32(C_EXC) = 0xFFFFFFFF;
	run();
	kprintf("svmm.rdpmc.off: code=%x rip=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RIP) - (u32)gcode);
	*(u32 *)(gdata + 0x10) = 0x1F00;
	vmcb_flat(G(0x0f, 0xae, 0x10, 0x0f, 0x57, 0xc0, 0x0f, 0x5e, 0xc0));
	VM32(C_EXC) = 0xFFFFFFFF; VM64(S_CR4) = 0x600; VM64(S_RAX) = (u32)gdata + 0x10;
	run();
	kprintf("svmm.exc.xm: code=%x rip=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RIP) - (u32)gcode);
	vmcb_flat(G(0x0f, 0x01, 0xf6));   /* LMSW si changing only TS: the selective intercept anyway */
	VM32(C_I3) |= 1u << I_CR0SEL; svm_g[6] = 0x9;
	run();
	kprintf("svmm.lmsw.ts: code=%x\n", (u32)VM64(C_CODE));
	/* virtual-8086 mode: every SVM instruction is #UD (vol. 3) */
	u8 *c = (u8 *)RMBASE;
	c[0] = 0x0f; c[1] = 0x01; c[2] = 0xd8;
	vmcb_flat(0);
	VM32(C_EXC) = 0xFFFFFFFF; VM64(S_RFLAGS) = 0x20002;
	seg(S_CS, 0x2000, 0x0F3, 0xFFFF, RMBASE); seg(S_SS, 0x2000, 0x0F3, 0xFFFF, RMBASE);
	seg(S_DS, 0x2000, 0x0F3, 0xFFFF, RMBASE); seg(S_ES, 0x2000, 0x0F3, 0xFFFF, RMBASE);
	run();
	kprintf("svmm.vm86.vmrun: code=%x\n", (u32)VM64(C_CODE));
	/* nested paging with a 32-bit host and the host-paging-off check */
	t_np(1);
	t_np_hostpg0();
}

static void r_shadow(void);
void test_svm(void) {
	if (!has_feature(0x80000001, 0, 2, 2)) { kputs("svm: not available\n"); return; }
	svm_setup();
	if (param("svmr", 0)) {   /* development runs of one review regression: the setup they need */
		wrmsr(EFER_MSR, rdmsr(EFER_MSR) | SVME); wrmsr(VM_HSAVE, (u32)vmcb2); LR(0xF0) = 0x1FF;
		gpd = page_alloc(1); gpt = page_alloc(1);
		static const u8 smh[] = { 0x66, 0xff, 0x06, 0x00, 0x61, 0x0f, 0xaa };   /* inc dword [6100h]; rsm */
		for (u32 k = 0; k < sizeof smh; k++) ((u8 *)0xA8000)[k] = smh[k];
		return;
	}
	t_enable();
	t_cpl3();
	t_basic();
	t_intercepts();
	t_cr0sel();
	t_ioio();
	t_msr();
	t_exc();
	t_df();
	t_prio();
	t_inject();
	t_consist();
	t_vmloadsave();
	LR(0xF0) = 0x1FF; LR(0x80) = 0;
	trap_hook = svm_hook;
	t_gif();
	t_irq();
	trap_hook = 0;
	t_real();
	t_vm86();
	t_pm16();
	t_paged();
	t_np(2);
	t_fuzz();
	t_npfuzz();
	r_shadow();   /* TCG agrees: the shadow and RF as the intercept triggers (review regression) */
}

/* Model-only, smp=2 pass: an INIT the guest does not intercept resets the AP in a nested-paging guest;
   PAT and SPEC_CTRL, which VMRUN replaced by gPAT and the guest's SPEC_CTRL, are the host's again
   (INIT does not modify them; vol. 3 VMRUN: gPAT leaves the host PAT unchanged). The AP's host runs
   with 32-bit paging (identity) and its own PAT; the BSP sends INIT, then STARTUP into the SVM
   trampoline, where the AP reports. */
static void svm_ap_np(void) {
	WRCR(4, (RDCR(4) & ~0x20u) | 0x10);
	WRCR(3, (u32)hpd32);
	WRCR(0, RDCR(0) | 0x80000000u);
	wrmsr(0x277, 0x0606060606060606ULL);
	wrmsr(0x48, 0);
	ap_guest_vmcb();
	u8 *v = ap_vmcb;
	*(u32 *)(v + C_I3) = 0;   /* no INIT intercept */
	*(u64 *)(v + C_NP) = 1; *(u64 *)(v + C_NCR3) = (u32)npd32;
	*(u64 *)(v + S_GPAT) = 0x0007040600070406ULL;
	*(u64 *)(v + 0x6E0) = 1;   /* the guest's SPEC_CTRL */
	__asm__ volatile(".byte 0x0f,0x01,0xdd" ::: "memory");   /* CLGI */
	sap_phase = 20;
	ap_vmrun();   /* the INIT resets the AP inside the guest: no return */
	sap_phase = 21;
}

void test_svm_smp_model(void) {
	if (!ap_vmcb) return;
	/* test_svm_smp's INIT with the INIT intercept: #VMEXIT(INIT), 63h (15.13.4, table 15-12) */
	kprintf("svmm.smp.init_exit: %x\n", sap_code[2]);
	if (!hpd32) { hpd32 = page_alloc(1); hpdpt = page_alloc(1); hpd64 = page_alloc(4); }
	for (u32 k = 0; k < 1024; k++) hpd32[k] = (k << 22) | 0x83 | (k >= 0x3F8 ? 0x18 : 0);
	build_nested(0);
	memcpy((void *)SAP_TRAMP, sap_tramp, sap_tramp_end - sap_tramp);
	*(volatile u16 *)(SAP_TRAMP + (sap_gdtr - sap_tramp)) = sizeof gdt - 1;
	*(volatile u32 *)(SAP_TRAMP + (sap_gdtr - sap_tramp) + 2) = (u32)gdt;
	sap_stack_top = (u32)sap_stack + sizeof sap_stack;
	sap_mode = 2; sap_phase = 0; sap_res[5] = 0;
	ipi(1, 0xC500); ipi(1, 0x8500); ipi(1, 0x600 | (SAP_TRAMP >> 12));
	sap_wait(&sap_phase, 20);
	*gcount = 0;
	sap_wait(gcount, 1);   /* the guest runs */
	sap_mode = 3;
	ipi(1, 0x4500);   /* INIT (not intercepted) */
	ipi(1, 0x600 | (SAP_TRAMP >> 12));
	sap_wait(&sap_res[5], 1);
	kprintf("svmm.smp.init_np: guest_ran=%d pat=%x:%x spec=%x efer=%x pg=%d\n", *gcount != 0, sap_res[1], sap_res[0],
	        sap_res[2], sap_res[3], sap_res[4] >> 31);
	sap_mode = 0;
	smp_restart_ap();
}

/* ---------------- long mode (long=1 pass, qemu-system-x86_64) ---------------- */

/* Called by t_long.c in compatibility mode (EFER.LMA = 1, 4-level host paging, NXE): VMRUN from a
   compatibility-mode host, so the nested tables are 4-level (15.25.3), for a guest without paging and
   for a compatibility-mode guest (EFER.LMA = 1, CS.L = 0) with its own 4-level tables under nested
   paging (the 2D walk of 15.25.5 with 4-level tables in both dimensions). The same accesses as t_np
   (nacc); every exception is intercepted (a long-mode guest would need a 64-bit IDT). Nested tables:
   identity 0..64 MiB in 2 MiB pages, the window GPA0 in 4 KiB pages (pages k = 0..15 of `npages`,
   nperm; page 11 with reserved address bit 51); the guest's tables in window pages 12 (PML4), 13
   (PDPT), 14 (PD0: identity 0..64 MiB), 15 (PD1: NWIN) and 10 (PT). */
static u64 *lnpml4, *lnpdpt, *lnpd, *lnpt;

static void build_nested4(void) {
	if (!lnpml4) { lnpml4 = page_alloc(1); lnpdpt = page_alloc(1); lnpd = page_alloc(1); lnpt = page_alloc(1); }
	if (!npages) npages = page_alloc(16);
	memset(lnpml4, 0, 4096); memset(lnpdpt, 0, 4096); memset(lnpd, 0, 4096); memset(lnpt, 0, 4096);
	lnpml4[0] = (u32)lnpdpt | 7;
	lnpdpt[0] = (u32)lnpd | 7;
	for (u32 k = 0; k < 32; k++) lnpd[k] = ((u64)k << 21) | 0x87;
	lnpd[GPA0 >> 21] = (u32)lnpt | 7;
	lnpd[(GPA0 >> 21) + 1] = (GPA0 + 0x200000) | 0x87 | 0x2000;   /* reserved bit 13 of a 2 MiB PDE */
	for (int k = 0; k < 16; k++) lnpt[k] = nperm(k, 1) ? ((u32)npages + 0x1000 * k) | nperm(k, 1) : 0;
	lnpt[11] = ((u32)npages + 0xB000) | 7 | (1ULL << 51);   /* above MAXPHYADDR 48: reserved */
	memset(npages, 0, 16 * 4096);
	*(u32 *)npages = 0x600DF00D;
	*(u32 *)(npages + 0x2000) = 0x5EADBEEF;
	u8 *code = npages + 0x7000;   /* mov eax,7777h; vmmcall */
	code[0] = 0xb8; code[1] = 0x77; code[2] = 0x77; code[3] = 0; code[4] = 0; code[5] = 0x0f; code[6] = 0x01; code[7] = 0xd9;
	/* the guest's 4-level tables (guest-physical addresses) */
	u64 *pml4 = (u64 *)(npages + 0xC000), *pdpt = (u64 *)(npages + 0xD000), *pd0 = (u64 *)(npages + 0xE000),
	    *pd1 = (u64 *)(npages + 0xF000), *pt = (u64 *)(npages + 0xA000);
	pml4[0] = (GPA0 + 0xD000) | 7;
	pdpt[0] = (GPA0 + 0xE000) | 7;
	pdpt[1] = (GPA0 + 0xF000) | 7;
	for (u32 k = 0; k < 32; k++) pd0[k] = ((u64)k << 21) | 0x87;
	pd1[0] = (GPA0 + 0xA000) | 7;
	pd1[2] = (GPA0 + 0x6000) | 7;   /* a guest page table in a page not present at the nested level */
	u64 map[6] = { GPA0 | 7, (GPA0 + 0x1000) | 7, (GPA0 + 0x2000) | 7, 0, (GPA0 + 0x7000) | 7, (GPA0 + 0xB000) | 7 };
	for (int k = 0; k < 6; k++) pt[k] = map[k];
}

void test_svm_long(void) {
	if (!has_feature(0x80000001, 0, 2, 2)) { kputs("svm: not available\n"); return; }
	if (!vmcb) svm_setup();
	wrmsr(EFER_MSR, rdmsr(EFER_MSR) | SVME);
	wrmsr(VM_HSAVE, (u32)vmcb2);
	static const char *gn[] = { "goff", "", "", "glong" };
	for (int gmode = 0; gmode < 4; gmode += 3) {
		for (u32 a = 0; a < sizeof nacc / sizeof nacc[0]; a++) {
			if (gmode == 0 && (nacc[a].off == 0x3000 || nacc[a].off == 0x400000)) continue;
			build_nested4();
			u32 addr;
			if (gmode == 0) {
				static const u32 gpa[] = { 0, 4, 0x1000, 0x2008, 0x2000, 0, 0x7000, 0xB000 };
				addr = GPA0 + gpa[a];
			} else addr = NWIN + nacc[a].off;
			u32 rip = nacc[a].kind == 1 ? G(0x89, 0x01) : nacc[a].kind == 0 ? G(0x8b, 0x01) : G(0xff, 0xd1);
			vmcb_flat(rip);
			VM32(C_EXC) = 0xFFFFFFFF;
			VM64(C_NP) = 1;
			VM64(C_NCR3) = (u32)lnpml4;
			VM64(S_GPAT) = 0x0007040600070406ULL;
			svm_g[1] = addr;
			VM64(S_RAX) = 0x11223344;
			if (gmode == 3) {
				VM64(S_EFER) = SVME | 0x100 | 0x400 | 0x800;   /* LME, LMA, NXE */
				VM64(S_CR0) = 0x80010011; VM64(S_CR4) = 0x20; VM64(S_CR3) = GPA0 + 0xC000;
			}
			run();
			/* accessed/dirty bits of the nested PTEs of window pages 0, 2, 3, 4, 5, 10, 12, 15 and of the
			   guest PTEs of window pages 0, 1, 2, 4 */
			u32 nad = 0, gad = 0;
			static const int nk[] = { 0, 2, 3, 4, 5, 10, 12, 15 };
			for (int j = 0; j < 8; j++) nad = (nad << 2) | (((u32)lnpt[nk[j]] >> 5) & 3);
			static const int gk[] = { 0, 1, 2, 4 };
			for (int j = 0; j < 4; j++) gad = (gad << 2) | (((u32)((u64 *)(npages + 0xA000))[gk[j]] >> 5) & 3);
			kprintf("svm.np.h64.%s.%s: code=%x", gn[gmode], nacc[a].n, (u32)VM64(C_CODE));
			x64("i1", VM64(C_CODE) == 0x81 ? 0 : VM64(C_INFO1));
			x64("i2", VM64(C_CODE) == 0x81 ? 0 : (VM64(C_CODE) == 0x400 || VM64(C_CODE) == 0x4E) ? VM64(C_INFO2) : 0);
			kprintf(" rax=%x d0=%x nad=%x gad=%x\n", VM64(C_CODE) == 0x81 ? (u32)VM64(S_RAX) : 0,
			        *(u32 *)(npages + 4), nad, gad);
		}
	}
}

/* ---------------- review regressions (model-only, except r_shadow) ---------------- */

/* With GIF = 0 an instruction-breakpoint match is ignored and discarded (table 15-10), like a data
   breakpoint (m_gifdb); with GIF = 1 it faults. */
__asm__(".globl rv_bpf\nrv_bpf:\n nop\n.globl rv_bpl\nrv_bpl:\n nop\n ret\n");
extern char rv_bpf[], rv_bpl[];
static volatile u32 rv_db;
static int rv_hook(struct frame *f) {
	if (f->vec == 1) { rv_db++; f->eflags |= 0x10000; return 1; }   /* RF: resume past the breakpoint */
	return 0;
}
static void r_gif_ibp(void) {
	int (*old)(struct frame *) = trap_hook;
	trap_hook = rv_hook;
	WRDR(0, (u32)rv_bpl); WRDR(6, 0);
	rv_db = 0; clgi(); WRDR(7, 0x401); ((void (*)(void))rv_bpf)(); WRDR(7, 0x400); stgi();
	u32 g0 = rv_db;
	rv_db = 0; WRDR(7, 0x401); ((void (*)(void))rv_bpf)(); WRDR(7, 0x400);
	trap_hook = old;
	kprintf("svmr.gif.ibp: gif0=%d gif1=%d\n", g0, rv_db);
}

/* The interrupt shadow and RFLAGS.RF a #VMEXIT saves are those of the moment the intercept triggers
   (15.7.1, 15.21.5): also for an intercepted exception (UD2 with the VMCB's shadow; an instruction
   after MOV SS that takes an intercepted #PF), as for an intercepted instruction (CPUID). */
static void r_shadow(void) {
	vmcb_flat(G(0x0f, 0x0b));
	VM32(C_EXC) = 1u << 6; VM32(C_INTST) = 1;
	run();
	u32 ud = (u32)VM64(C_CODE), uds = VM32(C_INTST) & 1;
	vmcb_flat(G(0x0f, 0xa2));
	VM32(C_I3) |= 1u << I_CPUID; VM32(C_INTST) = 1;
	run();
	kprintf("svmr.shadow.exc: ud=%x shadow=%d cpuid=%x shadow=%d\n", ud, uds, (u32)VM64(C_CODE), VM32(C_INTST) & 1);
	build_gpt32();
	u32 rip = G(0x8c, 0xd0, 0x8e, 0xd0, 0x8b, 0x01);   /* mov eax,ss; mov ss,eax; mov eax,[ecx] */
	vmcb_flat(rip);
	VM32(C_EXC) = 1u << 14;
	VM64(S_CR0) = 0x80000011; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd;
	svm_g[1] = GWIN + 0x1000;   /* not present */
	run();
	kprintf("svmr.shadow.movss_pf: code=%x rip=%x shadow=%d\n", (u32)VM64(C_CODE), (u32)VM64(S_RIP) - rip,
	        VM32(C_INTST) & 1);
	vmcb_flat(G(0x0f, 0xa2));
	VM32(C_I3) |= 1u << I_CPUID;
	VM64(S_RFLAGS) = 0x10002;
	run();
	kprintf("svmr.rf.cpuid: code=%x fl=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RFLAGS));
	vmcb_flat(G(0x0f, 0x0b));
	VM32(C_EXC) = 1u << 6;
	VM64(S_RFLAGS) = 0x10002;
	run();
	kprintf("svmr.rf.ud: code=%x fl=%x\n", (u32)VM64(C_CODE), (u32)VM64(S_RFLAGS));
}

/* An intercepted INTR exits also in the guest's interrupt shadow, which the VMCB records (15.21.5;
   KVM: "vmexits aren't blocked by the interrupt shadow"); without the intercept the shadow holds it. */
static void r_intr_shadow(void) {
	for (int icpt = 0; icpt < 2; icpt++) {
		u32 rip = G(0x90, 0x90);
		vmcb_flat(rip);
		VM64(S_RFLAGS) = 0x202;
		VM32(C_INTST) = 1;
		if (icpt) VM32(C_I3) |= 1u << I_INTR;
		trap_hook = svm_hook;
		h_intr = 0;
		clgi();
		self_ipi(0x50);
		settle();
		svm_vmcb_pa = (u32)vmcb;
		svm_vmrun_raw();
		stgi();
		__asm__ volatile("sti");
		settle();
		__asm__ volatile("cli");
		LR(0xB0) = 0;
		trap_hook = 0;
		/* delivered: the guest's stub for vector 50h reports it with VMMCALL (RIP in the stub) */
		kprintf("svmr.intr.shadow.%s: code=%x rip=%x rax=%x shadow=%d\n", icpt ? "icpt" : "deliver",
		        (u32)VM64(C_CODE), icpt ? (u32)VM64(S_RIP) - rip : 0, (u32)VM64(S_RAX), VM32(C_INTST) & 1);
	}
}

/* An I/O or MSR permission map at or above 4 GiB reads as open bus (all ones): every access it covers
   is intercepted, also through a map whose pages cross 4 GiB. */
static void r_pm4g(void) {
	vmcb_flat(G(0xe4, 0x80));   /* in al,80h */
	VM32(C_I3) |= 1u << I_IOIO;
	VM64(C_IOPM) = 0x100000000ULL;
	run();
	u32 a = (u32)VM64(C_CODE);
	vmcb_flat(G(0x66, 0xba, 0x00, 0x80, 0xec));   /* mov dx,8000h; in al,dx: byte 1000h of the map */
	VM32(C_I3) |= 1u << I_IOIO;
	VM64(C_IOPM) = 0xFFFFF000ULL;
	run();
	u32 b = (u32)VM64(C_CODE);
	vmcb_flat(G(0xb9, 0x10, 0, 0, 0, 0x0f, 0x32));   /* mov ecx,10h; rdmsr */
	VM32(C_I3) |= 1u << I_MSR;
	VM64(C_MSRPM) = 0x100000000ULL;
	run();
	kprintf("svmr.pm4g: iopm=%x iopm_cross=%x msrpm=%x\n", a, b, (u32)VM64(C_CODE));
}

/* VM_CR: setting SVMDIS with EFER.SVME = 1 is #GP(0) also while LOCK is set (15.30.1). */
static void r_vmcr_lock(void) {
	wrmsr(SVM_KEY, 0x77);
	wrmsr(VM_CR, VM_CR_LOCK);
	int e = try_wr(VM_CR, VM_CR_LOCK | VM_CR_SVMDIS);
	u32 v = (u32)rdmsr(VM_CR);
	wrmsr(SVM_KEY, 0x77);
	wrmsr(VM_CR, 0);
	kprintf("svmr.vmcr.lock_svmdis: vec=%x vmcr=%x after=%x\n", e, v, (u32)rdmsr(VM_CR));
}

/* nCR3 is a full system-physical address: 32-bit nested tables at nCR3 = 1_0000_0000h + x are not
   those at x (they read as open bus: a reserved-bit NPF). */
static void r_ncr3_4g(void) {
	host_paging(1);
	build_nested(0);
	vmcb_flat(G(0x90));
	VM64(C_NP) = 1; VM64(C_NCR3) = 0x100000000ULL | (u32)npd32; VM64(S_GPAT) = 0x0007040600070406ULL;
	run();
	host_paging(0);
	kprintf("svmr.ncr3.4g: code=%x", (u32)VM64(C_CODE));
	x64("i1", VM64(C_INFO1)); kprintf(" i2_rip=%d\n", VM64(C_INFO2) == (u32)gcode);
}

/* SMM_CTL from a guest without the MSR intercept: ENTER blocks SMIs and NMIs but does not enter SMM,
   so the guest's intercepts and nested paging stay in force (15.30.3, 15.22). */
static void r_smmctl_guest(void) {
	host_paging(1);
	build_nested(0);
	/* mov ecx,C0010116h; mov eax,2; xor edx,edx; wrmsr; mov ebx,[10000000h]; cpuid */
	vmcb_flat(G(0xb9, 0x16, 0x01, 0x01, 0xc0, 0xb8, 0x02, 0, 0, 0, 0x31, 0xd2, 0x0f, 0x30,
	            0x8b, 0x1d, 0x00, 0x00, 0x00, 0x10, 0x0f, 0xa2));
	VM32(C_I3) |= 1u << I_CPUID;
	VM64(C_NP) = 1; VM64(C_NCR3) = (u32)npd32; VM64(S_GPAT) = 0x0007040600070406ULL;
	run();
	host_paging(0);
	u32 code = (u32)VM64(C_CODE), ebx = svm_g[3];
	/* SMIs are held until EXIT */
	volatile u32 *cnt = (volatile u32 *)0x6100;
	*cnt = 0;
	outb(0xB2, 0);
	u32 held = *cnt;
	wrmsr(0xC0010116, 8);   /* EXIT */
	settle();
	kprintf("svmr.smmctl.guest: code=%x ebx=%x smi_held=%d smi_after_exit=%d\n", code, ebx, held == 0, *cnt);
}

/* HWCR.SmmLock (bit 0, sticky): SMM_CTL writes are #GP(0). Last: the lock stays until RESET. */
static void r_smmlock(void) {
	int a = try_wr(0xC0010116, 0);
	wrmsr(0xC0010015, rdmsr(0xC0010015) | 1);
	int b = try_wr(0xC0010116, 0);
	wrmsr(0xC0010015, rdmsr(0xC0010015) & ~1ULL);
	kprintf("svmr.smmlock: before=%x locked=%x hwcr0=%x\n", a, b, (u32)rdmsr(0xC0010015) & 1);
}

/* An SMI in a paged-real-mode guest (CR0.PE = 0, PG = 1, 15.19) returns to it: RSM allows PG without
   PE when EFER.SVME = 1. */
static void r_smi_realpg(void) {
	volatile u32 *cnt = (volatile u32 *)0x6100;
	*cnt = 0;
	build_gpt32();
	vmcb_flat(G(0xe6, 0xb2, 0x90, 0x90));   /* out 0b2h,al (32-bit code in big real mode) */
	VM64(S_CR0) = 0x80000010; VM64(S_CR4) = 0x10; VM64(S_CR3) = (u32)gpd;
	seg(S_CS, 0, 0xC9B, 0xFFFFFFFF, 0); seg(S_DS, 0, 0xC93, 0xFFFFFFFF, 0);
	seg(S_SS, 0, 0xC93, 0xFFFFFFFF, 0); seg(S_ES, 0, 0xC93, 0xFFFFFFFF, 0);
	run();
	kprintf("svmr.smi.realpg: code=%x smm=%d cr0=%x\n", (u32)VM64(C_CODE), *cnt, (u32)VM64(S_CR0));
}

/* FERR_FREEZE (vector 3 bit 30, exit 7Eh): with CR0.NE = 0 a waiting x87 instruction with a pending
   unmasked exception would freeze; the intercept exits at it. With IGNNE asserted (the IGNNE MSR) no
   freeze: FERR# and execution continues. */
static void r_ferr(void) {
	for (int ign = 0; ign < 2; ign++) {
		/* fninit; fldcw [ebx] (exceptions unmasked); fld1; fldz; fdivp (ZE pending); fwait */
		vmcb_flat(G(0xdb, 0xe3, 0xd9, 0x2b, 0xd9, 0xe8, 0xd9, 0xee, 0xde, 0xf9, 0x9b));
		*(u16 *)gdata = 0x0340;
		svm_g[3] = (u32)gdata;
		VM64(S_CR0) = 0x11;   /* NE = 0 */
		VM32(C_I3) |= 1u << I_FERR;
		wrmsr(0xC0010115, ign);
		run();
		wrmsr(0xC0010115, 0);
		kprintf("svmr.ferr.%s: code=%x rip=%x\n", ign ? "ignne" : "freeze", (u32)VM64(C_CODE),
		        (u32)VM64(S_RIP) - (u32)gcode);
	}
	outb(0xF0, 0);   /* FERR#/IRQ13 off (IGNNE port) */
}

/* Development run only (svmr=11; it ends the run): a halted guest with a stale EVENTINJ (V = 0) and
   nothing to wake it is idle, so the simulation stops instead of spinning (Machine.svmIdle,
   MpMachine.runnableState: only V counts, as in stepAtSvm). */
static void r_stale_inject(void) {
	vmcb_flat(G(0xf4));   /* hlt (not intercepted), guest IF = 0 */
	VM32(C_INJ) = 0x30;   /* vector 30h, type 0, V = 0 */
	kputs("svmr.stale_inject: halting\n");
	run();
	kputs("svmr.stale_inject: not reached\n");
}

static void m_review(u32 only) {
	if (only == 11) r_stale_inject();
	if (!only || only == 1) r_gif_ibp();
	if (only == 2) r_shadow();   /* in test_svm (QEMU-compared) */
	if (!only || only == 3) r_intr_shadow();
	if (!only || only == 4) r_pm4g();
	if (!only || only == 5) r_vmcr_lock();
	if (!only || only == 6) r_ncr3_4g();
	if (!only || only == 7) r_ferr();
	if (!only || only == 8) r_smmctl_guest();
	if (!only || only == 9) r_smi_realpg();
	if (!only || only == 10) r_smmlock();
}

void test_svm_model(void) {
	if (!vmcb) return;
	u32 only = param("svmr", 0);   /* development runs: one review regression only */
	if (only) { m_review(only); return; }
	m_cpuid();
	m_vmcr();
	m_nrip();
	m_bytes();
	m_pause();
	m_tsc();
	m_vgif();
	m_inject();
	m_consist();
	m_vmload();
	m_tlb();
	m_init();
	m_smi();
	m_skinit();
	m_swap();
	m_gifdb();
	m_misc();
	m_svfx();
	m_npx();
	t_df_case(0, "svmm.df");   /* TCG shuts down (formerly a rewriting deviation rule) */
	m_review(0);
}
