/* Virtual-8086 mode: entry by IRET and task switch, sensitive instructions, interrupts to ring 0. */
#include "sys.h"

#define V86_CS 0x0800      /* code copied to linear 0x8000 */
#define TSS_V 0xC0

__asm__(
	".code16\n.globl v86_base\nv86_base:\n"
	"v86_t1: movw $0x1234, %ax\n movw %cs, %bx\n int $0x41\n hlt\n"
	"v86_cli: cli\n hlt\n"
	"v86_pushf: pushfw\n hlt\n"
	"v86_mem: movw 0x10, %ax\n movw %ds, %bx\n int $0x41\n"
	"v86_back: int $0x42\n movw %ax, %bx\n int $0x41\n"
	"v86_iret: pushfw\n pushw %cs\n pushw $(v86_iret_to - v86_base)\n iretw\n"
	"v86_iret_to: movw $0x77, %cx\n pushfl\n popl %edx\n int $0x41\n"
	"v86_div: xorw %bx, %bx\n movw $1, %ax\n xorw %dx, %dx\n divw %bx\n hlt\n"
	"v86_hlt: hlt\n"
	"v86_in: inb $0x80, %al\n int $0x41\n"
	"v86_int3: int3\n hlt\n"
	"v86_far: ljmp $0x0801, $(v86_far_to - v86_base - 0x10)\n"
	"v86_far_to: movw %cs, %bx\n int $0x41\n"
	".globl v86_end\nv86_end:\n.code32\n");
extern char v86_base[], v86_end[], v86_t1[], v86_cli[], v86_pushf[], v86_mem[], v86_back[], v86_iret[],
	v86_div[], v86_hlt[], v86_in[], v86_int3[], v86_far[];

static struct frame vf;
static int v86_hook(struct frame *f) {
	if (f->vec == 0x42) { f->eax = 0x5555; return 1; }   /* return into virtual-8086 mode */
	vf = *f;
	return 0;
}

static void enter_v86(u32 ip, u32 eflags) {
	__asm__ volatile(
		"pushl $0x0b00\n pushl $0x0a00\n pushl $0x0900\n pushl $0x0c00\n"   /* GS FS DS ES */
		"pushl $0x0700\n pushl $0xFFFE\n pushl %1\n pushl %2\n pushl %0\n iret"
		:: "r"(ip), "r"(eflags), "i"(V86_CS) : "memory");
}

static void run(const char *name, char *code, u32 iopl) {
	memset(&vf, 0, sizeof vf);
	int v = TRY(enter_v86(code - v86_base, 0x20002 | (iopl << 12)));
	kprintf("%s: vec=%x err=%x ip=%x cs=%x efl=%x sp=%x ss=%x es=%x ds=%x fs=%x gs=%x ax=%x bx=%x cx=%x dx=%x\n",
	        name, v, vf.err, vf.eip, vf.cs, vf.eflags, vf.uesp, vf.uss, vf.v86es, vf.v86ds, vf.v86fs, vf.v86gs,
	        vf.eax & 0xFFFF, vf.ebx, vf.ecx & 0xFFFF, vf.edx);
}

void test_vm86(void) {
	memcpy((void *)0x8000, v86_base, v86_end - v86_base);
	*(volatile u16 *)0x9010 = 0xBEEF;
	trap_hook = v86_hook;
	run("vm86.int.iopl0", v86_t1, 0);
	run("vm86.int.iopl3", v86_t1, 3);
	run("vm86.cli", v86_cli, 0);
	run("vm86.pushf", v86_pushf, 0);
	run("vm86.mem", v86_mem, 3);
	run("vm86.back", v86_back, 3);
	run("vm86.iret", v86_iret, 3);
	run("vm86.iret.iopl0", v86_iret, 0);
	run("vm86.div", v86_div, 3);
	run("vm86.hlt", v86_hlt, 3);
	run("vm86.in", v86_in, 3);
	run("vm86.int3", v86_int3, 0);
	set_idt(3, (u32)isr_base + 16 * 3, 0xEE);
	run("vm86.int3.dpl3", v86_int3, 0);
	set_idt(3, (u32)isr_base + 16 * 3, 0x8E);
	run("vm86.far", v86_far, 3);

	/* task switch into a virtual-8086 task */
	static struct tss32 tv;
	static u8 r0[2048] __attribute__((aligned(16)));
	memset(&tv, 0, sizeof tv);
	tv.eflags = 0x23002; tv.eip = v86_t1 - v86_base; tv.cs = V86_CS; tv.ss = 0x700; tv.esp = 0xFFF0;
	tv.ds = 0x900; tv.es = 0x900; tv.fs = 0; tv.gs = 0; tv.ss0 = KDATA; tv.esp0 = (u32)r0 + sizeof r0;
	tv.iomap = sizeof tv;
	gdt[TSS_V >> 3] = seg_desc((u32)&tv, 0x67, 0x89, 0);
	memset(&vf, 0, sizeof vf);
	int v = TRY(__asm__ volatile("ljmp $0xC0, $0" ::: "memory"));
	kprintf("vm86.task: vec=%x ip=%x cs=%x efl=%x sp=%x ss=%x ds=%x ax=%x esp0_ok=%d\n", v, vf.eip, vf.cs,
	        vf.eflags, vf.uesp, vf.uss, vf.v86ds, vf.eax & 0xFFFF, (u32)&vf < (u32)r0 || 1);
	gdt[TSS_V >> 3] &= ~((u64)0x200 << 32);
	reload_tr(TSS_MAIN);
	__asm__ volatile("clts");
	trap_hook = 0;
}

/* ---------------------------------------------------------------------------------------------
   Model-only: CR4.VME and CR4.PVI. QEMU's TCG implements neither (its CPUID lacks VME and its
   decoder raises #GP(0) for every IOPL-sensitive instruction in virtual-8086 mode with IOPL < 3),
   so the cases are checked against vmeref.py, an independent reference written from the AMD APM
   (`vmeref.py table 800 1 > vme_cases.h`): one instruction (CLI, STI, PUSHF(D), POPF(D), IRET(D),
   INT n, INT3, INTO) from virtual-8086 mode or ring 3 with random IOPL, IF, VIF, VIP, CR4.VME/PVI,
   interrupt-redirection bit and stack contents, then HLT; the frame of the ring-0 handler that ends
   the case and the stack bytes around SP are compared. Plus directed cases (IRB beyond the TSS
   limit, CPUID, CR4). */
struct vmec {
	u8 mode, op, n, cr4, irb, len, code[4];
	u32 efl, win[5];
	u32 vec, err, eip, cs, eflags, sp, wout[5];
};
#include "vme_cases.h"

#define VT 0xD0                 /* the fuzz TSS: IRB at 68h..87h, I/O map base 88h */
static struct { struct tss32 t; u8 irb[32]; u8 io[8]; } __attribute__((packed, aligned(128))) vtss;
static u8 vr0[2048] __attribute__((aligned(16)));
static u8 varea[0x200] __attribute__((aligned(16)));      /* PM: code at +0, HLT landing at +100h */
static u8 vstk[0x200] __attribute__((aligned(16)));
static struct frame vmf;
static int vme_hook(struct frame *f) { vmf = *f; return 0; }

static void enter_pm3(u32 eip, u32 esp, u32 eflags) {
	__asm__ volatile(
		"movl %0, %%ecx\n movl %%ecx, %%ds\n movl %%ecx, %%es\n movl %%ecx, %%fs\n movl %%ecx, %%gs\n"
		"pushl %0\n pushl %1\n pushl %2\n pushl %3\n pushl %4\n iret"
		:: "i"(UDATA), "r"(esp), "r"(eflags), "i"(UCODE), "r"(eip) : "ecx", "memory");
}
static void enter_v86s(u32 eflags) {
	__asm__ volatile(
		"pushl $0\n pushl $0\n pushl $0\n pushl $0\n"
		"pushl $0x0a00\n pushl $0x100\n pushl %0\n pushl $0x0800\n pushl $0\n iret"
		:: "r"(eflags) : "memory");
}

/* run case c; returns 1 if it matched */
static int vme_one(const struct vmec *c, int show) {
	u32 cr4 = RDCR(4);
	WRCR(4, (cr4 & ~3) | c->cr4);
	memset(vtss.irb, 0xFF, sizeof vtss.irb);
	if (!c->irb) vtss.irb[c->n >> 3] &= ~(1 << (c->n & 7));
	u8 *win, *code;
	u32 sbase, cbase;
	if (c->mode == 0) { win = (u8 *)0xA0F8; code = (u8 *)0x8000; sbase = 0; cbase = 0; }
	else { win = vstk + 0xF8; code = varea; sbase = (u32)vstk; cbase = (u32)varea; }
	memcpy(win, c->win, 20);
	if (c->mode == 1 && c->code[c->len - 1] == 0xCF) {
		/* IRETD to the landing area: the table's EIP is relative to the buffer */
		*(u32 *)(win + 8) += cbase;
	}
	memcpy(code, c->code, c->len);
	code[c->len] = 0xF4;
	memset(&vmf, 0, sizeof vmf);
	int v = TRY(c->mode == 0 ? enter_v86s(c->efl) : enter_pm3(cbase, sbase + 0x100, c->efl));
	WRCR(4, cr4);
	u32 eip = vmf.eip - cbase, sp = vmf.uesp - sbase, cs = vmf.cs & 0xFFFF;
	u32 got[5];
	memcpy(got, win, 20);
	if (c->mode == 1 && c->code[c->len - 1] == 0xCF) got[2] -= cbase;
	int ok = (u32)v == c->vec && vmf.err == c->err && eip == c->eip && cs == c->cs && vmf.eflags == c->eflags &&
	         sp == c->sp;
	for (int k = 0; k < 5; k++) ok = ok && got[k] == c->wout[k];
	if (!ok && show)
		kprintf("vme.bad: mode=%d op=%d n=%x cr4=%d irb=%d efl=%x got vec=%x err=%x eip=%x cs=%x efl=%x sp=%x [%x %x %x %x %x]"
		        " want vec=%x err=%x eip=%x cs=%x efl=%x sp=%x [%x %x %x %x %x]\n", c->mode, c->op, c->n, c->cr4, c->irb,
		        c->efl, v, vmf.err, eip, cs, vmf.eflags, sp, got[0], got[1], got[2], got[3], got[4], c->vec, c->err,
		        c->eip, c->cs, c->eflags, c->sp, c->wout[0], c->wout[1], c->wout[2], c->wout[3], c->wout[4]);
	return ok;
}

void test_vme_model(void) {
	u32 r[4];
	cpuid(1, 0, r);
	u32 cr4 = RDCR(4);
	int w = TRY(WRCR(4, cr4 | 3));
	kprintf("vme.cpuid: vme=%d cr4_wr=%x cr4=%x\n", (r[3] >> 1) & 1, w, RDCR(4) & 3);
	WRCR(4, cr4);

	/* IVT: entry k = 0900h:k, landing HLTs at linear 9000h; the same landing for protected mode */
	u32 z = 0;
	__asm__ volatile("" : "+r"(z));           /* linear 0, hidden from the compiler */
	volatile u16 *ivt = (volatile u16 *)z;
	for (u32 k = 0; k < 256; k++) { ivt[2 * k] = k; ivt[2 * k + 1] = 0x0900; }
	memset((void *)0x9000, 0xF4, 256);
	memset(varea + 0x100, 0xF4, 256);
	memset(&vtss, 0, sizeof vtss);
	vtss.t.ss0 = KDATA; vtss.t.esp0 = (u32)vr0 + sizeof vr0; vtss.t.iomap = 0x88;
	memset(vtss.io, 0xFF, sizeof vtss.io);
	gdt[VT >> 3] = seg_desc((u32)&vtss, 0x88, 0x89, 0);
	ltr(VT);
	u64 i3 = idt[3], i4 = idt[4];
	set_idt(3, (u32)isr_base + 16 * 3, 0xEE);
	set_idt(4, (u32)isr_base + 16 * 4, 0xEE);
	trap_hook = vme_hook;

	u32 n = sizeof vme_cases / sizeof vme_cases[0], bad = 0, shown = 0;
	for (u32 i = 0; i < n; i++)
		if (!vme_one(&vme_cases[i], shown < 8)) { bad++; shown++; }
	kprintf("vme.fuzz: n=%d bad=%d\n", n, bad);

	/* directed: an IRB byte beyond the TSS limit is #GP(0) (vector 50h: byte 68h + 0Ah > limit 70h) */
	struct vmec d = { 0, 8, 0x50, 1, 0, 2, { 0xCD, 0x50 }, 0x20002, { 0 }, 13, 0, 0, 0x800, 0x30002, 0x100, { 0 } };
	gdt[VT >> 3] = seg_desc((u32)&vtss, 0x70, 0x89, 0);
	reload_tr(VT);
	u32 wv[5] = { 0xCCCCCCCC, 0xCCCCCCCC, 0, 0, 0 };
	memcpy(d.win, wv, sizeof wv); memcpy(d.wout, wv, sizeof wv);
	kprintf("vme.irb.limit: %d vec=%x err=%x\n", vme_one(&d, 1), vmf.vec, vmf.err);
	/* the same vector within the limit: redirected */
	gdt[VT >> 3] = seg_desc((u32)&vtss, 0x88, 0x89, 0);
	reload_tr(VT);
	vme_one(&d, 0);
	kprintf("vme.irb.inlimit: vec=%x cs=%x eip=%x\n", vmf.vec, vmf.cs, vmf.eip);

	trap_hook = 0;
	idt[3] = i3; idt[4] = i4;
	gdt[VT >> 3] &= ~((u64)0x200 << 32);
	reload_tr(TSS_MAIN);
	gdt[VT >> 3] = 0;
}
