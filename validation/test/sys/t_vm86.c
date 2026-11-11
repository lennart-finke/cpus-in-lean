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
