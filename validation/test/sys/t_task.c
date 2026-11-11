/* Hardware task switching: JMP/CALL to TSS and task gates, IDT task gates, IRET with NT, #DF task. */
#include "sys.h"

#define TSS_B 0x30
#define TSS_C 0x38
#define GATE_C 0x40
#define TSS_D 0x50
#define TSS_E 0x58
#define TSS_F 0x60
#define TSS_G 0x68
#define TSS_H 0x70
#define TSS_I 0x78
#define CODE_I 0x80
#define TSS_SMALL 0x88

struct tss16 { u16 link, sp0, ss0, sp1, ss1, sp2, ss2, ip, flags, ax, cx, dx, bx, sp, bp, si, di, es, cs, ss, ds, ldt; };

static struct tss32 tb, tc, td, te, tf, tg, th, tsmall;
static struct tss16 ti;
static u8 stacks[8][2048] __attribute__((aligned(16)));
volatile u32 tb_count, tc_count, tc_flags, td_count, te_err, tf_err, tf_count, th_count, ti_eax, ti_count;

__asm__(
	".globl task_b\ntask_b: incl tb_count\n ljmp $0x28, $0\n jmp task_b\n"
	".globl task_c\ntask_c: incl tc_count\n pushfl\n popl tc_flags\n iret\n jmp task_c\n"
	".globl task_d\ntask_d: incl td_count\n iret\n jmp task_d\n"
	".globl task_e\ntask_e: popl te_err\n movl $recover_e, tss_main+0x20\n iret\n jmp task_e\n"
	".globl task_f\ntask_f: popl tf_err\n incl tf_count\n movl $recover_f, tss_main+0x20\n iret\n jmp task_f\n"
	".globl task_g\ntask_g: hlt\n"
	".globl task_h\ntask_h: incl th_count\n ljmp $0x28, $0\n jmp task_h\n"
	/* runs in a code segment based at task_i (EIP = 0, 16-bit TSS) */
	".globl task_i\ntask_i: movl %eax, ti_eax\n incl ti_count\n ljmp $0x28, $0\n");
extern char task_b[], task_c[], task_d[], task_e[], task_f[], task_g[], task_h[], task_i[];

static void mk(struct tss32 *t, char *eip, int stack) {
	memset(t, 0, sizeof *t);
	t->cr3 = RDCR(3); t->eip = (u32)eip; t->eflags = 2;
	t->esp = (u32)stacks[stack] + sizeof stacks[stack];
	t->cs = KCODE; t->ss = t->ds = t->es = t->fs = t->gs = KDATA;
	t->iomap = sizeof *t;
}
static u64 tssd(void *t, u32 limit) { return seg_desc((u32)t, limit, 0x89, 0); }
static u32 busy(u16 sel) { return (u32)(gdt[sel >> 3] >> 40) & 0x2; }
static u16 str(void) { u16 s; __asm__ volatile("str %0" : "=r"(s)); return s; }
static void clts(void) { __asm__ volatile("clts"); }

__attribute__((noinline)) static void gp_via_task(u32 bad) {
	__asm__ volatile("movl %0, %%ds\n.globl recover_e\nrecover_e:\n" :: "r"(bad) : "memory");
}
__attribute__((noinline)) static void df_via_task(u32 bad) {
	__asm__ volatile("movl %0, %%ds\n.globl recover_f\nrecover_f:\n" :: "r"(bad) : "memory");
}

static volatile u32 bt_dr6, bt_eip, bt_tr;
static int bt_hook(struct frame *f) {
	if (f->vec != 1) return 0;
	bt_dr6 = RDDR(6); bt_eip = f->eip; bt_tr = str();
	WRDR(6, 0);
	return 1;
}

void test_task(void) {
	mk(&tb, task_b, 0); mk(&tc, task_c, 1); mk(&td, task_d, 2); mk(&te, task_e, 3);
	mk(&tf, task_f, 4); mk(&tg, task_g, 5); mk(&th, task_h, 6); mk(&tsmall, task_b, 7);
	tg.ds = 0xF0;          /* empty GDT slot: #TS after the switch has committed */
	th.trap = 1;
	gdt[TSS_B >> 3] = tssd(&tb, 0x67);
	gdt[TSS_C >> 3] = tssd(&tc, 0x67);
	gdt[GATE_C >> 3] = gate_desc(TSS_C, 0, 0x85);
	gdt[TSS_D >> 3] = tssd(&td, 0x67);
	gdt[TSS_E >> 3] = tssd(&te, 0x67);
	gdt[TSS_F >> 3] = tssd(&tf, 0x67);
	gdt[TSS_G >> 3] = tssd(&tg, 0x67);
	gdt[TSS_H >> 3] = tssd(&th, 0x67);
	gdt[TSS_SMALL >> 3] = tssd(&tsmall, 0x60);

	/* JMP to a TSS and back */
	__asm__ volatile("ljmp $0x30, $0" ::: "memory");
	kprintf("task.jmp: count=%d tr=%x busy_main=%d busy_b=%d ts=%d b.eip_off=%x\n", tb_count, str(),
	        busy(TSS_MAIN) >> 1, busy(TSS_B) >> 1, (RDCR(0) >> 3) & 1, tb.eip - (u32)task_b);
	clts();
	__asm__ volatile("ljmp $0x30, $0" ::: "memory");
	kprintf("task.jmp2: count=%d\n", tb_count);
	clts();

	/* CALL to a TSS: nested (NT, link), IRET returns */
	__asm__ volatile("lcall $0x38, $0" ::: "memory");
	kprintf("task.call: count=%d nt_in_task=%d link=%x busy_main=%d busy_c=%d nt_now=%d tr=%x\n", tc_count,
	        (tc_flags >> 14) & 1, tc.link, busy(TSS_MAIN) >> 1, busy(TSS_C) >> 1, (rdflags() >> 14) & 1, str());
	clts();
	/* through a task gate */
	__asm__ volatile("lcall $0x40, $0" ::: "memory");
	kprintf("task.gate: count=%d\n", tc_count);
	clts();

	/* INT through an IDT task gate */
	idt[0x50] = gate_desc(TSS_D, 0, 0x85);
	__asm__ volatile("int $0x50" ::: "memory");
	kprintf("task.int: count=%d link=%x tr=%x\n", td_count, td.link, str());
	clts();

	/* #GP through a task gate: the error code is pushed on the new task's stack */
	u64 saved13 = idt[13];
	idt[13] = gate_desc(TSS_E, 0, 0x85);
	gp_via_task(0xF3);
	kprintf("task.gp: err=%x e.esp_ok=%d tr=%x\n", te_err, te.esp == (u32)stacks[3] + sizeof stacks[3], str());
	idt[13] = saved13;
	clts();

	/* #DF through a task gate (as Linux/i386 does): #GP whose gate is not present -> #NP -> #DF */
	u64 saved8 = idt[8];
	idt[8] = gate_desc(TSS_F, 0, 0x85);
	idt[13] &= ~((u64)0x80 << 40);
	df_via_task(0xF3);
	idt[13] = saved13;
	idt[8] = saved8;
	kprintf("task.df: count=%d err=%x link=%x\n", tf_count, tf_err, tf.link);
	clts();

	/* error cases */
	report("task.busy", TRY(__asm__ volatile("ljmp $0x28, $0" ::: "memory")));
	report("task.small", TRY(__asm__ volatile("ljmp $0x88, $0" ::: "memory")));
	gdt[TSS_B >> 3] &= ~((u64)0x80 << 40);
	report("task.notpresent", TRY(__asm__ volatile("ljmp $0x30, $0" ::: "memory")));
	gdt[TSS_B >> 3] |= (u64)0x80 << 40;
	__asm__ volatile("pushfl\n orl $0x4000, (%%esp)\n popfl" ::: "memory");
	tss_main.link = TSS_B;   /* not busy: IRET to it is a #TS */
	report("task.iret.notbusy", TRY(__asm__ volatile("iret" ::: "memory")));

	/* 16-bit TSS: 16-bit fields, upper register halves */
	memset(&ti, 0, sizeof ti);
	ti.ip = 0; ti.flags = 2; ti.ax = 0x1234; ti.cs = CODE_I;
	ti.ss = ti.ds = ti.es = KDATA; ti.sp = 0x800;
	gdt[CODE_I >> 3] = seg_desc((u32)task_i, 0xFFFF, 0x9A, 0x4);
	gdt[TSS_I >> 3] = seg_desc((u32)&ti, 0x2B, 0x81, 0);
	__asm__ volatile("ljmp $0x78, $0" ::: "memory");
	kprintf("task.tss16: count=%d eax=%x busy_i=%d\n", ti_count, ti_eax, busy(TSS_I) >> 1);
	clts();

	/* fault after the commit point: delivered in the new task (last: TCG mishandles it, see
	   qemu-deviations.txt, and its state afterwards is unreliable) */
	int v = TRY(__asm__ volatile("ljmp $0x68, $0" ::: "memory"));
	kprintf("task.commit: vec=%x err=%x at_g=%d tr=%x\n", v, last.err, last.eip == (u32)task_g, str());
	gdt[TSS_G >> 3] &= ~((u64)0x200 << 32);
	reload_tr(TSS_MAIN);
	clts();

}

/* Model-only (TCG raises the T-flag #DB with the old task's EIP and loses track): the T flag of the
   new TSS raises #DB with DR6.BT before the new task's first instruction (SDM 7.3, 17.3.1.5). */
void test_task_trap(void) {
	/* T flag in the new TSS: #DB (BT) before its first instruction */
	trap_hook = bt_hook;
	WRDR(6, 0);
	__asm__ volatile("ljmp $0x70, $0" ::: "memory");
	trap_hook = 0;
	kprintf("task.trap: count=%d dr6=%x at_h=%d tr=%x\n", th_count, bt_dr6, bt_eip == (u32)task_h, bt_tr);
	WRDR(6, 0);
	clts();

}
