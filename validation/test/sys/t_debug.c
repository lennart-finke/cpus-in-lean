/* Debug registers: instruction, data and I/O breakpoints, single-step, general detect, RF, MOV SS. */
#include "sys.h"

__asm__(
	".globl bp_fn\nbp_fn: nop\n ret\n"
	".globl bp_gp\nbp_gp: movl %eax, %ds\n ret\n"
	/* mov ss from memory, then two NOPs: a data breakpoint on the load is reported after the first NOP */
	".globl movss_nop\nmovss_nop: movw (%eax), %ss\n.globl movss_n1\nmovss_n1: nop\n.globl movss_n2\nmovss_n2: nop\n ret\n"
	/* mov ss, then INT 0x41: the #DB is taken at the first instruction of the INT 0x41 handler */
	".globl movss_int\nmovss_int: movw (%eax), %ss\n int $0x41\n ret\n"
	/* single-step through a short sequence */
	".globl ss_seq\nss_seq: pushfl\n orl $0x100, (%esp)\n popfl\n nop\n nop\n pushfl\n andl $~0x100, (%esp)\n popfl\n ret\n"
	".globl rep_movs\nrep_movs: rep movsl\n ret\n");
extern char bp_fn[], bp_gp[], movss_nop[], movss_n1[], movss_n2[], movss_int[], ss_seq[], rep_movs[];

static volatile u32 db_count, db_set_rf, db_dr6[8], db_eip[8], db_efl[8], db_ecx[8];
static int db_hook(struct frame *f) {
	if (f->vec != 1) return 0;
	u32 i = db_count++;
	if (i < 8) { db_dr6[i] = RDDR(6); db_eip[i] = f->eip; db_efl[i] = f->eflags; db_ecx[i] = f->ecx; }
	WRDR(6, 0);
	if (db_set_rf) f->eflags |= 0x10000;
	return 1;
}
static void db_reset(void) { db_count = 0; db_set_rf = 0; for (int i = 0; i < 8; i++) db_dr6[i] = db_eip[i] = db_efl[i] = 0; }
static void db_show2(const char *what, int eip) {
	kprintf("%s: n=%d", what, db_count);
	for (u32 i = 0; i < db_count && i < 4; i++) {
		kprintf(" [dr6=%x", db_dr6[i]);
		if (eip) kprintf(" eip=%x", db_eip[i]);
		kprintf(" rf=%d]", (db_efl[i] >> 16) & 1);
	}
	kputc('\n');
}
static void db_show(const char *what) { db_show2(what, 1); }

static volatile u32 var[4] __attribute__((aligned(16)));
static volatile u32 ssvar;
static u32 src[8], dst[8];
static void callf(char *f) { void (*volatile g)(void) = (void (*)(void))f; g(); }

void test_debug(void) {
	trap_hook = db_hook;
	WRDR(6, 0);
	kprintf("db.dr6.init: %x dr7=%x\n", RDDR(6), RDDR(7));

	/* instruction breakpoint: fault before execution; handler sets RF to resume */
	db_reset(); db_set_rf = 1;
	WRDR(0, (u32)bp_fn); WRDR(7, 0x1);
	callf(bp_fn); callf(bp_fn);
	db_show("db.exec");
	/* G0 instead of L0, and a disabled breakpoint does not fire */
	db_reset(); db_set_rf = 1;
	WRDR(7, 0x2); callf(bp_fn);
	WRDR(7, 0x0); callf(bp_fn);
	db_show("db.exec.g0");

	/* data breakpoints: traps after the access */
	db_reset();
	WRDR(1, (u32)&var[1]); WRDR(7, 0x4 | (1 << 20) | (3 << 22));    /* DR1: write, 4 bytes */
	var[1] = 5; (void)var[1]; var[0] = 1; var[2] = 2;
	db_show("db.write");
	db_reset();
	WRDR(7, 0x4 | (3 << 20) | (3 << 22));                            /* DR1: read/write, 4 bytes */
	(void)var[1]; ((volatile u8 *)var)[7] = 1; (void)var[2];
	db_show("db.rw");
	db_reset();
	WRDR(1, (u32)&var[1] + 2); WRDR(7, 0x4 | (1 << 20) | (1 << 22)); /* DR1: write, 2 bytes */
	((volatile u8 *)var)[6] = 1; ((volatile u8 *)var)[8] = 1; ((volatile u8 *)var)[4] = 1;
	db_show("db.len2");
	db_reset();
	WRDR(1, (u32)&var[0]); WRDR(7, 0x4 | (1 << 20) | (2 << 22));     /* DR1: write, 8 bytes */
	((volatile u8 *)var)[7] = 1; ((volatile u8 *)var)[8] = 1;
	db_show("db.len8");

	/* two breakpoints matching one access */
	db_reset();
	WRDR(0, (u32)&var[2]); WRDR(1, (u32)&var[2]);
	WRDR(7, 0x5 | (1 << 16) | (3 << 18) | (3 << 20) | (3 << 22));
	var[2] = 9;
	db_show2("db.two", 0);

	/* single step */
	db_reset(); WRDR(7, 0);
	callf(ss_seq);
	db_show("db.step");

	/* general detect: MOV DR faults with BD; the handler entry clears GD */
	db_reset();
	trap_hook = 0;
	WRDR(7, 0x2000);
	int v = TRY((void)RDDR(0));
	kprintf("db.gd: vec=%x dr6=%x eip=%x dr7=%x\n", v, last.dr6, last.eip, RDDR(7));
	trap_hook = db_hook;
	WRDR(6, 0);

	/* I/O breakpoint (CR4.DE) on port 0x80 */
	db_reset();
	WRCR(4, RDCR(4) | 0x8);
	WRDR(2, 0x80); WRDR(7, 0x10 | (2 << 24));
	outb(0x80, 1); outb(0x81, 1); (void)inb(0x80);
	db_show("db.io");
	WRCR(4, RDCR(4) & ~0x8);

	/* instruction breakpoint on an instruction that then faults: the fault image has RF = 1 */
	db_reset(); db_set_rf = 1;
	WRDR(0, (u32)bp_gp); WRDR(7, 0x1);
	trap_hook = db_hook;
	v = TRY(({ register u32 a __asm__("eax") = 0x1234; __asm__ volatile("call bp_gp" :: "r"(a) : "memory"); }));
	db_show("db.exec.fault");
	kprintf("db.exec.fault.gp: vec=%x err=%x rf=%d\n", v, last.err, (last.eflags >> 16) & 1);

	/* MOV SS delays the data-breakpoint trap past the next instruction */
	db_reset();
	ssvar = KDATA;
	WRDR(3, (u32)&ssvar); WRDR(7, 0x40 | (3 << 28) | (1u << 30));    /* DR3: read/write, 2 bytes */
	__asm__ volatile("call movss_nop" :: "a"(&ssvar) : "memory");
	db_show2("db.movss", 0);
	kprintf("db.movss.at_n2: %d\n", db_eip[0] == (u32)movss_n2);
	db_reset();
	v = TRY(({ __asm__ volatile("call movss_int" :: "a"(&ssvar) : "memory"); }));
	db_show2("db.movss.int", 0);
	kprintf("db.movss.int.at_handler: %d vec=%x\n", db_eip[0] == (u32)isr_base + 16 * 0x41, v);

	/* data breakpoint inside REP MOVS: trap after the matching iteration, EIP at the instruction */
	db_reset();
	WRDR(3, (u32)&dst[3]); WRDR(7, 0x40 | (1 << 28) | (3u << 30));
	__asm__ volatile("cld\n call rep_movs" :: "S"(src), "D"(dst), "c"(8) : "memory");
	db_show2("db.rep", 0);
	kprintf("db.rep.ecx: %x at_insn=%d\n", db_ecx[0], db_eip[0] == (u32)rep_movs);

	WRDR(7, 0);
	WRDR(6, 0);
	trap_hook = 0;
}
