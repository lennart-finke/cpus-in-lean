/* Local APIC: registers, self-IPIs and priorities, EOI, timer. Every register printed is first set
   by the test (firmware leaves QEMU's APIC in a non-reset state). Timer tests print only facts that
   do not depend on the speed of time (QEMU's timer runs on host time, the model's on instructions). */
#include "sys.h"

#define APIC ((volatile u32 *)0xFEE00000)
#define R(off) APIC[(off) >> 2]

static volatile u32 seq[16], nseq, eoi_in_handler, timer_hits, ppr_in[16], isr_in[16];
static int apic_hook(struct frame *f) {
	if (f->vec < 0x50 || f->vec >= 0xF0) return 0;
	u32 i = nseq++;
	if (i < 16) { seq[i] = f->vec; ppr_in[i] = R(0xA0); isr_in[i] = R(0x100 + ((f->vec >> 5) << 4)); }
	if (f->vec == 0x65) timer_hits++;
	if (eoi_in_handler) R(0xB0) = 0;
	return 1;
}
static void show(const char *what) {
	kprintf("%s: n=%d", what, nseq);
	for (u32 i = 0; i < nseq && i < 8; i++) kprintf(" [%x ppr=%x isr=%x]", seq[i], ppr_in[i], isr_in[i]);
	kputc('\n');
	nseq = 0;
}
static void ipi_self(u32 vec) { R(0x310) = 0; R(0x300) = 0x40000 | vec; }
static void sti_window(void) { __asm__ volatile("sti\n nop\n nop\n cli" ::: "memory"); }
static void spin(void) { for (volatile int i = 0; i < 20000; i++) {} }

void test_apic(void) {
	outb(0x21, 0xFF); outb(0xA1, 0xFF);   /* PIC masked: only the APIC interrupts */
	trap_hook = apic_hook;
	kprintf("apic.base: %x\n", (u32)rdmsr(0x1B) & 0xFFFFF900);
	kprintf("apic.version: %x\n", R(0x30) & 0xFF00FF);
	R(0x80) = 0; R(0xE0) = 0xFFFFFFFF; R(0xD0) = 0x01000000;
	R(0xF0) = 0x1FF;
	R(0x350) = 0x10700; R(0x360) = 0x10400; R(0x370) = 0x10000; R(0x320) = 0x10000;
	kprintf("apic.regs: svr=%x tpr=%x ppr=%x dfr=%x ldr=%x lint0=%x\n", R(0xF0), R(0x80), R(0xA0),
	        R(0xE0), R(0xD0), R(0x350));

	/* self-IPIs: requested while IF = 0, delivered highest class first */
	eoi_in_handler = 1;
	ipi_self(0x61); ipi_self(0x71); ipi_self(0x51);
	kprintf("apic.irr: %x %x %x\n", R(0x220), R(0x230), R(0x240) | R(0x250));
	sti_window();
	show("apic.ipi.order");
	kprintf("apic.irr.after: %x %x isr=%x\n", R(0x220), R(0x230), R(0x130));

	/* TPR blocks classes at or below it */
	R(0x80) = 0x70;
	ipi_self(0x61);
	sti_window();
	show("apic.tpr.blocked");
	kprintf("apic.tpr.ppr: %x irr=%x\n", R(0xA0), R(0x230));
	R(0x80) = 0;
	sti_window();
	show("apic.tpr.released");

	/* no EOI: the in-service vector raises PPR; only higher classes get through */
	eoi_in_handler = 0;
	ipi_self(0x80);
	sti_window();
	ipi_self(0x70); ipi_self(0x90);
	sti_window();
	show("apic.noeoi");
	kprintf("apic.noeoi.state: ppr=%x isr4=%x irr3=%x\n", R(0xA0), R(0x140), R(0x230));
	R(0xB0) = 0;   /* retires 0x90 */
	kprintf("apic.eoi1: ppr=%x isr4=%x\n", R(0xA0), R(0x140));
	R(0xB0) = 0;   /* retires 0x80 */
	eoi_in_handler = 1;
	sti_window();
	show("apic.eoi.released");

	/* logical destination (flat model) and a non-matching physical destination */
	R(0x310) = 0x01000000; R(0x300) = 0x800 | 0x62;
	R(0x310) = 0x05000000; R(0x300) = 0x63;
	sti_window();
	show("apic.dest");

	/* timer: one-shot, periodic, masked */
	R(0x3E0) = 0xB;   /* divide by 1 */
	kprintf("apic.timer.div: %x\n", R(0x3E0));
	timer_hits = 0;
	R(0x320) = 0x65;
	R(0x380) = 5000;
	while (!timer_hits) __asm__ volatile("sti\n hlt\n cli" ::: "memory");   /* STI shadow: no lost wakeup */
	kprintf("apic.timer.oneshot: fired=%d cur=%x init=%x\n", timer_hits, R(0x390), R(0x380));
	timer_hits = 0;
	R(0x320) = 0x20065;
	R(0x380) = 1000000;   /* long period: no expiry races the stop below on host-timed QEMU */
	while (timer_hits < 3) __asm__ volatile("sti\n hlt\n cli" ::: "memory");
	R(0x380) = 0;
	kprintf("apic.timer.periodic: fired3=%d cur=%x\n", timer_hits >= 3, R(0x390));
	/* drain an expiry that host-timed QEMU may already have queued before the stop (seen under load) */
	R(0x320) = 0x10065;
	for (int k = 0; k < 4; k++) sti_window();
	nseq = 0;
	R(0x320) = 0x10065;
	R(0x380) = 0x7FFFFFFF;
	u32 c0 = R(0x390); spin(); u32 c1 = R(0x390);
	timer_hits = 0;
	__asm__ volatile("sti\n nop\n cli");
	kprintf("apic.timer.masked: decreasing=%d fired=%d\n", c1 < c0 && c0 <= 0x7FFFFFFF, timer_hits);
	R(0x380) = 0;

	/* software disable masks the LVT entries and stops delivery */
	R(0xF0) = 0xFF;
	kprintf("apic.swdisable: lvt_timer=%x lint1=%x\n", R(0x320), R(0x360));
	R(0x320) = 0x66;
	kprintf("apic.swdisable.write: lvt_timer=%x\n", R(0x320));
	ipi_self(0x67);
	sti_window();
	show("apic.swdisable.ipi");
	R(0xF0) = 0x1FF;
	sti_window();
	show("apic.reenable");
	trap_hook = 0;
}
