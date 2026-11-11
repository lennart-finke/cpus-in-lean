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

/* ---- SMP workstream: APIC errors and the AMD local APIC (AMD APM vol. 2, chapter 16) ---- */
#include "smp.h"

static volatile u32 a2_log[16], a2_n, a2_noeoi;
static int a2_hook(struct frame *f) {
	if (f->vec < 0x20 || f->vec == 0xFF) return 0;
	if (a2_n < 16) a2_log[a2_n] = f->vec;
	a2_n++;
	if (!a2_noeoi) LR(0xB0) = 0;
	return 1;
}
static void a2_show(const char *what) {
	kprintf("%s: n=%d", what, a2_n);
	for (u32 i = 0; i < a2_n && i < 8; i++) kprintf(" %x", a2_log[i]);
	kputc('\n');
	a2_n = 0;
}
static u32 esr(void) { LR(0x280) = 0; return LR(0x280); }

/* QEMU-compared: illegal register address, illegal vectors, the error interrupt */
void test_apic_errors(void) {
	trap_hook = a2_hook;
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0x370) = 0x10000;
	esr(); esr();
	kprintf("apic.esr.clean: %x\n", esr());
	u32 v = LR(0x40);   /* unimplemented register */
	kprintf("apic.esr.ira: read=%x esr=%x\n", v, esr());
	/* (an IPI with an illegal vector is model-only: TCG delivers it, as vector 5 here) */
	LR(0x370) = 0xE5;   /* error interrupt unmasked */
	v = LR(0x50);
	sti_nops();
	a2_show("apic.esr.lvterr");
	kprintf("apic.esr.lvterr.esr: %x\n", esr());
	LR(0x370) = 0x10000;
	esr();
	trap_hook = 0;
}

/* Model-only: the AMD-specific parts that TCG lacks (APR, remote read, extended APIC space, SEOI, IER,
   SAE, LVT timer with an illegal vector, LINT0 in fixed mode). */
void test_apic_model(void) {
	trap_hook = a2_hook;
	outb(0x21, 0xFF); outb(0xA1, 0xFF);
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0x370) = 0x10000;
	esr(); esr();
	kprintf("apicm.version: %x extfeat=%x extctl=%x ier7=%x xlvt=%x %x %x %x\n", LR(0x30), LR(0x400),
	        LR(0x410), LR(0x4F0), LR(0x500), LR(0x510), LR(0x520), LR(0x530));
	/* APR: highest of TPR and the classes of ISR/IRR (APM 16.6.2) */
	LR(0x80) = 0x35;
	kprintf("apicm.apr.tpr: apr=%x ppr=%x\n", LR(0x90), LR(0xA0));
	LR(0x310) = 0; LR(0x300) = 0x40000 | 0x71;   /* pending, IF = 0 */
	kprintf("apicm.apr.irr: apr=%x ppr=%x\n", LR(0x90), LR(0xA0));
	LR(0x80) = 0;
	sti_nops();
	a2_show("apicm.apr.int");
	/* remote read of this APIC's own TPR (APM 16.5: message type 011b, vector = offset / 16) */
	LR(0x80) = 0x42;
	LR(0x310) = 0; LR(0x300) = 0x300 | 0x08;
	kprintf("apicm.rr.self: icr=%x rrr=%x\n", LR(0x300) & 0x30F00, LR(0xC0));
	LR(0x310) = 0x05000000; LR(0x300) = 0x300 | 0x08;   /* no APIC with ID 5 */
	kprintf("apicm.rr.absent: icr=%x\n", LR(0x300) & 0x30F00);
	LR(0x310) = 0; LR(0x300) = 0x300 | 0x04;   /* unimplemented register 40h */
	kprintf("apicm.rr.invalid: icr=%x\n", LR(0x300) & 0x30F00);
	LR(0x80) = 0;
	/* SAE: an IPI no APIC accepts; SIV + RIV: illegal vector */
	esr();
	LR(0x310) = 0x05000000; LR(0x300) = 0x61;
	kprintf("apicm.esr.sae: %x\n", esr());
	LR(0x310) = 0; LR(0x300) = 0x40000 | 0x0F;
	kprintf("apicm.esr.ivec: %x\n", esr());
	/* LVT timer with an illegal vector: RIV when it fires */
	LR(0x3E0) = 0xB; LR(0x320) = 0x08; LR(0x380) = 50;
	for (volatile int i = 0; i < 200; i++) {}
	kprintf("apicm.esr.timerivec: %x irr0=%x\n", esr(), LR(0x200));
	LR(0x320) = 0x10000; LR(0x380) = 0;
	/* writes to read-only registers are ignored; to an unimplemented one: IRA */
	LR(0x30) = 0; LR(0xA0) = 0xFF; LR(0x390) = 5;
	kprintf("apicm.esr.rowrite: %x version=%x\n", esr(), LR(0x30));
	LR(0x60) = 1;
	kprintf("apicm.esr.badwrite: %x\n", esr());
	/* SEOI (APM 16.7.1): ignored without SN; with SN retires the named vector, not the highest */
	a2_noeoi = 1;
	LR(0x310) = 0; LR(0x300) = 0x40000 | 0x81;
	sti_nops();
	LR(0x300) = 0x40000 | 0x91;
	sti_nops();
	a2_noeoi = 0;
	a2_show("apicm.seoi.taken");
	LR(0x420) = 0x81;
	kprintf("apicm.seoi.off: isr=%x %x\n", LR(0x140), LR(0x150));
	LR(0x410) = 2;
	LR(0x420) = 0x81;
	kprintf("apicm.seoi.on: extctl=%x isr=%x %x ppr=%x\n", LR(0x410), LR(0x140), LR(0x150), LR(0xA0));
	LR(0x420) = 0x91;
	kprintf("apicm.seoi.on2: isr=%x %x ppr=%x\n", LR(0x140), LR(0x150), LR(0xA0));
	LR(0x410) = 0;
	/* IER (APM 16.7.2): writes need IERN; with IERN a disabled vector stays pending */
	LR(0x4A0) = 0;
	kprintf("apicm.ier.noiern: ier2=%x\n", LR(0x4A0));
	LR(0x410) = 1;
	LR(0x4A0) = ~(1u << (0x45 & 31));
	LR(0x310) = 0; LR(0x300) = 0x40000 | 0x45; LR(0x300) = 0x40000 | 0x46;
	sti_nops();
	a2_show("apicm.ier.masked");
	kprintf("apicm.ier.pending: irr2=%x ppr=%x\n", LR(0x220), LR(0xA0));
	LR(0x4A0) = 0xFFFFFFFF;
	sti_nops();
	a2_show("apicm.ier.released");
	LR(0x410) = 0;
	/* extended LVT entries: storage, masked by a software disable */
	LR(0x500) = 0x12345; LR(0x530) = 0x1FFFFFFF;
	kprintf("apicm.xlvt: %x %x\n", LR(0x500), LR(0x530));
	LR(0xF0) = 0xFF;
	kprintf("apicm.xlvt.swdisable: %x %x\n", LR(0x500), LR(0x530));
	LR(0xF0) = 0x1FF;
	LR(0x500) = 0x10000; LR(0x530) = 0x10000;
	/* LINT0 in fixed mode, edge-triggered: the PIC's INTR is the input pin (PIT IRQ 0 via the PIC) */
	outb(0x20, 0x11); outb(0x21, 0x20); outb(0x21, 0x04); outb(0x21, 0x01); outb(0x21, 0xFE);
	outb(0xA0, 0x11); outb(0xA1, 0x28); outb(0xA1, 0x02); outb(0xA1, 0x01); outb(0xA1, 0xFF);
	LR(0x350) = 0x00066;
	pit_oneshot(100);
	for (int k = 0; k < 2000 && !a2_n; k++) sti_nops();
	a2_show("apicm.lint0.fixed");
	kprintf("apicm.lint0.state: lvt0=%x pic_irr=%x\n", LR(0x350), inb(0x20));
	outb(0x21, 0xFF);
	LR(0x350) = 0x700;
	trap_hook = 0;
}
