/* I/O APIC (Intel 82093AA at 0xFEC00000): registers, redirection entries, edge and level triggering,
   remote IRR and the EOI message from the local APIC, masking, destination modes, delivery modes.
   Sources: the PIT (ISA IRQ 0 on pin 2) and the UART's THR-empty interrupt (IRQ 4, a level). The
   PICs stay masked: the ISA lines reach the I/O APIC directly. */
#include "smp.h"

static volatile u32 io_log[16], io_n, io_rirr, io_uart_eoi_first, io_limit;
static int io_hook(struct frame *f) {
	if (f->vec != 2 && (f->vec < 0x20 || f->vec == 0xFF)) return 0;
	if (io_n < 16) io_log[io_n] = f->vec;
	io_n++;
	if (f->vec == 0x62) {   /* UART THR empty, level-triggered on pin 4 */
		io_rirr = (ioapic_rd(0x18) >> 14) & 1;
		if (io_uart_eoi_first && io_n < 2) { LR(0xB0) = 0; return 1; }   /* EOI with the line still asserted */
		(void)inb(0x3FA);   /* IIR read clears THRE: the line drops */
	}
	if (f->vec == 0x6F) {   /* active-low pin that is always asserted: stop after io_limit */
		if (io_n >= io_limit) ioapic_wr(0x22, ioapic_rd(0x22) | 0x10000);
	}
	if (f->vec != 2) LR(0xB0) = 0;
	return 1;
}
static void io_show(const char *what) {
	kprintf("%s: n=%d", what, io_n);
	for (u32 i = 0; i < io_n && i < 8; i++) kprintf(" %x", io_log[i]);
	kputc('\n');
	io_n = 0;
}
/* PIT channel 0 one-shot with `count` ticks; wait for its interrupt (or a bounded number of HLTs) */
static void pit_wait(u16 count) {
	pit_oneshot(count);
	for (int k = 0; k < 200 && !io_n; k++) __asm__ volatile("sti\n hlt\n cli" ::: "memory");
}
/* PIT channel 0 one-shot that has certainly reached terminal count when this returns (polled) */
static void pit_expire(u16 count) {
	pit_oneshot(count);
	for (;;) {
		outb(0x43, 0x00);
		u32 c = inb(0x40); c |= (u32)inb(0x40) << 8;
		if (c > count) break;
	}
}
static void uart_irq(int on, u8 mcr0) {
	if (on) { outb(0x3FC, mcr0 | 0x08); outb(0x3F9, 0x02); }
	else { outb(0x3F9, 0x00); outb(0x3FC, mcr0); (void)inb(0x3FA); }
}

static void io_setup(void) {
	outb(0x21, 0xFF); outb(0xA1, 0xFF);
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x01000000;
	LR(0x350) = 0x10700;   /* LINT0 masked: no virtual wire */
	for (int p = 0; p < 24; p++) ioapic_entry(p, 0x10000, 0);
	io_n = 0;
}

void test_ioapic(void) {
	trap_hook = io_hook;
	io_setup();
	kprintf("ioapic.version: %x\n", ioapic_rd(1));
	u32 id0 = ioapic_rd(0);
	ioapic_wr(0, 0x0A000000);
	kprintf("ioapic.id: %x arb=%x\n", ioapic_rd(0), ioapic_rd(2));
	ioapic_wr(0, id0);
	ioapic_wr(0x1A, 0x000000E5); ioapic_wr(0x1B, 0x03000000);
	kprintf("ioapic.redir: %x %x\n", ioapic_rd(0x1A), ioapic_rd(0x1B));
	ioapic_entry(5, 0x10000, 0);
	kprintf("ioapic.redir.reset: %x %x\n", ioapic_rd(0x10), ioapic_rd(0x11));

	/* edge-triggered, fixed, physical destination 0: the PIT on pin 2 */
	ioapic_entry(2, 0x61, 0x00000000);
	pit_wait(500);
	io_show("ioapic.edge");
	kprintf("ioapic.edge.entry: %x\n", ioapic_rd(0x14));
	/* a masked edge is lost (82093AA) */
	ioapic_entry(2, 0x10061, 0);
	pit_expire(100);
	ioapic_wr(0x14, 0x61);
	sti_nops();
	io_show("ioapic.edge.masked");
	/* logical destination (flat model): LDR 01h matches 03h, not 02h */
	ioapic_entry(2, 0x800 | 0x63, 0x03000000);
	pit_wait(500);
	io_show("ioapic.logical.match");
	ioapic_entry(2, 0x800 | 0x63, 0x02000000);
	pit_expire(100);
	sti_nops();
	io_show("ioapic.logical.nomatch");
	/* lowest priority (one CPU) and NMI delivery modes */
	ioapic_entry(2, 0x900 | 0x64, 0x01000000);
	pit_wait(500);
	io_show("ioapic.lowpri");
	ioapic_entry(2, 0x400, 0);
	pit_wait(500);
	io_show("ioapic.nmi");
	/* physical destination of an absent APIC: nobody gets it */
	ioapic_entry(2, 0x65, 0x07000000);
	pit_expire(100);
	sti_nops();
	io_show("ioapic.absent");
	ioapic_entry(2, 0x10000, 0);

	/* level-triggered: the UART's THR-empty interrupt on pin 4; remote IRR until the EOI */
	u8 mcr0 = inb(0x3FC);
	ioapic_entry(4, 0x8000 | 0x62, 0);
	io_uart_eoi_first = 0;
	uart_irq(1, mcr0);
	for (int k = 0; k < 50 && !io_n; k++) sti_nops();
	uart_irq(0, mcr0);
	io_show("ioapic.level");
	kprintf("ioapic.level.rirr: in_handler=%d after=%d\n", io_rirr, (ioapic_rd(0x18) >> 14) & 1);
	/* EOI while the line is still asserted: the entry sends again */
	io_uart_eoi_first = 1;
	uart_irq(1, mcr0);
	for (int k = 0; k < 50 && io_n < 2; k++) sti_nops();
	uart_irq(0, mcr0);
	io_show("ioapic.level.reassert");
	/* masked level interrupt: held until unmasked */
	io_uart_eoi_first = 0;
	ioapic_entry(4, 0x18000 | 0x62, 0);
	uart_irq(1, mcr0);
	sti_nops();
	io_show("ioapic.level.masked");
	ioapic_wr(0x18, 0x8000 | 0x62);
	for (int k = 0; k < 50 && !io_n; k++) sti_nops();
	uart_irq(0, mcr0);
	io_show("ioapic.level.unmasked");
	ioapic_entry(4, 0x10000, 0);
	LR(0x350) = 0x700;
	trap_hook = 0;
}

/* Model-only: polarity (TCG ignores the polarity bit), ExtINT through the PIC, writing an edge-triggered
   entry clears remote IRR. */
void test_ioapic_model(void) {
	trap_hook = io_hook;
	io_setup();
	kprintf("ioapicm.version: %x\n", ioapic_rd(1));
	/* active-low, level-triggered pin 9 (no source: the line is low, so the pin is asserted) */
	io_limit = 3;
	ioapic_entry(9, 0xA000 | 0x6F, 0);
	for (int k = 0; k < 20 && io_n < 3; k++) sti_nops();
	io_show("ioapicm.polarity.low");
	kprintf("ioapicm.polarity.entry: %x\n", ioapic_rd(0x22));
	/* remote IRR is cleared by rewriting the entry as edge-triggered (the 82093AA idiom Linux uses) */
	ioapic_entry(9, 0x1A000 | 0x6F, 0);
	ioapic_wr(0x22, 0x12000 | 0x6F);
	kprintf("ioapicm.rirr.edge: %x\n", ioapic_rd(0x22));
	ioapic_entry(9, 0x10000, 0);
	/* ExtINT: the PIC supplies the vector (master base 30h, IRQ 0 -> 30h) */
	outb(0x20, 0x11); outb(0x21, 0x30); outb(0x21, 0x04); outb(0x21, 0x01); outb(0x21, 0xFE);
	ioapic_entry(2, 0x700, 0);
	pit_wait(500);
	io_show("ioapicm.extint");
	outb(0x20, 0x20);
	outb(0x21, 0xFF);
	ioapic_entry(2, 0x10000, 0);
	LR(0x350) = 0x700;
	trap_hook = 0;
}
