/* x2APIC mode (AMD APM vol. 2, 16.8-16.15): IA32_APIC_BASE transitions, the MSR interface 800h-8FFh
   with its read-only/write-only/reserved-bit rules, the 64-bit ICR and SELF IPI, 32-bit IDs and the
   derived logical ID, the memory-mapped page disabled. Ends back in xAPIC mode. */
#include "smp.h"

static volatile u32 x2_log[16], x2_n;
static int x2_hook(struct frame *f) {
	if (f->vec < 0x20 || f->vec == 0xFF) return 0;
	if (x2_n < 16) x2_log[x2_n] = f->vec;
	x2_n++;
	wrmsr(0x80B, 0);
	return 1;
}
static void x2_show(const char *what) {
	kprintf("%s: n=%d", what, x2_n);
	for (u32 i = 0; i < x2_n && i < 8; i++) kprintf(" %x", x2_log[i]);
	kputc('\n');
	x2_n = 0;
}
static void gp_line(const char *what, int vec) { kprintf("%s: %s\n", what, vec == 13 ? "gp" : vec == 0xFFFF ? "ok" : "other"); }

/* Back to xAPIC mode through the disabled state, with the registers the other tests expect. */
static void x2_restore(u64 base) {
	(void)try_wrmsr(0x1B, base & ~0xC00ull);
	(void)try_wrmsr(0x1B, (base & ~0x400ull) | 0x800);
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x01000000;
	LR(0x350) = 0x700; LR(0x360) = 0x10400; LR(0x370) = 0x10000; LR(0x320) = 0x10000;
}

void test_x2apic(void) {
	if (!has_feature(1, 0, 2, 21)) { kputs("x2apic: absent\n"); return; }
	trap_hook = x2_hook;
	outb(0x21, 0xFF); outb(0xA1, 0xFF);
	u64 base = rdmsr(0x1B);
	u64 v = 0;
	kprintf("x2apic.base: %x\n", (u32)base & 0xD00);
	gp_line("x2apic.msr.xapic.rd", try_rdmsr(0x802, &v));
	gp_line("x2apic.msr.xapic.wr", try_wrmsr(0x808, 0));
	gp_line("x2apic.base.extd_only", try_wrmsr(0x1B, (base & ~0xC00ull) | 0x400));
	gp_line("x2apic.base.enter", try_wrmsr(0x1B, base | 0xC00));
	kprintf("x2apic.base.x2: %x\n", (u32)rdmsr(0x1B) & 0xD00);
	u32 id = (u32)rdmsr(0x802);
	kprintf("x2apic.regs: id=%x ver=%x ldr=%x ldr_ok=%d\n", id, (u32)rdmsr(0x803) & 0xFF00FF, (u32)rdmsr(0x80D),
	        (u32)rdmsr(0x80D) == (((id >> 4) << 16) | (1u << (id & 15))));
	kprintf("x2apic.mmio: %x\n", LR(0x30));
	gp_line("x2apic.base.toxapic", try_wrmsr(0x1B, (base | 0x800) & ~0x400ull));
	/* register rules */
	gp_line("x2apic.id.write", try_wrmsr(0x802, 0));
	gp_line("x2apic.ver.write", try_wrmsr(0x803, 0));
	gp_line("x2apic.ppr.write", try_wrmsr(0x80A, 0));
	gp_line("x2apic.ldr.write", try_wrmsr(0x80D, 0));
	gp_line("x2apic.isr.write", try_wrmsr(0x810, 0));
	gp_line("x2apic.ccr.write", try_wrmsr(0x839, 0));
	gp_line("x2apic.eoi.read", try_rdmsr(0x80B, &v));
	gp_line("x2apic.selfipi.read", try_rdmsr(0x83F, &v));
	gp_line("x2apic.eoi.nonzero", try_wrmsr(0x80B, 1));
	gp_line("x2apic.esr.nonzero", try_wrmsr(0x828, 1));
	gp_line("x2apic.esr.zero", try_wrmsr(0x828, 0));
	gp_line("x2apic.dfr.read", try_rdmsr(0x80E, &v));
	gp_line("x2apic.rrr.read", try_rdmsr(0x80C, &v));
	gp_line("x2apic.icrhi.read", try_rdmsr(0x831, &v));
	gp_line("x2apic.unimpl.read", try_rdmsr(0x804, &v));
	gp_line("x2apic.tpr.rsvd", try_wrmsr(0x808, 0x100));
	gp_line("x2apic.tpr.hi", try_wrmsr(0x808, 0x100000000ull));
	gp_line("x2apic.selfipi.rsvd", try_wrmsr(0x83F, 0x171));
	/* interrupts */
	wrmsr(0x80F, 0x1FF); wrmsr(0x808, 0);
	wrmsr(0x83F, 0x71);
	sti_nops();
	x2_show("x2apic.selfipi");
	wrmsr(0x830, ((u64)id << 32) | 0x72);
	sti_nops();
	x2_show("x2apic.icr.phys");
	kprintf("x2apic.icr.read: %x %x\n", (u32)(rdmsr(0x830) >> 32) == id, (u32)rdmsr(0x830));
	wrmsr(0x830, (0xFFFFFFFFull << 32) | 0x73);
	sti_nops();
	x2_show("x2apic.icr.broadcast");
	wrmsr(0x830, ((u64)(u32)rdmsr(0x80D) << 32) | 0x800 | 0x74);
	sti_nops();
	x2_show("x2apic.icr.logical");
	wrmsr(0x830, ((u64)(id + 1) << 32) | 0x75);   /* no such APIC */
	sti_nops();
	x2_show("x2apic.icr.absent");
	wrmsr(0x808, 0x80);
	wrmsr(0x83F, 0x76); wrmsr(0x83F, 0x96);
	sti_nops();
	x2_show("x2apic.tpr.blocked");
	kprintf("x2apic.tpr: ppr=%x irr3=%x\n", (u32)rdmsr(0x80A), (u32)rdmsr(0x823));
	wrmsr(0x808, 0);
	sti_nops();
	x2_show("x2apic.tpr.released");
	wrmsr(0x83E, 0xB); wrmsr(0x832, 0x10077); wrmsr(0x838, 0x7FFFFFFF);
	u32 c0 = (u32)rdmsr(0x839);
	for (volatile int i = 0; i < 2000; i++) {}
	u32 c1 = (u32)rdmsr(0x839);
	kprintf("x2apic.timer: decreasing=%d div=%x lvt=%x\n", c1 < c0, (u32)rdmsr(0x83E), (u32)rdmsr(0x832));
	wrmsr(0x838, 0);
	/* leaving x2APIC mode: only to disabled; disabled -> x2APIC is invalid */
	gp_line("x2apic.base.leave", try_wrmsr(0x1B, base & ~0xC00ull));
	kprintf("x2apic.base.disabled: %x\n", (u32)rdmsr(0x1B) & 0xD00);
	gp_line("x2apic.base.disabled_to_x2", try_wrmsr(0x1B, base | 0xC00));
	gp_line("x2apic.base.reenable", try_wrmsr(0x1B, (base & ~0x400ull) | 0x800));
	kprintf("x2apic.base.xapic: %x version=%x\n", (u32)rdmsr(0x1B) & 0xD00, LR(0x30) & 0xFF00FF);
	x2_restore(base);
	trap_hook = 0;
}

/* Model-only: AMD's x2APIC rules TCG does not check (eliminated ICR message types, reserved ICR and
   SVR bits, no TSC-deadline mode), the extended registers, the xAPIC ID carried into x2APIC mode, and
   the CPUID topology leaves of a one-CPU machine. */
void test_x2apic_model(void) {
	trap_hook = x2_hook;
	u64 base = rdmsr(0x1B);
	u32 r[4];
	cpuid(1, 0, r);
	kprintf("x2apicm.cpuid1: ebx=%x htt=%d x2apic=%d\n", r[1], (r[3] >> 28) & 1, (r[2] >> 21) & 1);
	cpuid(0xB, 0, r);
	kprintf("x2apicm.cpuidb.0: %x %x %x %x\n", r[0], r[1], r[2], r[3]);
	cpuid(0xB, 1, r);
	kprintf("x2apicm.cpuidb.1: %x %x %x %x\n", r[0], r[1], r[2], r[3]);
	cpuid(0xB, 2, r);
	kprintf("x2apicm.cpuidb.2: %x %x %x %x\n", r[0], r[1], r[2], r[3]);
	cpuid(0x80000001, 0, r);
	kprintf("x2apicm.cpuid81: cmplegacy=%d extapic=%d topoext=%d\n", (r[2] >> 1) & 1, (r[2] >> 3) & 1, (r[2] >> 22) & 1);
	cpuid(0x80000008, 0, r);
	kprintf("x2apicm.cpuid88: ecx=%x\n", r[2]);
	/* xAPIC ID written by software becomes the x2APIC ID (APM 16.9.1) */
	LR(0x20) = 0x05000000;
	wrmsr(0x1B, base | 0xC00);
	kprintf("x2apicm.id: %x ldr=%x\n", (u32)rdmsr(0x802), (u32)rdmsr(0x80D));
	gp_line("x2apicm.icr.lowpri", try_wrmsr(0x830, (5ull << 32) | 0x100 | 0x70));
	gp_line("x2apicm.icr.remoteread", try_wrmsr(0x830, (5ull << 32) | 0x300 | 0x08));
	gp_line("x2apicm.icr.extint", try_wrmsr(0x830, (5ull << 32) | 0x700));
	gp_line("x2apicm.icr.ds", try_wrmsr(0x830, (5ull << 32) | 0x1000 | 0x70));
	gp_line("x2apicm.icr.rrs", try_wrmsr(0x830, (5ull << 32) | 0x10000 | 0x70));
	gp_line("x2apicm.svr.bit12", try_wrmsr(0x80F, 0x11FF));
	gp_line("x2apicm.lvt.tscdeadline", try_wrmsr(0x832, 0x40070));
	gp_line("x2apicm.lvt.ro_ds", try_wrmsr(0x832, 0x11070));
	kprintf("x2apicm.ext: feat=%x ctl=%x\n", (u32)rdmsr(0x840), (u32)rdmsr(0x841));
	gp_line("x2apicm.extfeat.write", try_wrmsr(0x840, 0));
	gp_line("x2apicm.extctl.rsvd", try_wrmsr(0x841, 8));
	gp_line("x2apicm.xlvt.rsvd", try_wrmsr(0x850, 0x20000));
	gp_line("x2apicm.unimpl.8ff", try_wrmsr(0x8FF, 0));
	wrmsr(0x80F, 0x1FF);
	wrmsr(0x83F, 0x05);   /* illegal vector: SIV and RIV */
	wrmsr(0x828, 0);
	kprintf("x2apicm.esr: %x\n", (u32)rdmsr(0x828));
	x2_restore(base);
	LR(0x20) = 0;
	trap_hook = 0;
}
