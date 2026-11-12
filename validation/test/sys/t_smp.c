/* Two CPUs (run with smp=2: QEMU -smp 2,sockets=2, x86sys --smp 2). The boot processor starts the
   application processor with INIT, INIT de-assert and STARTUP (a real-mode trampoline at 0x8000 that
   enters protected mode and calls ap_main on its own stack), then drives it through a command
   mailbox. Only the BSP prints, after the AP has reported back, so the transcript does not depend on
   how the CPUs interleave. Covered: AP startup state, IPIs of every delivery mode the QEMU part can
   compare (fixed, lowest priority, NMI, INIT, STARTUP) with physical, logical flat and cluster
   destinations and every shorthand, INIT/STARTUP restart, a TLB shootdown, the I/O APIC routing to
   the AP, x2APIC IPIs with 32-bit destinations, an MWAIT ended by the other CPU's store and LOCKed
   counters. Model-only: AMD lowest-priority arbitration and focus, ExtINT and SMI IPIs, remote read,
   SAE and the CPUID topology of each CPU. */
#include "smp.h"

#define AP_TRAMP 0x8000
#define AP_VEC (AP_TRAMP >> 12)

__asm__(
	".code16\n.globl ap_tramp\nap_tramp:\n"
	" cli\n"
	" movl %edx, %ebx\n"
	" movw %cs, %ax\n movw %ax, %ds\n"
	" movw %ax, ap_tr_cs - ap_tramp\n"
	" movl %ebx, ap_tr_edx - ap_tramp\n"
	" lgdtl ap_tr_gdtr - ap_tramp\n"
	" movl %cr0, %eax\n orl $1, %eax\n movl %eax, %cr0\n"
	" ljmpl $0x08, $ap_entry32\n"
	" .p2align 2\n"
	".globl ap_tr_gdtr\nap_tr_gdtr: .word 0\n .long 0\n"
	".globl ap_tr_cs\nap_tr_cs: .word 0\n"
	" .p2align 2\n"
	".globl ap_tr_edx\nap_tr_edx: .long 0\n"
	".globl ap_tramp_end\nap_tramp_end:\n"
	".code32\n"
	"ap_entry32:\n"
	" movl $0x10, %eax\n movl %eax, %ds\n movl %eax, %es\n movl %eax, %fs\n movl %eax, %gs\n movl %eax, %ss\n"
	" movl ap_stack_step, %eax\n lock xaddl %eax, ap_stack_top\n movl %eax, %esp\n"   /* own stack in smpn mode */
	" call ap_entry\n"
	"1: cli\n hlt\n jmp 1b\n");
extern char ap_tramp[], ap_tramp_end[], ap_tr_gdtr[], ap_tr_cs[], ap_tr_edx[];

static u8 ap_stack[8192] __attribute__((aligned(16)));
u32 ap_stack_top, ap_stack_step;   /* each AP takes the stack at ap_stack_top, which moves by ap_stack_step */

/* mailbox and logs */
static volatile u32 ap_gen, ap_ready, ap_cmd, ap_arg[4], ap_ack, ap_res[8];
static volatile u32 ap_log[32], ap_n, bsp_log[32], bsp_n, smp_x2, shoot_done;
static volatile u32 counter __attribute__((aligned(64)));
static volatile u32 mw_flag[16] __attribute__((aligned(64)));
static volatile u32 mw_armed;

static int on_ap(void) {
	u32 esp;
	__asm__ volatile("movl %%esp, %0" : "=r"(esp));
	return esp >= (u32)ap_stack && esp < (u32)ap_stack + sizeof ap_stack;
}
static void eoi(void) { if (smp_x2) wrmsr(0x80B, 0); else LR(0xB0) = 0; }
/* system B: the AP's NMI handler can be held (NMIs blocked) until the BSP releases it */
static volatile u32 ap_nmi_hold, ap_nmi_in, ap_nmi_release;
static int smp_hook(struct frame *f) {
	if (f->vec != 2 && (f->vec < 0x20 || f->vec == 0xFF)) return 0;
	if (on_ap()) {
		if (ap_n < 32) ap_log[ap_n] = f->vec;
		ap_n++;
		if (f->vec == 0x5D) { invlpg(0x800000); shoot_done = 1; }
		if (f->vec == 2 && ap_nmi_hold) {
			ap_nmi_hold = 0;
			ap_nmi_in = 1;
			while (!ap_nmi_release) cpu_relax();
		}
	} else {
		if (bsp_n < 32) bsp_log[bsp_n] = f->vec;
		bsp_n++;
	}
	if (f->vec != 2 && f->vec != 0x37) eoi();
	return 1;
}
static void spin(u32 n) { for (volatile u32 k = 0; k < n; k++) cpu_relax(); }
static void wait_until(volatile u32 *p, u32 v) { for (u32 k = 0; k < 20000000 && *p != v; k++) cpu_relax(); }
static void wait_ap_n(u32 n) { for (u32 k = 0; k < 20000000 && ap_n < n; k++) cpu_relax(); }
static void logs(const char *what) {
	sti_nops();
	kprintf("%s: bsp=%d", what, bsp_n);
	for (u32 i = 0; i < bsp_n && i < 8; i++) kprintf(" %x", bsp_log[i]);
	kprintf(" ap=%d", ap_n);
	for (u32 i = 0; i < ap_n && i < 8; i++) kprintf(" %x", ap_log[i]);
	kputc('\n');
	bsp_n = 0; ap_n = 0;
}

enum { C_APIC = 1, C_IPI, C_PG_ON, C_PG_OFF, C_READ, C_X2_ON, C_X2_OFF, C_X2_IPI, C_MWAIT, C_COUNT, C_CPUID, C_TSC, C_MWAIT1, C_CR0 };

static void ap_apic_init(void) {
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x02000000;
	LR(0x350) = 0x10700; LR(0x360) = 0x10400; LR(0x370) = 0x10000; LR(0x320) = 0x10000;
}

void ap_main(void) {
	struct { u16 lim; u32 base; } __attribute__((packed)) id = { sizeof idt - 1, (u32)idt };
	__asm__ volatile("lidt %0" :: "m"(id));
	ap_apic_init();
	u32 r[4];
	cpuid(1, 0, r);
	ap_res[0] = LR(0x20) >> 24;
	ap_res[1] = r[1] >> 24;
	ap_res[2] = *(volatile u16 *)(AP_TRAMP + (ap_tr_cs - ap_tramp));
	ap_res[3] = *(volatile u32 *)(AP_TRAMP + (ap_tr_edx - ap_tramp)) == r[0];
	/* the whole CR0 (CD and NW come from RESET and are kept by INIT) and the x87 control and tag
	   words, which RESET sets to 0040h and 5555h and INIT does not change (AMD APM vol. 2, table 14-1) */
	ap_res[4] = RDCR(0);
	{
		u8 env[28];
		__asm__ volatile("fnstenv %0" : "=m"(env));
		ap_res[5] = *(u16 *)env;
		ap_res[6] = *(u16 *)(env + 8);
	}
	ap_gen++;
	ap_ready = 1;
	for (;;) {
		u32 c;
		while (!(c = ap_cmd)) __asm__ volatile("sti\n pause\n cli" ::: "memory");
		switch (c) {
		case C_APIC: LR(0xD0) = ap_arg[0]; LR(0xE0) = ap_arg[1]; LR(0x80) = ap_arg[2]; break;
		case C_IPI: ipi(ap_arg[0], ap_arg[1]); break;
		case C_PG_ON:
			WRCR(3, ap_arg[0]); WRCR(4, RDCR(4) | 0x10); WRCR(0, RDCR(0) | 0x80000000);
			ap_res[0] = *(volatile u32 *)0x800000;
			break;
		case C_PG_OFF: WRCR(0, RDCR(0) & ~0x80000000); break;
		case C_READ: ap_res[0] = *(volatile u32 *)ap_arg[0]; break;
		case C_X2_ON:
			smp_x2 = 1;   /* both CPUs switch; the BSP has set it already */
			wrmsr(0x1B, rdmsr(0x1B) | 0xC00);
			ap_res[0] = (u32)rdmsr(0x802); ap_res[1] = (u32)rdmsr(0x80D);
			wrmsr(0x80F, 0x1FF);
			break;
		case C_X2_OFF:
			wrmsr(0x1B, rdmsr(0x1B) & ~0xC00ull);
			wrmsr(0x1B, (rdmsr(0x1B) & ~0x400ull) | 0x800);
			ap_apic_init();
			break;
		case C_X2_IPI: wrmsr(0x830, ((u64)ap_arg[0] << 32) | ap_arg[1]); break;
		case C_MWAIT:
			while (!mw_flag[0]) {
				__asm__ volatile("monitor" :: "a"(&mw_flag[0]), "c"(0), "d"(0));
				mw_armed = 1;
				if (mw_flag[0]) break;
				__asm__ volatile("mwait" :: "a"(0), "c"(0));
			}
			ap_res[0] = mw_flag[0];
			break;
		case C_MWAIT1:   /* one MONITOR/MWAIT (IF = 0, ECX = 0: only a store to the line ends it) */
			__asm__ volatile("monitor" :: "a"(&mw_flag[0]), "c"(0), "d"(0));
			mw_armed = 1;
			if (ap_arg[0]) while (mw_armed != 2) cpu_relax();   /* the BSP stores between MONITOR and MWAIT */
			__asm__ volatile("mwait" :: "a"(0), "c"(0));
			ap_res[0] = 1;
			break;
		case C_CR0: WRCR(0, RDCR(0) & ~0x60000000); break;   /* clear CD and NW */
		case C_COUNT:
			for (u32 i = 0; i < ap_arg[0]; i++) __asm__ volatile("lock incl %0" : "+m"(counter));
			break;
		case C_CPUID:
			cpuid(ap_arg[0], ap_arg[1], r);
			ap_res[0] = r[0]; ap_res[1] = r[1]; ap_res[2] = r[2]; ap_res[3] = r[3];
			break;
		case C_TSC: {
			u32 lo, hi;
			__asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
			ap_res[0] = lo; ap_res[1] = hi;
			break;
		}
		}
		ap_cmd = 0;
		ap_ack++;
	}
}

/* smpn=N (model-only, any number of CPUs): every AP started at once reports its CPUID topology */
static volatile u32 smpn_mode, apn_count;
static volatile u32 (*apn_rec)[17];   /* page_alloc'd in smpn mode: the other passes keep their layout */

static void topo_record(volatile u32 *r) {
	u32 x[4];
	cpuid(1, 0, x); r[0] = x[1]; r[1] = (x[3] >> 28) & 1;
	cpuid(0xB, 0, x); r[2] = x[0]; r[3] = x[1]; r[4] = x[2]; r[5] = x[3];
	cpuid(0xB, 1, x); r[6] = x[0]; r[7] = x[1]; r[8] = x[2]; r[9] = x[3];
	cpuid(0x80000001, 0, x); r[10] = (x[2] >> 1) & 1;
	cpuid(0x80000008, 0, x); r[11] = x[2];
	cpuid(0x8000001E, 0, x); r[12] = x[0]; r[13] = x[1]; r[14] = x[2];
	r[15] = LR(0x20) >> 24;
	cpuid(0x80000000, 0, x); r[16] = x[0];
}
static void apn_main(void) {
	u32 x[4];
	cpuid(1, 0, x);
	u32 k = x[1] >> 24;
	if (k < 128) topo_record(apn_rec[k]);
	__sync_fetch_and_add(&apn_count, 1);
	for (;;) __asm__ volatile("cli\n hlt");
}
void ap_entry(void) { if (smpn_mode) apn_main(); else ap_main(); }

void test_smpn(u32 n) {
	LR(0xF0) = 0x1FF;
	apn_rec = page_alloc(3);
	ap_stack_top = (u32)page_alloc(32) + 32 * 4096;   /* 1 KiB per AP */
	ap_stack_step = (u32)-1024;
	smpn_mode = 1;
	memcpy((void *)AP_TRAMP, ap_tramp, ap_tramp_end - ap_tramp);
	*(volatile u16 *)(AP_TRAMP + (ap_tr_gdtr - ap_tramp)) = sizeof gdt - 1;
	*(volatile u32 *)(AP_TRAMP + (ap_tr_gdtr - ap_tramp) + 2) = (u32)gdt;
	/* INIT, STARTUP, STARTUP to all but self, back to back */
	ipi(0, 0xC0000 | 0x4500);
	ipi(0, 0xC0000 | 0x600 | AP_VEC);
	ipi(0, 0xC0000 | 0x600 | AP_VEC);
	for (u32 k = 0; k < 50000000 && apn_count < n - 1; k++) cpu_relax();
	topo_record(apn_rec[0]);
	kprintf("smpn: cpus=%d started=%d\n", n, apn_count);
	for (u32 k = 0; k < n && k < 128; k++) {
		volatile u32 *r = apn_rec[k];
		kprintf("smpn %d: apic=%x l1ebx=%x htt=%d b0=%x,%x,%x,%x b1=%x,%x,%x,%x cmpl=%d c88=%x maxext=%x e1e=%x,%x,%x\n", k, r[15],
		        r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11], r[16], r[12], r[13], r[14]);
	}
}

/* Run command `c` on the AP and wait for it to finish. */
static void ap_do(u32 c, u32 a0, u32 a1, u32 a2) {
	u32 t = ap_ack;
	ap_arg[0] = a0; ap_arg[1] = a1; ap_arg[2] = a2;
	__sync_synchronize();
	ap_cmd = c;
	wait_until(&ap_ack, t + 1);
}

static void start_ap(u32 gen) {
	ipi(1, 0xC500);   /* INIT, level assert */
	spin(1000);
	ipi(1, 0x8500);   /* INIT de-assert */
	spin(1000);
	ipi(1, 0x600 | AP_VEC);
	spin(1000);
	ipi(1, 0x600 | AP_VEC);   /* the second STARTUP of the MP protocol: ignored by a started CPU */
	wait_until(&ap_gen, gen);
	wait_until(&ap_ready, 1);
}

/* INIT and STARTUP back to back, without the delays of start_ap (Linux sends INIT, STARTUP, STARTUP
   with init_udelay = 0 on current CPUs): the AP is started whatever the scheduling of the two CPUs. The
   APIC accepts a STARTUP in the INIT state (AMD APM vol. 2, 16.5), also while the INIT is still being
   processed; a second STARTUP to a started CPU is ignored. */
static void start_b2b(const char *name, int kind) {
	u32 gen = ap_gen + 1;
	ap_ready = 0;
	LR(0x280) = 0;
	ipi(1, 0xC500);   /* INIT, level assert */
	if (kind == 1) ipi(1, 0x8500);   /* INIT de-assert */
	ipi(1, 0x600 | AP_VEC);
	if (kind == 3) spin(300);
	if (kind >= 2) ipi(1, 0x600 | AP_VEC);
	wait_until(&ap_gen, gen);
	wait_until(&ap_ready, 1);
	LR(0x280) = 0;
	kprintf("smp.b2b.%s: started=%d ready=%d esr=%x\n", name, ap_gen == gen, ap_ready, LR(0x280));
}

/* Start the AP into ap_main again and wait until it is ready: for a test that borrowed the AP and left
   it in the INIT state or elsewhere (t_svm.c's test_svm_smp). */
void smp_restart_ap(void) {
	u32 gen = ap_gen + 1;
	ap_ready = 0;
	ipi(1, 0xC500);
	ipi(1, 0x8500);
	ipi(1, 0x600 | AP_VEC);
	wait_until(&ap_gen, gen);
	wait_until(&ap_ready, 1);
	LR(0x280) = 0;
}

void test_smp(void) {
	trap_hook = smp_hook;
	outb(0x21, 0xFF); outb(0xA1, 0xFF);
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x01000000; LR(0x350) = 0x10700;
	ap_stack_top = (u32)ap_stack + sizeof ap_stack;
	memcpy((void *)AP_TRAMP, ap_tramp, ap_tramp_end - ap_tramp);
	*(volatile u16 *)(AP_TRAMP + (ap_tr_gdtr - ap_tramp)) = sizeof gdt - 1;
	*(volatile u32 *)(AP_TRAMP + (ap_tr_gdtr - ap_tramp) + 2) = (u32)gdt;
	LR(0x280) = 0;
	start_ap(1);
	LR(0x280) = 0;
	kprintf("smp.start: gen=%d ready=%d apicid=%x cpuid_id=%x cs=%x edx_sig=%d cr0=%x esr=%x fcw=%x ftw=%x\n", ap_gen,
	        ap_ready, ap_res[0], ap_res[1], ap_res[2], ap_res[3], ap_res[4], LR(0x280), ap_res[5], ap_res[6]);

	/* MWAIT ends with any store to the monitored line, also when a second store restores its contents
	   before the waiting CPU runs again (APM vol. 3 MWAIT); a store between MONITOR and MWAIT
	   triggers the monitor, so MWAIT does not wait. (QEMU's MWAIT with several CPUs does not wait.) */
	for (u32 k = 0; k < 2; k++) {
		u32 t = ap_ack;
		mw_flag[0] = 0; mw_flag[1] = 0; mw_armed = 0; ap_res[0] = 0;
		ap_arg[0] = k;
		__sync_synchronize();
		ap_cmd = C_MWAIT1;
		wait_until(&mw_armed, 1);
		if (!k) spin(5000);
		mw_flag[1] = 1; mw_flag[1] = 0;
		if (k) mw_armed = 2;
		wait_until(&ap_ack, t + 1);
		kprintf("smp.mwait.%s: woke=%d\n", k ? "armed_restore" : "restore", ap_res[0]);
	}

	/* fixed IPIs, physical destination, both directions */
	ipi(1, 0x4051);
	wait_ap_n(1);
	logs("smp.ipi.fixed.bsp2ap");
	ap_do(C_IPI, 0, 0x4052, 0);
	logs("smp.ipi.fixed.ap2bsp");
	ipi(0xFF, 0x53);
	wait_ap_n(1);
	logs("smp.ipi.broadcast");
	/* logical destinations: flat (BSP 01h, AP 02h), then cluster (BSP 11h, AP 12h) */
	ipi(0x02, 0x854);
	wait_ap_n(1);
	logs("smp.ipi.flat.ap");
	ipi(0x03, 0x855);
	wait_ap_n(1);
	logs("smp.ipi.flat.both");
	LR(0xE0) = 0x0FFFFFFF; LR(0xD0) = 0x11000000;
	ap_do(C_APIC, 0x12000000, 0x0FFFFFFF, 0);
	ipi(0x12, 0x856);
	wait_ap_n(1);
	logs("smp.ipi.cluster.ap");
	ipi(0x13, 0x857);
	wait_ap_n(1);
	logs("smp.ipi.cluster.both");
	ipi(0x21, 0x858);
	spin(20000);
	logs("smp.ipi.cluster.none");
	LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x01000000;
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0);
	/* shorthands */
	ipi(0, 0x80000 | 0x59);
	wait_ap_n(1);
	logs("smp.ipi.all");
	ipi(0, 0xC0000 | 0x5A);
	wait_ap_n(1);
	logs("smp.ipi.allbutself");
	ipi(0, 0x40000 | 0x5B);
	spin(20000);
	logs("smp.ipi.self");
	ap_do(C_IPI, 0, 0xC0000 | 0x5C, 0);
	logs("smp.ipi.ap.allbutself");
	/* lowest priority: the BSP (APR 0) against the AP (TPR 80h); TCG picks the lowest APIC ID */
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0x80);
	ipi(0x03, 0x900 | 0x5E);
	spin(20000);
	logs("smp.ipi.lowpri");
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0);
	/* NMI */
	ipi(1, 0x400);
	wait_ap_n(1);
	logs("smp.ipi.nmi");
	/* system B: an NMI IPI to the AP while it is in its NMI handler (NMIs blocked) is latched and taken
	   after the handler's IRET (AMD APM vol. 2, 8.2.3) */
	ap_nmi_release = 0; ap_nmi_in = 0; ap_nmi_hold = 1;
	ipi(1, 0x400);
	wait_until(&ap_nmi_in, 1);
	ipi(1, 0x400);
	spin(20000);
	u32 nmi_inside = ap_n;
	ap_nmi_release = 1;
	wait_ap_n(2);
	kprintf("smp.nmi.blocked.inside: ap=%d\n", nmi_inside);
	logs("smp.nmi.blocked");
	/* INIT and STARTUP again: the AP restarts in the trampoline */
	ap_ready = 0;
	start_ap(2);
	kprintf("smp.restart: gen=%d ready=%d cs=%x\n", ap_gen, ap_ready, ap_res[2]);
	start_b2b("init_sipi", 0);
	start_b2b("init_deassert_sipi", 1);
	start_b2b("init_sipi_sipi", 2);
	start_b2b("init_sipi_spin_sipi", 3);

	/* TLB shootdown: the BSP remaps a page, invalidates its own TLB entry and asks the AP by IPI */
	u32 *pd = page_alloc(1), *pt = page_alloc(1);
	u32 *fa = page_alloc(1), *fb = page_alloc(1);
	fa[0] = 0xAAAA0001; fb[0] = 0xBBBB0002;
	pd[0] = 0x00000083; pd[1] = 0x00400083; pd[2] = (u32)pt | 3;
	pd[0x3FB] = 0xFEC0009B;   /* the I/O APIC and local APIC pages, uncached */
	pt[0] = (u32)fa | 3;
	WRCR(3, (u32)pd); WRCR(4, RDCR(4) | 0x10); WRCR(0, RDCR(0) | 0x80000000);
	ap_do(C_PG_ON, (u32)pd, 0, 0);
	u32 before = ap_res[0];
	pt[0] = (u32)fb | 3;
	invlpg(0x800000);
	shoot_done = 0;
	ipi(1, 0x5D);
	wait_until(&shoot_done, 1);
	ap_do(C_READ, 0x800000, 0, 0);
	kprintf("smp.tlb: ap_before=%x bsp_after=%x ap_after=%x\n", before, *(volatile u32 *)0x800000, ap_res[0]);
	logs("smp.tlb.ipi");
	ap_do(C_PG_OFF, 0, 0, 0);
	WRCR(0, RDCR(0) & ~0x80000000);

	/* the I/O APIC delivers the PIT's IRQ 0 (pin 2) to the AP, then to both (logical 03h) */
	ioapic_entry(2, 0x61, 0x01000000);
	pit_oneshot(500);
	wait_ap_n(1);
	logs("smp.ioapic.ap");
	ioapic_entry(2, 0x800 | 0x62, 0x03000000);
	pit_oneshot(500);
	wait_ap_n(1);
	for (u32 k = 0; k < 2000 && !bsp_n; k++) __asm__ volatile("sti\n hlt\n cli" ::: "memory");
	logs("smp.ioapic.both");
	ioapic_entry(2, 0x10000, 0);

	/* x2APIC on both CPUs: 32-bit destinations, logical (cluster) IDs */
	smp_x2 = 1;
	wrmsr(0x1B, rdmsr(0x1B) | 0xC00);
	wrmsr(0x80F, 0x1FF);
	ap_do(C_X2_ON, 0, 0, 0);
	kprintf("smp.x2apic: bsp_id=%x bsp_ldr=%x ap_id=%x ap_ldr=%x\n", (u32)rdmsr(0x802), (u32)rdmsr(0x80D),
	        ap_res[0], ap_res[1]);
	wrmsr(0x830, (1ull << 32) | 0x63);
	wait_ap_n(1);
	logs("smp.x2apic.phys");
	ap_do(C_X2_IPI, 0, 0x64, 0);
	logs("smp.x2apic.ap2bsp");
	wrmsr(0x830, ((u64)ap_res[1] << 32) | 0x800 | 0x65);
	wait_ap_n(1);
	logs("smp.x2apic.logical");
	wrmsr(0x830, 0xC0000 | 0x66);
	wait_ap_n(1);
	logs("smp.x2apic.allbutself");
	wrmsr(0x830, (0xFFFFFFFFull << 32) | 0x67);
	wait_ap_n(1);
	logs("smp.x2apic.broadcast");
	ap_do(C_X2_OFF, 0, 0, 0);
	wrmsr(0x1B, rdmsr(0x1B) & ~0xC00ull);
	wrmsr(0x1B, (rdmsr(0x1B) & ~0x400ull) | 0x800);
	smp_x2 = 0;
	LR(0xF0) = 0x1FF; LR(0x80) = 0; LR(0xE0) = 0xFFFFFFFF; LR(0xD0) = 0x01000000; LR(0x350) = 0x10700;

	/* MWAIT on the AP ends with the BSP's store to the monitored line */
	mw_flag[0] = 0; mw_armed = 0;
	ap_arg[0] = 0;
	{
		u32 t = ap_ack;
		ap_cmd = C_MWAIT;
		wait_until(&mw_armed, 1);
		spin(5000);
		mw_flag[0] = 1;
		wait_until(&ap_ack, t + 1);
	}
	kprintf("smp.mwait: woke=%d\n", ap_res[0]);

	/* LOCKed increments from both CPUs at once */
	counter = 0;
	{
		u32 t = ap_ack;
		ap_arg[0] = 20000;
		ap_cmd = C_COUNT;
		for (u32 i = 0; i < 20000; i++) __asm__ volatile("lock incl %0" : "+m"(counter));
		wait_until(&ap_ack, t + 1);
	}
	kprintf("smp.lock: counter=%d\n", counter);

	/* time-stamp counters are synchronized: the AP's earlier reading is below the BSP's later one */
	ap_do(C_TSC, 0, 0, 0);
	{
		u32 lo, hi;
		__asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
		u64 ap = ((u64)ap_res[1] << 32) | ap_res[0], bsp = ((u64)hi << 32) | lo;
		kprintf("smp.tsc: monotonic=%d\n", bsp > ap);
	}
	trap_hook = 0;
}

extern char smi_h[], smi_h_end[];

/* Model-only: AMD's lowest-priority arbitration (TCG takes the lowest APIC ID), the focus processor,
   ExtINT, SMI and remote-read IPIs, SAE, and the CPUID topology seen by each CPU. */
void test_smp_model(void) {
	trap_hook = smp_hook;
	/* lowest APR wins: the AP (TPR 0) against the BSP (TPR 80h) */
	LR(0x80) = 0x80;
	ipi(0x03, 0x900 | 0x70);
	wait_ap_n(1);
	LR(0x80) = 0;
	logs("smpm.lowpri.apr");
	/* a tie goes to the highest APIC ID (the AP) */
	ipi(0x03, 0x900 | 0x71);
	wait_ap_n(1);
	logs("smpm.lowpri.tie");
	/* focus: the BSP has the vector pending (TPR F0h blocks it), so it accepts it */
	LR(0x80) = 0xF0;
	ipi(0, 0x40000 | 0x72);
	ipi(0x03, 0x900 | 0x72);
	spin(20000);
	LR(0x80) = 0;
	logs("smpm.lowpri.focus");
	/* focus checking disabled (SVR bit 9): arbitration again, the AP wins the tie */
	LR(0xF0) = 0x3FF; LR(0x80) = 0xF0;
	ipi(0, 0x40000 | 0x73);
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0);
	ipi(0x03, 0x900 | 0x73);
	wait_ap_n(1);
	LR(0x80) = 0; LR(0xF0) = 0x1FF;
	logs("smpm.lowpri.nofocus");
	/* the arbitration compares APR bits 7:4, the Arbitration Priority field (AMD APM vol. 2, 16.6.2): BSP
	   TPR 80h and AP TPR 8Fh tie, and the highest APIC ID (the AP) accepts; comparing the whole APR (the
	   Intel rule) would pick the BSP */
	LR(0x80) = 0x80;
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0x8F);
	ipi(0x03, 0x900 | 0x95);
	wait_ap_n(1);   /* the AP accepts (not a fixed spin: the AP may not run within it at a large quantum) */
	logs("smpm.lowpri.subclass");
	LR(0x80) = 0;
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0);
	/* remote read of the AP's TPR and APR */
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0x37);
	ipi(1, 0x300 | 0x08);
	kprintf("smpm.rr.tpr: rrs=%x rrr=%x\n", (LR(0x300) >> 16) & 3, LR(0xC0));
	ipi(1, 0x300 | 0x09);
	kprintf("smpm.rr.apr: rrs=%x rrr=%x\n", (LR(0x300) >> 16) & 3, LR(0xC0));
	ap_do(C_APIC, 0x02000000, 0xFFFFFFFF, 0);
	/* ExtINT IPI: the AP acknowledges the PIC (master base 30h, no request: spurious IRQ 7 = 37h) */
	outb(0x20, 0x11); outb(0x21, 0x30); outb(0x21, 0x04); outb(0x21, 0x01); outb(0x21, 0xFF);
	ipi(1, 0x700);
	wait_ap_n(1);
	logs("smpm.ipi.extint");
	/* SMI IPI: the AP enters SMM at its SMBASE (the t_smm handler counts at 0x6000) and resumes */
	memcpy((void *)0xA8000, smi_h, smi_h_end - smi_h);
	/* the t_smm handler replaces the saved EAX by 5A5A5A5Ah, which the AP's code may hold a live value
	   in when the SMI arrives: this copy leaves it alone (the 12 bytes 67 66 C7 86 D0 7F 00 00 imm32 of
	   each such store, one per save-map layout, become NOPs), so the outcome does not depend on where the AP is interrupted */
	{
		u8 *h = (u8 *)0xA8000;
		for (u32 i = 8; i + 4 <= (u32)(smi_h_end - smi_h); i++)
			if (*(volatile u32 *)(h + i) == 0x5A5A5A5A) for (u32 j = i - 8; j < i + 4; j++) h[j] = 0x90;
	}
	for (int i = 0; i < 20; i++) ((volatile u32 *)0x6000)[i] = 0;
	ipi(1, 0x200);
	spin(20000);
	ap_do(C_READ, 0x6000, 0, 0);
	kprintf("smpm.ipi.smi: count=%d ap_alive=1\n", ap_res[0]);
	/* SAE: an IPI to an absent APIC */
	LR(0x280) = 0; LR(0x280) = 0;
	ipi(5, 0x74);
	LR(0x280) = 0;
	kprintf("smpm.esr.sae: %x\n", LR(0x280));
	/* CPUID topology of both CPUs (2 threads of one core) */
	u32 r[4];
	cpuid(1, 0, r);
	ap_do(C_CPUID, 1, 0, 0);
	kprintf("smpm.cpuid1: bsp_ebx=%x htt=%d ap_ebx=%x ap_htt=%d\n", r[1], (r[3] >> 28) & 1, ap_res[1], (ap_res[3] >> 28) & 1);
	for (u32 s = 0; s < 2; s++) {
		cpuid(0xB, s, r);
		ap_do(C_CPUID, 0xB, s, 0);
		kprintf("smpm.cpuidb.%d: bsp=%x %x %x %x ap=%x %x %x %x\n", s, r[0], r[1], r[2], r[3], ap_res[0], ap_res[1],
		        ap_res[2], ap_res[3]);
	}
	cpuid(0x80000001, 0, r);
	kprintf("smpm.cpuid81: cmplegacy=%d\n", (r[2] >> 1) & 1);
	cpuid(0x80000008, 0, r);
	kprintf("smpm.cpuid88: ecx=%x\n", r[2]);
	/* INIT keeps CR0.CD and CR0.NW (AMD APM vol. 2, table 14-1): the AP clears them, then INIT and
	   STARTUP; its CR0 still has them clear. (TCG's INIT resets CR0 to 6000_0010h.) */
	ap_do(C_CR0, 0, 0, 0);
	ap_ready = 0;
	start_ap(ap_gen + 1);
	kprintf("smpm.init.cr0: %x ready=%d\n", ap_res[4], ap_ready);
	trap_hook = 0;
}
