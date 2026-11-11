/* Framework of the system-level test kernel: console, descriptor tables, trap dispatch. */
#include "sys.h"
#include "smp.h"
#include <stdarg.h>

u64 gdt[GDT_ENTRIES] __attribute__((aligned(8)));
u64 idt[256] __attribute__((aligned(8)));
struct tss32 tss_main __attribute__((aligned(128)));
static u8 ring0_stack[8192] __attribute__((aligned(16)));
volatile struct event last;
u32 mb_info;

/* Value of the last key=... on the multiboot command line (so campaign.sh EXTRA overrides), or dflt. */
/* The command line is copied at startup: tests reuse low memory (where a loader may have put it). */
static char cmdline_buf[512];
static void save_cmdline(void) {
	if (!mb_info || !(*(u32 *)mb_info & 4)) return;
	const char *c = (const char *)((u32 *)mb_info)[4];
	for (u32 i = 0; i < sizeof cmdline_buf - 1 && c[i]; i++) cmdline_buf[i] = c[i];
}

u32 param(const char *key, u32 dflt) {
	const char *s = cmdline_buf;
	while (*s) {
		while (*s == ' ') s++;
		const char *k = key;
		while (*k && *s == *k) { s++; k++; }
		if (!*k && *s == '=') {
			s++;
			u32 v = 0, base = 10;
			if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) { base = 16; s += 2; }
			for (;; s++) {
				u32 d = (*s >= '0' && *s <= '9') ? (u32)(*s - '0') : (*s >= 'a' && *s <= 'f') ? (u32)(*s - 'a' + 10)
				      : (*s >= 'A' && *s <= 'F') ? (u32)(*s - 'A' + 10) : 99;
				if (d >= base) break;
				v = v * base + d;
			}
			dflt = v;
		}
		while (*s && *s != ' ') s++;
	}
	return dflt;
}

u32 fuzz_seed(u32 dflt) {
	u32 s = param("seed", 0);
	if (!s) return dflt;
	u32 x = s * 0x9E3779B1u ^ dflt;
	x ^= x >> 16; x *= 0x85EBCA6Bu; x ^= x >> 13;
	return x ? x : dflt;
}
int (*trap_hook)(struct frame *);
struct jmpbuf fault_jb;
volatile int fault_armed;

void kputc(char c) {
	while (!(inb(0x3FD) & 0x20)) {}
	outb(0x3F8, c);
}
void kputs(const char *s) { while (*s) kputc(*s++); }
void puthex(u32 v) { for (int i = 28; i >= 0; i -= 4) kputc("0123456789abcdef"[(v >> i) & 15]); }
void putdec(u32 v) {
	char b[12]; int n = 0;
	do { b[n++] = '0' + v % 10; v /= 10; } while (v);
	while (n) kputc(b[--n]);
}
void kprintf(const char *fmt, ...) {
	va_list ap;
	va_start(ap, fmt);
	for (; *fmt; fmt++) {
		if (*fmt != '%') { kputc(*fmt); continue; }
		fmt++;
		if (*fmt == 'x') puthex(va_arg(ap, u32));
		else if (*fmt == 'd') putdec(va_arg(ap, u32));
		else if (*fmt == 's') kputs(va_arg(ap, const char *));
		else kputc(*fmt);
	}
	va_end(ap);
}

void memset(void *p, int v, u32 n) { u8 *q = p; while (n--) *q++ = (u8)v; }
void memcpy(void *d, const void *s, u32 n) { u8 *a = d; const u8 *b = s; while (n--) *a++ = *b++; }

static u32 next_page = 0x400000;
void *page_alloc(int n) {
	void *p = (void *)next_page;
	memset(p, 0, n * 4096);
	next_page += n * 4096;
	return p;
}

u64 seg_desc(u32 base, u32 limit, u32 access, u32 flags) {
	u32 lo = (limit & 0xFFFF) | (base << 16);
	u32 hi = ((base >> 16) & 0xFF) | (access << 8) | (limit & 0xF0000) | (flags << 20) | (base & 0xFF000000);
	return ((u64)hi << 32) | lo;
}
u64 gate_desc(u16 sel, u32 off, u32 access) {
	u32 lo = (off & 0xFFFF) | ((u32)sel << 16);
	u32 hi = (off & 0xFFFF0000) | (access << 8);
	return ((u64)hi << 32) | lo;
}
void set_idt(int vec, u32 handler, u32 access) { idt[vec] = gate_desc(KCODE, handler, access); }

void reload_tr(u16 sel) {
	gdt[sel >> 3] &= ~((u64)0x200 << 32);   /* clear busy */
	ltr(sel);
}

static void sys_exit(void) {
	kputs("END\n");
	outl(0xF4, 0);
	for (;;) __asm__ volatile("cli; hlt");
}

void report(const char *what, int vec) {
	if (vec == 0xFFFF) kprintf("%s: ok\n", what);
	else kprintf("%s: vec=%x err=%x eip=%x cr2=%x\n", what, vec, last.err, last.eip, last.cr2);
}

void trap(struct frame *f) {
	if (trap_hook && trap_hook(f)) return;
	last.vec = f->vec; last.err = f->err; last.eip = f->eip; last.cs = f->cs;
	last.eflags = f->eflags; last.cr2 = RDCR(2); last.esp = f->uesp;
	last.dr6 = f->vec == 1 ? RDDR(6) : 0;
	if (fault_armed) { fault_armed = 0; klongjmp(&fault_jb, 1); }
	kprintf("UNEXPECTED vec=%x err=%x eip=%x cs=%x eflags=%x\n", f->vec, f->err, f->eip, f->cs, f->eflags);
	sys_exit();
}

void enter_ring3(u32 eip, u32 esp, u32 eflags) {
	__asm__ volatile(
		"movl %3, %%ds\n movl %3, %%es\n movl %3, %%fs\n movl %3, %%gs\n"
		"pushl %3\n pushl %1\n pushl %2\n pushl %4\n pushl %0\n iret"
		:: "r"(eip), "r"(esp), "r"(eflags), "r"((u32)UDATA), "i"(UCODE) : "memory");
}

static void setup(void) {
	/* firmware leaves the PIT running with IRQ0 unmasked (vector 8 after its PIC setup): ring-3
	   snippets run with IF = 1, so mask both PICs; tests use the local APIC for interrupts */
	outb(0x21, 0xFF);
	outb(0xA1, 0xFF);
	gdt[1] = seg_desc(0, 0xFFFFF, 0x9A, 0xC);
	gdt[2] = seg_desc(0, 0xFFFFF, 0x92, 0xC);
	gdt[3] = seg_desc(0, 0xFFFFF, 0xFA, 0xC);
	gdt[4] = seg_desc(0, 0xFFFFF, 0xF2, 0xC);
	tss_main.ss0 = KDATA;
	tss_main.esp0 = (u32)ring0_stack + sizeof ring0_stack;
	tss_main.iomap = sizeof(struct tss32);
	gdt[TSS_MAIN >> 3] = seg_desc((u32)&tss_main, sizeof(struct tss32) - 1, 0x89, 0);
	struct { u16 lim; u32 base; } __attribute__((packed)) gd = { sizeof gdt - 1, (u32)gdt }, id = { sizeof idt - 1, (u32)idt };
	__asm__ volatile("lgdt %0" :: "m"(gd));
	__asm__ volatile("ljmp %0, $1f\n1:" :: "i"(KCODE));
	__asm__ volatile("movl %0, %%ds\n movl %0, %%es\n movl %0, %%ss\n movl %0, %%fs\n movl %0, %%gs" :: "r"((u32)KDATA));
	for (int v = 0; v < 256; v++) set_idt(v, (u32)isr_base + 16 * v, (v >= 0x40 && v < 0x50) ? 0xEE : 0x8E);
	__asm__ volatile("lidt %0" :: "m"(id));
	ltr(TSS_MAIN);
}

void sys_main(void) {
	save_cmdline();
	setup();
	kputs("BEGIN\n");
	if (param("seed", 0)) kprintf("PARAMS seed=%x\n", param("seed", 0));
	if (param("smp", 0)) {   /* the SMP transcript (second run of run.sh) */
		test_smp();
		kputs("MODEL-ONLY\n");
		test_smp_model();
		sys_exit();
	}
	if (param("long", 0)) {   /* long mode: a pass of its own (test/sys/run.sh, qemu-system-x86_64) */
		test_long();
		kputs("MODEL-ONLY\n");
		test_long_model();
		sys_exit();
	}
	test_paging();
	test_pae();
	test_paging_fuzz();
	test_debug();
	test_debug_fuzz();
	test_callgate();
	test_vm86();
	test_apic();
	test_smm();
	test_x87();
	test_x87_env();
	test_x87_trans();
	test_task();
	test_tsf();
	test_cgf();
	test_simd();
	test_simd_exc();
	test_sysa();
	test_xsave();
	test_sse();
	test_crypto();
	test_gpr();
	test_avx();
	test_apic_errors();
	test_ioapic();
	test_x2apic();
	test_avx2();
	/* Below: checked against test/sys/model-only.expected (SDM-derived), not against QEMU. */
	kputs("MODEL-ONLY\n");
	test_task_trap();
	test_xfer_model();
	test_x87_model();
	test_x87_trans_model();
	test_simd_model();
	test_xsave_model();
	test_crypto_model();
	test_debug_fuzz_model();
	test_paging_fuzz_model();
	test_sysa_model();
	test_sse_model();
	test_gpr_model();
	test_avx_model();
	test_apic_model();
	test_ioapic_model();
	test_x2apic_model();
	test_avx2_model();
	sys_exit();
}
