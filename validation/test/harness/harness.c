/*
 * Differential test harness: runs one instruction per test vector in ring 3 and
 * reports the resulting state over COM1. Vectors come from a multiboot module.
 * Shared fixed layout (mirrored by the Lean side, see TestMain.lean):
 *   0x1000 GDT, 0x1800 TSS, 0x2000 IDT, 0x3000 page directory, 0x4000 page table (identity, 4 MiB),
 *   0x8000 data area (8 KiB = pages 8 and 9, whose PTEs come from the vector), 0x20000 code buffer (512 B)
 * Record format v1 (88 bytes, no header) or v2 (header "X86VEC\0\2", 96-byte records with MXCSR and
 * vector flags; see test/gen.py): v2 also enables CR4.OSFXSR/OSXMMEXCPT (and, with vector flag bit 0,
 * CR4.OSXSAVE and XCR0 = 7), loads XMM0-7 (and YMM0-7[255:128]) from vec_pattern() and reports MXCSR,
 * XMM0-7 and the YMM upper halves. Vector instructions are written as bytes (clang builds this file
 * for i686 without SSE, so the compiler never touches the vector registers itself).
 */
#include <stdint.h>

#define GDT  ((uint64_t *)0x1000)
#define TSS  ((uint32_t *)0x1800)
#define IDT  ((uint64_t *)0x2000)
#define DATA ((uint8_t *)0x8000)
#define CODE ((uint8_t *)0x20000)
#define DATA_SIZE 8192
#define PD ((uint32_t *)0x3000)
#define PT ((uint32_t *)0x4000)
#define CODE_SIZE 512
#define INSN_OFF 256

struct vec {
	uint8_t len, bytes[15];
	uint32_t r[8];			/* eax ecx edx ebx esp ebp esi edi */
	uint32_t eflags;
	uint32_t seed;
	uint16_t sel[4];		/* ds es fs gs */
	uint16_t poff[2];		/* patch offsets into the data area (0xffff = none) */
	uint32_t pval[2];
	uint32_t mode;			/* bit 0: paging, bit 1: CR0.WP */
	uint32_t pte[2];		/* low 12 bits of the PTEs of pages 8 and 9 */
};					/* 88 bytes */

/* layout used by enter_user in boot.S */
struct ustate { uint32_t r[8]; uint32_t eflags, eip, ss, ds, es, fs, gs; } ustate;

static uint8_t *vecs;
static uint32_t nvec, cur, recsize = sizeof(struct vec), v2;
#define VEC(k) ((struct vec *)(vecs + (k) * recsize))
#define V2X(k) ((uint32_t *)(vecs + (k) * recsize + sizeof(struct vec)))	/* mxcsr, vflags */
static uint32_t pat[64] __attribute__((aligned(16)));	/* XMM0-7, then YMM0-7[255:128] */
static uint32_t ymm_on;
extern char tss_stack_top[];
extern void enter_user(void);

static inline void outb(uint16_t p, uint8_t v) { __asm__ volatile("outb %0,%1" :: "a"(v), "Nd"(p)); }
static inline uint8_t inb(uint16_t p) { uint8_t v; __asm__ volatile("inb %1,%0" : "=a"(v) : "Nd"(p)); return v; }

static void putc_(char c) { while (!(inb(0x3fd) & 0x20)); outb(0x3f8, c); }
static void puts_(const char *s) { while (*s) putc_(*s++); }
static void hex(uint32_t v) { for (int i = 28; i >= 0; i -= 4) putc_("0123456789abcdef"[(v >> i) & 15]); putc_(' '); }

uint32_t xorshift(uint32_t *s) { uint32_t x = *s; x ^= x << 13; x ^= x >> 17; x ^= x << 5; return *s = x; }

/* movdqu xmmK, [eax+16K]; movdqu [eax+16K], xmmK; vinsertf128 ymmK, ymmK, [eax+16K], 1;
   vextractf128 [eax+16K], ymmK, 1 */
#define LDX(k) ".byte 0xf3,0x0f,0x6f,0x40+" #k "*8," #k "*16\n\t"
#define STX(k) ".byte 0xf3,0x0f,0x7f,0x40+" #k "*8," #k "*16\n\t"
#define LDY(k) ".byte 0xc4,0xe3,((~" #k ")&15)*8+5,0x18,0x40+" #k "*8," #k "*16,1\n\t"
#define STY(k) ".byte 0xc4,0xe3,0x7d,0x19,0x40+" #k "*8," #k "*16,1\n\t"
#define ALL8(m) m(0) m(1) m(2) m(3) m(4) m(5) m(6) m(7)
static void load_vec(void) {
	__asm__ volatile(ALL8(LDX) :: "a"(pat) : "memory");
	if (ymm_on) __asm__ volatile(ALL8(LDY) :: "a"(pat + 32) : "memory");
}
static void save_vec(uint32_t *out) {
	__asm__ volatile(ALL8(STX) :: "a"(out) : "memory");
	if (ymm_on) __asm__ volatile(ALL8(STY) :: "a"(out + 32) : "memory");
	else for (int i = 32; i < 64; i++) out[i] = 0;
}
static inline uint32_t rd_cr4(void) { uint32_t v; __asm__ volatile("mov %%cr4, %0" : "=r"(v)); return v; }
static inline void wr_cr4(uint32_t v) { __asm__ volatile("mov %0, %%cr4" :: "r"(v) : "memory"); }

static uint64_t seg(uint32_t base, uint32_t limit, uint32_t type_dpl_p, uint32_t flags) {
	return (limit & 0xffff) | ((uint64_t)(base & 0xffffff) << 16) | ((uint64_t)type_dpl_p << 40) |
	       ((uint64_t)((limit >> 16) & 0xf) << 48) | ((uint64_t)flags << 52) | ((uint64_t)(base >> 24) << 56);
}

extern char isr0[], isr1[], isr2[], isr3[], isr4[], isr5[], isr6[], isr7[], isr8[], isr9[],
	isr10[], isr11[], isr12[], isr13[], isr14[], isr15[], isr16[], isr17[], isr18[], isr19[];
static char *isrs[20] = { isr0, isr1, isr2, isr3, isr4, isr5, isr6, isr7, isr8, isr9,
	isr10, isr11, isr12, isr13, isr14, isr15, isr16, isr17, isr18, isr19 };

static void setup(void) {
	GDT[0] = 0;
	GDT[1] = seg(0, 0xfffff, 0x9b, 0xc);		/* 0x08 kernel code */
	GDT[2] = seg(0, 0xfffff, 0x93, 0xc);		/* 0x10 kernel data */
	GDT[3] = seg(0, 0xfffff, 0xfb, 0xc);		/* 0x1b user code */
	GDT[4] = seg(0, 0xfffff, 0xf3, 0xc);		/* 0x23 user data */
	GDT[5] = seg(0x8000, 0xfff, 0xf3, 0x4);		/* 0x2b user data, base 0x8000 limit 0xfff */
	GDT[6] = seg(0, 0x7fff, 0xf7, 0x4);		/* 0x33 user data, expand-down, limit 0x7fff */
	GDT[7] = seg(0, 0xfffff, 0xf1, 0xc);		/* 0x3b user data, read-only */
	GDT[8] = seg(0x1800, 0x67, 0x89, 0x0);		/* 0x40 TSS */
	GDT[9] = seg(0, 0xfffff, 0x93, 0xc);		/* 0x48 kernel data (0x4b from ring 3: #GP) */
	GDT[10] = seg(0, 0xfffff, 0x73, 0xc);		/* 0x50 not-present user data (0x53: #NP) */
	GDT[11] = seg(0, 0xffff, 0xfb, 0x0);		/* 0x5b user code, 16-bit, limit 0xffff */
	GDT[12] = seg(0, 0xffff, 0xf3, 0x0);		/* 0x63 user data, 16-bit (B=0) */
	GDT[13] = seg(0, 0xfffff, 0xf9, 0xc);		/* 0x6b user code, execute-only */
	struct { uint16_t l; uint32_t b; } __attribute__((packed)) gd = { 14 * 8 - 1, 0x1000 }, id = { 20 * 8 - 1, 0x2000 };
	for (int i = 0; i < 26; i++) TSS[i] = 0;
	TSS[1] = (uint32_t)tss_stack_top;		/* esp0 */
	TSS[2] = 0x10;					/* ss0 */
	TSS[25] = 0x68u << 16;				/* I/O map base beyond the limit: no ports */
	for (int i = 0; i < 20; i++) {
		uint32_t a = (uint32_t)isrs[i];
		uint32_t dpl = (i == 3) ? 3 : 0;
		IDT[i] = (a & 0xffff) | (0x08ull << 16) | ((uint64_t)(0x8e | (dpl << 5)) << 40) | ((uint64_t)(a >> 16) << 48);
	}
	__asm__ volatile("lgdt %0; lidt %1" :: "m"(gd), "m"(id));
	__asm__ volatile("ljmp $0x08, $1f; 1: mov $0x10,%%eax; mov %%eax,%%ds; mov %%eax,%%es; mov %%eax,%%ss;"
			 "mov %%eax,%%fs; mov %%eax,%%gs; mov $0x40,%%eax; ltr %%ax; xor %%eax,%%eax; lldt %%ax" ::: "eax", "memory");
	__asm__ volatile("mov %0, %%cr0" :: "r"(0x31u));	/* PE ET NE */
	outb(0x21, 0xff); outb(0xa1, 0xff);		/* mask all IRQs */
	for (int i = 0; i < 1024; i++) PD[i] = 0;
	PD[0] = 0x4000 | 0x27;				/* P RW US A */
	for (int i = 0; i < 1024; i++) PT[i] = (i << 12) | 0x67;	/* P RW US A D */
	__asm__ volatile("mov %0, %%cr3" :: "r"(0x3000u));
}

static void run_next(void) {
	if (cur >= nvec) { puts_("END\n"); outb(0xf4, 0); for (;;) __asm__ volatile("hlt"); }
	struct vec *v = VEC(cur);
	uint32_t s = v->seed;
	for (int i = 0; i < DATA_SIZE; i += 4) *(uint32_t *)(DATA + i) = xorshift(&s);
	for (int k = 0; k < 2; k++) if (v->poff[k] != 0xffff) *(uint32_t *)(DATA + v->poff[k]) = v->pval[k];
	for (int i = 0; i < CODE_SIZE; i++) CODE[i] = 0xcc;
	for (int i = 0; i < v->len; i++) CODE[INSN_OFF + i] = v->bytes[i];
	/* re-mark the GDT entries we can modify through segment loads (accessed bits) */
	for (int i = 0; i < 8; i++) ustate.r[i] = v->r[i];
	ustate.eflags = v->eflags; ustate.eip = (uint32_t)CODE + INSN_OFF; ustate.ss = 0x23;
	ustate.ds = v->sel[0]; ustate.es = v->sel[1]; ustate.fs = v->sel[2]; ustate.gs = v->sel[3];
	PT[8] = 0x8000 | (v->pte[0] & 0xfff);
	PT[9] = 0x9000 | (v->pte[1] & 0xfff);
	__asm__ volatile("mov %0, %%cr3" :: "r"(0x3000u) : "memory");
	if (v2) {
		uint32_t mxcsr = V2X(cur)[0], vflags = V2X(cur)[1], a, b, c, d;
		__asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(1), "c"(0));
		ymm_on = (vflags & 1) && (c & (1u << 26)) && (c & (1u << 28));	/* XSAVE, AVX */
		if ((vflags & 1) && !ymm_on) { puts_("NO-XSAVE-AVX\n"); outb(0xf4, 0); for (;;) __asm__ volatile("hlt"); }
		wr_cr4((rd_cr4() & ~0x40000u) | 0x600u | (ymm_on ? 0x40000u : 0));	/* OSFXSR OSXMMEXCPT [OSXSAVE] */
		if (ymm_on) __asm__ volatile(".byte 0x0f,0x01,0xd1" :: "a"(7), "d"(0), "c"(0));	/* xsetbv XCR0 = 7 */
		uint32_t p = v->seed ^ 0xA5A5A5A5u;
		for (int i = 0; i < 64; i++) pat[i] = xorshift(&p);
		load_vec();
		__asm__ volatile(".byte 0x0f,0xae,0x10" :: "a"(&mxcsr) : "memory");	/* ldmxcsr */
	}
	if (v->mode & 1)
		__asm__ volatile("mov %0, %%cr0" :: "r"(0x80000031u | ((v->mode & 2) ? 0x10000u : 0)) : "memory");
	enter_user();
}

struct frame { uint32_t edi, esi, ebp, kesp, ebx, edx, ecx, eax, ds, es, fs, gs, vecno, err, eip, cs, eflags, esp, ss; };

static uint32_t fnv(void) { uint32_t h = 2166136261u; for (int i = 0; i < DATA_SIZE; i++) { h ^= DATA[i]; h *= 16777619u; } return h; }

void record(struct frame *f) {
	uint32_t cr2, vout[64] __attribute__((aligned(16))), mxcsr = 0;
	if (v2) {
		save_vec(vout);
		__asm__ volatile(".byte 0x0f,0xae,0x18" :: "a"(&mxcsr) : "memory");	/* stmxcsr */
	}
	__asm__ volatile("mov %%cr2, %0" : "=r"(cr2));
	__asm__ volatile("mov %0, %%cr0" :: "r"(0x31u) : "memory");	/* paging off */
	uint32_t eip = f->eip;
	if (f->vecno == 3) eip -= 1;	/* the int3 terminator */
	hex(cur); hex(f->vecno); hex(f->err); hex(eip);
	hex(f->eax); hex(f->ecx); hex(f->edx); hex(f->ebx); hex(f->esp); hex(f->ebp); hex(f->esi); hex(f->edi);
	hex(f->eflags); hex(f->ds & 0xffff); hex(f->es & 0xffff); hex(f->fs & 0xffff); hex(f->gs & 0xffff); hex(f->ss & 0xffff);
	hex(fnv()); hex(f->vecno == 14 ? cr2 : 0); hex(PT[8]); hex(PT[9]);
	if (v2) { hex(mxcsr); for (int i = 0; i < 64; i++) hex(vout[i]); }
	putc_('\n');
	cur++;
	run_next();
}

void harness_main(uint32_t *mbi) {
	setup();
	uint32_t *mods = (uint32_t *)mbi[6];
	vecs = (uint8_t *)mods[0];
	uint32_t size = mods[1] - mods[0];
	static const char magic[8] = { 'X', '8', '6', 'V', 'E', 'C', 0, 2 };
	v2 = 1;
	for (int i = 0; i < 8; i++) if (vecs[i] != (uint8_t)magic[i]) v2 = 0;
	if (v2) { recsize = *(uint32_t *)(vecs + 8); vecs += 16; size -= 16; }
	nvec = size / recsize;
	puts_("BEGIN "); hex(nvec); putc_('\n');
	cur = 0;
	run_next();
}
