/* Paging differential fuzzing: random 32-bit/PSE/PAE/NX page tables for a small linear window, random
   accesses (reads, writes, instruction fetches; ring 0 and ring 3; page-crossing), compared with QEMU.
   Each case rebuilds the tables with paging off and re-enables paging, so no TLB entry survives. */
#include "sys.h"

#define EFER 0xC0000080
#define NFRAMES 8
#define LARGE 0x3800000         /* 4 MiB aligned physical region (56..60 MiB) backing large pages */
#define W32 0x403FA000          /* window: 6 pages through PDE 256, then 2 pages through PDE 257 */
#define WPAE 0x401FA000         /* window: 6 pages through PD1[0], then 2 pages through PD1[1] */
#define NPAGES 8

static u32 rs = 0x6B43A9B5;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

/* Ring-3 snippets (see u_read in t_paging.c): sizes 1 and 2, and the stub that returns an immediate */
__asm__(
	".globl pgf_r1\npgf_r1: movzbl (%eax), %ebx\n int $0x40\n"
	".globl pgf_r2\npgf_r2: movzwl (%eax), %ebx\n int $0x40\n"
	".globl pgf_w1\npgf_w1: movb %bl, (%eax)\n int $0x40\n"
	".globl pgf_w2\npgf_w2: movw %bx, (%eax)\n int $0x40\n");
extern char pgf_r1[], pgf_r2[], pgf_w1[], pgf_w2[];

static u32 *pd32, *ipt32;       /* 32-bit page directory and its identity page tables (0..64 MiB) */
static u64 *pdpt, *pd0, *pd1;   /* PAE: PDPT, identity PD (2 MiB pages), window PD */
static u32 *pta, *ptb;          /* window page tables (32-bit or PAE format) */
static u32 frames[NFRAMES];
static int pae, pse;
static volatile u32 u_eax, u_ebx;

static int pgf_hook(struct frame *f) {
	if (f->vec == 0x40) { u_eax = f->eax; u_ebx = f->ebx; }
	return 0;
}

/* Physical address of a linear address in the current tables (ignoring permissions and reserved
   bits), or 0xFFFFFFFF if some level is not present. */
static u32 lin2phys(u32 lin) {
	if (pae) {
		u64 e = pdpt[lin >> 30];
		if (!(e & 1)) return ~0u;
		e = ((u64 *)(u32)(e & 0xFFFFFF000ULL))[(lin >> 21) & 0x1FF];
		if (!(e & 1)) return ~0u;
		if (e & 0x80) return ((u32)e & 0xFFE00000) | (lin & 0x1FFFFF);
		e = ((u64 *)(u32)(e & 0xFFFFFF000ULL))[(lin >> 12) & 0x1FF];
		if (!(e & 1)) return ~0u;
		return ((u32)e & 0xFFFFF000) | (lin & 0xFFF);
	}
	u32 e = pd32[lin >> 22];
	if (!(e & 1)) return ~0u;
	if ((e & 0x80) && pse) return (e & 0xFFC00000) | (lin & 0x3FFFFF);
	e = ((u32 *)(e & 0xFFFFF000))[(lin >> 12) & 0x3FF];
	if (!(e & 1)) return ~0u;
	return (e & 0xFFFFF000) | (lin & 0xFFF);
}

static void clear(u32 *p) { for (int i = 0; i < 1024; i++) p[i] = 0; }

/* Random attribute bits shared by every level: P (mostly set), R/W and U/S (mostly set), PWT, PCD,
   A, D, G and the software-available bits 11:9. */
static u32 rnd_attr(void) {
	u32 r = rnd();
	u32 e = (r & 7) ? 1 : 0;
	if ((r >> 3) % 4) e |= 2;
	if ((r >> 5) % 4) e |= 4;
	e |= ((r >> 7) & 0xF) << 3;          /* PWT, PCD, A, D */
	e |= ((r >> 11) & 0xF) << 8;         /* G, AVL */
	return e;
}

/* A random PAE reserved bit (none most of the time): bits 62:36, and 63 when NXE = 0 */
static u64 pae_rsvd(int nxe) {
	if (rnd() % 24) return 0;
	u32 b = 36 + rnd() % (nxe ? 27 : 28);
	return 1ULL << b;
}

static void put(u32 *pt, u32 idx, u64 e) {
	if (pae) ((u64 *)pt)[idx] = e; else pt[idx] = (u32)e;
}
static u64 get(u32 *pt, u32 idx) { return pae ? ((u64 *)pt)[idx] : pt[idx]; }

/* 4 KiB leaf entry for a random pool frame */
static u64 leaf4k(int nxe) {
	u64 e = rnd_attr() | (rnd() & 0x80) | frames[rnd() % NFRAMES];   /* bit 7: PAT */
	if (pae) { e |= pae_rsvd(nxe); if (nxe && rnd() % 4 == 0) e |= 1ULL << 63; }
	return e;
}

/* Non-leaf directory entry pointing at page table `pt` */
static u64 nonleaf(u32 *pt, int nxe) {
	u64 e = (rnd_attr() & ~0x80u) | (u32)pt;
	if (!pae && !pse && rnd() % 2) e |= 0x80;            /* PS is ignored without CR4.PSE */
	if (pae) { e |= pae_rsvd(nxe); if (nxe && rnd() % 6 == 0) e |= 1ULL << 63; }
	return e;
}

/* Large-page directory entry */
static u64 large(int nxe) {
	u64 e = rnd_attr() | 0x80 | (rnd() & 0x1000);       /* bit 12: PAT */
	if (pae) {
		e |= LARGE + (rnd() % 2) * 0x200000;
		e |= pae_rsvd(nxe);
		if (nxe && rnd() % 4 == 0) e |= 1ULL << 63;
		if (rnd() % 24 == 0) e |= 1u << (13 + rnd() % 8);   /* reserved bits 20:13 */
	} else {
		e |= LARGE;
		if (rnd() % 24 == 0) e |= 1u << 21;               /* reserved bit 21 */
	}
	return e;
}

static void show64(u64 e) { if (pae) kprintf(" %x_%x", (u32)(e >> 32), (u32)e); else kprintf(" %x", (u32)e); }

static const char *const kname[] = { "rd", "wr", "x" };

void test_paging_fuzz(void) {
	u32 n = param("pgf", 400);
	rs = fuzz_seed(rs);
	trap_hook = pgf_hook;

	pd32 = page_alloc(1);
	ipt32 = page_alloc(16);
	for (u32 a = 0; a < 0x4000000; a += 0x1000) ipt32[a >> 12] = a | 7;
	for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)ipt32 + i * 0x1000) | 7;
	pdpt = page_alloc(1); pd0 = page_alloc(1); pd1 = page_alloc(1);
	for (u32 i = 0; i < 32; i++) pd0[i] = ((u64)i << 21) | 0x87;
	pta = page_alloc(1); ptb = page_alloc(1);
	for (int i = 0; i < NFRAMES; i++) {
		u32 *f = page_alloc(1);
		frames[i] = (u32)f;
		for (int k = 0; k < 1024; k++) f[k] = 0x01010101u * (u32)(i * 16 + 1) + (u32)k * 0x04030201u;
	}
	for (u32 k = 0; k < 3 * 1024; k++) {
		((u32 *)LARGE)[k] = 0xA5000000u + k;
		((u32 *)(LARGE + 0x200000))[k] = 0x5A000000u + k;
	}

	u32 cr0 = RDCR(0) & ~0x80010000u, cr4 = RDCR(4) & ~0x30u;
	for (u32 c = 0; c < n; c++) {
		WRCR(0, cr0);
		u32 mode = rnd() % 4;
		pae = mode >= 2; pse = mode == 1;
		int nxe = pae ? mode == 3 : (int)(rnd() % 2);   /* NXE has no effect on 32-bit paging */
		int wp = rnd() % 2;
		wrmsr(EFER, nxe ? 0x800 : 0);
		clear(pta); clear(ptb);
		int big = rnd() % 3 == 0;
		u32 W = pae ? WPAE : W32;
		u32 ia = pae ? 0x1FA : 0x3FA;                     /* first window index in pta */
		u64 pdeA = nonleaf(pta, nxe), pdeB = (big && (pae || pse)) ? large(nxe) : nonleaf(ptb, nxe);
		if (big && !pae && !pse) pdeB |= 0x80;            /* ignored PS bit */
		for (u32 i = 0; i < 6; i++) put(pta, ia + i, leaf4k(nxe));
		for (u32 i = 0; i < 2; i++) put(ptb, i, leaf4k(nxe));
		u64 pdpte = 0;
		if (pae) {
			pdpte = (u32)pd1 | ((rnd() % 16) ? 1 : 0) | (rnd() & 0x18) | (rnd() & 0xE00);
			pdpt[0] = (u32)pd0 | 1; pdpt[1] = pdpte; pdpt[2] = pdpt[3] = 0;
			clear((u32 *)pd1);
			pd1[0] = pdeA; pd1[1] = pdeB;
		} else {
			for (u32 i = 16; i < 1024; i++) pd32[i] = 0;
			pd32[256] = (u32)pdeA; pd32[257] = (u32)pdeB;
		}
		kprintf("pgf %d: %s wp=%d nxe=%d", c, pae ? "pae" : pse ? "pse" : "32", wp, nxe);
		if (pae) { kputs(" pdpte"); show64(pdpte); }
		kputs(" pde"); show64(pdeA); show64(pdeB);
		kputs(" pte");
		for (u32 i = 0; i < 6; i++) show64(get(pta, ia + i));
		for (u32 i = 0; i < 2; i++) show64(get(ptb, i));
		kputc('\n');

		WRCR(4, cr4 | (pae ? 0x20 : 0) | (pse || (pae && rnd() % 2) ? 0x10 : 0));   /* PSE: ignored with PAE */
		WRCR(3, pae ? (u32)pdpt : (u32)pd32);
		WRCR(0, cr0 | 0x80000000u | (wp ? 0x10000 : 0));

		u32 na = 3 + rnd() % 6;
		for (u32 a = 0; a < na; a++) {
			u32 kind = rnd() % 5;
			kind = kind < 2 ? 0 : kind < 4 ? 1 : 2;
			u32 size = kind == 2 ? 6 : (1u << (rnd() % 3));
			u32 user = rnd() % 2;
			u32 off = rnd() % 3 ? 0x1000 - 1 - rnd() % 8 : rnd() % 0x1000;
			u32 lin = W + (rnd() % NPAGES) * 0x1000 + off;
			u32 v = rnd(), got = 0;
			int vec;
			if (kind == 2) {
				/* mov $v, %eax; ret: plant it through the physical addresses of the mapped bytes */
				u8 code[6] = { 0xB8, (u8)v, (u8)(v >> 8), (u8)(v >> 16), (u8)(v >> 24), 0xC3 };
				for (u32 k = 0; k < 6; k++) { u32 p = lin2phys(lin + k); if (p != ~0u) *(volatile u8 *)p = code[k]; }
				u_eax = 0;
				if (user) { vec = run_user(u_call, lin, 0); got = u_eax; }
				else { u32 (*volatile fn)(void) = (u32 (*)(void))lin; vec = TRY(got = fn()); }
			} else if (kind == 0) {
				u_ebx = 0;
				if (user) { vec = run_user(size == 1 ? pgf_r1 : size == 2 ? pgf_r2 : u_read, lin, 0); got = u_ebx; }
				else if (size == 1) vec = TRY(got = *(volatile u8 *)lin);
				else if (size == 2) vec = TRY(got = *(volatile u16 *)lin);
				else vec = TRY(got = *(volatile u32 *)lin);
			} else {
				if (user) vec = run_user(size == 1 ? pgf_w1 : size == 2 ? pgf_w2 : u_write, lin, v);
				else if (size == 1) vec = TRY(*(volatile u8 *)lin = (u8)v);
				else if (size == 2) vec = TRY(*(volatile u16 *)lin = (u16)v);
				else vec = TRY(*(volatile u32 *)lin = v);
				/* the bytes as they are now in memory (all or nothing written) */
				for (u32 k = 0; k < size; k++) {
					u32 p = lin2phys(lin + k);
					got |= (p == ~0u ? 0xEEu : *(volatile u8 *)p) << (8 * k);
				}
			}
			int pf = vec == 14;
			kprintf("pgf %d.%d: %s%d r%d %x vec=%x err=%x cr2=%x val=%x\n", c, a, kname[kind], size, user ? 3 : 0,
			        lin, vec, pf || vec == 13 ? last.err : 0, pf ? last.cr2 : 0, got);
		}
		/* accessed and dirty flags of every entry of the window: (D << 1) | A */
		kprintf("pgf %d ad:", c);
		u64 eA = pae ? pd1[0] : pd32[256], eB = pae ? pd1[1] : pd32[257];
		kputc(' '); kputc('0' + ((eA >> 5) & 3)); kputc('0' + ((eB >> 5) & 3)); kputc(' ');
		for (u32 i = 0; i < 6; i++) kputc('0' + ((get(pta, ia + i) >> 5) & 3));
		for (u32 i = 0; i < 2; i++) kputc('0' + ((get(ptb, i) >> 5) & 3));
		kputc('\n');
	}
	WRCR(0, cr0);
	WRCR(4, cr4);
	wrmsr(EFER, 0);
	trap_hook = 0;
}

/* Model-only: a 4 MiB page whose PDE has one of bits 21:13 set. Without PSE-36 (CPUID.1:EDX[17] = 0)
   they are all reserved (SDM vol. 3 table 4-4 with M = 32): #PF with P = 1 and RSVD = 1 for a ring-0
   read (9) and a ring-3 write (f), and the PDE's accessed flag stays clear. TCG implements PSE-36
   whatever CPUID says (bits 20:13 address memory above 4 GiB), so this is not compared with QEMU. */
void test_paging_fuzz_model(void) {
	u32 cr0 = RDCR(0) & ~0x80010000u, cr4 = RDCR(4) & ~0x30u;
	pae = 0; pse = 1;
	trap_hook = pgf_hook;
	kputs("pgfm.pse.rsvd:");
	for (u32 b = 13; b <= 21; b++) {
		WRCR(0, cr0);
		pd32[257] = LARGE | 0x87 | (1u << b);
		WRCR(4, cr4 | 0x10);
		WRCR(3, (u32)pd32);
		WRCR(0, cr0 | 0x80000000u);
		int vec = TRY((void)*(volatile u32 *)(W32 + 0x6000));
		u32 e = last.err;
		int w = run_user(u_write, W32 + 0x7000, 0);
		kprintf(" %d:%x/%x/%x/%x a=%d", b, vec, e, w, last.err, (pd32[257] >> 5) & 1);
	}
	kputc('\n');
	WRCR(0, cr0);
	pd32[257] = 0;
	WRCR(4, cr4);
	trap_hook = 0;
}
