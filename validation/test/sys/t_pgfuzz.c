/* Paging differential fuzzing: random 32-bit/PSE/PAE/NX page tables for a small linear window, random
   accesses (reads, writes, instruction fetches; ring 0 and ring 3; page-crossing), compared with QEMU.
   Each case rebuilds the tables with paging off and re-enables paging, so no TLB entry survives.
   Dimensions of system workstream A: CR4.PGE at random; PSE-36 (4 MiB PDE bits 20:13 = physical
   address bits 39:32, beyond the RAM: values read there are not printed); PAE reserved bits only
   above MAXPHYADDR = 48 (CPUID 8000_0008); and in about half of the cases (when CPUID reports SMEP and
   SMAP) a supervisor identity map with CR4.SMEP/SMAP at random and EFLAGS.AC at random for ring-0
   accesses. The ring-3 snippets and their stack are then copied to user pages at USERPG. */
#include "sys.h"

#define EFER 0xC0000080
#define NFRAMES 8
#define LARGE 0x3800000         /* 4 MiB aligned physical region (56..60 MiB) backing large pages */
#define W32 0x403FA000          /* window: 6 pages through PDE 256, then 2 pages through PDE 257 */
#define WPAE 0x401FA000         /* window: 6 pages through PD1[0], then 2 pages through PD1[1] */
#define NPAGES 8
#define USERPG 0x3400000        /* user code and stack (52 MiB, a 2 MiB region of its own) */

static u32 rs = 0x6B43A9B5;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

/* Ring-3 snippets (see u_read in t_paging.c): sizes 1 and 2, and the stub that returns an immediate */
__asm__(
	".globl pgf_r1\npgf_r1: movzbl (%eax), %ebx\n int $0x40\n"
	".globl pgf_r2\npgf_r2: movzwl (%eax), %ebx\n int $0x40\n"
	".globl pgf_w1\npgf_w1: movb %bl, (%eax)\n int $0x40\n"
	".globl pgf_w2\npgf_w2: movw %bx, (%eax)\n int $0x40\n");
extern char pgf_r1[], pgf_r2[], pgf_w1[], pgf_w2[];
/* ring-3 entry with the stack at the top of USERPG's second page (run_user's stack is kernel data) */
static int pgf_user(char *code, u32 eax, u32 ebx) {
	return TRY(({
		register u32 a __asm__("eax") = eax;
		register u32 b __asm__("ebx") = ebx;
		__asm__ volatile(
			"movl %2, %%ecx\n movl %%ecx, %%ds\n movl %%ecx, %%es\n"
			"pushl %2\n pushl %3\n pushl $0x202\n pushl %4\n pushl %5\n iret"
			:: "a"(a), "b"(b), "i"(UDATA), "i"(USERPG + 0x2000), "i"(UCODE), "r"((u32)code)
			: "ecx", "memory");
	}));
}
/* copies of the snippets in USERPG: r1 r2 r4 w1 w2 w4 call */
static char *usnip[7];
static void copy_snippets(void) {
	char *src[7] = { pgf_r1, pgf_r2, u_read, pgf_w1, pgf_w2, u_write, u_call };
	char *d = (char *)USERPG;
	for (int k = 0; k < 7; k++) {
		usnip[k] = d;
		for (int i = 0; i < 6; i++) d[i] = src[k][i];   /* each is at most 6 bytes, ending with INT 0x40 */
		d += 16;
	}
}

static u32 *pd32, *ipt32;       /* 32-bit page directory and its identity page tables (0..64 MiB) */
static u32 *ipt32s;             /* the same with supervisor pages except USERPG (SMEP/SMAP cases) */
static u64 *pdpt, *pd0, *pd1;   /* PAE: PDPT, identity PD (2 MiB pages), window PD */
static u64 *pd0s;               /* the same, supervisor except USERPG's 2 MiB page */
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
	if ((e & 0x80) && pse) return (e & 0x1FE000) ? ~0u : (e & 0xFFC00000) | (lin & 0x3FFFFF);  /* PSE-36: above 4 GiB */
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

/* A random PAE reserved bit (none most of the time): bits 62:48 (MAXPHYADDR = 48), and 63 when NXE = 0.
   Bits 47:36 are address bits on the EPYC 7742 but reserved under TCG (fewer physical-address bits):
   t_pae.c checks one of them with a deviation rule. */
static u64 pae_rsvd(int nxe) {
	if (rnd() % 24) return 0;
	u32 b = 48 + rnd() % (nxe ? 15 : 16);
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
		if (rnd() % 8 == 0) e |= (rnd() & 0xFF) << 13;    /* PSE-36: physical-address bits 39:32 */
	}
	return e;
}

static void show64(u64 e) { if (pae) kprintf(" %x_%x", (u32)(e >> 32), (u32)e); else kprintf(" %x", (u32)e); }

static const char *const kname[] = { "rd", "wr", "x" };

/* Make one access (kind 0 read, 1 write, 2 fetch; `size` bytes; ring 3 if `user`; EFLAGS.AC for a ring-0
   access if `ac`; `high`: a PSE-36 page above 4 GiB whose values are not printed) and print its result. */
static void pg_access(const char *tag, u32 c, u32 a, u32 kind, u32 size, u32 user, u32 lin, u32 v, int ac, int high) {
	u32 got = 0;
	int vec;
	if (kind == 2) {
		/* mov $v, %eax; ret: plant it through the physical addresses of the mapped bytes */
		u8 code[6] = { 0xB8, (u8)v, (u8)(v >> 8), (u8)(v >> 16), (u8)(v >> 24), 0xC3 };
		for (u32 k = 0; k < 6; k++) { u32 p = lin2phys(lin + k); if (p != ~0u) *(volatile u8 *)p = code[k]; }
		u_eax = 0;
		if (user) { vec = pgf_user(usnip[6], lin, 0); got = u_eax; }
		else { u32 (*volatile fn)(void) = (u32 (*)(void))lin; vec = TRY(got = fn()); }
	} else if (kind == 0) {
		u_ebx = 0;
		if (user) { vec = pgf_user(usnip[size == 1 ? 0 : size == 2 ? 1 : 2], lin, 0); got = u_ebx; }
		else {
			if (ac) __asm__ volatile("pushfl\n orl $0x40000, (%%esp)\n popfl" ::: "memory", "cc");
			if (size == 1) vec = TRY(got = *(volatile u8 *)lin);
			else if (size == 2) vec = TRY(got = *(volatile u16 *)lin);
			else vec = TRY(got = *(volatile u32 *)lin);
			__asm__ volatile("pushfl\n andl $~0x40000, (%%esp)\n popfl" ::: "memory", "cc");
		}
		if (high) got = 0;
	} else {
		if (user) vec = pgf_user(usnip[size == 1 ? 3 : size == 2 ? 4 : 5], lin, v);
		else {
			if (ac) __asm__ volatile("pushfl\n orl $0x40000, (%%esp)\n popfl" ::: "memory", "cc");
			if (size == 1) vec = TRY(*(volatile u8 *)lin = (u8)v);
			else if (size == 2) vec = TRY(*(volatile u16 *)lin = (u16)v);
			else vec = TRY(*(volatile u32 *)lin = v);
			__asm__ volatile("pushfl\n andl $~0x40000, (%%esp)\n popfl" ::: "memory", "cc");
		}
		/* the bytes as they are now in memory (all or nothing written) */
		for (u32 k = 0; k < size; k++) {
			u32 p = lin2phys(lin + k);
			got |= (p == ~0u ? 0xEEu : *(volatile u8 *)p) << (8 * k);
		}
	}
	int pf = vec == 14;
	kprintf("%s %d.%d: %s%d r%d%s %x vec=%x err=%x cr2=%x val=%x\n", tag, c, a, kname[kind], size, user ? 3 : 0,
	        ac ? "ac" : "", lin, vec, pf || vec == 13 ? last.err : 0, pf ? last.cr2 : 0, got);
}

void test_paging_fuzz(void) {
	u32 n = param("pgf", 400);
	rs = fuzz_seed(rs);
	trap_hook = pgf_hook;

	pd32 = page_alloc(1);
	ipt32 = page_alloc(16);
	for (u32 a = 0; a < 0x4000000; a += 0x1000) ipt32[a >> 12] = a | 7;
	for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)ipt32 + i * 0x1000) | 7;
	ipt32s = page_alloc(16);
	for (u32 a = 0; a < 0x4000000; a += 0x1000) ipt32s[a >> 12] = a | ((a >> 21) == (USERPG >> 21) ? 7 : 3);
	pdpt = page_alloc(1); pd0 = page_alloc(1); pd1 = page_alloc(1);
	for (u32 i = 0; i < 32; i++) pd0[i] = ((u64)i << 21) | 0x87;
	pd0s = page_alloc(1);
	for (u32 i = 0; i < 32; i++) pd0s[i] = ((u64)i << 21) | (i == (USERPG >> 21) ? 0x87 : 0x83);
	copy_snippets();
	int smx_ok = has_feature(7, 0, 1, 7) && has_feature(7, 0, 1, 20);
	int pge_ok = has_feature(1, 0, 3, 13);
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

	u32 cr0 = RDCR(0) & ~0x80010000u, cr4 = RDCR(4) & ~0x3000B0u;
	for (u32 c = 0; c < n; c++) {
		WRCR(0, cr0);
		u32 mode = rnd() % 4;
		pae = mode >= 2; pse = mode == 1;
		int nxe = pae ? mode == 3 : (int)(rnd() % 2);   /* NXE has no effect on 32-bit paging */
		int wp = rnd() % 2;
		int smx = smx_ok && rnd() % 2;                    /* supervisor identity map, SMEP/SMAP */
		int smep = smx && rnd() % 2, smap = smx && rnd() % 2, pge = pge_ok && rnd() % 2;
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
			pdpt[0] = (u32)(smx ? pd0s : pd0) | 1; pdpt[1] = pdpte; pdpt[2] = pdpt[3] = 0;
			clear((u32 *)pd1);
			pd1[0] = pdeA; pd1[1] = pdeB;
		} else {
			for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)(smx ? ipt32s : ipt32) + i * 0x1000) | 7;
			for (u32 i = 16; i < 1024; i++) pd32[i] = 0;
			pd32[256] = (u32)pdeA; pd32[257] = (u32)pdeB;
		}
		kprintf("pgf %d: %s wp=%d nxe=%d", c, pae ? "pae" : pse ? "pse" : "32", wp, nxe);
		if (smx || pge) kprintf(" smx=%d smep=%d smap=%d pge=%d", smx, smep, smap, pge);
		if (pae) { kputs(" pdpte"); show64(pdpte); }
		kputs(" pde"); show64(pdeA); show64(pdeB);
		kputs(" pte");
		for (u32 i = 0; i < 6; i++) show64(get(pta, ia + i));
		for (u32 i = 0; i < 2; i++) show64(get(ptb, i));
		kputc('\n');

		WRCR(4, cr4 | (pae ? 0x20 : 0) | (pse || (pae && rnd() % 2) ? 0x10 : 0) |   /* PSE: ignored with PAE */
		        (smep ? 0x100000 : 0) | (smap ? 0x200000 : 0) | (pge ? 0x80 : 0));
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
			u32 v = rnd();
			/* a PSE-36 page above 4 GiB: no instruction fetch (beyond any memory), values not printed */
			int high = !pae && pse && (pdeB & 0x80) && (pdeB & 0x1FE000) && lin + size - 1 >= W + 0x6000;
			if (high && kind == 2) { kind = 0; size = 4; }
			/* EFLAGS.AC for a ring-0 access (overrides SMAP for explicit accesses) */
			int ac = !user && kind != 2 && rnd() % 2;
			pg_access("pgf", c, a, kind, size, user, lin, v, ac, high);
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
	for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)ipt32 + i * 0x1000) | 7;
	trap_hook = 0;
}

/* TLB fuzzing (`pgt=N`, 300 cases by default): the tables are built as in `pgf`, paging is enabled
   once per case, and then 6 to 15 steps follow with paging on, so that accesses hit translations cached
   by earlier ones: accesses as in `pgf`; permission upgrades of a PTE or PDE without invalidation;
   arbitrary changes of a PTE (new frame and attributes) or of a PDE (also between a page table and a
   4 MiB / 2 MiB page), with or without a following INVLPG or MOV CR3; INVLPG of any window page; MOV
   CR3 with the same value; CR0.WP, CR4.PGE and (on the supervisor identity map) CR4.SMEP/SMAP
   toggles. EFLAGS.AC is chosen per access.
   Only accesses whose result the architecture fixes are generated. A page is "uncertain" from an
   arbitrary change of its PTE or PDE until an invalidation that covers it: until then "it is
   unpredictable whether the old or updated entry will be used" (AMD APM vol. 2, 5.5.3 "Invalidation of
   Table Entry Upgrades"; also "Speculative Caching of Address Translations": any valid entry may be in
   the TLB), and no access touches it (accesses crossing into it are not generated either). Covering
   invalidations: INVLPG of the page (5.5.3 "Explicit Invalidations"), and of any page of a 4 MiB /
   2 MiB page if every version of the PDE since the region was last certain mapped a large page (the
   INVLPG drops the large translation); MOV CR3, except for pages one of whose versions was global
   (G = 1 with CR4.PGE: kept by CR3 loads, 5.5.2 "Global Pages"; their retention is not determined);
   CR4.PGE changes (5.5.3 "Implicit Invalidations": the whole TLB). Upgrades (P, R/W or U/S set, NX
   cleared, nothing else changed) leave every page certain: "if a table entry is updated to remove a
   page access constraint, such as removing supervisor, read-only, and/or no-execute restrictions, an
   invalidation is not required because the hardware will automatically detect the changes" (5.5.3; on
   a would-be page fault the walk is repeated from memory, "Use of Cached Entries When Reporting a Page
   Fault Exception"). The Intel SDM is weaker here (vol. 3, 4.10.4.3: an upgrade without invalidation
   may still fault); this is an AMD rule. U/S is not upgraded on the supervisor identity map, where
   SMEP/SMAP make U/S = 1 a restriction for supervisor accesses. CR0.WP, CR4.SMEP/SMAP and EFLAGS.AC
   are checked at the time of the access (APM 5.6.4-5.6.6 state the checks for the access and require
   no invalidation; SDM vol. 3, 4.10.2.2: a TLB entry holds the logical AND of the R/W and U/S flags,
   and the access rights follow from them and the current control bits), so their toggles keep every
   page certain. EFER.NXE and PDPTEs are not changed (a WRMSR may flush the TLB, "writes to certain
   model-specific registers"; PAE PDPTEs are loaded by MOV CR3). */
#define TPAGES 9                /* window pages 0..7 and page 8, the page after the window (through PDE B) */
static u32 t_unc, t_gmay, t_allLargeB, t_pge, t_ia;

static int t_large(u64 e) { return (pae || pse) && (e & 0x80); }
static u64 pde_get(int k) { return pae ? pd1[k] : pd32[256 + k]; }
static void pde_set(int k, u64 e) { if (pae) pd1[k] = e; else pd32[256 + k] = (u32)e; }
/* the page table and index of the PTE of window page p (0..7) */
static u32 *pt_of(u32 p, u32 *idx) { if (p < 6) { *idx = t_ia + p; return pta; } *idx = p - 6; return ptb; }
/* G of the leaf that maps page p now (with CR4.PGE): the large PDE or the PTE */
static u32 t_leafg(u32 p) {
	if (!t_pge) return 0;
	u64 b = pde_get(1);
	if (p >= 6 && t_large(b)) return (b >> 8) & 1;
	if (p == 8) return 0;   /* ptb[2] is 0 */
	u32 idx; u32 *pt = pt_of(p, &idx);
	return (get(pt, idx) >> 8) & 1;
}
/* page p is about to change arbitrarily: the version now in the tables may stay cached */
static void t_mark(u32 p) { t_gmay |= t_leafg(p) << p; t_unc |= 1u << p; }
static void t_regionB(void) { if (!(t_unc & 0x1C0)) t_allLargeB = t_large(pde_get(1)); }
static void t_settle(u32 p) { t_unc &= ~(1u << p); t_gmay &= ~(1u << p); t_regionB(); }
static void t_invlpg(u32 p, u32 off) {
	invlpg((pae ? WPAE : W32) + p * 0x1000 + off);
	int all = p >= 6 && t_allLargeB;
	t_settle(p);
	if (all) { t_settle(6); t_settle(7); t_settle(8); }
}
static void t_cr3(void) {
	WRCR(3, pae ? (u32)pdpt : (u32)pd32);
	t_unc &= t_pge ? t_gmay : 0; t_gmay &= t_unc;
	t_regionB();
}

void test_paging_tlb_fuzz(void) {
	u32 n = param("pgt", 300);
	rs = fuzz_seed(0x2C9277B5);
	trap_hook = pgf_hook;
	int smx_ok = has_feature(7, 0, 1, 7) && has_feature(7, 0, 1, 20);
	int pge_ok = has_feature(1, 0, 3, 13);
	u32 cr0 = RDCR(0) & ~0x80010000u, cr4 = RDCR(4) & ~0x3000B0u;
	for (u32 c = 0; c < n; c++) {
		WRCR(0, cr0);
		u32 mode = rnd() % 4;
		pae = mode >= 2; pse = mode == 1;
		int nxe = pae ? mode == 3 : (int)(rnd() % 2);
		int wp = rnd() % 2;
		int smx = smx_ok && rnd() % 2;
		int smep = smx && rnd() % 2, smap = smx && rnd() % 2;
		t_pge = pge_ok && rnd() % 2;
		wrmsr(EFER, nxe ? 0x800 : 0);
		clear(pta); clear(ptb);
		u32 W = pae ? WPAE : W32;
		t_ia = pae ? 0x1FA : 0x3FA;
		int big = rnd() % 3 == 0;
		u64 pdeA = nonleaf(pta, nxe), pdeB = (big && (pae || pse)) ? large(nxe) : nonleaf(ptb, nxe);
		for (u32 i = 0; i < 6; i++) put(pta, t_ia + i, leaf4k(nxe));
		for (u32 i = 0; i < 2; i++) put(ptb, i, leaf4k(nxe));
		if (pae) {
			pdpt[0] = (u32)(smx ? pd0s : pd0) | 1; pdpt[1] = (u32)pd1 | 1; pdpt[2] = pdpt[3] = 0;
			clear((u32 *)pd1);
		} else {
			for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)(smx ? ipt32s : ipt32) + i * 0x1000) | 7;
			for (u32 i = 16; i < 1024; i++) pd32[i] = 0;
		}
		pde_set(0, pdeA); pde_set(1, pdeB);
		kprintf("pgt %d: %s wp=%d nxe=%d smx=%d smep=%d smap=%d pge=%d pde", c, pae ? "pae" : pse ? "pse" : "32",
		        wp, nxe, smx, smep, smap, t_pge);
		show64(pdeA); show64(pdeB);
		kputs(" pte");
		for (u32 i = 0; i < 6; i++) show64(get(pta, t_ia + i));
		for (u32 i = 0; i < 2; i++) show64(get(ptb, i));
		kputc('\n');
		u32 c4 = cr4 | (pae ? 0x20 : 0) | (pse || (pae && rnd() % 2) ? 0x10 : 0) |
		         (smep ? 0x100000 : 0) | (smap ? 0x200000 : 0) | (t_pge ? 0x80 : 0);
		WRCR(4, c4);
		WRCR(3, pae ? (u32)pdpt : (u32)pd32);
		WRCR(0, cr0 | 0x80000000u | (wp ? 0x10000 : 0));
		t_unc = t_gmay = 0;
		t_allLargeB = t_large(pdeB);

		u32 ns = 6 + rnd() % 10;
		for (u32 s = 0; s < ns; s++) {
			u32 op = rnd() % 16;
			if (op < 7) {
				/* an access that touches certain pages only */
				for (int tries = 0; tries < 4; tries++) {
					u32 kind = rnd() % 5;
					kind = kind < 2 ? 0 : kind < 4 ? 1 : 2;
					u32 size = kind == 2 ? 6 : (1u << (rnd() % 3));
					u32 user = rnd() % 2;
					u32 off = rnd() % 3 ? 0x1000 - 1 - rnd() % 8 : rnd() % 0x1000;
					u32 lin = W + (rnd() % NPAGES) * 0x1000 + off;
					u32 v = rnd();
					u64 b = pde_get(1);
					int high = !pae && pse && (b & 0x80) && (b & 0x1FE000) && lin + size - 1 >= W + 0x6000;
					if (high && kind == 2) { kind = 0; size = 4; }
					int ac = !user && kind != 2 && rnd() % 2;
					u32 p0 = (lin - W) >> 12, p1 = (lin + size - 1 - W) >> 12;
					if ((t_unc >> p0) & 1 || (t_unc >> p1) & 1) continue;
					pg_access("pgt", c, s, kind, size, user, lin, v, ac, high);
					break;
				}
			} else if (op < 9) {
				/* upgrade: set P, R/W or U/S, or clear NX, of a PTE (0..7) or of PDE A/B (8, 9) */
				u32 t = rnd() % 10, idx = 0;
				u32 *pt = t < 8 ? pt_of(t, &idx) : 0;
				u64 e = t < 8 ? get(pt, idx) : pde_get(t - 8);
				u64 cand[4]; int nc = 0;
				if (!(e & 1)) cand[nc++] = 1;
				if (!(e & 2)) cand[nc++] = 2;
				if (!smx && !(e & 4)) cand[nc++] = 4;
				if (pae && nxe && (e >> 63)) cand[nc++] = 1ULL << 63;
				if (!nc) { kprintf("pgt %d.%d: up -\n", c, s); continue; }
				u64 bit = cand[rnd() % nc];
				e = bit >> 63 ? e & ~bit : e | bit;
				if (t < 8) put(pt, idx, e); else pde_set(t - 8, e);
				kprintf("pgt %d.%d: up %s%d", c, s, t < 8 ? "pte" : "pde", t < 8 ? t : t - 8);
				show64(e); kputc('\n');
			} else if (op < 11) {
				/* a new PTE for page p, then INVLPG or not */
				u32 p = rnd() % 8, idx;
				u32 *pt = pt_of(p, &idx);
				t_mark(p);
				u64 e = leaf4k(nxe);
				put(pt, idx, e);
				kprintf("pgt %d.%d: pte%d", c, s, p); show64(e);
				if (rnd() % 2) { u32 off = rnd() % 0x1000; t_invlpg(p, off); kprintf(" invlpg %x", off); }
				kputc('\n');
			} else if (op < 12) {
				/* a new PDE A or B, then INVLPG of a page under it, MOV CR3, or nothing */
				u32 k = rnd() % 2;
				for (u32 p = k ? 6 : 0; p < (k ? TPAGES : 6); p++) t_mark(p);
				u64 e;
				if (!k) e = nonleaf(pta, nxe);
				else {
					e = ((pae || pse) && rnd() % 3 == 0) ? large(nxe) : nonleaf(ptb, nxe);
					if (!pae && !pse && rnd() % 3 == 0) e |= 0x80;     /* ignored PS bit */
					t_allLargeB = t_allLargeB && t_large(e);
				}
				pde_set(k, e);
				kprintf("pgt %d.%d: pde%d", c, s, k); show64(e);
				u32 r = rnd() % 3;
				if (r == 0) {
					u32 p = k ? 6 + rnd() % 3 : rnd() % 6, off = rnd() % 0x1000;
					t_invlpg(p, off);
					kprintf(" invlpg %d %x", p, off);
				} else if (r == 1) { t_cr3(); kputs(" cr3"); }
				kputc('\n');
			} else if (op == 12) {
				u32 p = rnd() % TPAGES, off = rnd() % 0x1000;
				t_invlpg(p, off);
				kprintf("pgt %d.%d: invlpg %d %x\n", c, s, p, off);
			} else if (op == 13) {
				t_cr3();
				kprintf("pgt %d.%d: cr3\n", c, s);
			} else if (op == 14 && pge_ok && rnd() % 2) {
				/* CR4.PGE toggle: the whole TLB is invalidated */
				t_pge = !t_pge;
				c4 ^= 0x80;
				WRCR(4, c4);
				t_unc = t_gmay = 0;
				t_regionB();
				kprintf("pgt %d.%d: pge=%d\n", c, s, t_pge);
			} else if (op == 15 && smx) {
				c4 ^= rnd() % 2 ? 0x100000 : 0x200000;
				WRCR(4, c4);
				kprintf("pgt %d.%d: smep=%d smap=%d\n", c, s, (c4 >> 20) & 1, (c4 >> 21) & 1);
			} else {
				wp = !wp;
				WRCR(0, cr0 | 0x80000000u | (wp ? 0x10000 : 0));
				kprintf("pgt %d.%d: wp=%d\n", c, s, wp);
			}
		}
		/* accessed and dirty flags of every entry of the window: (D << 1) | A */
		kprintf("pgt %d ad:", c);
		u64 eA = pde_get(0), eB = pde_get(1);
		kputc(' '); kputc('0' + ((eA >> 5) & 3)); kputc('0' + ((eB >> 5) & 3)); kputc(' ');
		for (u32 i = 0; i < 6; i++) kputc('0' + ((get(pta, t_ia + i) >> 5) & 3));
		for (u32 i = 0; i < 2; i++) kputc('0' + ((get(ptb, i) >> 5) & 3));
		kputc('\n');
	}
	WRCR(0, cr0);
	WRCR(4, cr4);
	wrmsr(EFER, 0);
	for (u32 i = 0; i < 16; i++) pd32[i] = ((u32)ipt32 + i * 0x1000) | 7;
	trap_hook = 0;
}

/* Model-only: a 4 MiB page whose PDE has one of bits 21:13 set. With PSE-36 (CPUID.1:EDX[17] = 1)
   bits 20:13 are physical-address bits 39:32 (AMD APM vol. 2, figure 5-8): the access goes to memory
   above 4 GiB, which the model has none of (reads are open bus, all ones; writes are dropped), and the
   PDE gets its accessed flag; bit 21 is reserved: #PF with P = 1 and RSVD = 1 for a ring-0 read (9) and
   a ring-3 write (f), accessed flag clear. The values read are model-specific (TCG's unassigned memory
   differs), so this stays model-only; the vectors are compared with QEMU by sysa.pse36. */
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
		u32 val = 0;
		int vec = TRY(val = *(volatile u32 *)(W32 + 0x6000));
		u32 e = vec == 14 ? last.err : 0;
		int w = run_user(u_write, W32 + 0x7000, 0);
		kprintf(" %d:%x/%x/%x/%x a=%d v=%x", b, vec, e, w, w == 14 ? last.err : 0, (pd32[257] >> 5) & 1, val);
	}
	kputc('\n');
	WRCR(0, cr0);
	pd32[257] = 0;
	WRCR(4, cr4);
	trap_hook = 0;
}
