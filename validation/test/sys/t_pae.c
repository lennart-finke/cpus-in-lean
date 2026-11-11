/* PAE paging and execute-disable. */
#include "sys.h"

#define EFER 0xC0000080
static u64 *pdpt, *pd0, *pd1, *pt1;

static void show(const char *what, u64 e) { kprintf("%s: %x_%x\n", what, (u32)(e >> 32), (u32)e); }

static void pae_on(void) {
	WRCR(3, (u32)pdpt);
	WRCR(4, RDCR(4) | 0x20);
	WRCR(0, RDCR(0) | 0x80010000);
}
static void pae_off(void) {
	WRCR(0, RDCR(0) & ~0x80000000);
	WRCR(4, RDCR(4) & ~0x20);
}

void test_pae(void) {
	pdpt = page_alloc(1);
	pd0 = page_alloc(1); pd1 = page_alloc(1); pt1 = page_alloc(1);
	u8 *data = page_alloc(4);
	u8 *big = page_alloc(1024);   /* 4 MiB: room for a 2 MiB aligned page */
	u32 bigphys = ((u32)big + 0x1FFFFF) & ~0x1FFFFF;
	for (int i = 0; i < 8; i++) pd0[i] = (u64)(i << 21) | 0x87;   /* identity 0..16 MiB, 2 MiB pages, user */
	pdpt[0] = (u32)pd0 | 1;
	pdpt[1] = (u32)pd1 | 1;
	pd1[0] = (u32)pt1 | 7;
	u32 L = 0x40000000;
	pt1[0] = (u32)data | 0x3;                   /* supervisor RW */
	pt1[1] = ((u32)data + 0x1000) | 0x1;        /* supervisor RO */
	pt1[2] = ((u32)data + 0x2000) | 0x7 | (1ULL << 50);  /* reserved bit 50 (MAXPHYADDR = 48) */
	pt1[4] = ((u32)data + 0x2000) | 0x7 | (1ULL << 40);  /* address bit 40: above the RAM, not reserved */
	pt1[3] = ((u32)data + 0x3000) | 0x7 | (1ULL << 63);  /* XD (reserved while NXE = 0) */
	pd1[1] = bigphys | 0x83;                    /* 2 MiB page at 0x40200000 */
	pd1[2] = bigphys | 0x83 | 0x2000;           /* 2 MiB page with reserved bit 13 */
	((u32 *)data)[0] = 0x600DF00D;
	data[0x3000] = 0xC3;                        /* RET */
	*(u32 *)(bigphys + 0x5000) = 0xB16B16;

	void (*volatile fn)(void) = (void (*)(void))(L + 0x3000);
	pae_on();
	volatile u32 *p = (u32 *)L;
	u32 v = 0;
	report("pae.read", TRY(v = p[0]));
	kprintf("pae.read.value: %x\n", v);
	report("pae.write", TRY(p[1] = 7));
	show("pae.pte0", pt1[0]);
	report("pae.write.ro", TRY(p[0x400] = 1));
	report("pae.rsvd50", TRY(v = p[0x800]));
	report("pae.maxphy40", TRY(v = p[0x1000]));
	report("pae.xd.nonxe", TRY(v = p[0xC00]));
	volatile u32 *b = (u32 *)0x40205000;
	report("pae.2m.read", TRY(v = *b));
	kprintf("pae.2m.value: %x\n", v);
	report("pae.2m.write", TRY(*b = 0x1234));
	show("pae.2m.pde", pd1[1]);
	report("pae.2m.rsvd13", TRY(v = *(volatile u32 *)0x40400000));
	report("pae.pdpte.np", TRY(v = *(volatile u32 *)0x80000000));
	report("pae.user.super", run_user(u_read, L, 0));

	/* execute-disable; EFER bit 1 is reserved (bit 0, SCE, and the other EFER bits: sysa.efer.*) */
	kprintf("pae.efer.rsvd: vec=%x\n", TRY(wrmsr(EFER, 2)));
	report("pae.efer.nxe", TRY(wrmsr(EFER, 0x800)));
	kprintf("pae.efer: %x\n", (u32)rdmsr(EFER));
	report("pae.nx.read", TRY(v = p[0xC00]));
	report("pae.nx.fetch", TRY(fn()));
	pt1[3] |= 4;
	invlpg(L + 0x3000);
	report("pae.nx.user.fetch", run_user(u_call, L + 0x3000, 0));
	pt1[3] &= ~(1ULL << 63);
	invlpg(L + 0x3000);
	report("pae.x.fetch", TRY(fn()));
	pd1[0] |= 1ULL << 63;                       /* XD at the PDE level */
	invlpg(L + 0x3000);
	report("pae.nx.pde.fetch", TRY(fn()));
	pd1[0] &= ~(1ULL << 63);
	invlpg(L + 0x3000);

	/* PDPTE registers: loaded by MOV CR3, validated, not re-read from memory */
	u64 *pdpt2 = page_alloc(1);
	memcpy(pdpt2, pdpt, 32);
	pdpt2[1] |= 0x2;                            /* reserved bit 1 */
	kprintf("pae.cr3.rsvd: vec=%x\n", TRY(WRCR(3, (u32)pdpt2)));
	kprintf("pae.cr3: %x\n", RDCR(3) == (u32)pdpt);
	WRCR(3, (u32)pdpt);
	pdpt[1] = 0;                                /* not seen until CR3 is reloaded */
	invlpg(L);
	report("pae.pdpte.cached", TRY(v = p[0]));
	WRCR(3, (u32)pdpt);
	report("pae.pdpte.reloaded", TRY(v = p[0]));
	pdpt[1] = (u32)pd1 | 1;
	WRCR(3, (u32)pdpt);

	/* INVLPG anywhere in a 2 MiB page drops all its cached slices */
	v = *(volatile u32 *)0x40200000 + *(volatile u32 *)0x40300000;
	pd1[1] = (bigphys + 0x200000) | 0x83;       /* points elsewhere now (zeroed memory) */
	*(u32 *)(bigphys + 0x200000 + 0x100000) = 0x5ECD;
	invlpg(0x40200000);
	kprintf("pae.invlpg.large: %x\n", *(volatile u32 *)0x40300000);

	wrmsr(EFER, 0);
	pae_off();
}
