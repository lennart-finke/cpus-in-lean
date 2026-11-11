/* Legacy two-level paging: baseline checks that the harness itself agrees between QEMU and the model. */
#include "sys.h"

/* Ring-3 snippets: load/store through EAX, then return to the kernel with INT 0x40. */
__asm__(
	".globl u_read\nu_read: movl (%eax), %ebx\n int $0x40\n"
	".globl u_write\nu_write: movl %ebx, (%eax)\n int $0x40\n"
	".globl u_call\nu_call: call *%eax\n int $0x40\n");
extern char u_read[], u_write[], u_call[];

/* Run a ring-3 snippet with EAX/EBX preset; returns the event vector (0x40 = completed). */
int run_user(char *code, u32 eax, u32 ebx) {
	static u8 ustack[4096] __attribute__((aligned(16)));
	return TRY(({
		__asm__ volatile("" :: "a"(eax), "b"(ebx));
		register u32 a __asm__("eax") = eax;
		register u32 b __asm__("ebx") = ebx;
		__asm__ volatile(
			"movl %2, %%ecx\n movl %%ecx, %%ds\n movl %%ecx, %%es\n"
			"pushl %2\n pushl %3\n pushl $0x202\n pushl %4\n pushl %5\n iret"
			:: "a"(a), "b"(b), "i"(UDATA), "r"((u32)ustack + sizeof ustack), "i"(UCODE), "r"((u32)code)
			: "ecx", "memory");
	}));
}

static u32 *pd;

static void map4k(u32 *dir, u32 lin, u32 phys, u32 flags) {
	u32 *pt;
	if (!(dir[lin >> 22] & 1)) {
		pt = page_alloc(1);
		dir[lin >> 22] = (u32)pt | 7;
	} else pt = (u32 *)(dir[lin >> 22] & ~0xFFF);
	pt[(lin >> 12) & 0x3FF] = phys | flags;
}
static u32 *pte_of(u32 *dir, u32 lin) { return &((u32 *)(dir[lin >> 22] & ~0xFFF))[(lin >> 12) & 0x3FF]; }

void test_paging(void) {
	pd = page_alloc(1);
	for (u32 a = 0; a < 0x800000; a += 4096) map4k(pd, a, a, 7);
	u32 *data = page_alloc(3);
	data[0] = 0x11111111; data[1024] = 0x22222222; data[2048] = 0x33333333;
	u32 L = 0x40000000;
	map4k(pd, L, (u32)data, 0x1);              /* supervisor, read-only */
	map4k(pd, L + 0x1000, (u32)data + 0x1000, 0x7);  /* user, writable */
	map4k(pd, L + 0x2000, (u32)data + 0x2000, 0x0);  /* not present */
	pd[0x81] = 0x02000000 | 0x87;               /* 4 MiB page at 0x20400000 -> 0x02000000 (needs PSE) */
	WRCR(3, (u32)pd);
	WRCR(4, RDCR(4) | 0x10);
	WRCR(0, RDCR(0) | 0x80000000);

	volatile u32 *p = (u32 *)L;
	u32 v = 0;
	report("pg.read", TRY(v = p[0]));
	kprintf("pg.read.value: %x pte=%x\n", v, *pte_of(pd, L));
	WRCR(0, RDCR(0) & ~0x10000);
	report("pg.write.nowp", TRY(p[1] = 0x44));
	kprintf("pg.write.nowp.pte: %x\n", *pte_of(pd, L));
	WRCR(0, RDCR(0) | 0x10000);
	report("pg.write.wp", TRY(p[2] = 0x55));
	report("pg.notpresent", TRY(v = p[2048]));
	report("pg.user.super", run_user(u_read, L, 0));
	report("pg.user.write.ro", run_user(u_write, L, 0));
	report("pg.user.write.ok", run_user(u_write, L + 0x1000, 0x99));
	kprintf("pg.user.pte: %x val=%x\n", *pte_of(pd, L + 0x1000), data[1024]);
	volatile u32 *big = (u32 *)0x20400010;
	report("pg.4m.write", TRY(*big = 0xABCD));
	kprintf("pg.4m.pde: %x val=%x\n", pd[0x81], *big);
	/* change a PTE, then INVLPG (a stale entry before the flush is implementation-dependent) */
	*pte_of(pd, L + 0x1000) = ((u32)data + 0x2000) | 7;
	invlpg(L + 0x1000);
	kprintf("pg.tlb.flushed: %x\n", ((volatile u32 *)L)[1024]);

	WRCR(0, RDCR(0) & ~0x80000000);
	WRCR(4, RDCR(4) & ~0x10);
}
