/* A static 32-bit Linux process: the image is mapped at its link address, output goes to stdout. */
#include "driver.h"
#include "syms.h"
/* int 0x80 with five arguments; the sixth (ebp) is always 0 here. */
static long sys(long n, long a, long b, long c, long d, long e) {
	long r;
	__asm__ volatile("pushl %%ebp\n xorl %%ebp, %%ebp\n int $0x80\n popl %%ebp"
		: "=a"(r) : "a"(n), "b"(a), "c"(b), "d"(c), "S"(d), "D"(e) : "memory");
	return r;
}
static char buf[4096];
static u32 used;
static void flush(void) {
	u32 off = 0;
	while (off < used) {
		long n = sys(4, 1, (long)(buf + off), used - off, 0, 0);
		if (n <= 0) break;
		off += (u32)n;
	}
	used = 0;
}
void plat_init(void) {
	u32 len = ((u32)(image_end - image_blob) + 4095) & ~4095u;
	/* mmap2(base, len, READ|WRITE, PRIVATE|FIXED|ANONYMOUS), copy, then READ|EXEC: the image is never written */
	long p = sys(192, IMAGE_BASE, len, 3, 0x32, -1);
	if (p != (long)IMAGE_BASE) { put("!cannot map the image at its link address\n"); plat_exit(); }
	u8 *dst = (u8 *)IMAGE_BASE;
	for (u32 i = 0; i < (u32)(image_end - image_blob); i++) dst[i] = image_blob[i];
	if (sys(125, IMAGE_BASE, len, 5, 0, 0) != 0) { put("!cannot make the image executable\n"); plat_exit(); }
}
void plat_putc(char c) {
	buf[used++] = c;
	if (used == sizeof buf) flush();
}
void plat_exit(void) {
	flush();
	sys(1, 0, 0, 0, 0, 0);
	for (;;) {}
}
void main(void);
__asm__(".text\n.globl _start\n_start:\n andl $-16, %esp\n call main\n hlt\n");
