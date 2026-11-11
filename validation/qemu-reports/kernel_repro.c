/* Bare-metal wrapper around repro_cases.h: run under qemu-system-i386 and the Lean model (x86sys). */
static inline void outb(unsigned short p, unsigned char v) { __asm__ volatile("outb %0, %1" :: "a"(v), "Nd"(p)); }
static inline unsigned char inb(unsigned short p) { unsigned char v; __asm__ volatile("inb %1, %0" : "=a"(v) : "Nd"(p)); return v; }
static void pc(char c) { while (!(inb(0x3FD) & 0x20)) {} outb(0x3F8, c); }
static void ps(const char *s) { while (*s) pc(*s++); }
static void ph(unsigned long long v, int n) { for (int i = n - 1; i >= 0; i--) pc("0123456789abcdef"[(v >> (4 * i)) & 15]); }
#include "repro_cases.h"
static void out(const char *name, const f80 *r0, int has1, const f80 *r1, unsigned short sw) {
	ps(name); ps(" st0="); ph(r0->se, 4); pc('_'); ph(r0->sig, 16);
	if (has1) { ps(" st1="); ph(r1->se, 4); pc('_'); ph(r1->sig, 16); }
	ps(" sw="); ph(sw, 4); pc('\n');
}
void kmain(void) {
	unsigned cr0;
	__asm__ volatile("mov %%cr0, %0" : "=r"(cr0));
	cr0 = (cr0 & ~0xCu) | 0x22;   /* EM = TS = 0, MP = NE = 1 */
	__asm__ volatile("mov %0, %%cr0" :: "r"(cr0));
	report1(); report2(); report3();
	ps("END\n");
	__asm__ volatile("outl %0, $0xf4" :: "a"(0));
	for (;;) __asm__ volatile("cli; hlt");
}
__asm__(".section .multiboot, \"a\"\n .align 4\n .long 0x1BADB002, 0, -0x1BADB002\n .text\n"
        ".globl _start\n_start: movl $kstack_top, %esp\n call kmain\n"
        ".bss\n .align 16\n .space 8192\nkstack_top:\n .text\n");
