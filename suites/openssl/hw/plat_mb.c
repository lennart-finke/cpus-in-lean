/* Bare machine: COM1 for output, the isa-debug-exit port to stop QEMU. */
#include "driver.h"
#include "syms.h"
static inline void outb(unsigned short p, u8 v) { __asm__ volatile("outb %0, %1" : : "a"(v), "Nd"(p)); }
static inline u8 inb(unsigned short p) { u8 v; __asm__ volatile("inb %1, %0" : "=a"(v) : "Nd"(p)); return v; }
static inline void outl(unsigned short p, u32 v) { __asm__ volatile("outl %0, %1" : : "a"(v), "Nd"(p)); }

void plat_init(void) {
	u8 *dst = (u8 *)IMAGE_BASE;
	for (u32 i = 0; i < (u32)(image_end - image_blob); i++) dst[i] = image_blob[i];
}
void plat_putc(char c) {
	while (!(inb(0x3FD) & 0x20)) {}
	outb(0x3F8, (u8)c);
}
void plat_exit(void) {
	outl(0xF4, 0);
	for (;;) __asm__ volatile("hlt");
}
