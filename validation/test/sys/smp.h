/* Helpers of the SMP workstream's system tests (t_apic.c model part, t_ioapic.c, t_x2apic.c, t_smp.c). */
#ifndef SMP_H
#define SMP_H
#include "sys.h"

#define LAPIC ((volatile u32 *)0xFEE00000)
#define LR(off) LAPIC[(off) >> 2]
#define IOAPIC_SEL (*(volatile u32 *)0xFEC00000)
#define IOAPIC_WIN (*(volatile u32 *)0xFEC00010)

static inline u32 ioapic_rd(u32 r) { IOAPIC_SEL = r; return IOAPIC_WIN; }
static inline void ioapic_wr(u32 r, u32 v) { IOAPIC_SEL = r; IOAPIC_WIN = v; }
static inline void ioapic_entry(int pin, u32 lo, u32 hi) {
	ioapic_wr(0x10 + 2 * pin, 0x10000);   /* mask while changing */
	ioapic_wr(0x11 + 2 * pin, hi);
	ioapic_wr(0x10 + 2 * pin, lo);
}
/* WRMSR/RDMSR that may fault: returns the vector (0xFFFF if none) */
static inline int try_wrmsr(u32 n, u64 v) { return TRY(wrmsr(n, v)); }
static inline int try_rdmsr(u32 n, u64 *v) { u64 r = 0; int e = TRY(r = rdmsr(n)); *v = r; return e; }
/* xAPIC IPI: destination (8 bits) and ICR low */
static inline void ipi(u32 dest, u32 lo) { LR(0x310) = dest << 24; LR(0x300) = lo; }
static inline void sti_nops(void) { __asm__ volatile("sti\n nop\n nop\n nop\n nop\n cli" ::: "memory"); }
static inline void cpu_relax(void) { __asm__ volatile("pause" ::: "memory"); }
/* PIT channel 0 one-shot (mode 0): IRQ 0 rises after `count` ticks */
static inline void pit_oneshot(u16 count) { outb(0x43, 0x30); outb(0x40, count & 0xFF); outb(0x40, count >> 8); }

void test_apic_errors(void);
void test_apic_model(void);
void test_ioapic(void);
void test_ioapic_model(void);
void test_x2apic(void);
void test_x2apic_model(void);
void test_smp(void);
void test_smp_model(void);
void test_smpn(u32 n);
#endif
