/* Shared definitions for the system-level test kernel (runs identically on QEMU and the Lean model). */
#ifndef SYS_H
#define SYS_H

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;

/* GDT selectors */
#define KCODE 0x08
#define KDATA 0x10
#define UCODE 0x1B
#define UDATA 0x23
#define TSS_MAIN 0x28
#define GDT_ENTRIES 32

struct frame {
	u32 edi, esi, ebp, esp0, ebx, edx, ecx, eax;
	u32 ds, es, fs, gs;
	u32 vec, err;
	u32 eip, cs, eflags, uesp, uss;
	u32 v86es, v86ds, v86fs, v86gs;
};

struct jmpbuf { u32 ebx, esi, edi, ebp, esp, eip; };
int ksetjmp(struct jmpbuf *);
void klongjmp(struct jmpbuf *, int) __attribute__((noreturn));

struct tss32 {
	u32 link, esp0, ss0, esp1, ss1, esp2, ss2, cr3, eip, eflags;
	u32 eax, ecx, edx, ebx, esp, ebp, esi, edi;
	u32 es, cs, ss, ds, fs, gs, ldt;
	u16 trap, iomap;
};

extern u64 gdt[GDT_ENTRIES];
extern u64 idt[256];
extern struct tss32 tss_main;
extern char isr_base[], isr_noerr[], trap_return[], stack_top[];

/* Last trapped event, filled by the default handler. */
struct event { u32 vec, err, eip, cs, eflags, cr2, dr6, esp; };
extern volatile struct event last;
/* Optional per-test hook: return 1 if the frame was handled (resume with IRET). */
extern int (*trap_hook)(struct frame *);

/* Port I/O and control registers */
static inline void outb(u16 p, u8 v) { __asm__ volatile("outb %0, %1" :: "a"(v), "Nd"(p)); }
static inline u8 inb(u16 p) { u8 v; __asm__ volatile("inb %1, %0" : "=a"(v) : "Nd"(p)); return v; }
static inline void outl(u16 p, u32 v) { __asm__ volatile("outl %0, %1" :: "a"(v), "Nd"(p)); }
#define RDCR(n) ({ u32 _v; __asm__ volatile("mov %%cr" #n ", %0" : "=r"(_v)); _v; })
#define WRCR(n, v) __asm__ volatile("mov %0, %%cr" #n :: "r"((u32)(v)) : "memory")
#define RDDR(n) ({ u32 _v; __asm__ volatile("mov %%db" #n ", %0" : "=r"(_v)); _v; })
#define WRDR(n, v) __asm__ volatile("mov %0, %%db" #n :: "r"((u32)(v)) : "memory")
static inline u64 rdmsr(u32 n) { u32 lo, hi; __asm__ volatile("rdmsr" : "=a"(lo), "=d"(hi) : "c"(n)); return ((u64)hi << 32) | lo; }
static inline void wrmsr(u32 n, u64 v) { __asm__ volatile("wrmsr" :: "c"(n), "a"((u32)v), "d"((u32)(v >> 32))); }
static inline u32 rdflags(void) { u32 f; __asm__ volatile("pushfl; popl %0" : "=r"(f)); return f; }
static inline void invlpg(u32 a) { __asm__ volatile("invlpg (%0)" :: "r"(a) : "memory"); }
static inline void ltr(u16 s) { __asm__ volatile("ltr %0" :: "r"(s)); }

/* Output */
void kputc(char c);
void kputs(const char *s);
void puthex(u32 v);
void putdec(u32 v);
/* "name: k1=v1 k2=v2" lines via a tiny formatter: %x (8 hex digits), %s, %d */
void kprintf(const char *fmt, ...);

/* Descriptors */
u64 seg_desc(u32 base, u32 limit, u32 type_dpl_p, u32 flags);   /* type_dpl_p = access byte, flags = G/D nibble */
u64 gate_desc(u16 sel, u32 off, u32 type_dpl_p);                /* access byte: 0x8E int gate, 0x85 task gate ... */
void set_idt(int vec, u32 handler, u32 access);
void reload_tr(u16 sel);

/* Running code that may fault: returns the vector (or 0xFFFF if no event). */
extern struct jmpbuf fault_jb;
extern volatile int fault_armed;
#define TRY(stmt) ({ last.vec = 0xFFFF; int _r; if (ksetjmp(&fault_jb) == 0) { fault_armed = 1; stmt; fault_armed = 0; _r = 0xFFFF; } else { _r = last.vec; } fault_armed = 0; _r; })
void report(const char *what, int vec);

/* Simple bump allocator for page-aligned scratch memory */
void *page_alloc(int n);
void memset(void *p, int v, u32 n);
void memcpy(void *d, const void *s, u32 n);

/* Enter ring 3 at `eip` with the given stack; returns via a fault caught by TRY. */
void enter_ring3(u32 eip, u32 esp, u32 eflags);
/* Run a ring-3 snippet (u_read/u_write/u_call) with EAX/EBX preset; 0x40 = completed. */
int run_user(char *code, u32 eax, u32 ebx);
extern char u_read[], u_write[], u_call[];

/* Fuzzing parameters from the multiboot command line, e.g. "seed=12345 sse=200000" (decimal or 0x hex).
   `fuzz_seed(dflt)` is the generator seed of a fuzzer: its fixed default unless seed= is given, then a
   value derived from seed= and the fuzzer's default (so fuzzers stay independent). */
u32 param(const char *key, u32 dflt);
u32 fuzz_seed(u32 dflt);

/* Test groups */
void test_paging(void);
void test_pae(void);
void test_debug(void);
void test_task(void);
void test_task_trap(void);
void test_callgate(void);
void test_vm86(void);
void test_apic(void);
void test_smm(void);
void test_x87(void);
void test_x87_env(void);
void test_x87_model(void);
void test_x87_trans(void);
void test_x87_trans_model(void);
void test_simd(void);
void test_simd_exc(void);
void test_simd_model(void);
void test_paging_fuzz(void);
void test_debug_fuzz(void);
void test_debug_fuzz_model(void);
void test_paging_fuzz_model(void);
void test_tsf(void);
void test_cgf(void);
void test_xfer_model(void);

#endif
