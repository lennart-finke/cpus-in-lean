/* Randomized control transfers compared with QEMU: hardware task switches (tsf=N) and call gates / far
   transfers (cgf=N).

   Every exception of interest (#DB, #UD, #DF, #TS, #NP, #SS, #GP) and the end of every case (INT 0x5F) go
   through IDT task gates to "recovery" tasks. The outcome is therefore observed from a clean task whatever
   state the transfer under test left behind: TCG raises a fault after the task-switch commit point with
   the old task's EIP and with inconsistent flags (only the vector, error code and faulting task are
   compared), and the inner stacks in the TSS are random. The recovery task records the event (vector,
   error code, the task it interrupted = its TSS link field) and either ends the case (longjmp to the
   kernel) or resumes the interrupted task (IRET).

   The fuzz runs on a private GDT (xgdt, 128 entries) so that selectors beyond the table limit are easy to
   form. Descriptors are created with the accessed bit set: TCG does not set it on far JMP or task-switch
   segment loads (see qemu-deviations.txt). */
#include "sys.h"

#define STR_(x) #x
#define STR(x) STR_(x)

#define NGDT 128
#define S(i) ((i) << 3)
#define I_BACK 32      /* task gate (DPL 3) to TSS_MAIN: how tasks return to the kernel */
#define I_REC 33       /* 33..41: recovery tasks */
#define NREC 9
#define I_NEW 42       /* the new task's TSS */
#define I_ALT 43       /* another valid task (random busy bit) */
#define I_GATE 44      /* task gate in the GDT */
#define I_LDT 45       /* LDT descriptor: xldt */
#define I_LDTNP 46     /* the same, not present */
#define I_LDTBAD 47    /* a data descriptor */
#define I_RND 48       /* 48..55: random descriptors */
#define NRND 8
#define I_DATA 56      /* flat writable data, DPL 0..3 */
#define I_DATA16 60    /* writable data, limit 0xFFFF, B = 0, DPL 0..3 */
#define I_CODE 64      /* flat readable 32-bit code, DPL 0..3 */
#define I_TCODE 68     /* task code (based at tsf_code), 32-bit, DPL 0..3 */
#define I_TCODE16 72   /* task code (based at tsf_code16), 16-bit, DPL 0..3 */
#define I_DATARO 76    /* flat read-only data, DPL 0..3 */
#define I_CONF 80      /* flat readable conforming code, DPL 0..3 */
#define I_CG 84        /* call gate */
#define I_TGT 85       /* call-gate / far target code */
#define I_SSNP 88      /* 88..91: not-present writable data, DPL 0..3: used only as SS (deviation rules) */
#define I_DNP 92       /* 92..95: not-present writable data, DPL 0..3: data segment registers */
#define I_TCONF 96     /* task code, conforming, DPL 0..3 */
#define LDT_GATE 4     /* xldt[4]: task gate */
#define LDT_TSS 5      /* xldt[5]: TSS descriptor (selector 0x2C: TSS descriptors in an LDT) */
#define VEC_INT 0x5B   /* INT n source through an IDT task gate */
#define V86_CODE 0x7000
#define LOW_STUBS 0x7100 /* copy of xs_jmp..xs_fret: 16-bit returns (truncated EIP) land there */
#define LOW(sym) (LOW_STUBS + (u32)((sym) - xs_jmp))

/* recovery tasks: vector, error code (asm pushes 0 for vectors without one) */
#define RECN(k, v) ".globl xrec" #k "\nxrec" #k ": pushl $0\n pushl $" #v "\n call xrec_c\n addl $8, %esp\n iret\n jmp xrec" #k "\n"
#define RECE(k, v) ".globl xrec" #k "\nxrec" #k ": pushl $" #v "\n call xrec_c\n addl $8, %esp\n iret\n jmp xrec" #k "\n"
__asm__(
	RECN(0, 1) RECN(1, 6) RECE(2, 8) RECE(3, 10) RECE(4, 11) RECE(5, 12) RECE(6, 13) RECN(7, 0x5E) RECN(8, 0x5F)
	/* the new task: UD2 (observed by the #UD recovery task, which then resumes it at offset 2 if NT is
	   set, else at offset 3), IRET back, or JMP back through the DPL-3 task gate */
	".globl tsf_code\ntsf_code: ud2\n iret\n ljmp $" STR(S(I_BACK)) ", $0\n"
	".code16\n.globl tsf_code16\ntsf_code16: ud2\n iret\n ljmp $" STR(S(I_BACK)) ", $0\n.code32\n"
	/* sources: the far pointer is read through CS (all code segments here are readable) */
	".globl xs_jmp\nxs_jmp: ljmp *%cs:xfar\n int $0x5F\n"
	".globl xs_call\nxs_call: lcall *%cs:xfar\n int $0x5F\n"
	".globl xs_int\nxs_int: int $" STR(VEC_INT) "\n int $0x5F\n"
	".globl xs_iret\nxs_iret: pushfl\n orl $0x4000, (%esp)\n popfl\n iret\n int $0x5F\n"
	".globl xs_done\nxs_done: int $0x5F\n"
	".globl xs_fret\nxs_fret: lret $0\n"
	".globl xs_fretw\nxs_fretw: .byte 0x66\n lret $0\n"
	/* enter the case's main task state xent = {eip, cs, esp, ss, ds, es, fs, gs, eflags}: by a far
	   return at ring 0, by IRET to an outer ring */
	".globl xenter\nxenter:\n"
	" movl xent+20, %eax\n movw %ax, %es\n movl xent+24, %eax\n movw %ax, %fs\n movl xent+28, %eax\n movw %ax, %gs\n"
	" movl xent+4, %ecx\n movl xent+16, %esi\n testl $3, %ecx\n jnz 1f\n"
	" movl xent+0, %eax\n movl xent+8, %edx\n movl xent+12, %ebx\n movw %bx, %ss\n movl %edx, %esp\n"
	" pushl %ecx\n pushl %eax\n movw %si, %ds\n lret\n"
	"1: movl $0x5F00, %esp\n pushl xent+12\n pushl xent+8\n pushl xent+32\n pushl %ecx\n pushl xent+0\n movw %si, %ds\n iret\n");
extern char xrec0[], xrec1[], xrec2[], xrec3[], xrec4[], xrec5[], xrec6[], xrec7[], xrec8[];
extern char tsf_code[], tsf_code16[], xs_jmp[], xs_call[], xs_int[], xs_iret[], xs_done[], xs_fret[], xs_fretw[];
extern void xenter(void) __attribute__((noreturn));

/* call-gate targets: record ESP, SS, CS and the top of the stack, load DS/ES/FS chosen for the new
   privilege level, then RETF imm (patched), with the natural or the other operand size; or end (JMP) */
#define CG_BODY \
	"movl $cgf_rec, %ebx\n movl %esp, %gs:0(%ebx)\n movw %ss, %gs:4(%ebx)\n movw %cs, %gs:8(%ebx)\n" \
	"movl %gs:12(%ebx), %ecx\n xorl %esi, %esi\n" \
	"1: movl %ss:(%esp,%esi,4), %eax\n movl %eax, %gs:24(%ebx,%esi,4)\n incl %esi\n cmpl %ecx, %esi\n jb 1b\n" \
	"movw %gs:16(%ebx), %ds\n movw %gs:18(%ebx), %es\n movw %gs:20(%ebx), %fs\n"
__asm__(
	".globl cgf_t32\ncgf_t32:\n"
	".globl cgf_t32a\ncgf_t32a: " CG_BODY ".globl cgf_r32a\ncgf_r32a: lret $0\n"
	".globl cgf_t32b\ncgf_t32b: " CG_BODY ".byte 0x66\n.globl cgf_r32b\ncgf_r32b: lret $0\n"
	".globl cgf_t32c\ncgf_t32c: " CG_BODY "int $0x5F\n"
	".globl cgf_t32d\ncgf_t32d: int $0x5F\n"
	".globl cgf_t32e\ncgf_t32e:\n"
	".code16\n.globl cgf_t16\ncgf_t16:\n"
	".globl cgf_t16a\ncgf_t16a: " CG_BODY ".globl cgf_r16a\ncgf_r16a: lret $0\n"
	".globl cgf_t16b\ncgf_t16b: " CG_BODY ".byte 0x66\n.globl cgf_r16b\ncgf_r16b: lret $0\n"
	".globl cgf_t16c\ncgf_t16c: " CG_BODY "int $0x5F\n"
	".globl cgf_t16d\ncgf_t16d: int $0x5F\n"
	".globl cgf_t16e\ncgf_t16e:\n"
	".code32\n");
extern char cgf_t32[], cgf_t32a[], cgf_t32b[], cgf_t32c[], cgf_t32d[], cgf_t32e[], cgf_r32a[], cgf_r32b[];
extern char cgf_t16[], cgf_t16a[], cgf_t16b[], cgf_t16c[], cgf_t16d[], cgf_t16e[], cgf_r16a[], cgf_r16b[];

struct cgrec { u32 esp, ss, cs, nfr; u16 ld[4]; u32 frame[40]; };
volatile struct cgrec cgf_rec;
struct { u32 off; u16 sel; } __attribute__((packed)) xfar;
struct { u32 eip, cs, esp, ss, ds, es, fs, gs, eflags; } xent;

static u64 xgdt[NGDT] __attribute__((aligned(8)));
static u64 xldt[8] __attribute__((aligned(8)));
static struct tss32 rtss[NREC] __attribute__((aligned(128)));
static u8 rstack[NREC][1024] __attribute__((aligned(16)));
static u8 tnew[0x200] __attribute__((aligned(256)));
static struct tss32 talt __attribute__((aligned(128)));
static u8 mstack[4096] __attribute__((aligned(16)));
static u8 istack[3][1024] __attribute__((aligned(16)));
static const u32 rv[NREC] = { 1, 6, 8, 10, 11, 12, 13, 0x5E, 0x5F };
static char *const rentry[NREC] = { xrec0, xrec1, xrec2, xrec3, xrec4, xrec5, xrec6, xrec7, xrec8 };
static u64 idt_saved[NREC], idt_int_saved;

struct tss16 { u16 link, sp0, ss0, sp1, ss1, sp2, ss2, ip, flags, ax, cx, dx, bx, sp, bp, si, di, es, cs, ss, ds, ldt; };

/* ---- output helpers ---- */
static void h4(u32 v) { for (int i = 12; i >= 0; i -= 4) kputc("0123456789abcdef"[(v >> i) & 15]); }
static void h2(u32 v) { for (int i = 4; i >= 0; i -= 4) kputc("0123456789abcdef"[(v >> i) & 15]); }
static void hx(u32 v) { puthex(v); }
static void kv4(const char *k, u32 v) { kputc(' '); kputs(k); kputc('='); h4(v); }

/* ---- generator ---- */
static u32 xs;
static u32 rc32, rc16;   /* bases of random code descriptors (D = 1, D = 0) */
static u32 rnd(void) { xs ^= xs << 13; xs ^= xs >> 17; xs ^= xs << 5; return xs; }
static u32 rn(u32 n) { return rnd() % n; }
static int pct(u32 p) { return rn(100) < p; }
/* per case: the probability (%) that a field is made invalid, so that many cases are entirely valid */
static u32 bp;
static int bad(void) { return pct(bp); }
static u32 at_least(u32 m) { return m + rn(4 - m); }

static u32 dhi(u16 sel) { return (u32)(xgdt[sel >> 3] >> 32); }
static u32 busy(u16 sel) { return (dhi(sel) >> 9) & 1; }
static void lldt(u16 s) { __asm__ volatile("lldt %0" :: "r"(s)); }

/* ---- events seen by the recovery tasks ---- */
struct ev { u32 vec, err, in, cap, t16, vm, eip, efl, r[8], link; u16 sg[6]; };
#define NEV 6
static struct ev evs[NEV];
static int nev;
static int xmode;           /* 0: tsf (resume a new task after its UD2), 1: cgf */
static struct jmpbuf xjb;
static u32 main_efl;        /* TSS_MAIN's saved EFLAGS at the end of the case */
static u16 main_sg[6];
static u32 main_esp;
/* model-only bookkeeping: a fault in the new task before it executed an instruction (that is, after
   the task-switch commit point) must be delivered with the new task's EIP (SDM 7.3) */
static u32 new_eip, commit_seen, commit_bad;
/* model-only: a fault delivered through a task gate saves EFLAGS with RF set (SDM 17.3.1.1); TCG sets RF
   only in frames pushed for interrupt and trap gates, so the QEMU comparison prints EFLAGS without RF */
static u32 rf_seen, rf_bad;

static u8 *tss_of(u32 sel) {
	sel &= 0xFFF8;
	if (sel == S(I_NEW)) return tnew;
	if (sel == S(I_ALT)) return (u8 *)&talt;
	if (sel == TSS_MAIN) return (u8 *)&tss_main;
	return 0;
}

int xrec_c(u32 vec, u32 err) {
	int k = 0;
	while (rv[k] != vec) k++;
	u32 in = rtss[k].link;
	struct ev *e = &evs[nev < NEV ? nev++ : NEV - 1];
	memset(e, 0, sizeof *e);
	e->vec = vec; e->err = err; e->in = in;
	u8 *t = tss_of(in);
	int t16 = t && !((dhi(in) >> 8) & 8);
	if (xmode == 0 && t && in != TSS_MAIN) {
		/* the state of the interrupted task as saved by the switch to the recovery task */
		e->cap = 1; e->t16 = t16;
		if (t16) {
			struct tss16 *s = (struct tss16 *)t;
			e->eip = s->ip; e->efl = s->flags; e->link = s->link;
			u16 *r = &s->ax;
			for (int j = 0; j < 8; j++) e->r[j] = r[j];
			e->sg[0] = s->es; e->sg[1] = s->cs; e->sg[2] = s->ss; e->sg[3] = s->ds;
		} else {
			struct tss32 *s = (struct tss32 *)t;
			e->eip = s->eip; e->efl = s->eflags; e->link = s->link;
			u32 *r = &s->eax;
			for (int j = 0; j < 8; j++) e->r[j] = r[j];
			e->sg[0] = s->es; e->sg[1] = s->cs; e->sg[2] = s->ss; e->sg[3] = s->ds; e->sg[4] = s->fs; e->sg[5] = s->gs;
			e->vm = (s->eflags >> 17) & 1;
		}
		if (nev == 1 && (in & 0xFFF8) == S(I_NEW) && vec != 6) {
			commit_seen = 1;
			if (e->eip != new_eip) commit_bad++;
		}
		if (vec == 6 && !t16) { rf_seen = 1; if (!(e->efl & 0x10000)) rf_bad++; }
		if (vec == 6 && nev < NEV - 1 && !e->vm) {
			/* resume: IRET back if NT is set, else JMP back through the task gate */
			u32 to = (e->efl >> 14) & 1 ? 2 : 3;
			if (t16) ((struct tss16 *)t)->ip = to;
			else ((struct tss32 *)t)->eip = to;
			return 1;
		}
	}
	if (vec == 0x5E && nev < NEV - 1) return 1;
	if (vec == 0x5F) {
		main_efl = tss_main.eflags; main_esp = tss_main.esp;
		main_sg[0] = tss_main.es; main_sg[1] = tss_main.cs; main_sg[2] = tss_main.ss;
		main_sg[3] = tss_main.ds; main_sg[4] = tss_main.fs; main_sg[5] = tss_main.gs;
	}
	klongjmp(&xjb, 1);
}

static void rec_reset(void) {
	for (int k = 0; k < NREC; k++) {
		struct tss32 *t = &rtss[k];
		memset(t, 0, sizeof *t);
		t->cr3 = RDCR(3); t->eip = (u32)rentry[k]; t->eflags = 2;
		t->esp = (u32)rstack[k] + sizeof rstack[k];
		t->cs = KCODE; t->ss = t->ds = t->es = t->fs = t->gs = KDATA;
		t->iomap = sizeof *t;
		xgdt[I_REC + k] = seg_desc((u32)t, 0x67, 0x89, 0);
	}
}

static void ldt_reset(void) {
	memset(xldt, 0, sizeof xldt);
	xldt[1] = seg_desc((u32)tsf_code, 0xFFF, 0xFB, 0x4);    /* task code, DPL 3 */
	xldt[2] = seg_desc(0, 0xFFFFF, 0xF3, 0xC);              /* data, DPL 3 */
	xldt[3] = seg_desc(0, 0xFFFFF, 0x93, 0xC);              /* data, DPL 0 */
	xldt[6] = seg_desc((u32)tsf_code, 0xFFF, 0x9B, 0x4);    /* task code, DPL 0 */
	xldt[7] = seg_desc(0, 0xFFFF, 0x93, 0x0);               /* 16-bit data, DPL 0 */
}

static u32 tss_saved_ss0, tss_saved_esp0;
static void xsetup(void) {
	tss_saved_ss0 = tss_main.ss0; tss_saved_esp0 = tss_main.esp0;
	for (int i = 0; i < NGDT; i++) xgdt[i] = i < GDT_ENTRIES ? gdt[i] : 0;
	xgdt[I_BACK] = gate_desc(TSS_MAIN, 0, 0xE5);
	for (u32 d = 0; d < 4; d++) {
		xgdt[I_DATA + d] = seg_desc(0, 0xFFFFF, 0x93 | d << 5, 0xC);
		xgdt[I_DATA16 + d] = seg_desc(0, 0xFFFF, 0x93 | d << 5, 0x0);
		xgdt[I_CODE + d] = seg_desc(0, 0xFFFFF, 0x9B | d << 5, 0xC);
		xgdt[I_TCODE + d] = seg_desc((u32)tsf_code, 0xFFF, 0x9B | d << 5, 0x4);
		xgdt[I_TCODE16 + d] = seg_desc((u32)tsf_code16, 0xFFF, 0x9B | d << 5, 0x0);
		xgdt[I_DATARO + d] = seg_desc(0, 0xFFFFF, 0x91 | d << 5, 0xC);
		xgdt[I_CONF + d] = seg_desc(0, 0xFFFFF, 0x9F | d << 5, 0xC);
		xgdt[I_SSNP + d] = seg_desc(0, 0xFFFFF, 0x13 | d << 5, 0xC);
		xgdt[I_DNP + d] = seg_desc(0, 0xFFFFF, 0x13 | d << 5, 0xC);
		xgdt[I_TCONF + d] = seg_desc((u32)tsf_code, 0xFFF, 0x9F | d << 5, 0x4);
	}
	xgdt[I_LDT] = seg_desc((u32)xldt, sizeof xldt - 1, 0x82, 0);
	xgdt[I_LDTNP] = seg_desc((u32)xldt, sizeof xldt - 1, 0x02, 0);
	xgdt[I_LDTBAD] = seg_desc((u32)xldt, sizeof xldt - 1, 0x93, 0);
	rec_reset();
	struct { u16 lim; u32 base; } __attribute__((packed)) gd = { sizeof xgdt - 1, (u32)xgdt };
	__asm__ volatile("lgdt %0" :: "m"(gd));
	for (int k = 0; k < NREC; k++) { idt_saved[k] = idt[rv[k]]; idt[rv[k]] = gate_desc(S(I_REC + k), 0, 0xE5); }
	idt_int_saved = idt[VEC_INT];
	*(volatile u16 *)V86_CODE = 0x0B0F;        /* UD2 for virtual-8086 tasks */
	memcpy((void *)LOW_STUBS, xs_jmp, xs_fret - xs_jmp);
}

static void xteardown(void) {
	/* the cases point the main TSS at their own inner stacks; later ring transitions need the kernel's */
	tss_main.ss0 = tss_saved_ss0; tss_main.esp0 = tss_saved_esp0;
	for (int k = 0; k < NREC; k++) idt[rv[k]] = idt_saved[k];
	idt[VEC_INT] = idt_int_saved;
	struct { u16 lim; u32 base; } __attribute__((packed)) gd = { sizeof gdt - 1, (u32)gdt };
	__asm__ volatile("lgdt %0" :: "m"(gd));
	__asm__ volatile("movl %0, %%ds\n movl %0, %%es\n movl %0, %%fs\n movl %0, %%gs\n movl %0, %%ss" :: "r"((u32)KDATA));
}

/* back to a clean kernel state: no busy TSS but TSS_MAIN, TR = TSS_MAIN, no LDT, CR0.TS clear */
static void xclean(void) {
	for (int i = 6; i < NGDT; i++) {
		u32 hi = (u32)(xgdt[i] >> 32);
		if (!(hi & 0x1000) && ((hi >> 8) & 7) == 3) xgdt[i] &= ~((u64)0x200 << 32);
	}
	xgdt[TSS_MAIN >> 3] &= ~((u64)0x200 << 32);
	ltr(TSS_MAIN);
	lldt(0);
	__asm__ volatile("clts");
	tss_main.link = 0; tss_main.ldt = 0;
}

/* run the prepared case (xent), returns after the recovery task ended it */
static void xrun(void) {
	nev = 0;
	main_efl = 0; main_esp = 0;
	memset(main_sg, 0, sizeof main_sg);
	if (ksetjmp(&xjb) == 0) xenter();
}

static void print_events(void) {
	for (int j = 0; j < nev; j++) {
		struct ev *e = &evs[j];
		kputs(" #"); h2(e->vec);
		if (e->vec == 8 || (e->vec >= 10 && e->vec <= 13)) { kputc('('); h4(e->err); kputc(')'); }
		kputc('@'); h4(e->in);
		if (e->cap && e->vec == 6) {
			kputc('[');
			for (int r = 0; r < 8; r++) { hx(e->r[r]); kputc(' '); }
			kputs("efl="); hx(e->efl & ~0x10000u);
			kputs(" eip="); hx(e->eip);
			for (int s = 0; s < 6; s++) { kputc(' '); h4(e->sg[s]); }
			kputs(" link="); h4(e->link);
			kputc(']');
		}
	}
}

/* ===================== hardware task switches ===================== */

static int is_conf_code(u16 sel) {
	if (sel & 4) return 0;
	if ((sel >> 3) >= NGDT) return 0;
	u32 hi = dhi(sel);
	return (hi & 0x1C00) == 0x1C00;
}

static void rnd_desc(int i) {
	u32 dpl = rn(4), p = pct(80) ? 0x80 : 0, k = rn(12);
	u32 base = 0, lim = 0xFFFFF, fl = 0xC, acc;
	if (k < 4) {
		acc = 0x11 | (rn(2) << 1) | (pct(15) << 2);       /* data: W, expand-down */
		/* a not-present writable data segment as SS is #SS, where TCG raises #NP or #TS: such
		   stack segments come only from I_SSNP, which the deviation rules recognize */
		if (acc & 2) p = 0x80;
		if (rn(2)) fl = 0x8;
	} else if (k < 7) {
		acc = 0x19 | (rn(2) << 1) | (rn(2) << 2);         /* code: R, C */
		int d = rn(2);
		base = d ? rc32 : rc16; fl = d ? 0x4 : 0;
		lim = xmode == 0 && pct(30) ? rn(4) : 0xFFF;
	} else {
		static const u8 sys[] = { 0x2, 0x9, 0xB, 0x1, 0x3, 0x5, 0xC, 0xE, 0x0, 0x8, 0xA, 0xD };
		acc = sys[rn(sizeof sys)];
		base = acc == 2 ? (u32)xldt : (u32)&talt; lim = acc == 2 ? 63 : 0x67; fl = 0;
	}
	xgdt[I_RND + i] = seg_desc(base, lim, p | dpl << 5 | acc, fl);
}

static u16 beyond(void) { return S(NGDT + rn(64)); }

static u16 pick_cs(u32 cpl, int t16) {
	u16 s;
	if (!bad()) return pct(90) ? S((t16 ? I_TCODE16 : I_TCODE) + cpl) | cpl : S(I_TCONF + cpl) | cpl;
	switch (rn(10)) {
	case 0: s = rn(4); break;
	case 1: s = S(I_TCODE + rn(4)) | rn(4); break;
	case 2: s = S(I_DATA + cpl) | cpl; break;
	case 3: s = beyond() | cpl; break;
	case 4: case 5: s = S(I_RND + rn(NRND)) | rn(4); break;
	case 6: s = (cpl == 3 ? 1 << 3 : 6 << 3) | 4 | rn(4); break;  /* LDT code */
	case 7: s = S(I_LDT) | cpl; break;
	case 8: s = S(I_TCONF + cpl) | cpl; break;
	default: s = S((t16 ? I_TCODE : I_TCODE16) + cpl) | cpl; break;
	}
	/* TCG requires DPL = RPL for a conforming CS too (SDM: DPL <= RPL): not compared with QEMU */
	if (is_conf_code(s) && ((dhi(s) >> 13) & 3) != (s & 3u)) s = S(I_TCODE + cpl) | cpl;
	return s;
}

static u16 pick_ss(u32 cpl) {
	if (!bad()) return S((pct(75) ? I_DATA : I_DATA16) + cpl) | cpl;
	switch (rn(10)) {
	case 0: return rn(4);
	case 1: return S(I_SSNP + cpl) | cpl;
	case 2: return S(I_DATA + rn(4)) | rn(4);
	case 3: return S(I_DATARO + cpl) | cpl;
	case 4: return S(I_TCODE + cpl) | cpl;
	case 5: return beyond() | cpl;
	case 6: return S(I_RND + rn(NRND)) | cpl;
	case 7: return (cpl == 3 ? 2 << 3 : 3 << 3) | 4 | cpl;
	case 8: return S(I_LDT) | cpl;
	default: return S(I_DATA16 + rn(4)) | cpl;
	}
}

static u16 pick_data(u32 cpl) {
	u32 k = rn(100), d = at_least(cpl);
	if (!bad()) {
		if (k < 50) return S(I_DATA + d) | rn(d + 1);
		if (k < 70) return rn(4);
		if (k < 80) return S(I_CONF + rn(4)) | rn(4);
		if (k < 90) return S(I_CODE + d) | rn(d + 1);
		return S(I_DATA16 + d) | rn(d + 1);
	}
	switch (rn(8)) {
	case 0: return S(I_DATA + rn(4)) | rn(4);
	case 1: return S(I_DNP + rn(4)) | rn(4);
	case 2: return beyond() | rn(4);
	case 3: case 4: return S(I_RND + rn(NRND)) | rn(4);
	case 5: return (rn(10) << 3) | 4 | rn(4);
	case 6: return S(I_DATARO + rn(4)) | rn(4);
	default: return S(I_BACK) | rn(4);
	}
}

static u16 pick_ldt(void) {
	if (!bad()) return pct(60) ? rn(4) : S(I_LDT) | rn(4);
	switch (rn(6)) {
	case 0: return S(I_LDTNP);
	case 1: return S(I_LDTBAD);
	case 2: return S(I_LDT) | 4;
	case 3: return beyond();
	case 4: return S(I_DATA);
	default: return 4 | rn(4);
	}
}

/* previous-task link of the new task (used when it IRETs with NT set but was not nested) */
static u16 pick_link(void) {
	switch (rn(8)) {
	case 0: case 1: case 2: return TSS_MAIN;
	case 3: case 4: return S(I_ALT);
	case 5: return rn(4);
	case 6: return S(I_NEW);
	default: return pct(50) ? beyond() : (pct(50) ? S(I_DATA) : (1 << 3) | 4);
	}
}

static void mk_alt(void) {
	memset(&talt, 0, sizeof talt);
	talt.cr3 = RDCR(3); talt.eip = 0; talt.eflags = 2; talt.esp = 0x1234;
	talt.cs = S(I_TCODE); talt.ss = talt.ds = talt.es = talt.fs = talt.gs = S(I_DATA);
	talt.link = TSS_MAIN; talt.iomap = sizeof talt;
	xgdt[I_ALT] = seg_desc((u32)&talt, 0x67, pct(50) ? 0x8B : 0x89, 0);
}

static const char *const tsf_src[] = { "jmp", "call", "jmpg", "callg", "int", "iret" };

static void tsf_case(u32 i) {
	xmode = 0;
	rec_reset(); ldt_reset(); mk_alt();
	for (int k = 0; k < NRND; k++) rnd_desc(k);

	bp = pct(40) ? 0 : pct(60) ? 6 : 25;
	u32 src = rn(6), ring = pct(60) ? 0 : 3;
	int t16 = pct(20), vm = !t16 && pct(6);
	u32 rpl = rn(4);
	u32 dpl = bad() ? rn(4) : at_least(ring > rpl ? ring : rpl);
	u32 present = !bad(), bsy = (src == 5) != bad();
	u32 min = t16 ? 0x2B : 0x67;
	u32 lim = bad() ? min - 1 - rn(4) : pct(50) ? min : min + rn(0x100);
	u32 type = (t16 ? 1 : 9) | (bsy ? 2 : 0);
	xgdt[I_NEW] = seg_desc((u32)tnew, lim, (present ? 0x80 : 0) | dpl << 5 | type, 0);
	xldt[LDT_TSS] = seg_desc((u32)tnew, lim, 0x80 | dpl << 5 | type, 0);

	/* the new task */
	u32 cpl = vm ? 3 : (pct(40) ? 0 : pct(67) ? 3 : 1 + rn(2));
	u32 efl = 2 | (rnd() & (0x0CD5 | 0x0200 | 0x3000 | 0x10000 | 0x40000 | 0x200000)) | (pct(25) ? 0x4000 : 0);
	int nested = src == 1 || src == 3 || src == 4;
	u32 eip = 0, k = rn(100);
	if (k >= 80 && k < 85 && (nested || (efl & 0x4000))) eip = 2;
	else if (k >= 85 && k < 90) eip = 3;
	if (bad()) eip = vm ? 0x10000 + rn(16) : pct(50) ? 0x1000 + rn(0x100) : 0xFFFFFFF0 + rn(16);
	u16 cs, ss, ds, es, fs, gs, ldt = pick_ldt(), link = pick_link();
	if (vm) {
		cs = V86_CODE >> 4; ss = rnd(); ds = rnd(); es = rnd(); fs = rnd(); gs = rnd();
		if (eip == 2 || eip == 3) eip = 0;
		efl |= 0x20000;
	} else {
		cs = pick_cs(cpl, t16); ss = pick_ss(cpl);
		ds = pick_data(cpl); es = pick_data(cpl); fs = pick_data(cpl); gs = pick_data(cpl);
	}
	memset(tnew, 0, sizeof tnew);
	u32 regs[8];
	for (int r = 0; r < 8; r++) regs[r] = rnd();
	if (t16) {
		struct tss16 *t = (struct tss16 *)tnew;
		t->link = link; t->ip = eip; t->flags = efl; t->ldt = ldt;
		u16 *r = &t->ax;
		for (int j = 0; j < 8; j++) r[j] = regs[j];
		t->es = es; t->cs = cs; t->ss = ss; t->ds = ds;
		t->ss0 = KDATA; t->sp0 = 0x4F00;
		fs = gs = 0;
		eip &= 0xFFFF; efl &= 0xFFFF;
	} else {
		struct tss32 *t = (struct tss32 *)tnew;
		t->link = link; t->cr3 = RDCR(3); t->eip = eip; t->eflags = efl; t->ldt = ldt;
		u32 *r = &t->eax;
		for (int j = 0; j < 8; j++) r[j] = regs[j];
		t->es = es; t->cs = cs; t->ss = ss; t->ds = ds; t->fs = fs; t->gs = gs;
		t->ss0 = KDATA; t->esp0 = 0x4F00; t->iomap = 0x68;
	}
	new_eip = eip;

	/* the transfer */
	u16 sel = S(I_NEW) | rpl, gsel = 0, tsel = 0;
	u32 gdpl = 0, gp = 0;
	if (src == 0 || src == 1) {
		u32 v = rn(100);
		if (!bad()) {}
		else if (v < 40) sel = S(I_ALT) | rpl;
		else if (v < 80) sel = (LDT_TSS << 3) | 4 | rpl;
		else sel = beyond() | rpl;
	} else if (src >= 2 && src <= 4) {
		gdpl = bad() ? rn(4) : at_least(src == 4 ? ring : ring > rpl ? ring : rpl);
		gp = !bad();
		u32 v = rn(100);
		tsel = !bad() ? S(I_NEW) : v < 25 ? (LDT_TSS << 3) | 4 : v < 40 ? rn(4) : v < 55 ? beyond()
		     : v < 75 ? S(I_ALT) : v < 90 ? S(I_DATA) : S(I_GATE);
		tsel |= rn(4);
		u64 g = gate_desc(tsel, rnd(), (gp ? 0x80 : 0) | gdpl << 5 | 0x05);
		if (src == 4) idt[VEC_INT] = g;
		else if (pct(80)) { xgdt[I_GATE] = g; gsel = S(I_GATE) | rpl; }
		else { xldt[LDT_GATE] = g; gsel = (LDT_GATE << 3) | 4 | rpl; }
		sel = gsel;
	} else {
		u32 v = rn(100);
		tss_main.link = !bad() ? S(I_NEW) : v < 20 ? rn(4) : v < 40 ? S(I_ALT) : v < 60 ? S(I_DATA)
		              : v < 80 ? beyond() : (1 << 3) | 4;
		sel = tss_main.link;
	}
	xfar.off = rnd(); xfar.sel = sel;
	u32 mldt = pct(30);
	tss_main.ldt = mldt ? S(I_LDT) : 0;
	lldt(tss_main.ldt);

	static char *const code[] = { xs_jmp, xs_call, xs_jmp, xs_call, xs_int, xs_iret };
	xent.eip = (u32)code[src];
	if (ring == 0) {
		xent.cs = KCODE; xent.ss = KDATA; xent.esp = (u32)mstack + sizeof mstack;
		xent.ds = xent.es = xent.fs = xent.gs = KDATA;
	} else {
		xent.cs = S(I_CODE + 3) | 3; xent.ss = S(I_DATA + 3) | 3; xent.esp = (u32)mstack + sizeof mstack - 256;
		xent.ds = xent.es = xent.fs = xent.gs = S(I_DATA + 3) | 3;
	}
	xent.eflags = 2;
	xrun();

	u32 bm = busy(TSS_MAIN), bn = busy(S(I_NEW)), ba = busy(S(I_ALT));
	u32 nlink = *(u16 *)tnew, ts = (RDCR(0) >> 3) & 1;
	xclean();

	kprintf("tsf %d %s r%d", i, tsf_src[src], ring);
	kv4("sel", sel);
	if (src >= 2 && src <= 4) { kv4("tss", tsel); kprintf(" g=d%dp%d", gdpl, gp); }
	kprintf(" t%d d%d p%d b%d", t16 ? 16 : 32, dpl, present, bsy);
	kv4("lim", lim);
	kprintf(" eip=%x efl=%x", eip, efl);
	kv4("cs", cs); kv4("ss", ss); kv4("ds", ds); kv4("es", es); kv4("fs", fs); kv4("gs", gs);
	kv4("ldt", ldt); kv4("link", link);
	kprintf(" mldt=%d ->", mldt);
	print_events();
	kprintf(" | b=%d%d%d", bm, bn, ba);
	kv4("link", nlink);
	kprintf(" nt=%d ts=%d\n", evs[nev - 1].vec == 0x5F ? (main_efl >> 14) & 1 : 9, ts);
}

void test_tsf(void) {
	xs = fuzz_seed(0x7A5C0DE1);
	xmode = 0; rc32 = (u32)tsf_code; rc16 = (u32)tsf_code16;
	u32 n = param("tsf", 300);
	xsetup();
	for (u32 i = 0; i < n; i++) tsf_case(i);
	xteardown();
}

/* ===================== call gates and far transfers ===================== */

static u16 pick_data_at(u32 cpl, int fsgs) {
	u32 k = rn(100), d = cpl + rn(4 - cpl);
	if (k < 50) return S(I_DATA + d) | rn(d + 1);
	if (k < 65) return fsgs ? 0 : rn(4);   /* TCG keeps null FS/GS with RPL > 0 on returns to outer levels */
	if (k < 75) return S(I_CONF + rn(4)) | rn(4);
	if (k < 85) return S(I_CODE + d) | rn(d + 1);
	return S(I_DATA16 + d) | rn(d + 1);
}

/* any segment that can be loaded at CPL 0 (for returns that null some of them) */
static u16 pick_data_any(int fsgs) {
	u32 k = rn(100), d = rn(4);
	if (k < 50) return S(I_DATA + d) | rn(d + 1);
	if (k < 65) return fsgs ? 0 : rn(4);
	if (k < 75) return S(I_CONF + d) | rn(4);
	if (k < 90) return S(I_CODE + d) | rn(d + 1);
	return S(I_DATA16 + d) | rn(d + 1);
}

static u32 ring_pick(void) { u32 k = rn(100); return k < 30 ? 0 : k < 70 ? 3 : 1 + (k & 1); }

static void stack_fill(u32 lo, u32 n) { for (u32 a = lo; a < lo + n; a += 4) *(volatile u32 *)a = rnd(); }

static void print_rec(u32 gsz, u32 nent) {
	kv4("cs", cgf_rec.cs & ~3u); kprintf(" rpl=%d", cgf_rec.cs & 3); kv4("ss", cgf_rec.ss);
	kprintf(" esp=%x [", cgf_rec.esp);
	for (u32 j = 0; j < nent; j++) {
		if (j) kputc(' ');
		if (gsz == 4) hx(cgf_rec.frame[j]);
		else h4(((volatile u16 *)cgf_rec.frame)[j]);
	}
	kputc(']');
}

static void print_main(void) {
	kv4("cs", main_sg[1]); kv4("ss", main_sg[2]);
	kprintf(" esp=%x", main_esp);
	kv4("ds", main_sg[3]); kv4("es", main_sg[0]); kv4("fs", main_sg[4]); kv4("gs", main_sg[5]);
}

/* a far CALL or JMP, direct or through a call gate, from ring 0..3 */
static void cgf_gate(u32 i) {
	bp = pct(40) ? 0 : pct(60) ? 6 : 25;
	u32 ring = ring_pick(), call = pct(75), viagate = pct(80);
	/* the gate */
	u32 g32 = pct(70), pc = pct(30) ? rn(32) : rn(4);
	u32 rpl = viagate || bad() ? rn(4) : rn(ring + 1);
	u32 gdpl = bad() ? rn(4) : at_least(ring > rpl ? ring : rpl), gpres = !bad();
	u32 gsz = viagate ? (g32 ? 4 : 2) : 4;
	/* the target: usually I_TGT (based at the target code), else another descriptor */
	u32 tp = !bad(), small = bad();
	/* TCG: JMP through a call gate to a not-present segment raises #GP, not #NP (SDM JMP) */
	if (viagate && !call) tp = 1;
	u32 td0 = pct(75), tconf0 = pct(25);
	u32 tdpl0 = bad() ? rn(4) : (viagate && call) || tconf0 ? rn(ring + 1) : ring;
	xgdt[I_TGT] = seg_desc(td0 ? (u32)cgf_t32 : (u32)cgf_t16, 0xFFF,
	                       (tp ? 0x80 : 0) | tdpl0 << 5 | 0x1B | (tconf0 ? 4 : 0), td0 ? 0x4 : 0x0);
	for (int k = 0; k < NRND; k++) rnd_desc(k);
	u16 tsel = S(I_TGT) | rn(4);
	if (viagate && bad()) {
		switch (rn(7)) {
		case 0: tsel = rn(4); break;
		case 1: tsel = S(I_DATA + rn(4)) | rn(4); break;
		case 2: tsel = beyond() | rn(4); break;
		case 3: tsel = S(I_CONF + rn(4)) | rn(4); break;
		case 4: tsel = S(I_RND + rn(NRND)) | rn(4); break;
		case 5: tsel = S(I_CG); break;
		default: tsel = S(I_CODE + rn(4)) | rn(4); break;
		}
	}
	u32 thi = (tsel >> 3) < NGDT && (tsel & 0xFFF8) ? dhi(tsel) : 0;
	if (viagate && !call && (thi & 0x1800) == 0x1800 && !(thi & 0x8000)) {   /* see tp above */
		xgdt[tsel >> 3] |= (u64)0x8000 << 32;
		thi = dhi(tsel);
	}
	u32 tcode = (thi & 0x1800) == 0x1800, td = (thi >> 22) & 1, tconf = (thi >> 10) & 1, tdpl = (thi >> 13) & 3;
	u32 tbase = (u32)(xgdt[tsel >> 3] >> 16 & 0xFFFFFF) | (thi & 0xFF000000);
	if (!tcode) td = 1, tbase = (u32)cgf_t32;
	u32 bias = td && tbase == 0 ? (u32)cgf_t32 : 0;     /* flat code */
	/* a 16-bit gate cannot hold the offset of the target code in a flat segment */
	if (bias && !g32) { g32 = 1; gsz = 4; }
	u32 eoff;
	if (!call) eoff = td ? (u32)(cgf_t32c - cgf_t32) : (u32)(cgf_t16c - cgf_t16);
	else if (td == (gsz == 4)) eoff = td ? (u32)(cgf_t32a - cgf_t32) : (u32)(cgf_t16a - cgf_t16);
	else eoff = td ? (u32)(cgf_t32b - cgf_t32) : (u32)(cgf_t16b - cgf_t16);
	eoff += bias;
	/* TCG does not check the offset of a far CALL against the limit (through a gate) or reports the
	   selector (direct): only far JMPs go beyond the limit */
	u32 tlim = 0xFFF;
	if (small && !call && (tsel & 0xFFF8) == S(I_TGT)) {
		tlim = eoff - 1 - rn(eoff);
		xgdt[I_TGT] = (xgdt[I_TGT] & ~0x000F00000000FFFFull) | (tlim & 0xFFFF) | ((u64)(tlim & 0xF0000) << 32);
	}
	u64 g = gate_desc(tsel, eoff, (gpres ? 0x80 : 0) | gdpl << 5 | (g32 ? 0xC : 0x4)) | ((u64)pc << 32);
	xgdt[I_CG] = g;
	u16 sel = viagate ? S(I_CG) | rpl : S(I_TGT) | rpl;
	xfar.sel = sel; xfar.off = viagate ? rnd() : eoff;

	/* inner stacks in the TSS */
	u16 iss[3]; u32 iesp[3], i16[3];
	for (u32 n = 0; n < 3; n++) {
		i16[n] = pct(25);
		u32 v = rn(100);
		iss[n] = S((i16[n] ? I_DATA16 : I_DATA) + n) | n;
		if (bad()) {
			switch (v % 9) {
			case 0: iss[n] = rn(4); break;
			case 1: iss[n] = S(I_SSNP + n) | n; break;
			case 2: iss[n] = S(I_DATA + rn(4)) | rn(4); break;
			case 3: iss[n] = S(I_DATARO + n) | n; break;
			case 4: iss[n] = S(I_CODE + n) | n; break;
			case 5: iss[n] = beyond() | n; break;
			case 6: iss[n] = S(I_RND + rn(NRND)) | n; break;
			case 7: iss[n] = S(I_DATA16 + rn(4)) | n; break;
			default: iss[n] = S(I_TGT) | n; break;
			}
		}
		/* a 16-bit inner stack gets ESP < 0x10000: TCG keeps the caller's ESP[31:16] where the SDM loads
		   ESP from the TSS (model-only: xfer.callg.esp16) */
		if ((iss[n] >> 3) < NGDT && (iss[n] & 0xFFF8) && (dhi(iss[n]) & 0x1800) == 0x1000 && !(dhi(iss[n]) & 0x400000))
			i16[n] = 1;
		/* room for the largest frame (16 + 31 * 4 bytes) */
		iesp[n] = i16[n] ? 0x4200 + n * 0x200 - rn(64) : (u32)istack[n] + sizeof istack[n] - rn(64);
		if (pct(10)) iesp[n] &= ~1u; else iesp[n] &= ~3u;
		stack_fill((iesp[n] & ~3u) - 256, 256);
	}
	tss_main.ss0 = iss[0]; tss_main.esp0 = iesp[0];
	tss_main.ss1 = iss[1]; tss_main.esp1 = iesp[1];
	tss_main.ss2 = iss[2]; tss_main.esp2 = iesp[2];

	/* the caller: its stack holds the parameters */
	u32 c16 = pct(25);
	u32 cesp = 0x5800 - rn(16) * 4 - (pct(10) ? 2 : 0);
	stack_fill(0x5700, 0x200);
	xent.eip = call ? LOW(xs_call) : LOW(xs_jmp);
	xent.cs = S(I_CODE + ring) | ring;
	xent.ss = S((c16 ? I_DATA16 : I_DATA) + ring) | ring;
	xent.esp = cesp;
	xent.ds = pick_data_at(ring, 0); xent.es = pick_data_at(ring, 0); xent.fs = pick_data_at(ring, 1);
	xent.gs = S(I_DATA + 3) | 3;
	xent.eflags = 2;

	/* what the target loads before returning, and its RETF immediate */
	u32 ncpl = (tcode && !tconf && tdpl < ring && call) ? tdpl : ring;   /* expected */
	memset((void *)&cgf_rec, 0, sizeof cgf_rec);
	cgf_rec.ld[0] = pick_data_at(ncpl, 0); cgf_rec.ld[1] = pick_data_at(ncpl, 0); cgf_rec.ld[2] = pick_data_at(ncpl, 1);
	u32 nent = viagate ? 4 + pc : 2;
	cgf_rec.nfr = (nent * gsz + 3) / 4;
	u32 imm = viagate ? pc * gsz : 0;
	if (pct(15)) imm = rn(8) * gsz;
	if (td) { *(volatile u16 *)(cgf_r32a + 1) = imm; *(volatile u16 *)(cgf_r32b + 1) = imm; }
	else { *(volatile u16 *)(cgf_r16a + 1) = imm; *(volatile u16 *)(cgf_r16b + 1) = imm; }

	xmode = 1;
	rec_reset();
	xrun();
	xclean();
	tss_main.ss0 = KDATA; tss_main.esp0 = 0; tss_main.ss1 = tss_main.esp1 = tss_main.ss2 = tss_main.esp2 = 0;

	kprintf("cgf %d %s r%d", i, call ? (viagate ? "callg" : "call") : (viagate ? "jmpg" : "jmp"), ring);
	kv4("sel", sel);
	if (viagate) { kprintf(" g%d d%d p%d pc=%d", g32 ? 32 : 16, gdpl, gpres, pc); kv4("t", tsel); }
	if (tcode) kprintf(" tgt=d%dc%dp%dD%d", tdpl, tconf, (thi >> 15) & 1, td);
	else kputs(" tgt=-");
	kv4("lim", tlim); kprintf(" off=%x", eoff);
	kv4("ss0", iss[0]); kv4("ss1", iss[1]); kv4("ss2", iss[2]);
	kprintf(" c16=%d esp=%x imm=%d", c16, cesp, imm);
	kv4("ld", cgf_rec.ld[0]); kv4("le", cgf_rec.ld[1]); kv4("lf", cgf_rec.ld[2]);
	kputs(" ->");
	int reached = cgf_rec.cs != 0;
	if (reached) {
		kputs(" in:");
		print_rec(gsz, nent);
	}
	print_events();
	if (nev && evs[nev - 1].vec == 0x5F) { kputs(" back:"); print_main(); }
	kputc('\n');
}

/* a far RET from ring 0 to random CS/SS selectors, with random data segment registers */
static void cgf_ret(u32 i) {
	bp = pct(40) ? 0 : pct(60) ? 6 : 25;
	u32 o32 = pct(75), rpl = pct(10) ? 0 : 1 + rn(3), imm = rn(6) * (o32 ? 4 : 2);
	for (int j = 0; j < NRND; j++) rnd_desc(j);
	u16 csel, ssel;
	u32 off;
	u32 k = rn(100);
	if (!bad() && k < 70) { csel = S(I_CODE + rpl) | rpl; off = LOW(xs_done); }
	else if (!bad() && k < 85) { csel = S(I_CONF + rn(rpl + 1)) | rpl; off = LOW(xs_done); }
	else if (!bad()) { csel = S(I_TGT) | rpl; off = 0; }
	else {
		switch (rn(6)) {
		case 0: csel = rn(4); break;
		case 1: csel = S(I_CODE + rn(4)) | rpl; break;
		case 2: csel = S(I_CONF + rn(4)) | rpl; break;
		case 3: csel = S(I_DATA + rpl) | rpl; break;
		case 4: csel = beyond() | rpl; break;
		default: csel = S(I_RND + rn(NRND)) | rpl; break;
		}
		off = LOW(xs_done);
	}
	/* a 16-bit return can only reach the based target */
	u32 td = pct(50);
	u32 doff = td ? (u32)(cgf_t32d - cgf_t32) : (u32)(cgf_t16d - cgf_t16);
	xgdt[I_TGT] = seg_desc(td ? (u32)cgf_t32 : (u32)cgf_t16, 0xFFF, 0x80 | rpl << 5 | 0x1B, td ? 0x4 : 0);
	if ((csel & 0xFFF8) == S(I_TGT)) off = doff;
	/* TCG does not check the return offset against the limit: based code (the random descriptors)
	   gets the offset of its INT 0x5F */
	if ((csel >> 3) < NGDT && (csel & 0xFFF8) && (dhi(csel) & 0x1800) == 0x1800 && (dhi(csel) & 0xFF0000FF))
		off = (dhi(csel) & 0x400000) ? (u32)(cgf_t32d - cgf_t32) : (u32)(cgf_t16d - cgf_t16);
	u32 s16 = pct(25);
	if (!bad()) ssel = S((s16 ? I_DATA16 : I_DATA) + rpl) | rpl;
	else switch (rn(8)) {
		case 0: ssel = rn(4); break;
		case 1: ssel = S(I_SSNP + rpl) | rpl; break;
		case 2: ssel = S(I_DATA + rn(4)) | rn(4); break;
		case 3: ssel = S(I_DATARO + rpl) | rpl; break;
		case 4: ssel = S(I_CODE + rpl) | rpl; break;
		case 5: ssel = beyond() | rpl; break;
		case 6: ssel = S(I_RND + rn(NRND)) | rpl; break;
		default: ssel = S(I_DATA16 + ((rpl + 1) & 3)) | rpl; break;
	}
	/* the returning code's stack: low (16-bit capable) or high */
	u32 hi = pct(40);
	u32 esp = hi ? (u32)istack[0] + 512 - rn(16) * 4 : 0x4800 - rn(16) * 4;
	u32 ss0 = hi || pct(70) ? KDATA : S(I_DATA16);
	u32 oesp = pct(70) ? 0x5800 - rn(64) * 4 : rnd();
	stack_fill(esp, 64);
	u32 w = o32 ? 4 : 2;
	u8 *f = (u8 *)esp;
	if (o32) { ((u32 *)f)[0] = off; ((u32 *)f)[1] = csel | (rnd() & 0xFFFF0000); }
	else { ((u16 *)f)[0] = off; ((u16 *)f)[1] = csel; }
	if (o32) { *(u32 *)(f + 2 * w + imm) = oesp; *(u32 *)(f + 3 * w + imm) = ssel | (rnd() & 0xFFFF0000); }
	else { *(u16 *)(f + 2 * w + imm) = oesp; *(u16 *)(f + 3 * w + imm) = ssel; }
	*(volatile u16 *)(xs_fret + 1) = imm;
	*(volatile u16 *)(xs_fretw + 2) = imm;
	xent.eip = (u32)(o32 ? xs_fret : xs_fretw);
	xent.cs = KCODE; xent.ss = ss0; xent.esp = esp;
	xent.ds = pick_data_any(0); xent.es = pick_data_any(0); xent.fs = pick_data_any(1); xent.gs = pick_data_any(1);
	xent.eflags = 2;
	xmode = 1;
	rec_reset();
	xrun();
	xclean();

	kprintf("cgf %d ret%d imm=%d", i, o32 ? 32 : 16, imm);
	kv4("cs", csel); kprintf(" off=%x", off); kv4("ss", ssel);
	kprintf(" oesp=%x esp=%x", oesp, esp);
	kv4("ds", xent.ds); kv4("es", xent.es); kv4("fs", xent.fs); kv4("gs", xent.gs);
	kputs(" ->");
	print_events();
	if (nev && evs[nev - 1].vec == 0x5F) { kputs(" back:"); print_main(); }
	kputc('\n');
}

void test_cgf(void) {
	xs = fuzz_seed(0x0CA11CA7);
	xmode = 1; rc32 = (u32)cgf_t32; rc16 = (u32)cgf_t16;
	u32 n = param("cgf", 300);
	xsetup();
	for (u32 i = 0; i < n; i++) {
		if (pct(75)) cgf_gate(i);
		else cgf_ret(i);
	}
	xteardown();
}

/* ===================== model-only checks (TCG deviates) ===================== */

static void xm_line(const char *name, int back) {
	kputs(name); kputc(':');
	if (cgf_rec.cs) { kputs(" in:"); print_rec(4, cgf_rec.nfr); }
	print_events();
	if (back && nev && evs[nev - 1].vec == 0x5F) { kputs(" back:"); print_main(); }
	kputc('\n');
}

/* a far CALL/JMP from ring `ring` (flat 32-bit code and stack, ESP = 0x5800 holding 0x11111111,
   0x22222222), through xfar.sel; the target loads DS/ES/FS = 0x1DB and returns with RETF imm */
static void xm_call(const char *name, u32 ring, u16 sel, u32 off, int call, u32 imm, u32 nfr) {
	memset((void *)&cgf_rec, 0, sizeof cgf_rec);
	cgf_rec.nfr = nfr;
	cgf_rec.ld[0] = cgf_rec.ld[1] = cgf_rec.ld[2] = S(I_DATA + 3) | 3;
	*(volatile u16 *)(cgf_r32a + 1) = imm;
	*(volatile u32 *)0x5800 = 0x11111111; *(volatile u32 *)0x5804 = 0x22222222;
	xfar.sel = sel; xfar.off = off;
	xent.eip = call ? LOW(xs_call) : LOW(xs_jmp);
	xent.cs = S(I_CODE + ring) | ring; xent.ss = S(I_DATA + ring) | ring; xent.esp = 0x5800;
	xent.ds = xent.es = xent.fs = xent.gs = S(I_DATA + 3) | 3;
	xent.eflags = 2;
	xmode = 1;
	rec_reset();
	xrun();
	xclean();
	tss_main.ss0 = KDATA; tss_main.esp0 = 0;
	xm_line(name, 1);
}

/* RETF from ring 0 with the given frame and data segment registers */
static void xm_ret(const char *name, u16 cs, u32 off, u16 ss, u16 ds, u16 es, u16 fs, u16 gs) {
	u32 *f = (u32 *)(0x4800 - 16);
	f[0] = off; f[1] = cs; f[2] = 0x5800; f[3] = ss;
	*(volatile u16 *)(xs_fret + 1) = 0;
	xent.eip = (u32)xs_fret; xent.cs = KCODE; xent.ss = KDATA; xent.esp = (u32)f;
	xent.ds = ds; xent.es = es; xent.fs = fs; xent.gs = gs; xent.eflags = 2;
	memset((void *)&cgf_rec, 0, sizeof cgf_rec);
	xmode = 1;
	rec_reset();
	xrun();
	xclean();
	xm_line(name, 1);
}

void test_xfer_model(void) {
	/* checks of the fuzz above */
	kprintf("tsf.commit.eip: seen=%d bad=%d\n", commit_seen, commit_bad);
	kprintf("tsf.fault.rf: seen=%d bad=%d\n", rf_seen, rf_bad);
	xsetup();
	rc32 = (u32)cgf_t32; rc16 = (u32)cgf_t16;

	/* a task whose CS is conforming with DPL 0 < RPL 3 runs at CPL 3 (TCG requires DPL = RPL) */
	xmode = 0;
	rec_reset(); ldt_reset();
	struct tss32 *t = (struct tss32 *)tnew;
	memset(tnew, 0, sizeof tnew);
	t->cr3 = RDCR(3); t->eflags = 2; t->esp = 0x1000;
	t->eax = 0x11111111; t->ecx = 0x22222222; t->edx = 0x33333333; t->ebx = 0x44444444;
	t->ebp = 0x66666666; t->esi = 0x77777777; t->edi = 0x88888888;
	t->cs = S(I_TCONF) | 3; t->ss = t->ds = t->es = t->fs = t->gs = S(I_DATA + 3) | 3;
	t->iomap = 0x68;
	xgdt[I_NEW] = seg_desc((u32)tnew, 0x67, 0xE9, 0);
	xfar.sel = S(I_NEW);
	xent.eip = (u32)xs_jmp; xent.cs = KCODE; xent.ss = KDATA; xent.esp = (u32)mstack + sizeof mstack;
	xent.ds = xent.es = xent.fs = xent.gs = KDATA; xent.eflags = 2;
	memset((void *)&cgf_rec, 0, sizeof cgf_rec);
	xrun();
	xclean();
	xm_line("xfer.task.conf", 0);

	u32 e_a = cgf_t32a - cgf_t32, e_b = cgf_t32b - cgf_t32;
	tss_main.ss0 = KDATA; tss_main.esp0 = (u32)istack[0] + sizeof istack[0];
	/* CALL through a call gate (to an inner level, to the same level) or direct: the offset is
	   checked against the limit, #GP(0) (TCG: no check through a gate, #GP(selector) direct) */
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0x10, 0x9B, 0x4);
	xgdt[I_CG] = gate_desc(S(I_TGT), e_b, 0xEC);
	xm_call("xfer.callg.limit", 3, S(I_CG) | 3, 0, 1, 0, 1);
	tss_main.ss0 = KDATA; tss_main.esp0 = (u32)istack[0] + sizeof istack[0];
	xm_call("xfer.callg.limit.same", 0, S(I_CG), 0, 1, 0, 1);
	xm_call("xfer.call.limit", 0, S(I_TGT), e_b, 1, 0, 1);
	/* JMP through a call gate to a not-present segment: #NP (TCG: #GP) */
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0xFFF, 0x7B, 0x4);
	xgdt[I_CG] = gate_desc(S(I_TGT), cgf_t32c - cgf_t32, 0xEC);
	xm_call("xfer.jmpg.np", 3, S(I_CG) | 3, 0, 0, 0, 1);
	/* the inner stack has no room for the frame (6 dwords): #SS(new SS), also before the offset check
	   (TCG does not check stack limits) */
	xgdt[I_RND] = seg_desc(0, 0x5FFF, 0x93, 0x4);
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0xFFF, 0x9B, 0x4);
	xgdt[I_CG] = gate_desc(S(I_TGT), e_a, 0xEC) | ((u64)2 << 32);
	tss_main.ss0 = S(I_RND); tss_main.esp0 = 0x14;
	xm_call("xfer.callg.room", 3, S(I_CG) | 3, 0, 1, 8, 6);
	tss_main.ss0 = S(I_RND); tss_main.esp0 = 0x6008;
	xm_call("xfer.callg.room.top", 3, S(I_CG) | 3, 0, 1, 8, 6);
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0x10, 0x9B, 0x4);
	xgdt[I_CG] = gate_desc(S(I_TGT), e_b, 0xEC) | ((u64)2 << 32);
	tss_main.ss0 = S(I_RND); tss_main.esp0 = 0x14;
	xm_call("xfer.callg.room.limit", 3, S(I_CG) | 3, 0, 1, 8, 6);
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0xFFF, 0x9B, 0x4);
	xgdt[I_CG] = gate_desc(S(I_TGT), e_a, 0xEC) | ((u64)2 << 32);
	tss_main.ss0 = S(I_RND); tss_main.esp0 = 0x18;
	xm_call("xfer.callg.room.exact", 3, S(I_CG) | 3, 0, 1, 8, 6);
	/* a 16-bit inner stack: ESP is loaded from the TSS and the pushes change only SP, so the target sees
	   ESP[31:16] of the TSS value (its 32-bit stack read then faults) */
	xgdt[I_CG] = gate_desc(S(I_TGT), e_a, 0xEC);
	tss_main.ss0 = S(I_DATA16); tss_main.esp0 = 0x00134000;
	xm_call("xfer.callg.esp16", 3, S(I_CG) | 3, 0, 1, 0, 1);
	/* RET to an outer level: null FS/GS with RPL > 0 become 0 like DS/ES (TCG keeps them) */
	xm_ret("xfer.ret.null", S(I_CODE + 3) | 3, LOW(xs_done), S(I_DATA + 3) | 3, 1, 2, 3, 3);
	/* RET to an outer level beyond the CS limit: #GP(0) (TCG does not check) */
	xgdt[I_TGT] = seg_desc((u32)cgf_t32, 0x10, 0xFB, 0x4);
	xm_ret("xfer.ret.limit", S(I_TGT) | 3, 0x40, S(I_DATA + 3) | 3, 0, 0, 0, 0);
	xteardown();
}
