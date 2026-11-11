/* Debug-breakpoint differential fuzzing: random DR0-DR3/DR7 (instruction, data write, data read/write
   and I/O breakpoints of every length, L/G enables, CR4.DE), optionally EFLAGS.TF, then one random
   instruction (load, store, read-modify-write, MOVS, PUSH/POP, IN/OUT) in ring 0 or ring 3. Prints every
   #DB: DR6, EIP relative to the instruction and RF in the pushed EFLAGS.
   Avoided (TCG deviations or undefined): two enabled data/I/O breakpoints matching one instruction
   (TCG reports only the first watchpoint; see db.two), unaligned breakpoint addresses, R/W = 10 with
   CR4.DE = 0, LEN != 1 for instruction breakpoints, MOV SS / POP SS and REP prefixes, disabled
   instruction breakpoints on code (TCG sets their Bn; the SDM allows but does not require it), and
   instruction breakpoints after the test instruction. */
#include "sys.h"

static u32 rs = 0x1F2E3D4C;
static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

static u8 dcode[4096] __attribute__((aligned(4096)));
static u8 dbuf[256] __attribute__((aligned(256)));
struct dregs { u32 eflags, eip, eax, edx, esi, edi, esp; };
static struct dregs R;

/* Ring 0: push a return address and the EFLAGS image, load registers, jump to the code (which starts
   with POPF and ends with RET); then restore a clean EFLAGS (DF = TF = 0).
   Ring 3: IRET to the code with the given EFLAGS and stack; the code ends with INT 0x40. */
__asm__(
	".globl dbf_run0\ndbf_run0:\n"
	" pushl %ebx\n pushl %esi\n pushl %edi\n pushl %ebp\n"
	" movl 20(%esp), %ebp\n"
	" pushl $1f\n pushl 0(%ebp)\n"
	" movl 8(%ebp), %eax\n movl 12(%ebp), %edx\n movl 16(%ebp), %esi\n movl 20(%ebp), %edi\n"
	" jmp *4(%ebp)\n"
	"1: pushl $2\n popfl\n"
	" popl %ebp\n popl %edi\n popl %esi\n popl %ebx\n ret\n"
	".globl dbf_run3\ndbf_run3:\n"
	" movl 4(%esp), %ebp\n"
	" movl $0x23, %ecx\n movl %ecx, %ds\n movl %ecx, %es\n"
	" pushl $0x23\n pushl 24(%ebp)\n pushl 0(%ebp)\n pushl $0x1b\n pushl 4(%ebp)\n"
	" movl 8(%ebp), %eax\n movl 12(%ebp), %edx\n movl 16(%ebp), %esi\n movl 20(%ebp), %edi\n"
	" iret\n");
void dbf_run0(struct dregs *);
void dbf_run3(struct dregs *);

static volatile u32 n_db, d_dr6[4], d_eip[4], d_efl[4];
static int dbf_hook(struct frame *f) {
	if (f->vec != 1) return 0;
	u32 d = RDDR(6), i = n_db++;
	if (i < 4) { d_dr6[i] = d; d_eip[i] = f->eip; d_efl[i] = f->eflags; }
	WRDR(6, 0);
	f->eflags |= 0x10000;                     /* RF: resume past an instruction breakpoint */
	if (d & 0x4000) f->eflags &= ~0x100u;     /* one single-step trap is enough */
	if (n_db > 8) { WRDR(7, 0); f->eflags &= ~0x100u; }
	return 1;
}

/* one access of the test instruction: type 0 read, 1 write, 2 I/O */
struct acc { u32 addr, size, type; };

static const char *const kname[] = { "ld", "st", "rmw", "movs", "out", "in", "pushm", "popm", "push", "pop", "nop" };

static int dbf_case(u32 c, int qemu) {
	u32 cr4 = RDCR(4) & ~0x8u;
	u32 base = (u32)dbuf;
	u32 kind = rnd() % 11;
	u32 user = kind >= 6 && kind <= 9 ? 1 : rnd() % 2;
	u32 size = 1u << (rnd() % 3);
	if (kind >= 6 && kind <= 9 && size == 1) size = 4;    /* no 8-bit PUSH/POP */
	u32 tf = rnd() % 4 == 0, df = rnd() % 2, de = rnd() % 2;
	u32 a1 = base + rnd() % 64, a2 = base + rnd() % 64;   /* memory operand, MOVS destination */
	u32 port = 0x80 + rnd() % 8;
	u32 esp = base + 120 + 4 * (rnd() % 4);
	struct acc acc[2];
	int na = 0;
	/* encode: ring 0 code starts with POPF */
	u8 *p = dcode;
	if (!user) *p++ = 0x9D;
	u8 *t = p;
	if (size == 2 && kind != 10) *p++ = 0x66;
	#define D32(x) do { u32 _x = (x); *p++ = (u8)_x; *p++ = (u8)(_x >> 8); *p++ = (u8)(_x >> 16); *p++ = (u8)(_x >> 24); } while (0)
	switch (kind) {
	case 0: *p++ = size == 1 ? 0x8A : 0x8B; *p++ = 0x05; D32(a1); acc[na++] = (struct acc){ a1, size, 0 }; break;
	case 1: *p++ = size == 1 ? 0x88 : 0x89; *p++ = 0x05; D32(a1); acc[na++] = (struct acc){ a1, size, 1 }; break;
	case 2: *p++ = size == 1 ? 0x80 : 0x83; *p++ = 0x05; D32(a1); *p++ = 1;
		acc[na++] = (struct acc){ a1, size, 0 }; acc[na++] = (struct acc){ a1, size, 1 }; break;
	case 3: *p++ = size == 1 ? 0xA4 : 0xA5;
		acc[na++] = (struct acc){ a1, size, 0 }; acc[na++] = (struct acc){ a2, size, 1 }; break;
	case 4: case 5:
		if (rnd() % 2) { *p++ = (kind == 4 ? 0xEE : 0xEC) | (size > 1); }
		else { *p++ = (kind == 4 ? 0xE6 : 0xE4) | (size > 1); *p++ = (u8)port; }
		acc[na++] = (struct acc){ port, size, 2 }; break;
	case 6: *p++ = 0xFF; *p++ = 0x35; D32(a1);
		acc[na++] = (struct acc){ a1, size, 0 }; acc[na++] = (struct acc){ esp - size, size, 1 }; break;
	case 7: *p++ = 0x8F; *p++ = 0x05; D32(a1);
		acc[na++] = (struct acc){ esp, size, 0 }; acc[na++] = (struct acc){ a1, size, 1 }; break;
	case 8: *p++ = 0x50; acc[na++] = (struct acc){ esp - size, size, 1 }; break;
	case 9: *p++ = 0x58; acc[na++] = (struct acc){ esp, size, 0 }; break;
	default: if (rnd() % 2) *p++ = 0x90; else { *p++ = 0x01; *p++ = 0xC0; } break;
	}
	u32 len = (u32)(p - t);
	if (user) { *p++ = 0xCD; *p++ = 0x40; } else *p++ = 0xC3;

	/* breakpoints */
	u32 dr[4], dr7 = rnd() & 0x300;   /* LE/GE: ignored */
	for (u32 k = 0; k < 4; k++) {
		u32 en = rnd() % 4, ty = rnd() % 4, lc = rnd() % 4;
		if (rnd() % 4 == 0) en = 0;
		if (ty == 2 && !de) ty = 3;
		u32 bl = lc == 0 ? 1 : lc == 1 ? 2 : lc == 3 ? 4 : 8;
		u32 a;
		if (ty == 0) {
			lc = 0; bl = 1;
			a = !en ? base + rnd() % 64 : (rnd() % 4 || len < 2) ? (u32)t : (u32)t + 1 + rnd() % (len - 1);
		} else if (ty == 2) a = 0x80 + rnd() % 16;
		else if (na && rnd() % 2) { struct acc *x = &acc[rnd() % na]; a = (x->type == 2 ? base : x->addr) + rnd() % 12 - 6; }
		else a = base + rnd() % 144;
		if (ty != 0 && ty != 2) a = base + ((a - base) & 0xFF);   /* only dbuf: the kernel must not hit them */
		dr[k] = a & ~(bl - 1);
		dr7 |= (en << (2 * k)) | (ty << (16 + 4 * k)) | (lc << (18 + 4 * k));
	}
	/* two enabled data/I/O breakpoints matching the instruction: keep one */
	u32 hit = 0;
	for (u32 k = 0; k < 4; k++) {
		u32 ty = (dr7 >> (16 + 4 * k)) & 3, lc = (dr7 >> (18 + 4 * k)) & 3;
		u32 bl = lc == 0 ? 1 : lc == 1 ? 2 : lc == 3 ? 4 : 8;
		if (!((dr7 >> (2 * k)) & 3) || ty == 0) continue;
		for (int i = 0; i < na; i++) {
			int ok = acc[i].type == 2 ? ty == 2 : ty == 3 || (ty == 1 && acc[i].type == 1);
			if (ok && dr[k] < acc[i].addr + acc[i].size && acc[i].addr < dr[k] + bl) hit |= 1u << k;
		}
	}
	if (qemu) {
		/* TCG reports only the first watchpoint: keep one of several matching ones */
		while (hit & (hit - 1)) {
			u32 k = rnd() % 4;
			if (hit & (1u << k)) { hit &= ~(1u << k); dr7 &= ~(3u << (2 * k)); }
		}
		/* TCG splits a single-step trap and a data or I/O breakpoint of the same instruction into
		   two #DBs (the second at the first instruction of the handler) */
		if (hit) tf = 0;
	}

	R.eflags = 0x2 | (tf << 8) | (df << 10) | (user ? 0x3000 : 0);
	R.eip = (u32)dcode;
	R.eax = rnd(); R.edx = port; R.esp = esp;
	R.esi = a1; R.edi = a2;
	for (u32 k = 0; k < 4; k++) dbuf[120 + k] = (u8)(0x40 + k);

	n_db = 0;
	WRCR(4, cr4 | (de ? 0x8 : 0));
	WRDR(0, dr[0]); WRDR(1, dr[1]); WRDR(2, dr[2]); WRDR(3, dr[3]);
	WRDR(6, 0);
	WRDR(7, dr7);
	int vec = user ? TRY(dbf_run3(&R)) : TRY(dbf_run0(&R));
	WRDR(7, 0);
	WRDR(6, 0);
	/* expected (SDM 17.2.3, 17.3.1): an instruction-breakpoint fault with the Bn of every enabled
	   instruction breakpoint at the instruction, then one trap after it with the Bn of every matching
	   enabled data/I/O breakpoint and BS for single-step */
	u32 ex = 0;
	for (u32 k = 0; k < 4; k++)
		if (((dr7 >> (2 * k)) & 3) && !((dr7 >> (16 + 4 * k)) & 3) && dr[k] == (u32)t) ex |= 1u << k;
	u32 tb = hit | (tf ? 0x4000 : 0), ne = 0, bad = (u32)vec != (user ? 0x40u : 0xFFFFu);
	if (ex) { bad |= ne >= n_db || d_dr6[ne] != (0xFFFF0FF0 | ex) || d_eip[ne] != (u32)t || (d_efl[ne] & 0x10000); ne++; }
	if (tb) { bad |= ne >= n_db || d_dr6[ne] != (0xFFFF0FF0 | tb) || d_eip[ne] != (u32)t + len || (d_efl[ne] & 0x10000); ne++; }
	bad |= ne != n_db;
	if (qemu || bad) {
	kprintf("dbf%s %d: %s%d r%d tf=%d de=%d dr7=%x", qemu ? "" : "m", c, kname[kind], size, user ? 3 : 0, tf, de, dr7);
	for (u32 k = 0; k < 4; k++) kprintf(" %x", dr[k]);
	kprintf(" v=%x n=%d", vec, n_db);
	for (u32 i = 0; i < n_db && i < 4; i++)
		kprintf(" [dr6=%x eip=%x rf=%d]", d_dr6[i], d_eip[i] - (u32)t, (d_efl[i] >> 16) & 1);
	kputc('\n');
	}
	return bad;
}

void test_debug_fuzz(void) {
	u32 n = param("dbf", 400);
	rs = fuzz_seed(rs);
	trap_hook = dbf_hook;
	u32 cr4 = RDCR(4);
	for (u32 c = 0; c < n; c++) dbf_case(c, 1);
	WRCR(4, cr4);
	trap_hook = 0;
}

/* Model-only: the same generator without the TCG exclusions (several matching breakpoints,
   single-step together with a data or I/O breakpoint); every case is checked against the
   expectation computed in dbf_case. */
void test_debug_fuzz_model(void) {
	u32 n = param("dbfm", 400), bad = 0;
	rs = fuzz_seed(0x5EED0DB6);
	trap_hook = dbf_hook;
	u32 cr4 = RDCR(4);
	for (u32 c = 0; c < n; c++) bad += dbf_case(c, 0);
	WRCR(4, cr4);
	trap_hook = 0;
	kprintf("dbfm: bad=%d\n", bad);
}
