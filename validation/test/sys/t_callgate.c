/* Call gates: same privilege, ring 3 -> ring 0 with parameters, 16-bit gates, error cases. */
#include "sys.h"

#define GATE_K 0x90     /* DPL 0, 32-bit, to KCODE:cg_same */
#define GATE_U 0x98     /* DPL 3, 32-bit, 2 params, to KCODE:cg_inner */
#define GATE_U16 0xA0   /* DPL 3, 16-bit, 3 params, to CODE16:cg16 offset */
#define CODE16 0xA8     /* 16-bit ring-0 code segment based at cg16 */
#define GATE_NP 0xB0    /* not present */
#define GATE_K3 0xB8    /* DPL 0 gate used from ring 3 */

volatile u32 cg_count, cg_frame[8], cg_cs, cg16_frame[8];
__asm__(
	".globl cg_same\ncg_same: incl cg_count\n movw %cs, cg_cs\n lret\n"
	/* inner (ring 0) side: copy the 6 dwords at the top of the new stack, return popping 2 params */
	".globl cg_inner\ncg_inner: incl cg_count\n movw %cs, cg_cs\n"
	" movl 0(%esp), %eax\n movl %eax, cg_frame\n movl 4(%esp), %eax\n movl %eax, cg_frame+4\n"
	" movl 8(%esp), %eax\n movl %eax, cg_frame+8\n movl 12(%esp), %eax\n movl %eax, cg_frame+12\n"
	" movl 16(%esp), %eax\n movl %eax, cg_frame+16\n movl 20(%esp), %eax\n movl %eax, cg_frame+20\n"
	" lret $8\n"
	/* user side: push two params, call through the gate, then return to the kernel */
	".globl u_cg\nu_cg: pushl $0x1111\n pushl $0x2222\n lcall $0x9B, $0\n movl %esp, %ebx\n int $0x40\n"
	/* 16-bit gate: 16-bit pushes, 3 word params (a 16-bit return to 32-bit code would truncate EIP,
	   so the inner side reports back with INT 0x40) */
	".globl cg16\ncg16: .code16\n movl %esp, %ebp\n movl $cg16_frame, %edi\n"
	" movzwl 0(%ebp), %eax\n movl %eax, %ss:0(%edi)\n movzwl 2(%ebp), %eax\n movl %eax, %ss:4(%edi)\n"
	" movzwl 4(%ebp), %eax\n movl %eax, %ss:8(%edi)\n movzwl 8(%ebp), %eax\n movl %eax, %ss:12(%edi)\n"
	" movzwl 10(%ebp), %eax\n movl %eax, %ss:16(%edi)\n movzwl 12(%ebp), %eax\n movl %eax, %ss:20(%edi)\n"
	" int $0x40\n .code32\n"
	".globl u_cg16\nu_cg16: pushw $0xA\n pushw $0xB\n pushw $0xC\n lcall $0xA3, $0\n movl %esp, %ebx\n int $0x40\n"
	".globl u_cg_np\nu_cg_np: lcall $0xB3, $0\n int $0x40\n"
	".globl u_cg_k\nu_cg_k: lcall $0xBB, $0\n int $0x40\n"
	".globl u_jmp_inner\nu_jmp_inner: ljmp $0x9B, $0\n int $0x40\n");
extern char cg_same[], cg_inner[], u_cg[], cg16[], u_cg16[], u_cg_np[], u_cg_k[], u_jmp_inner[];

static u64 cgate(u16 sel, u32 off, u32 access, u32 params) { return gate_desc(sel, off, access) | ((u64)params << 32); }

void test_callgate(void) {
	gdt[GATE_K >> 3] = cgate(KCODE, (u32)cg_same, 0x8C, 0);
	gdt[GATE_U >> 3] = cgate(KCODE, (u32)cg_inner, 0xEC, 2);
	gdt[GATE_U16 >> 3] = cgate(CODE16, (u32)cg16 & 0xFFFF, 0xE4, 3);
	gdt[CODE16 >> 3] = seg_desc((u32)cg16 & ~0xFFFF, 0xFFFF, 0x9A, 0x0);
	gdt[GATE_NP >> 3] = cgate(KCODE, (u32)cg_same, 0x6C, 0);
	gdt[GATE_K3 >> 3] = cgate(KCODE, (u32)cg_same, 0x8C, 0);

	__asm__ volatile("lcall $0x90, $0" ::: "memory");
	kprintf("cg.same: count=%d cs=%x\n", cg_count, cg_cs);

	int v = run_user(u_cg, 0, 0);
	kprintf("cg.inner: vec=%x count=%d cs=%x\n", v, cg_count, cg_cs);
	kprintf("cg.inner.frame: eip_off=%x cs=%x p1=%x p2=%x ss=%x esp_delta=%x\n",
	        cg_frame[0] - (u32)u_cg, cg_frame[1], cg_frame[2], cg_frame[3], cg_frame[5],
	        last.esp - cg_frame[4]);

	v = run_user(u_cg16, 0, 0);
	kprintf("cg.16: vec=%x frame=%x %x %x %x %x %x\n", v, cg16_frame[0] - ((u32)u_cg16 & 0xFFFF),
	        cg16_frame[1], cg16_frame[2], cg16_frame[3], cg16_frame[4], cg16_frame[5] & 0xFFFF);

	report("cg.notpresent", run_user(u_cg_np, 0, 0));
	report("cg.dpl", run_user(u_cg_k, 0, 0));
	report("cg.jmp.inner", run_user(u_jmp_inner, 0, 0));
}
