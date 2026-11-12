/* System-management mode: SMI through the APM port, state save map, RSM, SMBASE relocation.
   QEMU: the firmware relocated SMBASE to 0xA0000 and left SMRAM unlocked; the test opens SMRAM
   (i440FX SMRAM register, D_OPEN) to install its handler and enables APMC SMIs (PIIX4 DEVACTB).
   The model has no chipset: SMRAM is plain RAM, port 0xB2 always raises an SMI, and x86sys starts
   with SMBASE = 0xA0000 like the firmware leaves it. */
#include "sys.h"

/* Handler results in normal RAM at 0x6000 (word index): 0 count, 1 saved EAX, 2 saved EIP,
   3 saved CR0, 4 revision, 5 SMBASE, 6 CS in SMM, 7 CR0 in SMM, 8 EFLAGS in SMM, 9 relocation
   request (input), 10 saved CS selector, 11 saved CS attributes, 12 saved CR4, 13 saved ESP,
   14 saved CR3, 15 ESP in SMM, 16 DS selector in SMM, 17 saved EFER (AMD64 map only).
   The handler reads the 32-bit map of qemu-system-i386 or the AMD64 map (AMD APM vol. 2, table 10-1,
   which AMD64 processors use in every mode: the model, qemu-system-x86_64), told apart by the
   revision identifier's low word (0064h for the AMD64 map). */
#define S ((volatile u32 *)0x6000)

__asm__(
	".code16\n.globl smi_h\nsmi_h:\n"
	" movl $0x6000, %ebx\n incl (%ebx)\n"
	" movw %cs, %ax\n movzwl %ax, %eax\n movl %eax, 0x18(%ebx)\n"
	" movl %cr0, %eax\n movl %eax, 0x1c(%ebx)\n"
	" movl %esp, %eax\n movl %eax, 0x3c(%ebx)\n movw %ds, %ax\n movzwl %ax, %eax\n movl %eax, 0x40(%ebx)\n"
	" movl $0x7000, %esp\n pushfl\n popl %eax\n movl %eax, 0x20(%ebx)\n"
	" movw %cs, %si\n movzwl %si, %esi\n shll $4, %esi\n addl $0x8000, %esi\n"
	" movl 0x7efc(%esi), %eax\n movl %eax, 0x10(%ebx)\n cmpw $0x64, %ax\n je 7f\n"
	/* Intel's 32-bit map (qemu-system-i386) */
	" movl 0x7fd0(%esi), %eax\n movl %eax, 0x04(%ebx)\n"
	" movl 0x7ff0(%esi), %eax\n movl %eax, 0x08(%ebx)\n"
	" movl 0x7ffc(%esi), %eax\n movl %eax, 0x0c(%ebx)\n"
	" movl 0x7ef8(%esi), %eax\n movl %eax, 0x14(%ebx)\n"
	" movl 0x7fac(%esi), %eax\n movl %eax, 0x28(%ebx)\n"
	" movl 0x7f90(%esi), %eax\n movl %eax, 0x2c(%ebx)\n"
	" movl 0x7f14(%esi), %eax\n movl %eax, 0x30(%ebx)\n"
	" movl 0x7fe0(%esi), %eax\n movl %eax, 0x34(%ebx)\n"
	" movl 0x7ff8(%esi), %eax\n movl %eax, 0x38(%ebx)\n"
	" movl $0x5a5a5a5a, 0x7fd0(%esi)\n"
	" movl 0x24(%ebx), %eax\n testl %eax, %eax\n jz 8f\n movl %eax, 0x7ef8(%esi)\n jmp 8f\n"
	/* the AMD64 map (AMD APM vol. 2, table 10-1; revision xx64h) */
	"7: movl 0x7ff8(%esi), %eax\n movl %eax, 0x04(%ebx)\n"
	" movl 0x7f78(%esi), %eax\n movl %eax, 0x08(%ebx)\n"
	" movl 0x7f58(%esi), %eax\n movl %eax, 0x0c(%ebx)\n"
	" movl 0x7f00(%esi), %eax\n movl %eax, 0x14(%ebx)\n"
	" movzwl 0x7e10(%esi), %eax\n movl %eax, 0x28(%ebx)\n"
	" movzwl 0x7e12(%esi), %eax\n movl %eax, 0x2c(%ebx)\n"
	" movl 0x7f48(%esi), %eax\n movl %eax, 0x30(%ebx)\n"
	" movl 0x7fd8(%esi), %eax\n movl %eax, 0x34(%ebx)\n"
	" movl 0x7f50(%esi), %eax\n movl %eax, 0x38(%ebx)\n"
	" movl 0x7ed0(%esi), %eax\n movl %eax, 0x44(%ebx)\n"
	" movl $0x5a5a5a5a, 0x7ff8(%esi)\n"
	" movl 0x24(%ebx), %eax\n testl %eax, %eax\n jz 8f\n movl %eax, 0x7f00(%esi)\n"
	"8:\n"
	" rsm\n"
	".globl smi_h_end\nsmi_h_end:\n.code32\n");
extern char smi_h[], smi_h_end[];

static void pci_w8(u32 dev, u32 reg, u8 v) { outl(0xCF8, 0x80000000 | dev | (reg & 0xFC)); outb(0xCFC + (reg & 3), v); }
static u8 pci_r8(u32 dev, u32 reg) { outl(0xCF8, 0x80000000 | dev | (reg & 0xFC)); return inb(0xCFC + (reg & 3)); }

static u32 smi(u32 eax) {
	__asm__ volatile("outb %%al, $0xb2" : "+a"(eax) :: "memory");
	return eax;
}
static void show(const char *what, u32 eax) {
	kprintf("%s: count=%d eax=%x saved_eax=%x eip_ok=%d cr0=%x rev=%x smbase=%x cs=%x smm_cr0=%x smm_efl=%x\n",
	        what, S[0], eax, S[1], S[2] != 0, S[3], S[4], S[5], S[6], S[7] & 0x8000000F, S[8]);
	kprintf("%s.more: cs_sel=%x cs_attr=%x cr4=%x esp_ok=%d smm_esp_ok=%d smm_ds=%x\n", what, S[10],
	        S[11], S[12], S[13] == S[15], S[15] != 0, S[16]);
}

void test_smm(void) {
	pci_w8(0x0B00, 0x5B, pci_r8(0x0B00, 0x5B) | 0x02);   /* PIIX4 function 3: APMC_EN */
	pci_w8(0x0000, 0x72, 0x4A);                          /* i440FX: D_OPEN | G_SMRAME | 0xA0000 */
	memcpy((void *)0xA8000, smi_h, smi_h_end - smi_h);
	for (int i = 0; i < 20; i++) S[i] = 0;

	u32 a = smi(0x1234);
	show("smm.basic", a);

	/* SMI while paging is on: CR0/CR3/CR4 saved and restored */
	u32 *pd = page_alloc(1);
	for (int i = 0; i < 8; i++) pd[i] = (i << 22) | 0x87;
	pd[0x40000000 >> 22] = 0x87;   /* alias of the first 4 MiB at 1 GiB */
	WRCR(3, (u32)pd); WRCR(4, 0x10); WRCR(0, RDCR(0) | 0x80000000);
	a = smi(7);
	u32 alias = *(volatile u32 *)(0x40000000 + 0x6000);
	WRCR(0, RDCR(0) & ~0x80000000); WRCR(4, 0);
	show("smm.paging", a);
	kprintf("smm.paging.after: alias_count=%d cr3_ok=%d\n", alias, S[14] == (u32)pd);

	/* SMBASE relocation: the next SMI enters at 0x50000 + 0x8000 */
	memcpy((void *)0x58000, smi_h, smi_h_end - smi_h);
	S[9] = 0x50000;
	a = smi(1);
	S[9] = 0;
	a = smi(2);
	show("smm.relocated", a);
	S[9] = 0xA0000;            /* move it back for the firmware */
	a = smi(3);
	S[9] = 0;

	kprintf("smm.gdt.cs.accessed: %d\n", (u32)(gdt[1] >> 40) & 1);
	report("smm.rsm.outside", TRY(__asm__ volatile("rsm" ::: "memory")));
	pci_w8(0x0000, 0x72, 0x0A);   /* close SMRAM again */
}
