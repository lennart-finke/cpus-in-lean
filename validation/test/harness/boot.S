/* Multiboot entry, IDT stubs and ring-3 entry for the differential test harness. */
#define MB_MAGIC 0x1BADB002
#define MB_FLAGS 0x00000003
	.section .multiboot, "a"
	.align 4
	.long MB_MAGIC, MB_FLAGS, -(MB_MAGIC + MB_FLAGS)

	.text
	.globl _start
_start:
	cli
	movl $stack_top, %esp
	pushl %ebx			/* multiboot info */
	call harness_main
1:	hlt
	jmp 1b

/* Exception stubs: push a dummy error code where the CPU does not push one. */
.macro STUB n, haserr
	.globl isr\n
isr\n:
	.if \haserr == 0
	pushl $0
	.endif
	pushl $\n
	jmp isr_common
.endm
STUB 0,0
STUB 1,0
STUB 2,0
STUB 3,0
STUB 4,0
STUB 5,0
STUB 6,0
STUB 7,0
STUB 8,1
STUB 9,0
STUB 10,1
STUB 11,1
STUB 12,1
STUB 13,1
STUB 14,1
STUB 15,0
STUB 16,0
STUB 17,1
STUB 18,0
STUB 19,0

isr_common:
	/* user DS/ES/FS/GS are still loaded: save them, then the GPRs */
	pushl %gs
	pushl %fs
	pushl %es
	pushl %ds
	pushal
	movl $0x10, %eax
	movl %eax, %ds
	movl %eax, %es
	movl %eax, %fs
	movl %eax, %gs
	pushl %esp
	call record		/* never returns */
1:	hlt
	jmp 1b

/* enter_user(): load the prepared user state from `ustate` and IRET to ring 3 */
	.globl enter_user
enter_user:
	movl $ustate, %ebp
	pushl 40(%ebp)		/* ss */
	pushl 16(%ebp)		/* esp */
	pushl 32(%ebp)		/* eflags */
	pushl $0x1b		/* cs */
	pushl 36(%ebp)		/* eip */
	movl 44(%ebp), %eax
	movl %eax, %ds
	movl 48(%ebp), %eax
	movl %eax, %es
	movl 52(%ebp), %eax
	movl %eax, %fs
	movl 56(%ebp), %eax
	movl %eax, %gs
	movl %cs:0(%ebp), %eax
	movl %cs:4(%ebp), %ecx
	movl %cs:8(%ebp), %edx
	movl %cs:12(%ebp), %ebx
	movl %cs:24(%ebp), %esi
	movl %cs:28(%ebp), %edi
	movl %cs:20(%ebp), %ebp
	iret

	.bss
	.align 16
	.space 16384
stack_top:
	.space 16384
	.globl tss_stack_top
tss_stack_top:
