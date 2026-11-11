/* System-level test kernel: multiboot entry, 256 interrupt stubs, trap frame, setjmp/longjmp. */
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
	movl %ebx, mb_info		/* multiboot information (command line: fuzzing parameters) */
	/* loaders differ in the multiboot info pointer (EBX) etc.: start from identical registers */
	xorl %eax, %eax
	xorl %ebx, %ebx
	xorl %ecx, %ecx
	xorl %edx, %edx
	xorl %esi, %esi
	xorl %edi, %edi
	xorl %ebp, %ebp
	call sys_main
	.globl halt_forever
halt_forever:
1:	hlt
	jmp 1b

/* 256 stubs, 16 bytes apart: isr_base + 16*vector. Vectors with a CPU error code skip the dummy push. */
	.align 16
	.globl isr_base
isr_base:
	.set vec, 0
	.rept 256
	.align 16
	.if (vec == 8) || (vec == 10) || (vec == 11) || (vec == 12) || (vec == 13) || (vec == 14) || (vec == 17)
	nop
	nop
	.else
	pushl $0
	.endif
	pushl $vec
	jmp isr_common
	.set vec, vec + 1
	.endr

/* Stub variant for vectors that the CPU reaches through a task gate or that must not push a dummy
   error code: tests that need an error-code-less entry for 8..17 use `isr_noerr + 16*vector`. */
	.align 16
	.globl isr_noerr
isr_noerr:
	.set vec, 0
	.rept 32
	.align 16
	pushl $0
	pushl $vec
	jmp isr_common
	.set vec, vec + 1
	.endr

isr_common:
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
	call trap
	addl $4, %esp
	.globl trap_return
trap_return:
	popal
	popl %ds
	popl %es
	popl %fs
	popl %gs
	addl $8, %esp
	iret

/* int ksetjmp(struct jmpbuf *): saves ebx, esi, edi, ebp, esp, eip. */
	.globl ksetjmp
ksetjmp:
	movl 4(%esp), %eax
	movl %ebx, 0(%eax)
	movl %esi, 4(%eax)
	movl %edi, 8(%eax)
	movl %ebp, 12(%eax)
	leal 4(%esp), %ecx
	movl %ecx, 16(%eax)
	movl (%esp), %ecx
	movl %ecx, 20(%eax)
	xorl %eax, %eax
	ret

/* void klongjmp(struct jmpbuf *, int): also reloads kernel data segments and clears EFLAGS (IF, NT, TF...). */
	.globl klongjmp
klongjmp:
	movl 4(%esp), %edx
	movl 8(%esp), %eax
	movl $0x10, %ecx
	movl %ecx, %ds
	movl %ecx, %es
	movl %ecx, %fs
	movl %ecx, %gs
	movl %ecx, %ss
	movl 0(%edx), %ebx
	movl 4(%edx), %esi
	movl 8(%edx), %edi
	movl 12(%edx), %ebp
	movl 16(%edx), %esp
	pushl $2
	popfl
	jmp *20(%edx)

	.bss
	.align 16
	.space 16384
	.globl stack_top
stack_top:
