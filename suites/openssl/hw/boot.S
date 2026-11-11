/* Multiboot entry (QEMU -kernel, and `sslcheck boot` on the Lean model). */
	.section .multiboot, "a"
	.align 4
	.long 0x1BADB002, 0x3, -(0x1BADB002 + 0x3)
	.text
	.globl _start
_start:
	cli
	movl $stack_top, %esp
	call main
1:	hlt
	jmp 1b
	.bss
	.align 16
	.skip 65536
stack_top:
	.section .note.GNU-stack,"",@progbits
