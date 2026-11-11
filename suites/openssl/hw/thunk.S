/* u32 call_fn(u32 fn, u32 ecx, u32 edx, u32 nargs, const u32 *args) -- see driver.h */
	.text
	.globl call_fn
call_fn:
	pushl %ebp
	movl %esp, %ebp
	pushl %ebx
	pushl %esi
	pushl %edi
	movl 20(%ebp), %ecx
	movl 24(%ebp), %esi
1:	testl %ecx, %ecx
	jz 2f
	decl %ecx
	pushl (%esi,%ecx,4)
	jmp 1b
2:	movl 12(%ebp), %ecx
	movl 16(%ebp), %edx
	movl 8(%ebp), %eax
	movl %ebp, saved_ebp
	movl %esp, saved_esp
	movl $0x1b1b1b1b, %ebx
	movl $0x51515151, %esi
	movl $0xd1d1d1d1, %edi
	movl $0xb9b9b9b9, %ebp
	cld
	calll *%eax
	cmpl saved_esp, %esp
	jne 3f
	cmpl $0xb9b9b9b9, %ebp
	jne 3f
	cmpl $0x1b1b1b1b, %ebx
	jne 3f
	cmpl $0x51515151, %esi
	jne 3f
	cmpl $0xd1d1d1d1, %edi
	jne 3f
	pushfl
	popl %ecx
	testl $0x400, %ecx
	jz 4f
3:	incl call_violations
4:	cld
	movl saved_ebp, %ebp
	leal -12(%ebp), %esp
	popl %edi
	popl %esi
	popl %ebx
	popl %ebp
	ret

	.bss
	.align 4
saved_ebp: .long 0
saved_esp: .long 0
	.globl call_violations
call_violations: .long 0

	.section .rodata
	.globl image_blob, image_end
image_blob:
	.incbin IMAGE
image_end:
	.section .note.GNU-stack,"",@progbits
