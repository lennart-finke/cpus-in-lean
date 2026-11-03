.section .multiboot,"a"
.balign 4
.long 0x1badb002, 3, -(0x1badb002+3)
.text
.code32
.global _start
_start:
 cli
 mov $0x70000, %esp
 mov %ebx, %edi
 /* 0x3000 PML4, 0x4000 PDPT, 0x5000 PD, 0x6000 PT */
 mov $0x3000, %eax
 mov $4096, %ecx
1: movl $0, (%eax)
 add $4, %eax
 loop 1b
 movl $0x4007, 0x3000
 movl $0x5007, 0x4000
 movl $0x6007, 0x5000
 xor %eax, %eax
2: mov %eax, %edx
 shl $12, %edx
 or $7, %edx
 mov %edx, 0x6000(,%eax,8)
 inc %eax
 cmp $512, %eax
 jne 2b
 /* Map the rest of the first GiB with 2 MiB pages. */
 mov $1, %eax
3: mov %eax, %edx
 shl $21, %edx
 or $0x87, %edx
 mov %edx, 0x5000(,%eax,8)
 inc %eax
 cmp $512, %eax
 jne 3b
 mov $0x3000, %eax
 mov %eax, %cr3
 mov $0x620, %eax
 mov %eax, %cr4
 mov $0xc0000080, %ecx
 mov $0x900, %eax
 xor %edx, %edx
 wrmsr
 lgdt gdt_ptr
 mov $0x80010011, %eax
 mov %eax, %cr0
 ljmp $8, $long_entry
.code64
long_entry:
 mov $0x10, %ax
 mov %ax, %ds
 mov %ax, %es
 mov %ax, %ss
 xor %eax, %eax
 mov %ax, %fs
 mov %ax, %gs
 call harness_main
 hlt

.balign 8
gdt:
.quad 0, 0x00af9b000000ffff, 0x00cf93000000ffff
.quad 0x00affb000000ffff, 0x00cff3000000ffff
.quad 0, 0
.global gdt
gdt_ptr:
.word 55
.quad gdt

.macro STUB n, err
.global isr\n
isr\n:
.if \err == 0
 pushq $0
.endif
 pushq $\n
 jmp common
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
common:
 push %r15
 push %r14
 push %r13
 push %r12
 push %r11
 push %r10
 push %r9
 push %r8
 push %rdi
 push %rsi
 push %rbp
 pushq $0
 push %rbx
 push %rdx
 push %rcx
 push %rax
 stmxcsr mxstate(%rip)
 movdqa %xmm0, xstate+0(%rip)
 movdqa %xmm1, xstate+16(%rip)
 movdqa %xmm2, xstate+32(%rip)
 movdqa %xmm3, xstate+48(%rip)
 movdqa %xmm4, xstate+64(%rip)
 movdqa %xmm5, xstate+80(%rip)
 movdqa %xmm6, xstate+96(%rip)
 movdqa %xmm7, xstate+112(%rip)
 movdqa %xmm8, xstate+128(%rip)
 movdqa %xmm9, xstate+144(%rip)
 movdqa %xmm10, xstate+160(%rip)
 movdqa %xmm11, xstate+176(%rip)
 movdqa %xmm12, xstate+192(%rip)
 movdqa %xmm13, xstate+208(%rip)
 movdqa %xmm14, xstate+224(%rip)
 movdqa %xmm15, xstate+240(%rip)
 mov %rsp, %rdi
 mov $0x70000, %rsp
 cld
 call record
 hlt

.global enter_user
enter_user:
 mov $0x23, %ax
 mov %ax, %ds
 mov %ax, %es
 xor %eax, %eax
 mov %ax, %fs
 mov %ax, %gs
 ldmxcsr mxstate(%rip)
 movdqa xstate+0(%rip), %xmm0
 movdqa xstate+16(%rip), %xmm1
 movdqa xstate+32(%rip), %xmm2
 movdqa xstate+48(%rip), %xmm3
 movdqa xstate+64(%rip), %xmm4
 movdqa xstate+80(%rip), %xmm5
 movdqa xstate+96(%rip), %xmm6
 movdqa xstate+112(%rip), %xmm7
 movdqa xstate+128(%rip), %xmm8
 movdqa xstate+144(%rip), %xmm9
 movdqa xstate+160(%rip), %xmm10
 movdqa xstate+176(%rip), %xmm11
 movdqa xstate+192(%rip), %xmm12
 movdqa xstate+208(%rip), %xmm13
 movdqa xstate+224(%rip), %xmm14
 movdqa xstate+240(%rip), %xmm15
 mov $0x70000, %rsp
 pushq $0x23
 pushq ustate+32(%rip)
 pushq ustate+128(%rip)
 pushq $0x1b
 pushq $0x20100
 mov ustate(%rip), %rax
 mov ustate+8(%rip), %rcx
 mov ustate+16(%rip), %rdx
 mov ustate+24(%rip), %rbx
 mov ustate+40(%rip), %rbp
 mov ustate+48(%rip), %rsi
 mov ustate+56(%rip), %rdi
 mov ustate+64(%rip), %r8
 mov ustate+72(%rip), %r9
 mov ustate+80(%rip), %r10
 mov ustate+88(%rip), %r11
 mov ustate+96(%rip), %r12
 mov ustate+104(%rip), %r13
 mov ustate+112(%rip), %r14
 mov ustate+120(%rip), %r15
 iretq
