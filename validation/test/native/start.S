.text
.global _start
_start:
 xor %rbp,%rbp
 mov %rsp,%rdi
 and $-16,%rsp
 call start
 ud2
.section .note.GNU-stack,"",@progbits
