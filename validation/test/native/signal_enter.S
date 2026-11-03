.text
.global signal_restorer
signal_restorer:
 mov $15,%rax
 syscall
 ud2
.section .note.GNU-stack,"",@progbits
