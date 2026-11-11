.section .text.halt,"ax",@progbits
.global halt
.type halt,@function
halt:
    hlt
.size halt, .-halt
.section .note.GNU-stack,"",@progbits
