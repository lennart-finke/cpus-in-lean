.text
.global signal_restorer
signal_restorer:
 mov $15,%rax
 syscall
 ud2
/* The end of the oracle's image: this object is linked last (build.py) and this empty section is its
 * last one, so the symbol's address is the end of the loaded image (signal_oracle.c write-protects and
 * checks [0x100000, oracle_image_end) while an instruction runs). */
.bss
.global oracle_image_end
oracle_image_end:
.section .note.GNU-stack,"",@progbits
