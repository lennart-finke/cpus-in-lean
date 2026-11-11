/* The driver sits at 2 MiB, clear of the task image it copies to 1 MiB. */
ENTRY(_start)
SECTIONS
{
  . = 0x200000;
  .text   : { *(.multiboot) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.*) }
  .bss    : { *(.bss .bss.* COMMON) }
  /DISCARD/ : { *(.comment) *(.note .note.*) *(.eh_frame) *(.llvm_addrsig) }
}
