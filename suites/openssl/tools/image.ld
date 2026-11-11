/* Layout of a task image: one contiguous block at 0x100000 holding code, constants and
   initialised data of everything reachable from the roots (ld.lld --gc-sections). */
ENTRY(halt)
SECTIONS
{
  . = 0x100000;
  .text   : { *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.*) }
  .bss    : { *(.bss .bss.* COMMON) }
  /DISCARD/ : { *(.comment) *(.note .note.*) *(.eh_frame) *(.llvm_addrsig) *(.rel.*) }
}
/* The flat image has no loader to clear memory, and the tasks hold for arbitrary memory contents. */
ASSERT(SIZEOF(.bss) == 0, "zero-initialised writable data is not supported in a task image")
