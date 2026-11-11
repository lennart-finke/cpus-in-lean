/* Driver that runs a pinned task image on a real or emulated CPU and prints what it computed.
   The same driver is built for a multiboot machine (QEMU, the Lean model) and as a Linux process
   (real hardware); see tools/hw.py. Not part of any task image. */
#ifndef HW_DRIVER_H
#define HW_DRIVER_H
#include <stddef.h>
#include <stdint.h>
typedef uint8_t u8;
typedef uint32_t u32;

/* platform */
void plat_init(void);            /* place the image bytes at their link address */
void plat_putc(char c);
void plat_exit(void);
extern const u8 image_blob[], image_end[];

/* Call `fn` with `ecx`, `edx` and `nargs` stack words (caller pops): the cdecl convention, and
   with ecx/edx the convention of the images' static functions. Counts a violation if the callee
   does not restore ebx/esi/edi/ebp/esp or returns with the direction flag set. */
u32 call_fn(u32 fn, u32 ecx, u32 edx, u32 nargs, const u32 *args);
extern u32 call_violations;

/* output */
void put(const char *s);
void put_hex(const u8 *p, u32 n);     /* "-" for the empty string */
void put_u32(u32 v);                  /* 8 hex digits */
u32 rnd(void);
void rnd_bytes(u8 *p, u32 n);

void run(void);                       /* the target's calls */
#endif
