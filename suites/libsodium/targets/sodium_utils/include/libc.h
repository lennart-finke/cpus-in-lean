/* The C library declarations libsodium's two source files need to compile for a freestanding i386
   image. Not an upstream file. Every hosted header they include (the other files of this directory)
   is this one. The image calls none of these functions: the allocation and memory-protection code
   of utils.c that would is unreachable from the roots and is not linked. */
#ifndef SUITE_LIBC_H
#define SUITE_LIBC_H
#include <stddef.h>
#include <stdint.h>
#include <limits.h>

/* A failed assertion and libsodium's `sodium_misuse()` (core.c, which aborts) both stop the machine
   with an invalid-opcode fault, so no task holds on a run that reaches either. */
#define assert(x) ((x) ? (void) 0 : __builtin_trap())

extern int errno;
#define ENOMEM 12
#define EINVAL 22
#define ERANGE 34
#define ENXIO 6

void *memcpy(void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
void *memchr(const void *, int, size_t);
char *strchr(const char *, int);
void *malloc(size_t);
void free(void *);
void abort(void);
#endif
