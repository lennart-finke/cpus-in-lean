/* Freestanding support shared by every target image: byte-loop memory routines and the
   64-bit integer helpers clang emits calls to on i386. Not part of any upstream source. */
#ifndef IDEAS_SHIM_H
#define IDEAS_SHIM_H
#include <stddef.h>
#include <stdint.h>
void *memcpy(void *dst, const void *src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memset(void *dst, int value, size_t n);
int memcmp(const void *a, const void *b, size_t n);
size_t strlen(const char *s);
#endif
