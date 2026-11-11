/* What the image needs besides libsodium's two files and the runtime (openssl/tools/runtime).
   Not an upstream file. */
#include <libc.h>

int errno = 0;

/* libsodium's is in core.c and aborts; here it faults (see include/libc.h). */
void sodium_misuse(void) { __builtin_trap(); }

void *memchr(const void *s, int c, size_t n) {
    const unsigned char *p = s;
    for (size_t i = 0; i < n; ++i) if (p[i] == (unsigned char)c) return (void *)(p + i);
    return 0;
}
char *strchr(const char *s, int c) {
    for (;; ++s) {
        if (*s == (char)c) return (char *)s;
        if (*s == 0) return 0;
    }
}
