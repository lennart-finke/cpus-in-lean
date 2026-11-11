/* The two C library functions the image calls besides the runtime's (openssl/tools/runtime):
   byte loops. Not an upstream file. */
#include <libc.h>

void *memchr(const void *s, int c, size_t n) {
    const unsigned char *p = s;
    for (size_t i = 0; i < n; ++i) if (p[i] == (unsigned char)c) return (void *)(p + i);
    return 0;
}
int strncmp(const char *a, const char *b, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        unsigned char x = (unsigned char)a[i], y = (unsigned char)b[i];
        if (x != y) return x < y ? -1 : 1;
        if (x == 0) break;
    }
    return 0;
}
