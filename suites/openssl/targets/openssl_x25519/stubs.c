/* Local replacement for OpenSSL's CRYPTO_memcmp (targets/openssl_x25519; not an upstream file).
   Upstream defines it in crypto/cpuid.c, which also carries the CPU-feature probing (OPENSSL_cpuid_setup,
   OPENSSL_ia32cap) that cannot be linked freestanding. The body below is that definition copied verbatim
   (openssl-3.5.9 crypto/cpuid.c, `int CRYPTO_memcmp`); contract (include/openssl/crypto.h.in): returns
   zero iff the |len| bytes at |a| and |b| are equal, in constant time. */
#include <stddef.h>
#include <openssl/crypto.h>

int CRYPTO_memcmp(const void *in_a, const void *in_b, size_t len)
{
    size_t i;
    const volatile unsigned char *a = in_a;
    const volatile unsigned char *b = in_b;
    unsigned char x = 0;

    for (i = 0; i < len; i++)
        x |= a[i] ^ b[i];

    return x;
}
