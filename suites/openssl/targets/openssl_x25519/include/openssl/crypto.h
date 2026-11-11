/* Stub <openssl/crypto.h>: the two prototypes curve25519.c and mem_clr.c need. Not upstream.
   OPENSSL_cleanse is the vendored crypto/mem_clr.c; CRYPTO_memcmp is targets/openssl_x25519/stubs.c
   (verbatim copy of crypto/cpuid.c's definition; returns zero iff the len bytes at a and b are equal). */
#ifndef SSL_STUB_OPENSSL_CRYPTO_H
#define SSL_STUB_OPENSSL_CRYPTO_H
#include <stddef.h>
void OPENSSL_cleanse(void *ptr, size_t len);
int CRYPTO_memcmp(const void *in_a, const void *in_b, size_t len);
#endif
