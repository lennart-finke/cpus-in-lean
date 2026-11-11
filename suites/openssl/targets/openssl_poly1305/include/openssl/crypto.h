/* Stub for OpenSSL's include/openssl/crypto.h: only the OPENSSL_cleanse prototype is needed by
   crypto/poly1305/poly1305.c (Poly1305_Final) and crypto/mem_clr.c (its definition). Not upstream. */
#ifndef OPENSSL_CRYPTO_H
#define OPENSSL_CRYPTO_H
#include <stddef.h>
void OPENSSL_cleanse(void *ptr, size_t len);
#endif
