/* Stub for include/openssl/crypto.h. The real header pulls in the whole public API (stacks, locks,
   ex_data, BIO …); crypto/sha/sha256.c, crypto/mem_clr.c and crypto/md32_common.h need only the
   OPENSSL_cleanse prototype from it (its definition is the vendored crypto/mem_clr.c). Not upstream. */
#ifndef OPENSSL_CRYPTO_H
#define OPENSSL_CRYPTO_H
#pragma once
#include <stddef.h>
#include <openssl/e_os2.h>
void OPENSSL_cleanse(void *ptr, size_t len);
#endif
