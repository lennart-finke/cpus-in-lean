/* Stub "crypto/ecx.h": the key-length macros curve25519.c uses (values as upstream include/crypto/ecx.h) and
   the prototypes of the functions it defines. Upstream additionally declares the ECX_KEY object and pulls in
   openssl/core.h, crypto/types.h and internal/refcount.h, none of which curve25519.c uses. Not upstream. */
#ifndef SSL_STUB_CRYPTO_ECX_H
#define SSL_STUB_CRYPTO_ECX_H
#include <stddef.h>
#include <stdint.h>
#include <openssl/evp.h>
#define X25519_KEYLEN 32
#define X448_KEYLEN 56
#define ED25519_KEYLEN 32
#define ED448_KEYLEN 57
#define ED25519_SIGSIZE 64
int ossl_x25519(uint8_t out_shared_key[32], const uint8_t private_key[32],
                const uint8_t peer_public_value[32]);
void ossl_x25519_public_from_private(uint8_t out_public_value[32],
                                     const uint8_t private_key[32]);
int ossl_ed25519_public_from_private(OSSL_LIB_CTX *ctx, uint8_t out_public_key[32],
                                     const uint8_t private_key[32], const char *propq);
int ossl_ed25519_sign(uint8_t *out_sig, const uint8_t *tbs, size_t tbs_len,
                      const uint8_t public_key[32], const uint8_t private_key[32],
                      const uint8_t dom2flag, const uint8_t phflag, const uint8_t csflag,
                      const uint8_t *context, size_t context_len,
                      OSSL_LIB_CTX *libctx, const char *propq);
int ossl_ed25519_verify(const uint8_t *tbs, size_t tbs_len,
                        const uint8_t signature[64], const uint8_t public_key[32],
                        const uint8_t dom2flag, const uint8_t phflag, const uint8_t csflag,
                        const uint8_t *context, size_t context_len,
                        OSSL_LIB_CTX *libctx, const char *propq);
int ossl_ed25519_pubkey_verify(const uint8_t *pub, size_t pub_len);
#endif
