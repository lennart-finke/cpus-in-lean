/* Stub <openssl/evp.h>: opaque types and prototypes for the EVP digest calls of the Ed25519 half of
   curve25519.c (ossl_ed25519_sign/verify/public_from_private, hash_init_with_dom). That code is compiled but
   not reachable from the roots ossl_x25519 / ossl_x25519_public_from_private, so the linker never
   resolves these symbols and no definitions are linked. SN_sha512 is the upstream openssl/obj_mac.h value.
   Not upstream. */
#ifndef SSL_STUB_OPENSSL_EVP_H
#define SSL_STUB_OPENSSL_EVP_H
#include <stddef.h>
#include <openssl/crypto.h>
typedef struct evp_md_st EVP_MD;
typedef struct evp_md_ctx_st EVP_MD_CTX;
typedef struct ossl_lib_ctx_st OSSL_LIB_CTX;
typedef struct engine_st ENGINE;
#define SN_sha512 "SHA512"
EVP_MD *EVP_MD_fetch(OSSL_LIB_CTX *ctx, const char *algorithm, const char *properties);
void EVP_MD_free(EVP_MD *md);
EVP_MD_CTX *EVP_MD_CTX_new(void);
void EVP_MD_CTX_free(EVP_MD_CTX *ctx);
int EVP_DigestInit_ex(EVP_MD_CTX *ctx, const EVP_MD *type, ENGINE *impl);
int EVP_DigestUpdate(EVP_MD_CTX *ctx, const void *d, size_t cnt);
int EVP_DigestFinal_ex(EVP_MD_CTX *ctx, unsigned char *md, unsigned int *s);
int EVP_Digest(const void *data, size_t count, unsigned char *md, unsigned int *size,
               const EVP_MD *type, ENGINE *impl);
#endif
