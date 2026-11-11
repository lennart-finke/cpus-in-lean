/* Stub <openssl/sha.h>: curve25519.c only uses SHA512_DIGEST_LENGTH (value as upstream include/openssl/sha.h)
   for the Ed25519 buffers; the SHA-512 computation itself goes through EVP (openssl/evp.h stub). Not upstream. */
#ifndef SSL_STUB_OPENSSL_SHA_H
#define SSL_STUB_OPENSSL_SHA_H
#define SHA512_DIGEST_LENGTH 64
#endif
