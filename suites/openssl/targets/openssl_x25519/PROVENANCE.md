# Provenance

Project: OpenSSL, tag `openssl-3.5.9` (https://github.com/openssl/openssl/tree/openssl-3.5.9), Apache License 2.0
([license](../../LICENSE.openssl)). The files below were fetched on 2026-10-21 from the raw-file URLs of that tag,
unmodified; `SOURCES.sha256` pins their contents and `tools/fetch_sources.py` re-fetches them on demand into the
ignored `vendor/` cache. The normal suite checks need no download.

* `vendor/LICENSE.txt` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/LICENSE.txt
* `vendor/crypto/ec/curve25519.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/ec/curve25519.c
* `vendor/crypto/mem_clr.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/mem_clr.c
* `vendor/include/internal/numbers.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/internal/numbers.h

Consulted (not vendored; the stub headers in `include/` reproduce the few macro values and prototypes
curve25519.c needs from them): `include/crypto/ecx.h` (`ED25519_KEYLEN 32` etc.), `include/openssl/sha.h`
(`SHA512_DIGEST_LENGTH 64`), `include/openssl/obj_mac.h` (`SN_sha512 "SHA512"`), `include/openssl/crypto.h.in`
(the `OPENSSL_cleanse`/`CRYPTO_memcmp` prototypes and the `CRYPTO_memcmp` contract), `crypto/cpuid.c` (the
`CRYPTO_memcmp` body copied verbatim into `stubs.c`).

Build: `python3 tools/build.py openssl_x25519` with the pinned toolchain and flags of [`BUILD.md`](../../BUILD.md) and
`-Ivendor/include -Iinclude`, sources `vendor/crypto/ec/curve25519.c`, `vendor/crypto/mem_clr.c`, `stubs.c`.
No defines: on i386 Clang `numbers.h` does not define `INT128_MAX` (`__SIZEOF_INT128__` is unset) and
`X25519_ASM` is not given, so the file compiles its reference base-2^25.5 (`int32_t[10]`) implementation.
Roots: `ossl_x25519`, `ossl_x25519_public_from_private`.
