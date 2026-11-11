# Provenance

Project: OpenSSL, tag `openssl-3.5.9` (https://github.com/openssl/openssl/tree/openssl-3.5.9), Apache License 2.0
([license](../../LICENSE.openssl)). The files below were fetched on 2026-10-21 from the raw-file URLs of that tag,
unmodified; `SOURCES.sha256` pins their contents and `tools/fetch_sources.py` re-fetches them on demand into the
ignored `vendor/` cache. The normal suite checks need no download.

* `vendor/LICENSE.txt` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/LICENSE.txt
* `vendor/crypto/mem_clr.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/mem_clr.c
* `vendor/crypto/poly1305/poly1305.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/poly1305/poly1305.c
* `vendor/include/crypto/poly1305.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/crypto/poly1305.h

Build: `python3 tools/build.py openssl_poly1305` with the pinned toolchain and flags of [`BUILD.md`](../../BUILD.md) and
`-Ivendor/include -Iinclude`. No defines: `POLY1305_ASM` stays undefined, so the file's portable C core is
compiled, and since i386 Clang defines neither `__SIZEOF_INT128__` nor `INT128_MAX`, the
`#if defined(INT64_MAX) && defined(INT128_MAX)` branch is skipped in favour of the 32-bit-limb / 64-bit-product
one. Roots: `Poly1305_Init`, `Poly1305_Update`, `Poly1305_Final`, `Poly1305_ctx_size`.
