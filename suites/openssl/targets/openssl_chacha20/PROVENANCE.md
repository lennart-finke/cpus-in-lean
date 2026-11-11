# Provenance

Project: OpenSSL, tag `openssl-3.5.9` (https://github.com/openssl/openssl/tree/openssl-3.5.9), Apache License 2.0
([license](../../LICENSE.openssl)). The files below were fetched on 2026-10-21 from the raw-file URLs of that tag,
unmodified; `SOURCES.sha256` pins their contents and `tools/fetch_sources.py` re-fetches them on demand into the
ignored `vendor/` cache. The normal suite checks need no download.

* `vendor/LICENSE.txt` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/LICENSE.txt
* `vendor/crypto/chacha/chacha_enc.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/chacha/chacha_enc.c
* `vendor/include/crypto/chacha.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/crypto/chacha.h
* `vendor/include/crypto/ctype.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/crypto/ctype.h
* `vendor/include/internal/endian.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/internal/endian.h

Build: `python3 tools/build.py openssl_chacha20` with the pinned toolchain and flags of [`BUILD.md`](../../BUILD.md) and
`-Ivendor/include -Iinclude`. No defines: without `CHACHA_ASM`/`INCLUDE_C_CHACHA20` the file defines the portable
`ChaCha20_ctr32` directly. Root: `ChaCha20_ctr32`.
