# Provenance

Project: OpenSSL, tag `openssl-3.5.9` (https://github.com/openssl/openssl/tree/openssl-3.5.9), Apache License 2.0
([license](../../LICENSE.openssl)). The files below were fetched on 2026-10-21 from the raw-file URLs of that tag,
unmodified; `SOURCES.sha256` pins their contents and `tools/fetch_sources.py` re-fetches them on demand into the
ignored `vendor/` cache. The normal suite checks need no download.

* `vendor/LICENSE.txt` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/LICENSE.txt
* `vendor/crypto/mem_clr.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/mem_clr.c
* `vendor/crypto/sha/sha256.c` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/crypto/sha/sha256.c
* `vendor/include/crypto/md32_common.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/crypto/md32_common.h
* `vendor/include/crypto/sha.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/crypto/sha.h
* `vendor/include/internal/deprecated.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/internal/deprecated.h
* `vendor/include/internal/endian.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/internal/endian.h
* `vendor/include/openssl/e_os2.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/openssl/e_os2.h
* `vendor/include/openssl/macros.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/openssl/macros.h
* `vendor/include/openssl/sha.h` — https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/include/openssl/sha.h

Build: `python3 tools/build.py openssl_sha256` with the pinned toolchain and flags of [`BUILD.md`](../../BUILD.md) and
`-Iinclude -Ivendor/include`; sources `vendor/crypto/sha/sha256.c` and `vendor/crypto/mem_clr.c`. No defines:
without `SHA256_ASM` the file compiles its portable `static sha256_block_data_order`. The Configure-generated headers
(`openssl/configuration.h`, `opensslconf.h`, `opensslv.h`) and `openssl/crypto.h` are minimal stubs in
`include/` (see `NOTES.md`). Roots: `SHA256_Init`, `SHA256_Update`, `SHA256_Final`, `SHA256_Transform`,
`SHA224_Init`, `SHA224_Update`, `SHA224_Final`.
