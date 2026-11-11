# openssl_sha256 — notes

Image: 4944 bytes at `0x100000`, 14 symbols (`image/openssl_sha256.syms.json`; disassembly in
`image/openssl_sha256.dis`). Functions linked: `SHA224_Init`, `SHA256_Init`, `SHA224_Update` (calls
`SHA256_Update` and returns 1), `SHA224_Final` (a jump to `SHA256_Final`) and the static
`sha256_block_data_order` with its table `K256` (`crypto/sha/sha256.c`); `SHA256_Update`, `SHA256_Transform`,
`SHA256_Final` (the `HASH_UPDATE`/`HASH_TRANSFORM`/`HASH_FINAL` template of `include/crypto/md32_common.h`,
included by `sha256.c`); `OPENSSL_cleanse` and its volatile pointer `memset_func` (`crypto/mem_clr.c`; the word
at `0x10134c` holds the address of the shim `memset`, and the call through it is the image's one indirect
call); `memcpy`/`memset` from `tools/runtime/shim.c`. `ossl_sha256_192_init` is compiled but unreachable from the
roots, so the linker drops it. Roots: the seven public functions, all cdecl.
`sha256_block_data_order(ctx, in, num)` is static (the compiler passes `ctx` in `ecx`, `in` in `edx`, `num` on
the stack); it is reached only through the roots and no task calls it directly.

`SHA256_CTX` on IA-32 (`vendor/include/openssl/sha.h`): `SHA_LONG h[8]` at 0, `Nl` at 0x20, `Nh` at 0x24,
`SHA_LONG data[16]` at 0x28 (64 bytes), `unsigned num` at 0x68, `md_len` at 0x6c; 112 bytes. The streaming
statements use only the size and, for the wipe, the offsets of `data` and `num`.

Stubs (`include/`, not upstream): `string.h` and `stdlib.h` (forward to `tools/runtime/shim.h`; `sha256.c` uses
nothing from `stdlib.h`), `inttypes.h` (Clang's resource-dir copy `#include_next`s a hosted header; the stub
is just `<stdint.h>`), `sys/types.h` (`ssize_t` for the vendored `e_os2.h`), `openssl/opensslconf.h` (the
two includes upstream's generated file consists of), `openssl/configuration.h` (`OPENSSL_CONFIGURED_API
30500`, the 3.5 default; no `OPENSSL_NO_*`), `openssl/opensslv.h` (version numbers 3.5.9 for
`OPENSSL_API_LEVEL`), `openssl/crypto.h` (only the `OPENSSL_cleanse` prototype; the real header drags in the
whole public API). `openssl/e_os2.h`, `openssl/macros.h` and `internal/deprecated.h` are vendored unchanged.
No `stubs.c`, no `-D` defines.

Excluded: the one-shot `SHA256()`/`SHA224()` (`crypto/sha/sha1_one.c`, an `EVP_Q_digest` call), the x86
assembly `sha256_block_data_order` (`sha256-586.pl`; not built, no `SHA256_ASM`), `ossl_sha256_192_init`
(unreachable), the EVP/provider digest wrappers.

Statements (`Ssl/OpensslSha256/Statement.lean`, spec `Ssl.Spec.Sha256`), each call by an arbitrary caller with
its own placement of the buffers: (a) `SHA256_Init(ctx)`, then `SHA256_Update(ctx, chunk, len)` per chunk of an
arbitrary chunking of a message of at most 2^20 bytes (each writes only the 112-byte context and returns 1),
then `SHA256_Final(out, ctx)` returns 1 and writes `Spec.sha256 (chunks.flatten)` at `out`; (b) the same with
`SHA224_*` and `Spec.sha224` (28 bytes); (c) `SHA256_Transform(ctx, block)` replaces `h[8]` by
`Spec.compress h block`, writing only those 32 bytes. An `Update` with `len = 0` reads nothing, so any pointer
is allowed then.

Wipe: `HASH_FINAL` does `c->num = 0; OPENSSL_cleanse(p, HASH_CBLOCK)` with `p = c->data`, i.e. it zeroes the
64-byte block buffer and `num` — offsets `[40, 108)` — and nothing else. `h` (the final hash words), `Nl`/`Nh`
(the bit count) and `md_len` survive the call. The statement says exactly that:
`bytesAt m3 (ctx + 40) 68 = List.replicate 68 0`, not a wipe of all 112 bytes (which would be false).

Not stated: messages above 2^20 bytes. The bound keeps `Nh` at 0, so the carry from `Nl` into `Nh` is code
the statements do not exercise. `SHA256_Final` returns 1 for `md_len` ∈ {28, 32}, the only values reachable
from `SHA256_Init`/`SHA224_Init`; its `return 0` branch for other values is likewise not exercised.
