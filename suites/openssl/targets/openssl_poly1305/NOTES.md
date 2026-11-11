# openssl_poly1305 — notes

Image: 1536 bytes at `0x100000`, 14 symbols (`image/openssl_poly1305.syms.json`; disassembly in
`image/openssl_poly1305.dis`). Functions linked, from `crypto/poly1305/poly1305.c`: the public cdecl API
`Poly1305_Init`, `Poly1305_Update`, `Poly1305_Final`, `Poly1305_ctx_size` (roots) and the static 32-bit-limb core
`poly1305_init`, `poly1305_blocks`, `poly1305_emit` plus `U8TOU32`, `U32TO8`; from `crypto/mem_clr.c`:
`OPENSSL_cleanse` and its `volatile` data pointer `memset_func`, a 4-byte `.data` word at `0x1005fc` that the
linker initialised to the address of the shim `memset` (`0x1005d0`); the call through it is the image's one
indirect call (`calll *%eax`). Nothing writes that word, and the statements require the whole image to be
unchanged after every call. From `tools/runtime/shim.c`: `memcpy`, `memset`. `halt` is at `0x1005f8`.

Which branch: `POLY1305_ASM` is undefined, so the C core is used and `ctx->func` is neither written nor
consulted. i386 Clang does not define `__SIZEOF_INT128__`, nothing defines `INT128_MAX`, so the `u64`-product
branch with `poly1305_internal { u32 h[5]; u32 r[4]; }` is compiled; the disassembly shows `mull`/`adcl`
64-bit arithmetic and no x87 or SSE instruction (`double opaque[24]` is only storage).

`struct poly1305_context` is 236 bytes on i386: `Poly1305_ctx_size` is `movl $0xec, %eax; retl`, and
`Poly1305_Final` passes the same size to `OPENSSL_cleanse`. The statements use only the size: the contents
are opaque bytes carried from one call to the next.

Stubs (`include/`, not upstream): `string.h` and `stdlib.h` (forward to `tools/runtime/shim.h`; `stdlib.h` is included
by `poly1305.c` but nothing from it is used), `openssl/crypto.h` (only the `OPENSSL_cleanse` prototype,
which both `poly1305.c` and `mem_clr.c` need). No `stubs.c`, no defines.

Excluded: the x86 assembly core (`poly1305-x86.pl`, `POLY1305_ASM`), the `__int128` branch, the EVP MAC
provider wrapper (`providers/implementations/macs/poly1305_prov.c`) and the ChaCha20-Poly1305 AEAD.

Statement (`Ssl/OpensslPoly1305/Statement.lean`): `Spec.Poly1305.poly1305` (RFC 8439 §2.5) of the concatenated
chunks, for every 32-byte key and arbitrary chunking of a message of any length (each chunk fits in memory
and in a C object; the message as a whole need not): `Poly1305_Init`, one
`Poly1305_Update` per chunk, `Poly1305_Final`, each call by an arbitrary caller with its own placement of the
buffers. `Init` and `Update` write only the 236-byte context; `Final` writes the tag and leaves the context
zeroed. `Poly1305_Init` does not initialise every field, and the statement does not need it to: whatever it
leaves is part of the opaque state. `Poly1305_Update` with `len = 0` reads nothing, so any pointer is allowed
then. `Poly1305_oneshot` is the single-chunk instance of `Poly1305_correct`
(`Poly1305_oneshot_of_correct`), not an independent result. `Poly1305_ctx_size()` returns 236.

Not stated: anything about the contents of the stack after `Final` (the wipe
covers the context only).
