# openssl_chacha20 — notes

Image: 1072 bytes at `0x100000`, 4 symbols (`image/openssl_chacha20.syms.json`; disassembly in
`image/openssl_chacha20.dis`). Functions linked: `ChaCha20_ctr32` and the static `chacha20_core`
(`crypto/chacha/chacha_enc.c`), `memcpy` (`tools/runtime/shim.c`), and the `halt` sentinel. Root:
`ChaCha20_ctr32`, plain cdecl. `chacha20_core` is reached only through it (the compiler passes its two
pointers in `ecx`/`edx`); no task calls it directly.

Stubs (`include/`, not upstream): `string.h` (forwards to `tools/runtime/shim.h`), `openssl/e_os2.h` (empty; only
pulled in by the vendored `crypto/ctype.h`, which `chacha_enc.c` includes for the `ossl_toascii(c) (c)` macro
used to spell the `expand 32-byte k` constants). The RISC-V inline-asm `ROTATE` is behind `__riscv_zbb`, so
the portable rotate is compiled. No `stubs.c`, no defines.

Excluded: the x86 assembly `ChaCha20_ctr32` (`chacha-x86.pl`), the EVP cipher wrappers
(`providers/implementations/ciphers/cipher_chacha20*.c`) and the Poly1305 AEAD composition.

Statement (`Ssl/OpensslChacha20/Statement.lean`): `Spec.Chacha.crypt` (RFC 8439 §2.1–2.4) applied to the
matrix `sigma ++ key ++ counter` that the function assembles, for every caller, every placement of the
buffers, every key (8 words), counter/nonce (4 words) and input that fits in memory and in a C object
(at most 2^31 - 1 bytes). The output may be the
input buffer (in-place encryption). The counter is 32-bit and wraps modulo 2^32, exactly
`Spec.Chacha.advance`; the upstream comment says callers wanting a wider counter split the call. RFC 8439
does not define the wrap; it is this function's behaviour, written into the specification. With `len = 0`
nothing is read or written, so the statement allows any pointers then.

Not stated: partially overlapping `out`/`inp`. The executable checks run inputs up to 200 bytes; nothing
in the function depends on the length beyond the block loop and the 32-bit counter, whose wrap is checked.
