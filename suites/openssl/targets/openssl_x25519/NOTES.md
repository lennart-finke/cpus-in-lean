# openssl_x25519 — notes

Image: 47024 bytes at `0x100000`, 43 symbols (`image/openssl_x25519.syms.json`; disassembly in
`image/openssl_x25519.dis`). Functions linked (all from `crypto/ec/curve25519.c` unless noted): the roots
`ossl_x25519` and `ossl_x25519_public_from_private`; `x25519_scalar_mult` → `x25519_scalar_mult_generic` (the
Montgomery ladder of the reference base-2^25.5 implementation, `typedef int32_t fe[10]`); the field helpers
`fe_frombytes`, `fe_tobytes`, `fe_add`, `fe_sub`, `fe_mul`, `fe_sq`, `fe_sq2`, `fe_invert`, `fe_neg`, `fe_cmov`,
`fe_cswap`, `fe_mul121666`, `fe_copy`, `fe_0`, `fe_1`, `load_3`, `load_4`; the Edwards-curve code behind
`ossl_x25519_public_from_private`: `ge_scalarmult_base`, `table_select`, `cmov`, `equal`, `negative`, `ge_madd`,
`ge_p2_dbl`, `ge_p3_dbl`, `ge_p1p1_to_p2`, `ge_p1p1_to_p3`, `ge_p3_to_p2`, `ge_p3_0`, `ge_precomp_0` and the
30720-byte precomputed table `k25519Precomp` (`ge_precomp[32][8]`, 3·40 bytes per entry) plus the 32-byte
`ossl_x25519.kZeros`; `OPENSSL_cleanse` (`crypto/mem_clr.c`; it calls `memset` through the volatile data
pointer `memset_func` at `0x10b7ac`, the image's one indirect call); `CRYPTO_memcmp` (`stubs.c`); `memcpy`,
`memmove`, `memset` (`tools/runtime/shim.c`).

Roots: `ossl_x25519`, `ossl_x25519_public_from_private`, plain cdecl. Everything else is reachable `static`
code that stays out of line because of `-fno-inline-functions`, so `Image.sym_fe_mul` etc. exist.

Calling convention of the `static` field functions (matters for Statement A), as the pinned disassembly shows
it: the first two arguments in `ecx`/`edx`, the third on the stack, popped by the caller.
`fe_add` (`0x100510`): `movl 0x8(%esp), %eax` after one push fetches `g`; each limb is
`movl (%eax)` / `addl (%edx)` / `movl …, (%ecx)`, so `h` = `ecx`, `f` = `edx`. `fe_sub` (`0x100570`):
`movl (%edx)` / `subl (%eax)` / store to `(%ecx)`: `f − g`. `fe_mul` (`0x100c20`) saves `ecx` as the
output pointer and reads `f` from `(%edx)…0x24(%edx)`; `fe_sq` (`0x102360`) takes `ecx`, `edx` only. Call
sites agree, e.g. `movl %ebx, %ecx; movl %esi, %edx; pushl %ebx; calll fe_mul; addl $0x4, %esp` in `fe_invert`.
This is the compiler's choice for these bytes, not an ABI; the statements are about these bytes.

Aliasing: the ladder calls the field functions with the output equal to an input (`fe_mul(z2, z2, tmp1)`,
`fe_sub(tmp1, tmp1, tmp0)`, `fe_sq(t1, t1)` in `fe_invert`), so Statement A allows `h = f` and `h = g` and
arbitrary overlap between the two inputs. `fe_add`/`fe_sub` store limb `i` before reading limb `i+1`, which is
why partial overlap of the output with an input is excluded.

Stubs (`include/`, not upstream): `string.h` (→ `tools/runtime/shim.h`), `internal/deprecated.h` (empty),
`ec_local.h` (empty; upstream pulls `openssl/ec.h`, `bn.h`, refcounts through it, nothing curve25519.c
uses), `openssl/crypto.h` (prototypes of `OPENSSL_cleanse`, `CRYPTO_memcmp`), `openssl/sha.h`
(`SHA512_DIGEST_LENGTH 64`), `openssl/evp.h` (opaque `EVP_MD`, `EVP_MD_CTX`, `OSSL_LIB_CTX`, `ENGINE`;
prototypes of `EVP_MD_fetch/free`, `EVP_MD_CTX_new/free`, `EVP_DigestInit_ex/Update/Final_ex`,
`EVP_Digest`; `SN_sha512 "SHA512"`), `crypto/ecx.h` (`X25519_KEYLEN`, `ED25519_KEYLEN` … as upstream, and
the prototypes of the six `ossl_*` functions the file defines). `stubs.c`: `CRYPTO_memcmp`, the body of
upstream `crypto/cpuid.c` copied verbatim (the `x |= a[i] ^ b[i]` loop over volatile bytes; returns 0 iff the
`len` bytes are equal) — upstream's file also carries the CPU-feature probing and cannot be linked
freestanding. No defines.

Excluded: the Ed25519 half of the file (`ossl_ed25519_sign`, `ossl_ed25519_verify`,
`ossl_ed25519_public_from_private`, `ossl_ed25519_pubkey_verify`, `sc_muladd`, `x25519_sc_reduce`,
`ge_double_scalarmult_vartime`, `ge_frombytes_vartime`, `fe_pow22523`, …) is compiled but not reachable from
the roots, so the linker drops it together with its EVP calls (the stub `openssl/evp.h` gives prototypes
only; no SHA-512 is linked). Also excluded: the x86_64 `X25519_ASM` base-2^64 path, the `INT128_MAX`
base-2^51 path (`fe51`, not compiled on i386), and the provider/EVP key-exchange wrappers
(`providers/implementations/exchange/ecx_exch.c`).

Statement A: the limb value is `Σ toInt32(t[i])·2^off(i)` over `Int` (`feValI`). Bounds are copied from the
function comments of `curve25519.c`: `fe_mul`/`fe_sq`: "|f| bounded by 1.65*2^26,1.65*2^25,…" /
"|h| bounded by 1.01*2^25,1.01*2^24,…"; `fe_add`/`fe_sub`: "|f| bounded by 1.1*2^25,1.1*2^24,…" /
"|h| bounded by 1.1*2^26,1.1*2^25,…". `Bounded num e v` states `|t[i]|·100 ≤ num·2^(e - i%2)`; none of
the bounds is an integer, so `≤` and `<` coincide. The value claims are modulo `p` via `Int.emod`; the limb
vectors are not required to be canonical (as upstream). The executable checks run all four functions with
every limb at its bound and with every permitted aliasing. `fe_sq2`, `fe_mul121666`, `fe_invert`, `fe_neg`,
`fe_cswap` etc. also survive but are not stated.

Statement B: `ossl_x25519(out, k, u)` writes `Spec.X25519.x25519 k u` (RFC 7748 §5 over `Nat`), returns
`eax = 1` iff the result is not all-zero, `0` otherwise (`CRYPTO_memcmp(kZeros, out, 32) != 0`), and writes only
`out[0..32)`; the ladder's scratch and the cleansed scalar copy are on the callee's stack.
`ossl_x25519_public_from_private(out, k)` writes `Spec.X25519.x25519 k (9 ∥ 0^31)`: upstream computes `e·B` on
the twisted Edwards curve with `ge_scalarmult_base` and maps it to the Montgomery u-coordinate `(Z+Y)/(Z-Y)`;
the statement is the RFC one, so a proof needs the birational equivalence between the two curves and the
correctness of the table. In both, `out` may be one of the input buffers.

The specification is the algorithm of RFC 7748, not scalar multiplication on the curve defined
independently; see `Ssl/Spec/X25519.lean`.

Not stated: that the scalar copy on the stack is cleansed (the statements say nothing about the stack below
the entry stack pointer), and any timing property. (The executable checks happen to take the same number of
instructions for every input tried; that is an observation, not a claim.)
