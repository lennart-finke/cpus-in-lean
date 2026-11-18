# libsodium verification tasks

The `sodium/codecs.c` and `sodium/utils.c` helpers of **libsodium 1.0.22** (keys, tags, padding).
**14 open tasks** (no proofs) about their pinned i386 code on the [`x86_32` model](../../x86_32/README.md):

| Function | What it computes | The same steps whatever the secret |
|---|---|---|
| `sodium_bin2hex` | `bin2hex_correct`: lower-case hex and a NUL | `bin2hex_constant_time` |
| `sodium_hex2bin` | `hex2bin_inverts`: the bytes of their hex digits | `hex2bin_constant_time` |
| `sodium_bin2base64` | `bin2base64_correct`: RFC 4648, all four variants | `bin2base64_constant_time` |
| `sodium_base642bin` | `base642bin_inverts`: the bytes of their encoding | `base642bin_constant_time` |
| `sodium_memcmp` | `memcmp_correct`: 0 exactly on equal buffers | `memcmp_constant_time` |
| `sodium_memzero` | `memzero_correct`: every byte zero afterwards | |
| `sodium_pad` | `pad_correct`: ISO/IEC 7816-4 padding | |
| `sodium_unpad` | `unpad_correct`: the data length, or -1 exactly on invalid padding | `unpad_constant_time` |

Tasks: [`Sodium/Utils/Statement.lean`](Sodium/Utils/Statement.lean); specification (from the
standards, no imports): [`Sodium/Spec/Utils.lean`](Sodium/Spec/Utils.lean). Each holds for every
caller and buffer placement; a call returns, restores callee-saved registers and writes only the
stated bytes and its stack. Constant time: two calls differing only in buffer contents execute the
same instruction addresses, in the compiled code (where a compiler may add branches or drop a wipe).

## Limits

- Constant time covers control flow only, not data addresses, caches or timing.
- Decoders get no `ignore` set or end pointer; their constant-time tasks cover valid encodings.
- No `HAVE_*` macros (`-DCONFIGURED=1`): `sodium_memzero`/`sodium_memcmp` are the portable `volatile`
  loops, not `explicit_bzero`/`memset_s`.
- `sodium_pad` holds for block sizes up to 2^24: with 32-bit `size_t`,
  `((i ^ xpadlen) - 1U) >> ((sizeof(size_t) - 1) * CHAR_BIT)` misfires once `i ^ xpadlen` exceeds 2^24.
  On the model, 2^24 + 1 leaves non-zero padding; at `0x01000010` `sodium_unpad` rejects the result.
- Length out-pointers of `sodium_hex2bin`, `sodium_base642bin`, `sodium_pad` are non-null (address 0
  is ordinary memory in the model).

## Run

```sh
python3 ../suite.py                # pins, cached sources, lake build, 3952 runs on the model (offline)
python3 ../suite.py build          # also rebuild the image with the pinned LLVM and compare
```

`build` fetches LLVM and the 7 files in `targets/sodium_utils/SOURCES.sha256`, checking each hash.

## What is here

Harness, test support and toolchain come from the [OpenSSL suite](../openssl/README.md) via [`../suite.py`](../suite.py).

- `Sodium/Spec/`, `Sodium/Utils/Statement.lean`: specification, tasks; `Sodium/Utils/Image.lean`: the bytes.
- `SodiumCheck.lean`: 13 lengths in four placements, each run checked against its task and its
  addresses against a run on other contents.
- `targets/sodium_utils/`: build description, hashes, pins, `include/libc.h` with six one-line headers,
  `libc.c` (`errno`, `memchr`, `strchr`, a faulting `sodium_misuse`).
