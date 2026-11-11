# libsodium verification tasks

One target from **libsodium 1.0.22**: the helpers of `sodium/codecs.c` and `sodium/utils.c` that
applications use on keys, authentication tags and padded plaintexts. The suite has **14 open
tasks** about their pinned i386 machine code running on the
[`x86_32` model](../../x86_32/README.md). There are statements and no proofs.

| Function | What it computes | The same steps whatever the secret |
|---|---|---|
| `sodium_bin2hex` | `bin2hex_correct`: lower-case hexadecimal and a NUL | `bin2hex_constant_time` |
| `sodium_hex2bin` | `hex2bin_inverts`: gives back the bytes of their hexadecimal digits | `hex2bin_constant_time` |
| `sodium_bin2base64` | `bin2base64_correct`: RFC 4648, all four variants | `bin2base64_constant_time` |
| `sodium_base642bin` | `base642bin_inverts`: gives back the bytes of their encoding | `base642bin_constant_time` |
| `sodium_memcmp` | `memcmp_correct`: 0 exactly on equal buffers | `memcmp_constant_time` |
| `sodium_memzero` | `memzero_correct`: every byte is zero afterwards | |
| `sodium_pad` | `pad_correct`: ISO/IEC 7816-4 padding | |
| `sodium_unpad` | `unpad_correct`: the data length, or -1 exactly on an invalid padding | `unpad_constant_time` |

The tasks are in [`Sodium/Utils/Statement.lean`](Sodium/Utils/Statement.lean), the specification,
written from the standards and importing nothing, in [`Sodium/Spec/Utils.lean`](Sodium/Spec/Utils.lean).
Each task holds for every caller and every placement of the buffers; a call must return, restore
the callee-saved registers and write nothing outside the stated bytes and its own stack.

A constant-time task says that two calls with the same pointers and lengths and different buffer
contents execute the same number of instructions at the same addresses. It is a statement about the
compiled code: a compiler may turn branch-free C into branches, and may delete a wipe it considers
dead.

## Limits

- The constant-time tasks are about the instruction addresses of the architectural model. They say
  the control flow does not depend on the secret, and nothing about data addresses, caches or
  instruction timing.
- The decoders are called without an `ignore` set and without an end pointer. Their constant-time
  tasks are about valid encodings: a decoder stops at the first invalid character by design.
- The image is built with `-DCONFIGURED=1` and none of libsodium's `HAVE_*` macros, so
  `sodium_memzero` and `sodium_memcmp` are the portable `volatile` loops. A platform build may call
  `explicit_bzero` or `memset_s` instead, which these tasks do not cover.
- `sodium_pad` is stated for block sizes up to 2^24, the largest bound for which it holds. With a
  32-bit `size_t` its test for the position of the `0x80` byte,
  `((i ^ xpadlen) - 1U) >> ((sizeof(size_t) - 1) * CHAR_BIT)`, is no longer zero at other positions
  once `i ^ xpadlen` exceeds 2^24. Run on the model, the image pads correctly at block size 2^24
  and leaves non-zero padding bytes at 2^24 + 1; at `0x01000010` `sodium_unpad` rejects the result.
- The pointers through which `sodium_hex2bin`, `sodium_base642bin` and `sodium_pad` store a length
  are not null: the functions skip the store for a null pointer, and address 0 is ordinary memory
  in the model.

## Run

```sh
python3 ../suite.py                # pins, cached sources, lake build, 3952 runs on the model
python3 ../suite.py build          # also rebuild the image with the pinned LLVM and compare
```

The first command needs Lean and Python 3 and no network. The second fetches the pinned LLVM
release and the 7 libsodium files named in `targets/sodium_utils/SOURCES.sha256`, each checked
against its hash.

## What is here

This suite adds only what is specific to libsodium. The call harness (`Ssl.Harness`), the test
support, the compiler, flags, runtime, linker script and image format are the
[OpenSSL suite's](../openssl/README.md), used through [`../suite.py`](../suite.py).

- `Sodium/Spec/`, `Sodium/Utils/Statement.lean`: specification and tasks. `Sodium/Utils/Image.lean`
  holds the machine-code bytes.
- `SodiumCheck.lean`: 13 lengths in four memory placements. Every run is checked against its task,
  and its instruction addresses against those of a run on other buffer contents.
- `targets/sodium_utils/`: the build description, source hashes and image pins, and what is not
  upstream: `include/libc.h` with six one-line hosted headers that include it, and `libc.c`
  (`errno`, `memchr`, `strchr`, and a `sodium_misuse` that faults where libsodium's aborts).
