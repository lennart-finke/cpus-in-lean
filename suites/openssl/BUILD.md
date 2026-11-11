# How the task images are built

A task is a statement about specific bytes. This file records where those bytes come from, why each
build option is there, and what has been done to make the build repeatable by someone else.

## Toolchain

Compiler, assembler, linker and binutils are the **official LLVM 23.1.5 release** published at
https://github.com/llvm/llvm-project/releases/tag/llvmorg-23.1.5. `tools/toolchain.py` downloads the
archive for the host (macOS arm64, Linux x86-64, Linux arm64), checks it against the SHA-256 pinned
in that file and unpacks `clang`, `ld.lld`, `llvm-objcopy`, `llvm-nm` and `llvm-objdump` into the
ignored `.toolchain/` directory. No other compiler can be selected.

## Sources

OpenSSL 3.5.9, unmodified, fetched from the upstream tag and pinned per file in
`targets/*/SOURCES.sha256`. Around them, per target (`targets/*/NOTES.md` lists them):

* stub headers in `targets/*/include/` standing in for OpenSSL's generated configuration headers
  and for the parts of its public headers that drag in the whole library;
* `tools/runtime/shim.c`: byte-loop `memcpy`/`memmove`/`memset` and the 64-bit division helpers a
  freestanding i386 build needs. These are part of the images and of what the tasks verify;
* `tools/runtime/entry.S`: the one-instruction `halt` sentinel calls return to;
* `targets/openssl_x25519/stubs.c`: `CRYPTO_memcmp`, copied from upstream `crypto/cpuid.c`, whose
  file cannot be linked freestanding.

## Compiler flags

| Flags | Why |
|---|---|
| `--target=i386-unknown-none-elf -march=i686` | 32-bit x86 without an operating system; i686 is the baseline of current 32-bit distributions (CMOV, no SSE) |
| `-O3 -fomit-frame-pointer` | OpenSSL's own release flags for `linux-x86` (`Configurations/10-main.conf`: `-O3` from `linux-generic32`, `-fomit-frame-pointer` added by `linux-x86`). Upstream also passes `-m32`, which the target implies, and `-DL_ENDIAN`, which the compiled files use only for a consistency check (byte order comes from the compiler's `__BYTE_ORDER__`) |
| `-ffreestanding -fno-builtin` | there is no C library: calls to `memcpy` and friends go to the shim instead of being expanded by the compiler |
| `-fno-pic` | the image is linked at a fixed address |
| `-fno-stack-protector` | a canary needs runtime support the image does not have |
| `-fno-asynchronous-unwind-tables -fno-unwind-tables` | no unwinder; keeps `.eh_frame` out of the image |
| `-ffunction-sections -fdata-sections` | lets the linker drop what the roots do not reach (the Ed25519 half of `curve25519.c`, for instance) |
| `-fno-inline-functions` | **the one deviation made for the tasks**: it keeps `fe_mul`, `fe_sq`, `fe_add` and `fe_sub` as callable functions, which the field-level X25519 tasks are about. It applies to all four images so that they share one build |

Nothing is defined on the command line. Which code paths that selects (no assembly, no `__int128`)
is recorded in each target's `PROVENANCE.md`.

What this build is **not**: it is not the code a default x86 build of OpenSSL runs for SHA-256,
ChaCha20 or Poly1305, where perlasm implementations replace these C functions. It is the portable C
that `no-asm` builds and unlisted platforms use, compiled for i686. For X25519, 32-bit x86 has no
assembly implementation and this C path is the one in use.

## Linking

`ld.lld -m elf_i386 -static --gc-sections --build-id=none -T tools/image.ld -u <root>…`, then
`llvm-objcopy -O binary`. The linker script places `.text`, `.rodata` and `.data` contiguously from
`0x100000` and rejects any `.bss`: nothing clears memory for a flat image, and the tasks hold for
arbitrary memory contents. Symbol addresses are read from the linked ELF with `llvm-nm`.

## What is pinned

For every target, `targets/<target>/image/SHA256SUMS` pins the image bytes, the symbol table, the
disassembly (`llvm-objdump -d`) and the build record (`build.txt`: compiler version line and the
exact commands). The bytes themselves are stored once, in `Ssl/<Module>/Image.lean`.

    python3 tools/build.py            # rebuild and compare with every pin; writes only out/
    python3 tools/build.py --pin      # regenerate the pins: redefines the tasks
    tools/rebuild_linux.sh            # the same comparison inside a Linux container

## Reproducibility

The pins were produced on macOS/arm64. A rebuild in a `python:3.13-slim` container on Linux/arm64
with that platform's LLVM 23.1.5 release reproduced all four images, symbol tables and
disassemblies byte for byte. CI repeats the rebuild on Linux/x86-64 on every run
(`verify.sh --rebuild`).

## Evidence that the bytes behave as the model says

Independent of any proof, and none of it part of the trusted base:

* `tools/hw.py` runs the four images on the Lean model and on QEMU and requires identical results;
  `tools/hw.py bundle` packages the same runs for a real machine (see that file).
* `tools/encodings.py` lists the instruction forms the images execute (`hw/encodings.txt`) and
  checks that the model's differential fuzzer against QEMU covers every one of them.
