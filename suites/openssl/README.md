# OpenSSL verification tasks

Four targets from **OpenSSL 3.5.9**, ported from `verify/suites/ssl/` at commit `4e16d42d`.
The suite has **13 open correctness obligations** about pinned i386 machine code running on
the [`x86_32` model](../../x86_32/README.md). The specifications are independent mathematical
definitions of the algorithms. This is a task suite, not a claim that the implementations have
been proved correct.

| Target | Obligations |
|---|---|
| [SHA-256 / SHA-224](Ssl/OpensslSha256/Statement.lean) | Streaming SHA-256, streaming SHA-224, SHA-256 compression (3) |
| [ChaCha20](Ssl/OpensslChacha20/Statement.lean) | Encryption with the specified 32-bit counter wrap (1) |
| [Poly1305](Ssl/OpensslPoly1305/Statement.lean) | Streaming authentication and context wiping, one-shot authentication, context size (3) |
| [X25519](Ssl/OpensslX25519/Statement.lean) | Field add/subtract/multiply/square, scalar multiplication, public-key derivation (6) |

Each obligation retains the original inputs, preconditions and postconditions. Calls must return,
restore callee-saved registers and preserve memory outside the stated writable regions and the
callee's stack area. Streaming messages are bounded by 1 MiB. The statements specify the portable
C implementations compiled with the recorded flags; they do not cover OpenSSL's assembly dispatch,
TLS, providers, arbitrary memory layouts, or side-channel properties.

## Run

From this directory:

```sh
lake build
./verify.sh
./verify.sh --rebuild  # also rebuild C sources and require identical bytes and symbol addresses
```

The default check needs Lean (the repository toolchain) and Python 3, with no network access.
It verifies the Lean-embedded image bytes against pinned hashes and symbol maps, checks any
cached sources, builds the suite and runs finite
examples on the CPU model against the specifications. The specifications also contain Lean-checked
standard test vectors. These checks do not prove the open obligations.

`--rebuild` additionally needs Clang and an i386-capable `objdump` (`CC` and `OBJDUMP` can override
them). It fetches missing upstream files from the pinned OpenSSL tag and checks every download
against `targets/*/SOURCES.sha256` before using it. Sources are cached in ignored
`targets/*/vendor/` directories; subsequent rebuilds can use that cache offline. They can also be
prefetched with `python3 tools/fetch_sources.py`.

The pins were produced by Apple Clang 21.0.0; exact compiler details are recorded in each
`targets/*/image/compiler.txt`. Another compiler may produce different bytes. Rebuilds write only
to ignored source caches and `out/` directories and fail on a mismatch; they never update the pinned task images.
To inspect one rebuilt target, run `python3 tools/build.py openssl_chacha20` and read
`out/openssl_chacha20/openssl_chacha20.dis`.

## Work on a task

Import the target's `Statement.lean` and prove its named proposition in a separate solution file.
For example, a solution to the context-size task has the type
`Ssl.OpensslPoly1305.Poly1305_ctx_size_correct`; a complete ChaCha20 solution has the type
`Ssl.OpensslChacha20.ChaCha20_ctr32_correct`. Both include all input quantifiers and preconditions.
Keep the specification, image and task definitions fixed while developing the proof.

The original suite expressed tasks as admitted theorems. Here they are `def … : Prop` declarations:
importing a task supplies its statement, not evidence of its truth. This port includes no solution
proofs or general symbolic-execution framework. The original `Ssl` namespace is retained.

## Separation and provenance

- `Ssl/Spec/` and `Ssl/Bytes.lean`: algorithm specifications and byte encodings; no CPU imports.
- `Ssl/Harness.lean`: the suite's small call/reachability harness, adapted from `verify/contract`.
  Execution uses the unchanged `X86.step`; there is no alternate emulator.
- `Ssl/Openssl*/`: the sole stored copy of the machine-code bytes, plus task definitions.
- `targets/`: minimal build headers, documented stubs, source/image hashes and symbol maps.
  Each target's `PROVENANCE.md` and `NOTES.md` records its configuration. Upstream sources are
  downloaded on demand; raw binaries and disassembly are produced under `out/` when rebuilding.
- `tools/`: local image checking/rebuilding support, including the linker and runtime from `verify`.
- `CheckMain.lean`: executable smoke checks, including all entry points named by the tasks.

This package depends only on `../../x86_32`. The CPU packages do not import or depend on it;
the suite has its own verification command and CI step. Upstream OpenSSL files retain their
Apache-2.0 license, included once as [`LICENSE.openssl`](LICENSE.openssl).
