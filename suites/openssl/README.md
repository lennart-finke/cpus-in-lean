# OpenSSL verification tasks

Four targets from **OpenSSL 3.5.9**, ported from `verify/suites/ssl/` at `4e16d42d`: **13 open
obligations** about pinned i386 code on the [`x86_32` model](../../x86_32/README.md), against
independent mathematical specifications. Nothing is proved.

| Target | Obligations |
|---|---|
| [SHA-256 / SHA-224](Ssl/OpensslSha256/Statement.lean) | Streaming SHA-256, streaming SHA-224, SHA-256 compression (3) |
| [ChaCha20](Ssl/OpensslChacha20/Statement.lean) | Encryption with the specified 32-bit counter wrap (1) |
| [Poly1305](Ssl/OpensslPoly1305/Statement.lean) | Streaming authentication and context wiping, one-shot authentication, context size (3) |
| [X25519](Ssl/OpensslX25519/Statement.lean) | Field add/subtract/multiply/square, scalar multiplication, public-key derivation (6) |

Calls must return, restore callee-saved registers and change only the writable regions and their
stack, for any caller memory and any message length the algorithm allows (SHA-256: below 2^61 bytes;
one buffer at most 2^31 - 1). `Ssl/Harness.lean` lists every fixed choice. Covered: the portable C
code with the recorded flags. Not covered: assembly dispatch, TLS, providers, environments other than
ring 0 without paging or interrupts, side channels.

## Run

```sh
lake build
./verify.sh
./verify.sh --rebuild  # also rebuild C sources and require identical bytes and symbol addresses
./verify.sh --high     # also the slow checks: buffers above address 2^31, SHA-256 past 2^32 bits
```

The default (Lean, Python 3, offline) checks image bytes against pinned hashes and symbol maps,
builds, and runs finite examples and test vectors against the specifications; it proves nothing.

`--rebuild` also needs Clang and an i386 `objdump` (`CC`, `OBJDUMP`). It fetches missing files from
the pinned tag, checks `targets/*/SOURCES.sha256`, caches in ignored `targets/*/vendor/` (prefetch:
`python3 tools/fetch_sources.py`), writes only to caches and `out/`, and fails on any mismatch. Pins
come from Apple Clang 21.0.0 (`targets/*/image/compiler.txt`). One target: `python3 tools/build.py
openssl_chacha20`, then `out/openssl_chacha20/openssl_chacha20.dis`.

## Work on a task

Prove the proposition of a target's `Statement.lean` in a separate file, e.g.
`Ssl.OpensslPoly1305.Poly1305_ctx_size_correct` or `Ssl.OpensslChacha20.ChaCha20_ctr32_correct`,
leaving specification, image and tasks unchanged. Tasks are `def … : Prop`, not admitted theorems as
in the original, so importing one gives no evidence. No solutions or symbolic-execution framework included.

## Separation and provenance

- `Ssl/Spec/`, `Ssl/Bytes.lean`: specifications and encodings; no CPU imports.
- `Ssl/Harness.lean`: call harness from `verify/contract`, running the unchanged `X86.step`.
- `Ssl/Openssl*/`: the only copy of the machine code, plus tasks.
- `targets/`: build headers, stubs, hashes, symbol maps, per-target `PROVENANCE.md` and `NOTES.md`.
- `tools/`: image checking/rebuilding, with the linker and runtime from `verify`.
- `CheckMain.lean`: smoke checks of every entry point the tasks name.

Depends only on `../../x86_32` (not vice versa), with its own verify command and CI step. OpenSSL
files keep their Apache-2.0 license ([`LICENSE.openssl`](LICENSE.openssl)).
