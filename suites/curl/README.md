# curl verification tasks

One target from **curl 8.23.0**: `Curl_cert_hostcheck` (`lib/vtls/hostcheck.c`), the function that
decides whether a name in a server's TLS certificate is acceptable for the host the user asked for.
The suite has **3 open tasks** about its pinned i386 machine code running on the
[`x86_32` model](../../x86_32/README.md). There are statements and no proofs.

| Task ([`Curl/Hostcheck/Statement.lean`](Curl/Hostcheck/Statement.lean)) | In words |
|---|---|
| `match_sound` | A name is accepted only if RFC 2818 §3.1 lets it match the host name. |
| `match_leftmost_wildcard` | `*.S` is accepted for every `L.S'` with one non-empty component `L` and `S'` equal to `S` up to case. |
| `ip_host_exact` | For a host given as an IP address, a name is accepted only if it is that address. |

Each task holds for every caller, every placement of the two names and every content of the rest of
memory; the call must return, restore the callee-saved registers and write nothing but its own
stack. The specification ([`Curl/Spec/Hostcheck.lean`](Curl/Spec/Hostcheck.lean)) is written from
RFC 2818, RFC 2459 and RFC 3986 and imports nothing. curl deliberately accepts less than RFC 2818
allows (no `f*.com`, no `*.com`), so completeness is stated only for the wildcard form curl
documents. The function has two CVEs in its history: CVE-2014-0139 (a wildcard matched an
IP-address host) and CVE-2023-28321 (a partial wildcard matched `xn--` hosts).

## Run

```sh
python3 ../suite.py                # pins, cached sources, lake build, 132 runs on the model
python3 ../suite.py build          # also rebuild the image with the pinned LLVM and compare
```

The first command needs Lean and Python 3 and no network. The second fetches the pinned LLVM
release and the 81 curl files named in `targets/hostcheck/SOURCES.sha256`, each checked against its
hash.

## What is here

This suite adds only what is specific to curl. The call harness (`Ssl.Harness`), the test support,
the compiler, flags, runtime, linker script and image format are the
[OpenSSL suite's](../openssl/README.md), used through [`../suite.py`](../suite.py).

- `Curl/Spec/`, `Curl/Hostcheck/Statement.lean`: specification and tasks. `Curl/Hostcheck/Image.lean`
  holds the machine-code bytes.
- `CurlCheck.lean`: 33 name pairs in four memory placements, each checked against all three tasks.
- `targets/hostcheck/`: the build description, source hashes and image pins, and what is not
  upstream: `include/curl_config.h` (a configuration with IPv6 and no optional feature),
  `include/libc.h` with twelve one-line hosted headers that include it (declarations only), and
  `libc.c` (`memchr` and `strncmp` as byte loops). curl's sources are compiled unchanged, with
  `-DUSE_OPENSSL` because that is the condition under which curl builds `hostcheck.c`; no OpenSSL
  code is involved.
