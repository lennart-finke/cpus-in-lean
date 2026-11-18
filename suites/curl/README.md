# curl verification tasks

`Curl_cert_hostcheck` from **curl 8.23.0** (`lib/vtls/hostcheck.c`): does a certificate name match the
requested host? **3 open tasks** (no proofs) about its pinned i386 code on the [`x86_32` model](../../x86_32/README.md):

| Task ([`Curl/Hostcheck/Statement.lean`](Curl/Hostcheck/Statement.lean)) | In words |
|---|---|
| `match_sound` | A name is accepted only if RFC 2818 §3.1 lets it match the host. |
| `match_leftmost_wildcard` | `*.S` is accepted for every `L.S'` with one non-empty component `L` and `S'` equal to `S` up to case. |
| `ip_host_exact` | For an IP-address host, only that address is accepted. |

Each holds for every caller, name placement and memory; the call returns, restores callee-saved
registers and writes only its stack. The specification ([`Curl/Spec/Hostcheck.lean`](Curl/Spec/Hostcheck.lean),
from RFCs 2818, 2459, 3986, no imports) is complete only for curl's documented wildcard form, since curl
rejects `f*.com` and `*.com`. Past CVEs: CVE-2014-0139 (wildcard matched an IP host), CVE-2023-28321
(partial wildcard matched `xn--` hosts).

## Run

```sh
python3 ../suite.py                # pins, cached sources, lake build, 132 runs on the model (offline)
python3 ../suite.py build          # also rebuild the image with the pinned LLVM and compare
```

`build` fetches LLVM and the 81 files in `targets/hostcheck/SOURCES.sha256`, checking each hash.

## What is here

Harness, test support and toolchain come from the [OpenSSL suite](../openssl/README.md) via [`../suite.py`](../suite.py).

- `Curl/Spec/`, `Curl/Hostcheck/Statement.lean`: specification, tasks; `Curl/Hostcheck/Image.lean`: the bytes.
- `CurlCheck.lean`: 33 name pairs in four placements, checked against all three tasks.
- `targets/hostcheck/`: build description, hashes, pins, `include/curl_config.h` (IPv6, no optional
  features), `include/libc.h` with twelve one-line headers, `libc.c` (`memchr`, `strncmp`). Sources
  compile unchanged with `-DUSE_OPENSSL`, which `hostcheck.c` needs; no OpenSSL code is involved.
