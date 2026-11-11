#!/bin/sh
# Validate the suite and audit which tasks are proved.
#   ./verify.sh              pins, trusted base, build, executable checks, spec vectors, audit, kernel replay
#   ./verify.sh --rebuild    first rebuild the images from source with the pinned LLVM and compare
#   ./verify.sh --hw         also run the images on QEMU and check the fuzzer covers their instructions
#   ./verify.sh --reference  also regenerate the spec vectors from the reference implementations
#   ./verify.sh --high       also run the slow executable checks: the SHA-256 bit count past 2^32 bits and
#                            every task with its buffers and stack above address 2^31 (a few minutes, 10 GiB)
# The flags can be combined. Only --rebuild and --reference may need the network.
set -eu
cd "$(dirname "$0")"
REBUILD= HW= REFERENCE= HIGH=
for arg in "$@"; do
  case "$arg" in
    --rebuild) REBUILD=1 ;;
    --hw) HW=1 ;;
    --reference) REFERENCE=1 ;;
    --high) HIGH=1 ;;
    *) echo "usage: $0 [--rebuild] [--hw] [--reference] [--high]" >&2; exit 2 ;;
  esac
done
[ -z "$REBUILD" ] || python3 tools/build.py
python3 tools/check.py
python3 -m unittest discover -s tools -p 'test_*.py'
LAKE=${LAKE:-lake}
command -v "$LAKE" >/dev/null || LAKE=~/.elan/bin/lake
"$LAKE" build
./.lake/build/bin/sslcheck
[ -z "$HIGH" ] || ./.lake/build/bin/sslcheck high
./.lake/build/bin/sslcheck spec tools/spec_vectors.txt sha256 sha224 chacha20 poly1305 x25519
[ -z "$REFERENCE" ] || python3 tools/spec_vectors.py
if [ -n "$HW" ]; then
  python3 tools/hw.py
  python3 tools/encodings.py
fi
# Which tasks are proved: the claims must have exactly the pinned statements as their types and use
# only the allowed axioms (Audit.lean); then every declaration is replayed through the kernel.
"$LAKE" env lean Audit.lean
"$LAKE" env leanchecker Ssl Solutions Claims
echo "OPENSSL SUITE CHECKS PASSED (see the audit above for which tasks are proved)"
