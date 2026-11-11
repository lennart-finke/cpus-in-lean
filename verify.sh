#!/bin/sh
# Verify both models.
#   ./verify.sh [N]          models + proofs, runners, x64check, N-vector QEMU differential tests
#                            (default 2000), TSO litmus tests and IA-32 system tests
#                            (QEMU tests skipped when qemu is missing)
#   ./verify.sh --full [N]   the full gates instead: x86_32/verify.sh + validation/verify.sh [N] +
#                            x86_64/verify.sh [N] (Linux boots and workloads; need the guest images)
set -e
cd "$(dirname "$0")"
LAKE=${LAKE:-lake}
command -v $LAKE >/dev/null || LAKE=~/.elan/bin/lake
export LAKE

if [ "${1:-}" = "--full" ]; then
  N=${2:-20000}
  x86_32/verify.sh
  validation/verify.sh "$N"
  (cd x86_64 && ./verify.sh "$N")
  echo "ALL CHECKS PASSED (full)"
  exit 0
fi
N=${1:-2000}
SEED=${SEED:-$(date +%s)}

echo "== 1. IA-32 model and proofs"
x86_32/verify.sh

echo "== 2. x86-64 model and proofs"
(cd x86_64 && $LAKE build x64run x64test x64check X64Proofs)
if grep -rnwE "sorry|admit|axiom" --include='*.lean' x86_64/X64; then
  echo "FAIL: proof hole or user-declared axiom in x86_64/X64"; exit 1
fi
python3 x86_64/test/test_tools.py
x86_64/.lake/build/bin/x64check

echo "== 3. IA-32 runners"
(cd validation && $LAKE build x86run x86test x86sys x86litmus)

echo "== 3a. x86-TSO litmus tests (pinned expected outcome sets)"
python3 validation/litmus/litmus.py check-expected validation/litmus/tests validation/litmus/diy

if command -v qemu-system-i386 >/dev/null && command -v qemu-system-x86_64 >/dev/null; then
  echo "== 4. QEMU differential tests ($N vectors each, seed $SEED)"
  qemu-system-i386 --version | head -1
  OUT=$(validation/test/run.sh "$N" "$SEED")
  echo "   x86_32:   $OUT"
  echo "$OUT" | grep -q ", 0 mismatches" || { echo "FAIL: x86_32 mismatches"; exit 1; }
  python3 x86_64/test/run.py "$N" "$SEED"
  echo "== 5. IA-32 system-level tests against QEMU"
  validation/test/sys/run.sh
else
  echo "== 4. skipped: qemu-system-i386/qemu-system-x86_64 not installed"
fi
echo "ALL CHECKS PASSED"
