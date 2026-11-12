#!/bin/sh
# Verify both models. The IA-32 model (x86_32/, validated by validation/) and the x86-64 model (x86_64/)
# get separate verdicts: a failure of the x86-64 model (including its known issues, validation/README.md
# "x86-64 model: known issues") is reported as such and never as an IA-32 failure.
#   ./verify.sh [N]          IA-32: model + proofs, runners, litmus tests, N QEMU differential vectors
#                            (default 2000), system tests, reference checks, x86fp (smoke sample), unit
#                            tests; x86-64: model + proofs, x64check, N QEMU vectors
#   ./verify.sh --full [N]   IA-32: x86_32/verify.sh + validation/verify.sh --full [N] (adds the bridge,
#                            Linux boot and workload, SMP Linux, the whole x86fp campaign); x86-64:
#                            x86_64/verify.sh [N] (its Linux boot); N defaults to 20000
# Exit status: 0 both pass, 1 an IA-32 check failed, 2 only the x86-64 model failed.
# QEMU tests are skipped (and said so) when qemu is missing.
cd "$(dirname "$0")"
LAKE=${LAKE:-lake}
command -v $LAKE >/dev/null || LAKE=~/.elan/bin/lake
export LAKE
FULL=
[ "${1:-}" = "--full" ] && { FULL=1; shift; }
N=${1:-}
SEED=${SEED:-$(date +%s)}
export SEED
X64=PASSED
ia32_fail() { echo "FAIL (IA-32): $1"; echo "IA-32: FAILED; x86-64: not run to completion"; exit 1; }
QEMU=1
command -v qemu-system-i386 >/dev/null && command -v qemu-system-x86_64 >/dev/null || QEMU=

if [ -n "$FULL" ]; then
  N=${N:-20000}
  echo "==== IA-32 (full)"
  x86_32/verify.sh || ia32_fail "x86_32/verify.sh"
  validation/verify.sh --full "$N" || ia32_fail "validation/verify.sh --full"
  echo "==== x86-64 (full)"
  (cd x86_64 && ./verify.sh "$N") || X64="FAILED (x86_64/verify.sh)"
else
  N=${N:-2000}
  echo "== 1. IA-32 model and proofs"
  x86_32/verify.sh || ia32_fail "model/proofs"
  echo "== 2. IA-32 runners"
  (cd validation && $LAKE build x86run x86test x86sys x86litmus x86fp x86bridge) > /dev/null || ia32_fail "build"
  echo "   built x86run x86test x86sys x86litmus x86fp x86bridge"
  echo "== 3. x86-TSO litmus tests (pinned expected outcome sets)"
  python3 validation/litmus/litmus.py check-expected validation/litmus/tests validation/litmus/diy | tail -1 | sed 's/^/   /'
  python3 validation/litmus/litmus.py check-expected validation/litmus/tests validation/litmus/diy | tail -1 \
    | grep -q ", 0 different, 0 skipped" || ia32_fail "litmus"
  if [ -n "$QEMU" ]; then
    qemu-system-i386 --version | head -1 | sed 's/^/   /'
    echo "== 4. IA-32 QEMU differential tests ($N vectors, seed $SEED)"
    OUT=$(validation/test/run.sh "$N" "$SEED")
    echo "$OUT" | tail -3 | sed 's/^/   /'
    echo "$OUT" | grep -q ", 0 mismatches" || ia32_fail "QEMU differential mismatches"
    echo "== 5. IA-32 system-level tests against QEMU"
    validation/test/sys/run.sh > "${TMPDIR:-/tmp}/i32sys$$.log" 2>&1 || { tail -20 "${TMPDIR:-/tmp}/i32sys$$.log"; ia32_fail "system tests"; }
    grep "^system tests" "${TMPDIR:-/tmp}/i32sys$$.log" | sed 's/^/   /'; rm -f "${TMPDIR:-/tmp}/i32sys$$.log"
    echo "== 6. independent references against the model"
    python3 validation/test/refs.py > "${TMPDIR:-/tmp}/i32refs$$.log" 2>&1 || { cat "${TMPDIR:-/tmp}/i32refs$$.log"; ia32_fail "reference checks"; }
    tail -1 "${TMPDIR:-/tmp}/i32refs$$.log" | sed 's/^/   /'; rm -f "${TMPDIR:-/tmp}/i32refs$$.log"
  else
    echo "== 4-6. skipped: qemu-system-i386/qemu-system-x86_64 not installed (no differential, system or transcript reference tests)"
  fi
  echo "== 7. native campaign on the model (x86fp, smoke sample)"
  python3 validation/test/fp_model_check.py --smoke | sed 's/^/   /'
  python3 validation/test/fp_model_check.py --smoke > /dev/null || ia32_fail "x86fp"
  echo "== 8. IA-32 unit tests"
  python3 -m unittest discover -s validation/test -p 'test_*.py' > "${TMPDIR:-/tmp}/i32unit$$.log" 2>&1 \
    || { tail -30 "${TMPDIR:-/tmp}/i32unit$$.log"; ia32_fail "unit tests"; }
  grep -E "^Ran " "${TMPDIR:-/tmp}/i32unit$$.log" | sed 's/^/   /'; rm -f "${TMPDIR:-/tmp}/i32unit$$.log"
  echo "   IA-32 checks passed"

  echo "==== x86-64"
  echo "== 9. x86-64 model and proofs"
  if (cd x86_64 && $LAKE build x64run x64test x64check X64Proofs > /dev/null) \
      && ! grep -rnwE "sorry|admit|axiom" --include='*.lean' x86_64/X64 \
      && python3 x86_64/test/test_tools.py > /dev/null 2>&1 && x86_64/.lake/build/bin/x64check; then
    echo "   x86-64 model, proofs and x64check ok"
  else
    X64="FAILED (model/proofs/x64check)"
  fi
  if [ -n "$QEMU" ]; then
    echo "== 10. x86-64 QEMU differential tests ($N vectors, seed $SEED)"
    python3 x86_64/test/run.py "$N" "$SEED" || X64="FAILED (x86_64/test/run.py $N $SEED; its known issues: validation/README.md)"
  fi
fi
echo "IA-32: ALL CHECKS PASSED${FULL:+ (full)}; x86-64: $X64"
[ "$X64" = PASSED ] || exit 2
exit 0
