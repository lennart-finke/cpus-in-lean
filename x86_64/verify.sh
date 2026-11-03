#!/usr/bin/env bash
# Full gate: missing Linux images or an unsupported instruction is a failure.
set -euo pipefail
cd "$(dirname "$0")"
N=${1:-20000}
SEED=${2:-1}
lake build x64run x64test x64check X64Proofs
if rg -n '\b(sorry|admit|axiom)\b' X64 --glob '*.lean'; then
  echo 'FAIL: proof hole or user-declared axiom' >&2
  exit 1
fi
python3 test/test_tools.py
./.lake/build/bin/x64check
python3 test/run.py "$N" "$SEED"
python3 guest/check.py
echo 'ALL X86-64 CHECKS PASSED'
