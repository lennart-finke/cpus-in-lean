#!/bin/sh
# Differential test: generate N vectors (seed S), run them on QEMU and on the Lean model.
#   test/run.sh [N] [SEED]
# QEMU runs an EPYC-Rome CPU (test/qemu-cpu.sh); forms that it executes but the model does not
# implement yet are not generated (test/isa_forms.py, NOT_YET_IMPLEMENTED).
set -e
N=${1:-10000}; SEED=${2:-1}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-$ROOT/test/out}
. "$ROOT/test/qemu-cpu.sh"
mkdir -p "$OUT"
"$ROOT/test/harness/build.sh"
python3 "$ROOT/test/gen.py" "$N" "$SEED" "$OUT/v$SEED" --v2
rm -f "$OUT/q$SEED.out"
qemu-system-i386 -cpu "$QEMU_CPU" -m 64 -kernel "$ROOT/test/harness/harness.elf" -initrd "$OUT/v$SEED.bin" \
  -display none -serial file:"$OUT/q$SEED.out" -monitor none \
  -device isa-debug-exit,iobase=0xf4,iosize=4 -no-reboot || true
grep -q '^END' "$OUT/q$SEED.out" || { echo "QEMU run did not complete"; exit 1; }
"$ROOT/.lake/build/bin/x86test" "$OUT/v$SEED.bin" "$OUT/v$SEED.meta" "$OUT/q$SEED.out" > "$OUT/diff$SEED.txt" || true
tail -1 "$OUT/diff$SEED.txt"
# Crypto workstream: QEMU's results of the AES-NI/PCLMULQDQ/SHA vectors (gen_crypto.py) against the
# independent reference (x86test compares the model with QEMU)
python3 "$ROOT/test/cryptoref.py" vectors "$OUT/v$SEED.bin" "$OUT/v$SEED.meta" "$OUT/q$SEED.out"
