#!/bin/sh
# System-level differential test: run the test kernel under QEMU and on the Lean model, diff the transcripts.
#   test/sys/run.sh          (needs qemu-system-i386, clang, and `lake build x86sys`)
# Environment (used by campaign.sh):
#   CMDLINE   fuzzing parameters for the kernel, e.g. "seed=123 sse=100000" (default: none, fixed seeds)
#   OUT       output directory (default test/sys/out)
#   TIMEOUT   seconds QEMU may run (default 30)
#   NOBUILD   set to skip building the kernel
# With CMDLINE set, the per-line transcendental deviations are regenerated from this run's QEMU transcript
# with the exact reference (x87ref.py); only the reasons already justified there are accepted.
set -eu
DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../.." && pwd)
OUT=${OUT:-$DIR/out}
CMDLINE=${CMDLINE:-}
TIMEOUT=${TIMEOUT:-30}
. "$ROOT/test/qemu-cpu.sh"
mkdir -p "$OUT"
[ -n "${NOBUILD:-}" ] || "$DIR/build.sh"
ELF="$DIR/out/systest.elf"
rm -f "$OUT/qemu.txt"
qemu-system-i386 -cpu "$QEMU_CPU" -m 64 -kernel "$ELF" -append "$CMDLINE" -display none \
  -serial file:"$OUT/qemu.txt" -monitor none -device isa-debug-exit,iobase=0xf4,iosize=4 -no-reboot &
QPID=$!
( sleep "$TIMEOUT"; kill $QPID 2>/dev/null ) &
wait $QPID 2>/dev/null || true
"$ROOT/.lake/build/bin/x86sys" --cmdline "$CMDLINE" "$ELF" > "$OUT/model.txt" || true
X87T="$DIR/x87t-deviations.txt"
if [ -n "$CMDLINE" ]; then
  X87T="$OUT/x87t-deviations.txt"
  tr -d '\r' < "$OUT/qemu.txt" > "$OUT/qemu.raw.txt"
  python3 "$DIR/x87ref.py" qemu "$OUT/qemu.raw.txt" > "$X87T" 2> "$OUT/x87t.summary"
  if grep -v '^#' "$X87T" | grep -v -e '# [a-z0-9]*: denormal operand: ' -e '# [a-z0-9]*: NaN operands: ' -e "# fyl2x: denormal ST(1): TCG's FYL2X returns about twice" \
       -e '# [a-z0-9]*: QEMU result is not correctly rounded: error [0-9.]* ulp (within ' > "$OUT/x87t.unexplained"; then
    echo "system tests: QEMU differs from the exact x87 reference for an unexplained reason:"; head -5 "$OUT/x87t.unexplained"
    exit 1
  fi
fi
tr -d '\r' < "$OUT/qemu.txt" | sed '/^MODEL-ONLY$/,$d' | python3 "$DIR/deviate.py" "$DIR/qemu-deviations.txt" "$X87T" > "$OUT/qemu.clean.txt"
sed '/^MODEL-ONLY$/,$d' "$OUT/model.txt" > "$OUT/model.qemu-part.txt"
sed -n '/^MODEL-ONLY$/,$p' "$OUT/model.txt" > "$OUT/model.only.txt"
fail=0
if diff -u "$OUT/qemu.clean.txt" "$OUT/model.qemu-part.txt" > "$OUT/diff.txt"; then
  echo "system tests: $(grep -c . "$OUT/model.qemu-part.txt") lines identical to QEMU"
else
  echo "system tests: transcripts differ"; head -40 "$OUT/diff.txt"; fail=1
fi
if diff -u "$DIR/model-only.expected" "$OUT/model.only.txt" > "$OUT/diff.only.txt"; then
  echo "system tests: $(grep -c . "$OUT/model.only.txt") model-only lines as expected"
else
  echo "system tests: model-only section differs from model-only.expected"; cat "$OUT/diff.only.txt"; fail=1
fi
exit $fail
