#!/bin/sh
# Validation of the IA-32 model against QEMU and a Linux boot (the model itself: ../x86_32/verify.sh).
#   ./verify.sh [N]     N = number of random differential vectors (default 20000)
# Requires: elan/lake, qemu-system-i386, python3. Guest images in guest/ (see guest/build.sh).
set -e
cd "$(dirname "$0")"
N=${1:-20000}
LAKE=${LAKE:-lake}
command -v $LAKE >/dev/null || LAKE=~/.elan/bin/lake

echo "== 1. build the runners (x86run, x86test, x86litmus, x86sys) on the model in ../x86_32"
$LAKE build x86run x86test x86litmus x86sys

echo "== 1a. x86-TSO: litmus tests against herd7's x86tso.cat (pinned outcome sets, litmus/README.md)"
OUT=$(python3 litmus/litmus.py check-expected litmus/tests litmus/diy | tail -1)
echo "   $OUT"
echo "$OUT" | grep -q ", 0 different, 0 skipped" || { echo "FAIL: litmus"; exit 1; }

echo "== 1b. x86-TSO: the access log is complete and inert (20000 random vectors, paging off)"
python3 test/gen.py 20000 "$(date +%s)" "${TMPDIR:-/tmp}/tsolog$$" > /dev/null
OUT=$(./.lake/build/bin/x86test --tso-log "${TMPDIR:-/tmp}/tsolog$$.bin")
rm -f "${TMPDIR:-/tmp}/tsolog$$.bin" "${TMPDIR:-/tmp}/tsolog$$.meta"
echo "   $OUT"
echo "$OUT" | grep -q ", 0 failures" || { echo "FAIL: TSO log"; exit 1; }

echo "== 2. differential testing against QEMU ($N random vectors)"
OUT=$(./test/run.sh "$N" "$(date +%s)")
echo "   $OUT"
echo "$OUT" | grep -q ", 0 mismatches" || { echo "FAIL: mismatches"; exit 1; }

echo "== 2b. system-level tests against QEMU (paging, PAE/NX, breakpoints, gates, tasks, vm86, APIC, SMM)"
./test/sys/run.sh

echo "== 3. boot Linux on the model and run a shell session"
LOG=$(mktemp)
./.lake/build/bin/x86run --max 1000000000 \
  --expect "~ # " --send "uname -sr; echo \$((6*7))\n" --expect "42" --send "@exit" \
  guest/bzImage guest/initramfs.cpio "console=ttyS0" < /dev/null > "$LOG" 2>&1 || true
grep -q "Run /init as init process" "$LOG" && grep -q "Linux 6.12" "$LOG" && grep -q "^42" "$LOG" \
  || { echo "FAIL: boot"; tail -20 "$LOG"; exit 1; }
grep -o "\[x86run\] [0-9]* instructions.*" "$LOG" | sed "s/^/   /"
echo "   Linux booted to a shell; uname and arithmetic ok"

echo "== 4. system-level differential workload (model vs QEMU reference output)"
./.lake/build/bin/x86run --max 3000000000 --expect "~ # " --send "sh /workload.sh\n" \
  --expect "== end" --send "@exit" guest/bzImage guest/initramfs.cpio "console=ttyS0" \
  < /dev/null > "$LOG" 2>&1 || true
sed -n '/== begin/,/== end/p' "$LOG" | tr -d '\r' > guest/workload.lean.txt
diff guest/workload.qemu.txt guest/workload.lean.txt >/dev/null || { echo "FAIL: workload differs"; diff guest/workload.qemu.txt guest/workload.lean.txt; exit 1; }
echo "   workload output identical to QEMU"
rm -f "$LOG"
echo "ALL CHECKS PASSED"
