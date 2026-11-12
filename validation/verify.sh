#!/bin/sh
# Validation of the IA-32 model against QEMU, independent references and Linux (the model itself:
# ../x86_32/verify.sh).
#   ./verify.sh [N]          the gate: N random differential vectors (default 20000), system tests, reference
#                            checks, the model side of the native campaign (smoke sample), the long-mode
#                            bridge, unit tests, the Linux boot and the workload against QEMU
#   ./verify.sh --full [N]   also: the whole native campaign on the model (x86fp), gpr_ref with more cases,
#                            topo_ref for 64/128 CPUs, SMP Linux (guest/smp-check.sh 2 at four quanta and 4;
#                            guest/topo-check.sh 4, and 16 with guest/bzImage-bigsmp if built)
# Requires: elan/lake, qemu-system-i386/x86_64, clang, python3. Guest images in guest/ (guest/build.sh).
# Every step prints one result line ("   ..."); the first failing step stops the run with "FAIL: ...".
set -e
cd "$(dirname "$0")"
FULL=
[ "${1:-}" = "--full" ] && { FULL=1; shift; }
N=${1:-20000}
SEED=${SEED:-$(date +%s)}
LAKE=${LAKE:-lake}
command -v $LAKE >/dev/null || LAKE=~/.elan/bin/lake
TMP=${TMPDIR:-/tmp}/i32verify$$
mkdir -p "$TMP"
fail() { echo "FAIL: $1"; [ -n "${2:-}" ] && tail -20 "$2"; exit 1; }

echo "== 1. build the runners (x86run, x86test, x86sys, x86litmus, x86fp, x86bridge)"
$LAKE build x86run x86test x86sys x86litmus x86fp x86bridge > "$TMP/build.log" 2>&1 || fail "build" "$TMP/build.log"
echo "   $(tail -1 "$TMP/build.log")"

echo "== 1a. x86-TSO: litmus tests against herd7's x86tso.cat (pinned outcome sets, litmus/README.md)"
OUT=$(python3 litmus/litmus.py check-expected litmus/tests litmus/diy | tail -1)
echo "   $OUT"
echo "$OUT" | grep -q ", 0 different, 0 skipped" || fail "litmus"

echo "== 1b. x86-TSO: the access log is complete and inert (20000 random vectors, paging off)"
python3 test/gen.py 20000 "$SEED" "$TMP/tsolog" > /dev/null
OUT=$(./.lake/build/bin/x86test --tso-log "$TMP/tsolog.bin")
echo "   $OUT"
echo "$OUT" | grep -q ", 0 failures" || fail "TSO log"

echo "== 2. differential testing against QEMU ($N random vectors, seed $SEED)"
./test/run.sh "$N" "$SEED" > "$TMP/run.log" 2>&1 || true
sed 's/^/   /' "$TMP/run.log" | tail -4
grep -q ", 0 mismatches" "$TMP/run.log" || fail "QEMU differential tests" "$TMP/run.log"

echo "== 3. system-level tests against QEMU (main, 2-CPU and long-mode passes; model-only parts)"
./test/sys/run.sh > "$TMP/sys.log" 2>&1 || fail "system tests" "$TMP/sys.log"
grep "^system tests" "$TMP/sys.log" | sed 's/^/   /'

echo "== 4. independent references against the model (test/refs.py)"
python3 test/refs.py ${FULL:+--full} > "$TMP/refs.log" 2>&1 || fail "reference checks" "$TMP/refs.log"
grep -c "^  ok" "$TMP/refs.log" | sed 's/^/   reference checks passed: /'

echo "== 5. native hardware campaign on the model: x86fp --compat and legacy mode (test/fp_model_check.py)"
FPARG=--smoke; [ -n "$FULL" ] && FPARG=
python3 test/fp_model_check.py $FPARG > "$TMP/fp.log" 2>&1 || fail "x86fp" "$TMP/fp.log"
sed 's/^/   /' "$TMP/fp.log"

echo "== 6. long-mode bridge: the IA-32 model's stops in 64-bit mode continued by the x86-64 model"
./.lake/build/bin/x86bridge --cmdline long=1 test/sys/out/systest.elf > "$TMP/bridge.log" 2>&1 || true
BR=$(grep "^BRIDGE:" "$TMP/bridge.log" || true)
echo "   $BR"
[ -n "$BR" ] || fail "x86bridge did not finish" "$TMP/bridge.log"
# The IA-32 side must reach every stop and the test's END; differences inside the x86-64 model are its own
# (validation/README.md, "x86bridge": it does not set RF in the RFLAGS image of a #GP) and are reported here,
# not counted as an IA-32 failure.
grep -q "^END" "$TMP/bridge.log" || fail "the long-mode test did not complete under x86bridge" "$TMP/bridge.log"
grep "^BRIDGE stop" "$TMP/bridge.log" | sed 's/^/   x86-64 model differs (known issue unless new): /' || true
# Known: 2 stops (an IRET/RETF stub after a #GP: the x86-64 model leaves RF clear in the pushed RFLAGS image).
[ "$(grep -c '^BRIDGE stop' "$TMP/bridge.log")" -le 2 ] || fail "x86bridge: more than the 2 known x86-64 differences" "$TMP/bridge.log"

echo "== 7. unit tests (python3 -m unittest discover -s test)"
python3 -m unittest discover -s test -p 'test_*.py' > "$TMP/unit.log" 2>&1 || fail "unit tests" "$TMP/unit.log"
echo "   $(grep -E '^Ran ' "$TMP/unit.log"), $(grep -E '^(OK|FAILED)' "$TMP/unit.log" | tail -1)"

echo "== 8. boot Linux on the model and run a shell session"
LOG="$TMP/boot.log"
./.lake/build/bin/x86run --max 1000000000 \
  --expect "~ # " --send "uname -sr; echo \$((6*7))\n" --expect "42" --send "@exit" \
  guest/bzImage guest/initramfs.cpio "console=ttyS0" < /dev/null > "$LOG" 2>&1 || true
grep -q "Run /init as init process" "$LOG" && grep -q "Linux 6.12" "$LOG" && grep -q "^42" "$LOG" \
  || fail "boot" "$LOG"
grep -o "\[x86run\] [0-9]* instructions.*" "$LOG" | sed "s/^/   /"
echo "   Linux booted to a shell ($(grep -o 'CPU: AMD EPYC 7742[^(]*' "$LOG" | head -1)); uname and arithmetic ok"

echo "== 9. system-level differential workload (model vs QEMU reference output, guest/qemu-workload.sh)"
./.lake/build/bin/x86run --max 3000000000 --expect "~ # " --send "sh /workload.sh\n" \
  --expect "== end" --send "@exit" guest/bzImage guest/initramfs.cpio "console=ttyS0" \
  < /dev/null > "$LOG" 2>&1 || true
sed -n '/== begin/,/== end/p' "$LOG" | tr -d '\r' > guest/workload.lean.txt
diff guest/workload.qemu.txt guest/workload.lean.txt >/dev/null || { diff guest/workload.qemu.txt guest/workload.lean.txt; fail "workload differs"; }
grep -o "\[x86run\] [0-9]* instructions.*" "$LOG" | sed "s/^/   /"
echo "   workload output identical to QEMU ($(grep -c . guest/workload.qemu.txt) lines)"

if [ -n "$FULL" ]; then
  echo "== 10. SMP Linux against QEMU (guest/smp-check.sh)"
  QUANTA="100 1000 20000 1000000" OUT="$TMP/smp2" guest/smp-check.sh 2 > "$TMP/smp2.log" 2>&1 || fail "smp-check 2" "$TMP/smp2.log"
  grep "^smp-check" "$TMP/smp2.log" | sed 's/^/   /'
  OUT="$TMP/smp4" guest/smp-check.sh 4 > "$TMP/smp4.log" 2>&1 || fail "smp-check 4" "$TMP/smp4.log"
  grep "^smp-check" "$TMP/smp4.log" | sed 's/^/   /'
  echo "== 11. Linux's CPU topology against topo_ref (guest/topo-check.sh)"
  OUT="$TMP/topo4" guest/topo-check.sh 4 > "$TMP/topo4.log" 2>&1 || fail "topo-check 4" "$TMP/topo4.log"
  tail -1 "$TMP/topo4.log" | sed 's/^/   4 CPUs: /'
  if [ -f guest/bzImage-bigsmp ]; then
    KERNEL=guest/bzImage-bigsmp OUT="$TMP/topo16" guest/topo-check.sh 16 > "$TMP/topo16.log" 2>&1 || fail "topo-check 16" "$TMP/topo16.log"
    tail -1 "$TMP/topo16.log" | sed 's/^/   16 CPUs (bzImage-bigsmp): /'
  else
    echo "   16 CPUs: skipped (guest/bzImage-bigsmp not built: guest/build.sh bigsmp)"
  fi
fi
rm -rf "$TMP"
echo "ALL CHECKS PASSED${FULL:+ (full)}"
