#!/bin/sh
# Boot the SMP guest kernel (build.sh smp) with N CPUs on the model (x86run --smp N) and under QEMU
# (-smp N,sockets=N: SeaBIOS lists one MP processor entry per package), run smp.sh and workload.sh,
# and compare the two transcripts (the "== smp" and "== begin/end" sections).
#   guest/smp-check.sh N        (from validation/, after `lake build x86run`)
# QUANTA="100 1000 20000 1000000" runs the model once per scheduling quantum (x86run --quantum); every
# run must give the transcript QEMU gives (the outcome must not depend on the quantum). Default 1000.
set -eu
cd "$(dirname "$0")/.."
N=${1:-2}
QUANTA=${QUANTA:-1000}
OUT=${OUT:-${TMPDIR:-/tmp}/smpcheck$$}
mkdir -p "$OUT"
. test/qemu-cpu.sh
CMD="console=ttyS0 no_timer_check"
( (sleep 4; printf 'dmesg -n 1; sh /smp.sh\n'; sleep 30; printf 'sh /workload.sh\n'; sleep 200) | qemu-system-i386 -cpu "$QEMU_CPU" \
    -smp "$N,sockets=$N" -m 128 -kernel guest/bzImage-smp -initrd guest/initramfs-smp.cpio -append "$CMD" \
    -display none -serial stdio -monitor none -no-reboot > "$OUT/qemu.raw" 2>&1 ) > /dev/null 2>&1 &
QPID=$!
for Q in $QUANTA; do
  ./.lake/build/bin/x86run --smp "$N" --quantum "$Q" --max 6000000000 --expect "~ # " --send "dmesg -n 1; sh /smp.sh\n" \
    --expect "== smp end" --send "sh /workload.sh\n" --expect "== end" --send "@exit" \
    guest/bzImage-smp guest/initramfs-smp.cpio "$CMD" < /dev/null > "$OUT/model-q$Q.raw" 2>&1 || true
done
i=0
while [ $i -lt 120 ] && ! grep -q "^== end" "$OUT/qemu.raw"; do sleep 1; i=$((i + 1)); done
pkill -f "kernel guest/bzImage-smp" 2>/dev/null || true
kill $QPID 2>/dev/null || true
tr -d '\r' < "$OUT/qemu.raw" | sed -n -e '/^== smp begin/,/^== smp end/p' -e '/^== begin/,/^== end/p' > "$OUT/qemu.txt"
fail=0
for Q in $QUANTA; do
  tr -d '\r' < "$OUT/model-q$Q.raw" | sed -n -e '/^== smp begin/,/^== smp end/p' -e '/^== begin/,/^== end/p' > "$OUT/model-q$Q.txt"
  grep -o "\[x86run\] [0-9]* instructions.*" "$OUT/model-q$Q.raw" || true
  grep "\[x86run\] per CPU" "$OUT/model-q$Q.raw" || true
  if [ -s "$OUT/model-q$Q.txt" ] && diff -u "$OUT/qemu.txt" "$OUT/model-q$Q.txt"; then
    echo "smp-check: $N CPUs, quantum $Q: $(grep -c . "$OUT/model-q$Q.txt") lines identical to QEMU"
  else
    echo "smp-check: $N CPUs, quantum $Q: transcripts differ (or are empty), see $OUT"; fail=1
  fi
done
exit $fail
