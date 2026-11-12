#!/bin/sh
# Regenerates the QEMU reference of the workload (guest/workload.qemu.txt), which verify.sh step 4
# compares byte for byte with the model's output: the UP guest (guest/bzImage, guest/initramfs.cpio)
# under qemu-system-i386 with the CPU of the differential tests (test/qemu-cpu.sh: EPYC-Rome under
# TCG), 128 MiB, the serial console on stdio; the shell runs /workload.sh and the lines from
# "== begin" to "== end" are kept.
#   guest/qemu-workload.sh [OUTFILE]      (from anywhere; default OUTFILE guest/workload.qemu.txt)
# The exact command is printed. QEMU 11.1.2; QEMU_CPU overrides the CPU.
set -eu
cd "$(dirname "$0")/.."
OUTFILE=${1:-guest/workload.qemu.txt}
RAW=$(mktemp)
. test/qemu-cpu.sh
set -- qemu-system-i386 -cpu "$QEMU_CPU" -m 128 -kernel guest/bzImage -initrd guest/initramfs.cpio \
  -append "console=ttyS0" -display none -serial stdio -monitor none -no-reboot
PIDF=$RAW.pid
echo "qemu-workload: $*" >&2
( (sleep 6; printf 'sh /workload.sh\n'; sleep 120) | "$@" -pidfile "$PIDF" > "$RAW" 2>&1 ) > /dev/null 2>&1 &
PID=$!
i=0
while [ $i -lt 150 ] && ! grep -q "^== end" "$RAW"; do sleep 1; i=$((i + 1)); done
[ -s "$PIDF" ] && kill "$(cat "$PIDF")" 2>/dev/null || true
rm -f "$PIDF"
kill $PID 2>/dev/null || true
wait $PID 2>/dev/null || true
grep -q "^== end" "$RAW" || { echo "qemu-workload: no '== end' from QEMU (see $RAW)" >&2; exit 1; }
tr -d '\r' < "$RAW" | sed -n '/^== begin/,/^== end/p' > "$OUTFILE"
rm -f "$RAW"
echo "qemu-workload: $(grep -c . "$OUTFILE") lines written to $OUTFILE" >&2
