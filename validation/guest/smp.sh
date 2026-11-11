#!/bin/sh
# SMP checks for the SMP guest kernel (initramfs-smp.cpio): run under QEMU -smp N and on the model
# (x86run --smp N); the lines between "== smp begin" and "== smp end" must be identical.
echo "== smp begin"
echo "nproc $(nproc)"
echo "online $(cat /sys/devices/system/cpu/online)"
echo "cpuinfo processors $(grep -c '^processor' /proc/cpuinfo)"
grep '^processor' /proc/cpuinfo | tr -d '\t' | tr '\n' ' '; echo
# interrupt lines and their controller (counts are timing dependent and left out)
grep -E 'IO-APIC|XT-PIC' /proc/interrupts | sed 's/^ *\([0-9]*\):.* \(IO-APIC\|XT-PIC\) *\(.*\)$/\1 \2 \3/'
grep -E '^ *(NMI|LOC|RES|CAL|TLB):' /proc/interrupts | sed 's/^ *\([A-Z]*\):.*$/\1/' | tr '\n' ' '; echo
# work on every CPU: the same computation pinned to each one
c=0
while [ $c -lt $(nproc) ]; do
  echo "cpu$c $(taskset -c $c sh -c 'seq 1 500 | md5sum')"
  c=$((c + 1))
done
# concurrent processes writing to one pipe, sorted
for c in 0 1 2 3; do (seq $((c * 100 + 1)) $((c * 100 + 50)) | md5sum | sed "s/^/job$c /") & done | sort
wait
echo "== smp end"
