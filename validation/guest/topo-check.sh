#!/bin/sh
# Boot the SMP guest kernel with N CPUs on the model (x86run --smp N) and check the topology Linux
# derives from CPUID (/proc/cpuinfo: physical id, siblings, core id, cpu cores, apicid) against the
# independent reference test/topo_ref.py. Model-only: QEMU runs -smp N,sockets=N (one CPU per package).
#   guest/topo-check.sh N        (from validation/, after `lake build x86run`)
set -eu
cd "$(dirname "$0")/.."
N=${1:-4}
KERNEL=${KERNEL:-guest/bzImage-smp}   # guest/bzImage-bigsmp for N > 8
OUT=${OUT:-${TMPDIR:-/tmp}/topocheck$$}
mkdir -p "$OUT"
./.lake/build/bin/x86run --smp "$N" --max 3000000000 --expect "~ # " \
  --send "grep -E '^(processor|physical id|siblings|core id|cpu cores|apicid|initial apicid)' /proc/cpuinfo; echo TOPO-E''ND\n" \
  --expect "TOPO-END" --send "@exit" \
  "$KERNEL" guest/initramfs-smp.cpio "console=ttyS0 no_timer_check" < /dev/null > "$OUT/model.raw" 2>&1 || true
python3 test/topo_ref.py cpuinfo "$N" "$OUT/model.raw"
