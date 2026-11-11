#!/bin/sh
# Fuzzing campaign: run the system-test kernel with RUNS different seeds, PAR at a time, comparing QEMU
# and the model each time (run.sh). COUNT sets the number of cases of every fuzzer per run.
#   test/sys/campaign.sh RUNS PAR COUNT [BASESEED] [EXTRA]
# e.g. test/sys/campaign.sh 40 8 25000           # 40 runs x 25,000 cases of each fuzzer
# EXTRA is appended to the kernel command line (e.g. "pgf=0" to switch a fuzzer off).
# Results go to test/sys/campaign/<baseseed>/: one directory per failing run (kept), summary.txt.
set -eu
DIR=$(cd "$(dirname "$0")" && pwd)
RUNS=${1:?runs}; PAR=${2:?parallel}; COUNT=${3:?count}
BASE=${4:-$(date +%s)}
EXTRA=${5:-}
CDIR="$DIR/campaign/$BASE"
mkdir -p "$CDIR"
"$DIR/build.sh"
FUZZERS="x87 x87t mmx sse pgf dbf tsf cgf"
ARGS=""
for f in $FUZZERS; do ARGS="$ARGS $f=$COUNT"; done
# Model time is about 1.5 ms per case: allow QEMU the same order of magnitude.
TIMEOUT=$((60 + COUNT / 50))
export DIR CDIR ARGS EXTRA TIMEOUT
i=0
seeds=""
while [ $i -lt "$RUNS" ]; do seeds="$seeds $(( (BASE + i * 7919) % 4294967291 + 1 ))"; i=$((i + 1)); done
printf '%s\n' $seeds | xargs -n 1 -P "$PAR" "$DIR/campaign_run.sh"
ok=$(grep -c "identical" "$CDIR/summary.txt" || true)
bad=$(grep -c "FAILED" "$CDIR/summary.txt" || true)
lines=$(awk '/identical/ { s += $3 } END { print s + 0 }' "$CDIR/summary.txt")
echo "campaign $BASE: $RUNS runs, $ok passed, $bad failed, $lines transcript lines compared ($CDIR/summary.txt)"
[ "$bad" -eq 0 ]
