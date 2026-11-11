#!/bin/sh
# One run of campaign.sh (see there): campaign_run.sh SEED, with DIR, CDIR, ARGS, EXTRA, TIMEOUT exported.
seed=$1
out="$CDIR/run-$seed"
if OUT="$out" NOBUILD=1 CMDLINE="seed=$seed$ARGS $EXTRA" "$DIR/run.sh" > "$out.log" 2>&1; then
  echo "seed $seed: $(grep -c . "$out/model.qemu-part.txt") lines identical" >> "$CDIR/summary.txt"
  rm -rf "$out" "$out.log"
else
  echo "seed $seed: FAILED (see $out, $out.log)" >> "$CDIR/summary.txt"
fi
