#!/bin/sh
# Differential test: play N frames of the demo1 timedemo on QEMU and on the Lean model and
# compare the per-frame CRC32s of the 320x200 framebuffer.   doom/test.sh [N]
set -e
N=${1:-100}
R=$(cd "$(dirname "$0")/.." && pwd); O=${OUT:-$R/doom/out}; mkdir -p "$O"
ARGS="console=ttyS0 doomframes=$N"
qemu-system-i386 -cpu pentium2 -m 128 -kernel "$R/guest/bzImage" -initrd "$R/doom/initramfs.cpio" \
  -append "$ARGS" -display none -serial file:"$O/qemu.log" -monitor none -no-reboot
"$R/.lake/build/bin/x86run" --expect DOOM-END --send @exit "$R/guest/bzImage" "$R/doom/initramfs.cpio" "$ARGS" \
  > "$O/lean.log" 2>&1 || true
for s in qemu lean; do grep -a '^F ' "$O/$s.log" | tr -d '\r' > "$O/$s.frames"; done
echo "qemu $(wc -l < "$O/qemu.frames") frames, lean $(wc -l < "$O/lean.frames") frames"
[ "$(wc -l < "$O/lean.frames")" -eq "$N" ] && cmp "$O/qemu.frames" "$O/lean.frames" && echo "PASS: $N frames identical"
