#!/bin/sh
# Build the system-level test kernel (systest.elf) with clang and the harness linker; no cross toolchain needed.
set -eu
cd "$(dirname "$0")"
CC=${CC:-clang}
OUT=${OUT:-out}
mkdir -p "$OUT"
CFLAGS="--target=i386-none-elf -march=i686 -O1 -ffreestanding -fno-builtin -fno-common -fno-pic -fno-pie \
  -fno-stack-protector -fno-asynchronous-unwind-tables -mno-sse -mno-mmx -mno-80387 -Wall -Wno-unused-function"
"$CC" --target=i386-none-elf -c boot.S -o "$OUT/boot.o"
objs="$OUT/boot.o"
for c in *.c; do
  "$CC" $CFLAGS -c "$c" -o "$OUT/${c%.c}.o"
  objs="$objs $OUT/${c%.c}.o"
done
python3 ../harness/link.py "$OUT/systest.elf" $objs
