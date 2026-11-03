#!/bin/sh
# Build the QEMU differential-test harness (harness.elf) with clang and link.py; no cross toolchain needed.
set -eu
cd "$(dirname "$0")"
CC=${CC:-clang}
"$CC" --target=i386-none-elf -c boot.S -o boot.o
"$CC" --target=i386-none-elf -march=i686 -O2 -ffreestanding -fno-builtin -fno-common -fno-pic -fno-pie -fno-stack-protector -fno-asynchronous-unwind-tables -Wno-empty-body -c harness.c -o harness.o
python3 link.py harness.elf boot.o harness.o
