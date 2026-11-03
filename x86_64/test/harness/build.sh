#!/bin/sh
set -eu
cd "$(dirname "$0")"
CC=${CC:-clang}
"$CC" --target=x86_64-none-elf -c boot.S -o boot.o
"$CC" --target=x86_64-none-elf -O2 -ffreestanding -fno-builtin -fno-stack-protector -fno-pic -fno-pie -mno-red-zone -mno-sse -mno-mmx -msoft-float -fno-asynchronous-unwind-tables -c harness.c -o harness.o
python3 link.py harness.elf boot.o harness.o
