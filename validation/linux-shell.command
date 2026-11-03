#!/bin/zsh
cd -- "${0:A:h}" || exit 1
exec ./.lake/build/bin/x86run guest/bzImage guest/initramfs.cpio
