#!/bin/zsh
cd -- "${0:A:h}" || exit 1
exec ./.lake/build/bin/x64run guest/bzImage guest/initramfs.cpio 'console=ttyS0 earlyprintk=serial,ttyS0 nokaslr noapic nolapic'
