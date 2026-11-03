#!/usr/bin/env bash
# Run on Linux; CROSS_COMPILE defaults to x86_64-linux-gnu- on non-x86 hosts.
# Requires make, gcc/cross-gcc, binutils, flex, bison, bc, libelf-dev, lz4,
# cpio, curl, xz, bzip2 and static cross-libc development files.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
KVER=${KVER:-6.12.111}
WORK=${WORK:-"$HOME/kbuild-x86_64"}
JOBS=${JOBS:-$(getconf _NPROCESSORS_ONLN)}
if [[ -z "${CROSS_COMPILE+x}" ]]; then
  if [[ $(uname -m) == x86_64 ]]; then CROSS_COMPILE=; else CROSS_COMPILE=x86_64-linux-gnu-; fi
fi
for command in make "${CROSS_COMPILE}gcc" "${CROSS_COMPILE}ld" flex bison bc lz4 cpio curl xz bzip2 python3; do
  command -v "$command" >/dev/null || {
    echo "Missing build dependency: $command" >&2
    echo "On Debian/Ubuntu: sudo apt-get install build-essential gcc-x86-64-linux-gnu binutils-x86-64-linux-gnu libc6-dev-amd64-cross flex bison bc libelf-dev libssl-dev lz4 cpio curl xz-utils bzip2 python3" >&2
    exit 1
  }
done
mkdir -p "$WORK"
if [[ ! -d "$WORK/linux-$KVER" ]]; then
  if [[ ! -f "$WORK/linux-$KVER.tar.xz" ]]; then
    curl --fail --location "https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-$KVER.tar.xz" -o "$WORK/linux-$KVER.tar.xz"
  fi
  tar -C "$WORK" -xf "$WORK/linux-$KVER.tar.xz"
fi
BUILD="$WORK/build"
mkdir -p "$BUILD"
make -C "$WORK/linux-$KVER" O="$BUILD" ARCH=x86_64 CROSS_COMPILE="$CROSS_COMPILE" tinyconfig
(cd "$BUILD" && "$WORK/linux-$KVER/scripts/kconfig/merge_config.sh" -m .config "$HERE/kernel.fragment")
make -C "$WORK/linux-$KVER" O="$BUILD" ARCH=x86_64 CROSS_COMPILE="$CROSS_COMPILE" olddefconfig
for option in X86_64 SERIAL_8250_CONSOLE BLK_DEV_INITRD KERNEL_LZ4 BINFMT_ELF EARLY_PRINTK; do
  grep -q "^CONFIG_${option}=y$" "$BUILD/.config" || { echo "Missing $option" >&2; exit 1; }
done
make -C "$WORK/linux-$KVER" O="$BUILD" ARCH=x86_64 CROSS_COMPILE="$CROSS_COMPILE" -j"$JOBS" bzImage
cp "$BUILD/arch/x86/boot/bzImage" "$HERE/bzImage"
cp "$BUILD/vmlinux" "$BUILD/System.map" "$BUILD/.config" "$HERE/"
if [[ -z "${BUSYBOX:-}" ]]; then
  BBVER=1.36.1
  if [[ ! -d "$WORK/busybox-$BBVER" ]]; then
    curl --fail --location "https://busybox.net/downloads/busybox-$BBVER.tar.bz2" -o "$WORK/busybox-$BBVER.tar.bz2"
    tar -C "$WORK" -xf "$WORK/busybox-$BBVER.tar.bz2"
  fi
  make -C "$WORK/busybox-$BBVER" CROSS_COMPILE="$CROSS_COMPILE" defconfig
  # TC's old kernel interfaces are unnecessary for the guest workload.
  sed -i -e 's/# CONFIG_STATIC is not set/CONFIG_STATIC=y/' -e 's/CONFIG_TC=y/# CONFIG_TC is not set/' "$WORK/busybox-$BBVER/.config"
  make -C "$WORK/busybox-$BBVER" CROSS_COMPILE="$CROSS_COMPILE" -j"$JOBS"
  BUSYBOX="$WORK/busybox-$BBVER/busybox"
fi
python3 - "$BUSYBOX" <<'PY'
import struct,sys
b=open(sys.argv[1],'rb').read()
assert b[:6]==b'\x7fELF\x02\x01' and struct.unpack_from('<H',b,18)[0]==62, 'BusyBox must be an amd64 ELF'
off=struct.unpack_from('<Q',b,32)[0];size,n=struct.unpack_from('<HH',b,54)
assert all(struct.unpack_from('<I',b,off+k*size)[0]!=3 for k in range(n)), 'BusyBox must be statically linked'
PY
ROOT=$(mktemp -d "$WORK/initramfs.XXXXXX")
trap 'rm -rf "$ROOT"' EXIT
mkdir -p "$ROOT"/{bin,sbin,dev,proc,sys,tmp,etc}
cp "$BUSYBOX" "$ROOT/bin/busybox"
for app in sh ls cat echo mount uname ps dmesg mkdir seq sort head md5sum sha256sum gzip gunzip dd awk tr rev wc expr printf; do
  ln -s busybox "$ROOT/bin/$app"
done
cat > "$ROOT/init" <<'INIT'
#!/bin/sh
mount -t proc proc /proc
mount -t sysfs sys /sys
mount -t devtmpfs dev /dev 2>/dev/null
echo "Hello from /init on the Lean x86-64 model"
exec /bin/sh
INIT
chmod +x "$ROOT/init"
# Deliberately use the original workload unchanged; compare to a fresh amd64 QEMU run.
cp "$HERE/../../validation/guest/workload.sh" "$ROOT/workload.sh"
(cd "$ROOT" && find . -print0 | cpio --null -o -H newc --owner=0:0) > "$HERE/initramfs.cpio"
echo "Built $HERE/bzImage and $HERE/initramfs.cpio"
