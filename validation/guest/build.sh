#!/bin/bash
# Builds the guest kernel (bzImage) and initramfs. Run inside the Linux build VM:
#   limactl shell kbuild -- bash "$PWD"/validation/guest/build.sh  (from the repository root)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
KVER=6.12.111
W=~/k
mkdir -p $W && cd $W
[ -f linux-$KVER.tar.xz ] || wget -q https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-$KVER.tar.xz
[ -d linux-$KVER ] || tar xf linux-$KVER.tar.xz
cd linux-$KVER
MK="make ARCH=i386 CROSS_COMPILE=i686-linux-gnu- -j$(nproc)"
$MK tinyconfig >/dev/null
./scripts/kconfig/merge_config.sh -m .config "$HERE/kernel.fragment" >/dev/null
$MK olddefconfig >/dev/null
for o in M486SX MATH_EMULATION SERIAL_8250_CONSOLE BLK_DEV_INITRD KERNEL_LZ4 BINFMT_ELF EARLY_PRINTK; do
  grep -q "^CONFIG_$o=y" .config || { echo "missing CONFIG_$o"; exit 1; }
done
$MK bzImage
cp arch/x86/boot/bzImage System.map vmlinux .config "$HERE/"
# initramfs: Debian i386 static busybox + /init
cd $W
[ -f bb/usr/bin/busybox ] || { apt-get download busybox-static:i386; dpkg-deb -x busybox-static_*_i386.deb bb; }
rm -rf root && mkdir -p root/{bin,sbin,dev,proc,sys,tmp,etc}
cp bb/usr/bin/busybox root/bin/busybox
for a in sh ls cat echo mount uname ps dmesg mkdir; do ln -s busybox root/bin/$a; done
cat > root/init <<'INIT'
#!/bin/sh
mount -t proc proc /proc
mount -t sysfs sys /sys
mount -t devtmpfs dev /dev 2>/dev/null
echo "Hello from /init on the Lean x86 model"
exec /bin/sh
INIT
chmod +x root/init
cp "$HERE/workload.sh" root/workload.sh
for a in seq sort head md5sum sha256sum gzip gunzip dd awk tr rev wc expr printf; do ln -s busybox root/bin/$a; done
(cd root && find . | cpio -o -H newc --owner=0:0 2>/dev/null) > "$HERE/initramfs.cpio"
ls -la "$HERE"/bzImage "$HERE"/initramfs.cpio
