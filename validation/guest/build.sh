#!/bin/bash
# Builds the guest kernel (bzImage) and initramfs. Run inside the Linux build VM:
#   limactl shell kbuild -- bash "$PWD"/validation/guest/build.sh  (from the repository root)
# `build.sh smp` builds the SMP variant instead (kernel.fragment plus kernel-smp.fragment: SMP, local
# APIC, I/O APIC, MP-table parsing) in its own source tree: bzImage-smp, initramfs-smp.cpio (the same
# initramfs plus smp.sh and a few more BusyBox applets). The default build is unchanged.
# `build.sh bigsmp` builds bzImage-bigsmp: the SMP variant plus kernel-bigsmp.fragment (X86_BIGSMP, NR_CPUS=64,
# the 32-bit maximum) in its own source tree, for guest/smp-check.sh and topo-check.sh with more than 8 CPUs
# (KERNEL=guest/bzImage-bigsmp); it uses initramfs-smp.cpio.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
KVER=6.12.111
VARIANT=${1:-}
SFX=""; SRC=linux-$KVER
[ "$VARIANT" = smp ] && { SFX=-smp; SRC=linux-$KVER-smp; }
[ "$VARIANT" = bigsmp ] && { SFX=-bigsmp; SRC=linux-$KVER-bigsmp; }
W=~/k
mkdir -p $W && cd $W
[ -f linux-$KVER.tar.xz ] || wget -q https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-$KVER.tar.xz
[ -d $SRC ] || { mkdir -p $SRC && tar xf linux-$KVER.tar.xz -C $SRC --strip-components=1; }
cd $SRC
MK="make ARCH=i386 CROSS_COMPILE=i686-linux-gnu- -j$(nproc)"
$MK tinyconfig >/dev/null
if [ "$SFX" = -bigsmp ]; then
  ./scripts/kconfig/merge_config.sh -m .config "$HERE/kernel.fragment" "$HERE/kernel-smp.fragment" "$HERE/kernel-bigsmp.fragment" >/dev/null
elif [ -n "$SFX" ]; then
  ./scripts/kconfig/merge_config.sh -m .config "$HERE/kernel.fragment" "$HERE/kernel-smp.fragment" >/dev/null
else
  ./scripts/kconfig/merge_config.sh -m .config "$HERE/kernel.fragment" >/dev/null
fi
$MK olddefconfig >/dev/null
for o in M486SX MATH_EMULATION SERIAL_8250_CONSOLE BLK_DEV_INITRD KERNEL_LZ4 BINFMT_ELF EARLY_PRINTK; do
  grep -q "^CONFIG_$o=y" .config || { echo "missing CONFIG_$o"; exit 1; }
done
if [ -n "$SFX" ]; then
  for o in SMP X86_LOCAL_APIC X86_IO_APIC X86_MPPARSE; do
    grep -q "^CONFIG_$o=y" .config || { echo "missing CONFIG_$o"; exit 1; }
  done
fi
if [ "$SFX" = -bigsmp ]; then
  grep -q '^CONFIG_X86_BIGSMP=y' .config && grep -q '^CONFIG_NR_CPUS=64' .config || { echo 'missing BIGSMP/NR_CPUS=64'; exit 1; }
fi
$MK bzImage
if [ -n "$SFX" ]; then
  cp arch/x86/boot/bzImage "$HERE/bzImage$SFX"; cp System.map "$HERE/System.map$SFX"
  cp vmlinux "$HERE/vmlinux$SFX"; cp .config "$HERE/config$SFX"
else
  cp arch/x86/boot/bzImage System.map vmlinux .config "$HERE/"
fi
[ "$SFX" = -bigsmp ] && exit 0   # uses initramfs-smp.cpio
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
if [ -n "$SFX" ]; then
  cp "$HERE/smp.sh" root/smp.sh
  for a in nproc grep cut sed taskset sleep; do ln -s busybox root/bin/$a; done
fi
(cd root && find . | cpio -o -H newc --owner=0:0 2>/dev/null) > "$HERE/initramfs$SFX.cpio"
ls -la "$HERE"/bzImage$SFX "$HERE"/initramfs$SFX.cpio
