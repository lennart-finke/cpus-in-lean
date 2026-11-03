#!/bin/bash
# Builds doom/initramfs.cpio: the guest/ busybox root plus a static i386 doomgeneric and the
# shareware IWAD. Needs guest/build.sh to have run once (for ~/k/root). Run in the build VM:
#   limactl shell kbuild -- bash "$PWD"/validation/doom/build.sh  (from the repository root)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=~/doom
mkdir -p $W && cd $W
[ -d doomgeneric ] || git clone -q https://github.com/ozkl/doomgeneric
git -C doomgeneric checkout -q e257a09527062bfb986b6e5e0780839b6cbd5b71
[ -f doom1.wad ] || wget -q https://github.com/Akbar30Bill/DOOM_wads/raw/master/doom1.wad
echo "5b2e249b9c5133ec987b3ea77596381dc0d6bc1d  doom1.wad" | sha1sum -c --quiet
D=doomgeneric/doomgeneric
SRC=$(sed -n 's/^SRC_DOOM = //p' $D/Makefile | tr ' ' '\n' | grep -v doomgeneric_xlib | sed "s|^|$D/|; s|\.o$|.c|")
i686-linux-gnu-gcc -O2 -march=i686 -static -w -o doom -DNORMALUNIX -DLINUX -D_DEFAULT_SOURCE \
  -DDOOMGENERIC_RESX=320 -DDOOMGENERIC_RESY=200 -I$D $SRC "$HERE/dg_lean.c" -lm
rm -rf root && cp -a ~/k/root root
cp doom doom1.wad root/
cat > root/init.new <<'INIT'
#!/bin/sh
mount -t proc proc /proc
mount -t sysfs sys /sys
mount -t devtmpfs dev /dev 2>/dev/null
[ -n "$doomframes" ] && { /doom -iwad /doom1.wad -hash -frames $doomframes -timedemo demo1; echo DOOM-END; busybox reboot -f; }
[ -n "$doomwin" ] && { /doom -iwad /doom1.wad -win; busybox reboot -f; }
echo "Hello from /init on the Lean x86 model"
exec /bin/sh
INIT
mv root/init.new root/init && chmod +x root/init
(cd root && find . | cpio -o -H newc --owner=0:0 2>/dev/null) > "$HERE/initramfs.cpio"
ls -la doom "$HERE/initramfs.cpio"
