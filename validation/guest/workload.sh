#!/bin/sh
# System-level differential workload: run under QEMU and under the Lean model, compare output.
echo "== begin"
echo "arith $((12345 * 6789)) $((0x7fffffff + 1)) $((-17 / 5)) $((-17 % 5)) $((1 << 31))"
seq 1 300 | sort -rn | head -3
seq 1 2000 | md5sum
head -c 65536 /bin/busybox | md5sum
head -c 65536 /bin/busybox | sha256sum
head -c 32768 /bin/busybox | gzip -1 | md5sum
head -c 32768 /bin/busybox | gzip -1 | gunzip | md5sum
dd if=/dev/zero bs=1024 count=64 2>/dev/null | md5sum
awk 'BEGIN { x = 1; for (i = 1; i <= 20; i++) x = x * 1.5; printf "%.6f %.3e %d\n", x, 1/7, int(x) }'
awk 'BEGIN { s = 0; for (i = 1; i <= 100; i++) s += 1/i; printf "%.9f\n", s }'
echo "hello world" | tr a-z A-Z | rev
printf '%s\n' c b a | sort | tr '\n' ' '; echo
ls /proc/self/ | wc -l
cat /proc/self/maps | wc -l
mkdir -p /tmp/t && cd /tmp/t && for i in 1 2 3 4 5; do echo "file $i" > f$i; done && cat f* | md5sum && cd /
expr 1000000 \* 3 / 7
echo "== end"
