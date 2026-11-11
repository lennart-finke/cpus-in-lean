#!/usr/bin/env python3
"""Run the pinned task images on QEMU and on real hardware, and compare with the Lean model.

usage: python3 tools/hw.py              build the drivers, run them on the model and on QEMU
       python3 tools/hw.py bundle       also write out/hw/openssl-suite-native.tar.gz
       python3 tools/hw.py compare DIR  check transcripts returned from a hardware run of the bundle
       python3 tools/hw.py linux BZIMAGE  run the Linux executables as init of a 32-bit kernel in QEMU
                                        (a test of the bundle itself, e.g. with validation/guest/bzImage)

A small driver (`hw/`) places the pinned image bytes at their link address, calls every task entry
point on pseudo-random and edge-case inputs, and prints each input/output pair as a line that
`sslcheck spec` can evaluate against the Lean specifications. The driver is built two ways from the
same source: a multiboot kernel, run by the Lean model (`sslcheck boot`) and by `qemu-system-i386`,
and a static 32-bit Linux executable for real hardware. For each image the check is:

  * the model's transcript satisfies the specifications,
  * QEMU's transcript is identical to the model's,
  * (compare) the hardware's transcript is identical to the model's.

The bundle is self-contained: unpack it on an x86 Linux machine, run `./run.sh`, and copy the
`returned/` directory back for `compare`. Running it is evidence about that machine's CPU executing
these exact instructions; it is not a proof and is not part of the trusted base.
"""
import io
import json
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

from gen_image import pinned_image
from toolchain import toolchain

ROOT = Path(__file__).resolve().parents[1]
HW = ROOT / "hw"
OUT = ROOT / "out" / "hw"
TARGETS = {"openssl_sha256": 1, "openssl_chacha20": 2, "openssl_poly1305": 3, "openssl_x25519": 4}
# line kinds each transcript must contain
KINDS = {"openssl_sha256": ["sha256", "sha224", "sha256_transform"],
         "openssl_chacha20": ["chacha20"],
         "openssl_poly1305": ["poly1305", "poly1305_ctx_size"],
         "openssl_x25519": ["x25519", "x25519_public", "fe_mul", "fe_sq", "fe_add", "fe_sub"]}
CFLAGS = ["--target=i386-unknown-none-elf", "-march=i686", "-O1", "-ffreestanding", "-fno-builtin",
          "-fno-pic", "-fno-stack-protector", "-fno-asynchronous-unwind-tables", "-mno-sse", "-mno-mmx",
          "-mno-80387", "-Wall", "-Werror"]
SSLCHECK = ROOT / ".lake/build/bin/sslcheck"
RUN_SH = """#!/bin/sh
# Run the four task images on this machine's CPU. Writes returned/<target>.txt and returned/host.txt.
set -u
cd "$(dirname "$0")"
mkdir -p returned
{ uname -a; grep -m1 'model name' /proc/cpuinfo; } > returned/host.txt 2>&1
status=0
for t in openssl_sha256 openssl_chacha20 openssl_poly1305 openssl_x25519; do
  ./$t.linux.elf > returned/$t.txt || { echo "$t: the driver failed to run"; status=1; continue; }
  if cmp -s returned/$t.txt expected/$t.txt; then echo "$t: identical to the Lean model"
  else echo "$t: DIFFERS from the Lean model"; status=1; fi
done
exit $status
"""


def build(target):
    bin_ = toolchain()
    out = OUT / target
    out.mkdir(parents=True, exist_ok=True)
    data, syms = pinned_image(target)
    (out / "image.bin").write_bytes(data)
    defines = [f"#define IMAGE_BASE 0x100000u"]
    defines += [f"#define SYM_{name.replace('.', '_')} 0x{addr:x}u" for name, addr in sorted(syms.items())]
    (out / "syms.h").write_text("\n".join(defines) + "\n")
    common = [*CFLAGS, f"-DTARGET={TARGETS[target]}", "-I", str(out), "-I", str(HW)]
    for kind, sources in [("mb", ["driver.c", "plat_mb.c", "thunk.S", "boot.S"]),
                          ("linux", ["driver.c", "plat_linux.c", "thunk.S"])]:
        objects = []
        for source in sources:
            obj = out / f"{kind}.{source}.o"
            subprocess.run([bin_ / "clang", *common, f'-DIMAGE="{out / "image.bin"}"', "-c",
                            str(HW / source), "-o", str(obj)], check=True)
            objects.append(str(obj))
        subprocess.run([bin_ / "ld.lld", "-m", "elf_i386", "-static", "--build-id=none", "-z",
                        "max-page-size=0x1000", "-T", str(HW / "link.ld"), "-o",
                        str(out / f"{target}.{kind}.elf"), *objects], check=True)
    return out


def model(target):
    """The transcript of the Lean model, checked against the specifications."""
    out = OUT / target
    text = subprocess.run([SSLCHECK, "boot", str(out / f"{target}.mb.elf")], check=True,
                          capture_output=True, text=True).stdout
    (out / "model.txt").write_text(text)
    subprocess.run([SSLCHECK, "spec", str(out / "model.txt"), *KINDS[target]], check=True,
                   stdout=subprocess.DEVNULL)
    return text


def qemu(target):
    out = OUT / target
    log = out / "qemu.txt"
    log.unlink(missing_ok=True)
    try:
        subprocess.run(["qemu-system-i386", "-cpu", "qemu32", "-m", "64", "-kernel",
                        str(out / f"{target}.mb.elf"), "-display", "none", "-serial", f"file:{log}",
                        "-monitor", "none", "-device", "isa-debug-exit,iobase=0xf4,iosize=4", "-no-reboot"],
                       timeout=300)
    except subprocess.TimeoutExpired:
        raise SystemExit(f"{target}: QEMU did not finish")
    return log.read_text().replace("\r", "")


def cpio(files):
    """A newc initramfs; `files` maps a name to (mode, rdev major, rdev minor, contents)."""
    out = bytearray()
    for ino, (name, (mode, major, minor, data)) in enumerate([*files.items(), ("TRAILER!!!", (0, 0, 0, b""))], 1):
        fields = [ino, mode, 0, 0, 1, 0, len(data), 0, 0, major, minor, len(name) + 1, 0]
        out += b"070701" + "".join(f"{v:08X}" for v in fields).encode() + name.encode() + b"\0"
        out += bytes(-len(out) % 4) + data
        out += bytes(-len(out) % 4)
    return bytes(out)


def linux(target, kernel):
    """Run the Linux executable as the init process of `kernel` under QEMU."""
    out = OUT / target
    (out / "initramfs.cpio").write_bytes(cpio({
        "dev": (0o040755, 0, 0, b""), "dev/console": (0o020600, 5, 1, b""),
        "init": (0o100755, 0, 0, (out / f"{target}.linux.elf").read_bytes())}))
    log = out / "linux.txt"
    log.unlink(missing_ok=True)
    try:
        subprocess.run(["qemu-system-i386", "-cpu", "qemu32", "-m", "64", "-kernel", kernel, "-initrd",
                        str(out / "initramfs.cpio"), "-append", "console=ttyS0 quiet loglevel=0 panic=-1",
                        "-display", "none", "-serial", f"file:{log}", "-monitor", "none", "-no-reboot"],
                       timeout=300)
    except subprocess.TimeoutExpired:
        pass                                    # init has exited; the kernel may just sit in its panic
    text = log.read_text(errors="replace").replace("\r", "")
    if "END\n" not in text:
        raise SystemExit(f"{target}: the Linux run did not finish (out/hw/{target}/linux.txt)")
    return text[:text.index("END\n") + 4]


def compare(directory):
    for target in TARGETS:
        expected = (OUT / target / "model.txt").read_text()
        got = (Path(directory) / f"{target}.txt").read_text()
        if got != expected:
            raise SystemExit(f"{target}: the returned transcript differs from the Lean model's")
        print(f"{target}: hardware transcript identical to the Lean model ({len(got.splitlines()) - 1} results)")
    host = Path(directory) / "host.txt"
    if host.is_file():
        print("host: " + " | ".join(host.read_text().splitlines()))


def main(args):
    if not SSLCHECK.is_file():
        raise SystemExit("build the suite first (lake build)")
    for target in TARGETS:
        build(target)
        text = model(target)
        print(f"{target}: model transcript satisfies the specifications ({len(text.splitlines()) - 1} results)")
    if args[:1] == ["compare"]:
        return compare(args[1])
    if args[:1] == ["linux"]:
        for target in TARGETS:
            if linux(target, args[1]) != (OUT / target / "model.txt").read_text():
                raise SystemExit(f"{target}: the Linux executable's transcript differs from the Lean model's")
            print(f"{target}: Linux executable (under QEMU) identical to the Lean model")
        return
    if shutil.which("qemu-system-i386"):
        version = subprocess.run(["qemu-system-i386", "--version"], capture_output=True, text=True).stdout
        for target in TARGETS:
            if qemu(target) != (OUT / target / "model.txt").read_text():
                raise SystemExit(f"{target}: QEMU's transcript differs from the Lean model's "
                                 f"(out/hw/{target}/qemu.txt, model.txt)")
            print(f"{target}: QEMU transcript identical to the Lean model")
        print(version.splitlines()[0])
    else:
        print("qemu-system-i386 not installed: QEMU comparison skipped")
    if args[:1] == ["bundle"]:
        dest = OUT / "openssl-suite-native.tar.gz"
        with tarfile.open(dest, "w:gz") as tar:
            def add(name, data, mode):
                info = tarfile.TarInfo(f"openssl-suite-native/{name}")
                info.size, info.mode = len(data), mode
                tar.addfile(info, io.BytesIO(data))
            add("run.sh", RUN_SH.encode(), 0o755)
            for target in TARGETS:
                add(f"{target}.linux.elf", (OUT / target / f"{target}.linux.elf").read_bytes(), 0o755)
                add(f"expected/{target}.txt", (OUT / target / "model.txt").read_bytes(), 0o644)
        print(f"wrote {dest.relative_to(ROOT)}")


if __name__ == "__main__":
    main(sys.argv[1:])
