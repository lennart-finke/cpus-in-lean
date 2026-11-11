#!/usr/bin/env python3
"""Rebuild the task images with the pinned toolchain and compare them with the pins.

usage: python3 tools/build.py [--pin] [openssl_sha256 ...]

Without --pin nothing tracked is written: the rebuilt image bytes, symbol addresses, disassembly
and build record must equal the pinned ones, or the command fails. With --pin the pins
(`Ssl/*/Image.lean` and `targets/*/image/`) are regenerated from the rebuild; this redefines the
tasks and invalidates every proof about the previous bytes.

The compiler, linker and binutils are the official LLVM release fetched by `tools/toolchain.py`.
`CC`-style overrides are deliberately not supported: another compiler produces other bytes.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

from fetch_sources import fetch
from gen_image import pinned_image, render
from toolchain import VERSION, toolchain

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"

# Each group is recorded in the pinned build record; see BUILD.md for the reason behind every flag.
TARGET = ["--target=i386-unknown-none-elf", "-march=i686"]
UPSTREAM = ["-O3", "-fomit-frame-pointer"]          # OpenSSL's release CFLAGS for linux-x86
FREESTANDING = ["-ffreestanding", "-fno-builtin", "-fno-pic", "-fno-stack-protector",
                "-fno-asynchronous-unwind-tables", "-fno-unwind-tables",
                "-ffunction-sections", "-fdata-sections"]
SUITE = ["-fno-inline-functions"]                   # keeps the field functions callable (X25519 tasks)
CFLAGS = TARGET + UPSTREAM + FREESTANDING + SUITE
LDFLAGS = ["-m", "elf_i386", "-static", "--gc-sections", "--build-id=none", "-T", "tools/image.ld"]


def symbols(nm, elf):
    """Addresses of the functions and data objects of the linked image."""
    out = subprocess.run([nm, "--defined-only", "--format=posix", str(elf)],
                         check=True, capture_output=True, text=True).stdout
    table = {}
    for line in out.splitlines():
        name, kind, value = line.split()[:3]
        if kind.upper() not in "TDRB":
            continue
        if name in table:
            raise SystemExit(f"{elf.name}: two symbols named {name}")
        table[name] = int(value, 16)
    return table


def build(target, pin):
    fetch(target)
    bin_ = toolchain()
    source = ROOT / "targets" / target
    cfg = json.loads((source / "target.json").read_text())
    out = ROOT / "out" / target
    out.mkdir(parents=True, exist_ok=True)
    objects = []
    for i, name in enumerate(cfg["sources"] + [str(TOOLS / "runtime/shim.c")]):
        obj = out / f"{i}.o"
        # The runtime is compiled separately, without target-specific stub headers.
        extra = cfg["cflags"] + ["-I", str(TOOLS / "runtime")] if i < len(cfg["sources"]) else []
        subprocess.run([bin_ / "clang", *CFLAGS, *extra, "-c", name, "-o", str(obj)], cwd=source, check=True)
        objects.append(obj)
    entry = out / "entry.o"
    subprocess.run([bin_ / "clang", *TARGET, "-c", str(TOOLS / "runtime/entry.S"), "-o", str(entry)],
                   check=True)
    objects.append(entry)
    elf = out / f"{target}.elf"
    roots = [arg for root in cfg["roots"] for arg in ("-u", root)]
    subprocess.run([bin_ / "ld.lld", *LDFLAGS, *roots, "-o", str(elf), *map(str, objects)],
                   cwd=ROOT, check=True)
    subprocess.run([bin_ / "llvm-objcopy", "-O", "binary", elf.name, f"{target}.bin"], cwd=out, check=True)
    data = (out / f"{target}.bin").read_bytes()
    syms = symbols(bin_ / "llvm-nm", elf)
    for root in ["halt", *cfg["roots"]]:
        if root not in syms:
            raise SystemExit(f"{target}: root {root} is not in the image")
    version = subprocess.run([bin_ / "clang", "--version"], check=True, capture_output=True,
                             text=True).stdout.splitlines()[0]
    built = {
        f"{target}.syms.json": json.dumps(syms, indent=2, sort_keys=True) + "\n",
        f"{target}.dis": subprocess.run(
            [bin_ / "llvm-objdump", "-d", "--no-show-raw-insn", elf.name],
            cwd=out, check=True, capture_output=True, text=True).stdout,
        "build.txt": "\n".join([
            f"toolchain: official LLVM {VERSION} release (tools/toolchain.py)", version,
            "compile: clang " + " ".join(CFLAGS + cfg["cflags"]),
            "runtime: clang " + " ".join(CFLAGS) + " tools/runtime/shim.c; clang "
            + " ".join(TARGET) + " tools/runtime/entry.S",
            "link: ld.lld " + " ".join(LDFLAGS + roots),
            "image: llvm-objcopy -O binary", ""]),
    }
    for name, text in built.items():
        (out / name).write_text(text)
    module = cfg["module"]
    if pin:
        image = source / "image"
        image.mkdir(exist_ok=True)
        for old in image.iterdir():
            old.unlink()
        sums = [f"{hashlib.sha256(data).hexdigest()}  {target}.bin"]
        for name, text in built.items():
            (image / name).write_text(text)
            sums.append(f"{hashlib.sha256(text.encode()).hexdigest()}  {name}")
        (image / "SHA256SUMS").write_text("\n".join(sums) + "\n")
        (ROOT / "Ssl" / module / "Image.lean").write_text(render(target, module, data, syms))
        print(f"{target}: pinned {len(data)} bytes, {len(syms)} symbols")
        return
    expected, _ = pinned_image(target)
    different = [name for name, text in built.items()
                 if (source / "image" / name).read_text() != text]
    if data != expected:
        different.insert(0, f"{target}.bin")
    if different:
        raise SystemExit(f"{target}: rebuild differs from the pin in {', '.join(different)}; "
                         f"compare out/{target}/ with targets/{target}/image/. Pins were not changed.")
    print(f"{target}: rebuilt image, symbols, disassembly and build record match the pins")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pin", action="store_true", help="regenerate the pins (redefines the tasks)")
    parser.add_argument("targets", nargs="*")
    args = parser.parse_args()
    names = sorted(p.name for p in (ROOT / "targets").iterdir())
    for target in args.targets or names:
        if target not in names:
            parser.error(f"unknown target: {target}")
        build(target, args.pin)
