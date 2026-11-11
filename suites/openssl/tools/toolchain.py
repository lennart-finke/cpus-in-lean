#!/usr/bin/env python3
"""The pinned compiler: an official LLVM release, fetched by hash.

Every image of this suite is produced by exactly this toolchain (clang, ld.lld, llvm-objcopy,
llvm-nm, llvm-objdump). The release archives are the ones published at
https://github.com/llvm/llvm-project/releases; each is verified against the SHA-256 below before
anything is unpacked. Only the tools and the compiler's own headers are extracted, into an
ignored cache (`.toolchain/`, or `$OPENSSL_SUITE_TOOLCHAIN`).

usage: toolchain.py            fetch if needed and print the tool directory
"""
import hashlib
import os
import platform
import shutil
import subprocess
import sys
import tarfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSION = "23.1.5"
ARCHIVES = {
    ("Darwin", "arm64"): ("LLVM-23.1.5-macOS-ARM64.tar.xz",
                          "aba592b4a15e8f90c634c5367b51ec8418b8bcd2829865db331a17dc9418dcff"),
    ("Linux", "x86_64"): ("LLVM-23.1.5-Linux-X64.tar.xz",
                          "f72edb0b36580ece7f52e23858f00c18fad4e87395ea7ad05d7e55c39f8fc78a"),
    ("Linux", "aarch64"): ("LLVM-23.1.5-Linux-ARM64.tar.xz",
                           "44f1e4b7a125b2763d56386a199928dd57ec32e151cc6042dce2f7b0da7bb651"),
}
URL = "https://github.com/llvm/llvm-project/releases/download/llvmorg-" + VERSION + "/"
TOOLS = ["clang", "ld.lld", "llvm-objcopy", "llvm-nm", "llvm-objdump"]


def _wanted(parts):
    """Members to unpack: the tools, their shared libraries and clang's resource directory."""
    if len(parts) < 2:
        return False
    if parts[0] == "bin":
        return parts[1] in TOOLS + ["lld", "clang-" + VERSION.split(".")[0]]
    if parts[0] == "lib":
        return parts[1] == "clang" or (len(parts) == 2 and (".so" in parts[1] or parts[1].endswith(".dylib")))
    return False


def cache_dir():
    return Path(os.environ.get("OPENSSL_SUITE_TOOLCHAIN", ROOT / ".toolchain"))


def toolchain():
    """Directory holding the pinned tools, fetching and verifying the release on first use."""
    key = (platform.system(), platform.machine())
    if key not in ARCHIVES:
        raise SystemExit(f"No pinned LLVM {VERSION} release for {key}; supported: {sorted(ARCHIVES)}")
    name, digest = ARCHIVES[key]
    dest = cache_dir() / f"llvm-{VERSION}"
    marker = dest / "ARCHIVE.sha256"
    if marker.is_file() and marker.read_text().split() == [digest, name]:
        return dest / "bin"
    cache_dir().mkdir(parents=True, exist_ok=True)
    archive = cache_dir() / name
    if not archive.is_file() or _sha256(archive) != digest:
        print(f"Fetching {URL + name} (about 2 GB)", file=sys.stderr)
        tmp = archive.with_suffix(".part")
        if shutil.which("curl"):                       # the content is checked against the pin below
            subprocess.run(["curl", "-fL", "--retry", "3", "-o", str(tmp), URL + name], check=True)
        else:
            with urllib.request.urlopen(URL + name, timeout=120) as response, tmp.open("wb") as out:
                shutil.copyfileobj(response, out, 1 << 20)
        if _sha256(tmp) != digest:
            tmp.unlink()
            raise SystemExit(f"Hash mismatch for {name}; nothing was unpacked")
        tmp.rename(archive)
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir()
    with tarfile.open(archive, "r:xz") as tar:
        for member in tar:
            parts = Path(member.name).parts[1:]            # drop the release's top-level directory
            if _wanted(parts):
                member.name = str(Path(*parts))
                if member.islnk():
                    member.linkname = str(Path(*Path(member.linkname).parts[1:]))
                tar.extract(member, dest, filter="tar")     # the archive is hash-verified
    for tool in TOOLS:
        if not (dest / "bin" / tool).exists():
            raise SystemExit(f"{name} does not contain {tool}")
    marker.write_text(f"{digest}  {name}\n")
    archive.unlink()
    return dest / "bin"


def _sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


if __name__ == "__main__":
    print(toolchain())
