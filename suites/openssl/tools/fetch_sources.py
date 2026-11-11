#!/usr/bin/env python3
"""Fetch the hash-pinned OpenSSL 3.5.9 files needed for an optional C rebuild.

Downloaded files are an ignored cache. Existing files are verified, never silently replaced.
The ordinary Lean build and suite checks do not invoke this script or access the network.
"""
import argparse
import hashlib
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = "https://raw.githubusercontent.com/openssl/openssl/openssl-3.5.9/"


def fetch(target):
    directory = ROOT / "targets" / target
    for line in (directory / "SOURCES.sha256").read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        name = name.removeprefix("./")
        path = directory / "vendor" / name
        cached = path.is_file()
        if cached:
            data = path.read_bytes()
        elif name == "LICENSE.txt":
            data = (ROOT / "LICENSE.openssl").read_bytes()
        else:
            print(f"Fetching {target}: {name}")
            with urllib.request.urlopen(BASE + name, timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != digest:
            raise SystemExit(f"Source hash mismatch: {path}")
        if not cached:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*")
    args = parser.parse_args()
    names = sorted(p.name for p in (ROOT / "targets").iterdir())
    for target in args.targets or names:
        if target not in names:
            parser.error(f"unknown target: {target}")
        fetch(target)
