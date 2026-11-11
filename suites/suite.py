#!/usr/bin/env python3
"""Build and check a task suite with the tools of the OpenSSL suite (`openssl/tools`).

usage, from a suite directory:
    python3 ../suite.py                          check, build the Lean package, run its checks
    python3 ../suite.py check                    pins, cached sources, statement library; offline
    python3 ../suite.py build [--pin] [TARGET…]  rebuild with the pinned LLVM and compare (or re-pin)

Besides the OpenSSL suite's keys, a `targets/*/target.json` names the suite's statement library
(`lib`: its directory and Lean namespace) and the URL the target's upstream sources are fetched
from (`upstream`, joined with the names in SOURCES.sha256). Everything else is the OpenSSL suite's:
compiler, flags, runtime, linker script, image format and the meaning of the pins (see
`openssl/BUILD.md`). Its tools are imported unchanged and pointed at this suite.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path.cwd()
TARGETS = {p.name: json.loads((p / "target.json").read_text()) for p in sorted((HERE / "targets").iterdir())}
LIB = next(iter(TARGETS.values()))["lib"]
sys.path.insert(0, str(Path(__file__).resolve().parent / "openssl" / "tools"))
import build, check, fetch_sources, gen_image  # noqa: E402


class Root(type(HERE)):
    """This suite's directory; the tools' statement-library directory `Ssl` is `LIB` here."""
    def __truediv__(self, key):
        return super().__truediv__(LIB if key == "Ssl" else key)


ROOT = Root(HERE)
for tool in (build, check, fetch_sources, gen_image):
    tool.ROOT = ROOT
gen_image.CFG = {**gen_image.CFG, "stmt_ns": LIB}
build.LDFLAGS = ["../openssl/tools/image.ld" if arg == "tools/image.ld" else arg for arg in build.LDFLAGS]


def check_suite():
    for target in TARGETS:
        check.check_sources(ROOT / "targets" / target)
        data, _ = gen_image.pinned_image(target)
        print(f"{target}: embedded image matches {hashlib.sha256(data).hexdigest()}")
    for path in (HERE / LIB).rglob("*.lean"):
        if re.search(r"\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe)\b", path.read_text()):
            raise SystemExit(f"Proof hole, declared axiom or kernel bypass in {path}")
    for path in (HERE / LIB / "Spec").glob("*.lean"):   # specifications are independent of the CPU model
        if re.findall(r"^import (.+)$", path.read_text(), re.M):
            raise SystemExit(f"A specification must not import anything: {path}")
    print("Image pins, cached sources and specification boundary checked.")


def verify():
    check_suite()
    lake = shutil.which(os.environ.get("LAKE", "lake")) or str(Path.home() / ".elan/bin/lake")
    subprocess.run([lake, "build"], check=True)
    subprocess.run([lake, "exe", "check"], check=True)
    print(f"{HERE.name.upper()} SUITE CHECKS PASSED (every task is open: there are statements, no proofs)")


if __name__ == "__main__":
    command, *args = sys.argv[1:] or ["verify"]
    if command == "verify" and not args:
        verify()
    elif command == "check" and not args:
        check_suite()
    elif command == "build":
        for name in [a for a in args if a != "--pin"] or TARGETS:
            if name not in TARGETS:
                raise SystemExit(f"unknown target: {name}")
            fetch_sources.BASE = TARGETS[name]["upstream"]
            build.build(name, "--pin" in args)
    else:
        raise SystemExit(__doc__)
