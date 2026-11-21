#!/usr/bin/env python3
"""Check the pinned images, the available source cache, the trusted base and the specification
boundary, offline."""
import hashlib
import re
from pathlib import Path

from gen_image import pinned_image
import tcb

ROOT = Path(__file__).resolve().parents[1]


def check_sources(target):
    for line in (target / "SOURCES.sha256").read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        path = ROOT / "LICENSE.openssl" if name == "./LICENSE.txt" else target / "vendor" / name
        if (name == "./LICENSE.txt" or path.is_file()) and hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Hash mismatch: {path}")


def main():
    for target in sorted((ROOT / "targets").iterdir()):
        check_sources(target)
        data, _ = pinned_image(target.name)
        print(f"{target.name}: embedded image matches {hashlib.sha256(data).hexdigest()}")
    # No holes or declared axioms in the statement library or the proofs (the audit additionally
    # collects the axioms each claim really depends on).
    for path in [*(ROOT / "Ssl").rglob("*.lean"), *(ROOT / "Solutions").rglob("*.lean"),
                 ROOT / "Solutions.lean", ROOT / "Claims.lean"]:
        if re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|extern|unsafe|skipKernelTC)\b",
                     path.read_text()):
            raise SystemExit(f"Proof hole, declared axiom or kernel bypass in {path}")
    # The mathematical specifications must stay independent of the CPU and call harness.
    for path in (ROOT / "Ssl/Spec").glob("*.lean"):
        imports = re.findall(r"^import (.+)$", path.read_text(), re.M)
        if imports != ["Ssl.Bytes"]:
            raise SystemExit(f"Unexpected specification dependencies: {path}: {imports}")
    print(f"trusted base: {tcb.check()} files match TCB.sha256")
    print("Image pins, cached sources and specification boundary checked.")


if __name__ == "__main__":
    main()
