#!/usr/bin/env python3
"""Pin everything a proved task is a statement about.

usage: python3 tools/tcb.py            compare the trusted files with TCB.sha256
       python3 tools/tcb.py --update   rewrite TCB.sha256 (a deliberate change of what is claimed)

A theorem `Claims.t : Ssl.….t_correct` says something only relative to the definitions it unfolds
to: the task statements, the call harness, the specifications, the image bytes, the CPU model and
the Lean toolchain, plus the build configuration that decides which files those names refer to and
the audit that decides what counts as proved. TCB.sha256 lists exactly those files. A change to any
of them must be made on purpose, reviewed on its own, and is never part of a change that adds or
edits a proof.
"""
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
PINS = ROOT / "TCB.sha256"


def model_files():
    """The modules `X86.lean` imports, transitively (the model without its proofs and TSO extension)."""
    model = REPO / "x86_32"
    seen, todo = set(), ["X86"]
    while todo:
        module = todo.pop()
        if module in seen or not module.startswith("X86"):
            continue
        seen.add(module)
        path = model / (module.replace(".", "/") + ".lean")
        todo += re.findall(r"^(?:public )?import (\S+)$", path.read_text(), re.M)
    return [model / (m.replace(".", "/") + ".lean") for m in seen] + \
           [model / "lakefile.toml", model / "lake-manifest.json", model / "lean-toolchain"]


def trusted_files():
    suite = [ROOT / name for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "Ssl.lean",
                                      "Ssl/Bytes.lean", "Ssl/Harness.lean", "Audit.lean"]]
    suite += sorted((ROOT / "Ssl/Spec").glob("*.lean"))
    suite += sorted((ROOT / "Ssl").glob("*/Statement.lean")) + sorted((ROOT / "Ssl").glob("*/Image.lean"))
    tracked = {p for p in (ROOT / "Ssl").rglob("*.lean")} | {ROOT / "Ssl.lean"}
    if tracked - set(suite):
        raise SystemExit(f"Unpinned files in the statement library: {sorted(map(str, tracked - set(suite)))}")
    return sorted(suite + model_files())


def current():
    return "".join(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(REPO)}\n"
                   for p in trusted_files())


def check():
    now, pinned = current(), PINS.read_text()
    if now != pinned:
        old = dict(reversed(line.split(maxsplit=1)) for line in pinned.splitlines())
        new = dict(reversed(line.split(maxsplit=1)) for line in now.splitlines())
        changed = sorted(name for name in old.keys() | new.keys() if old.get(name) != new.get(name))
        raise SystemExit("The trusted base differs from TCB.sha256:\n  " + "\n  ".join(changed) +
                         "\nIf the change is intended, review it on its own and run "
                         "`python3 tools/tcb.py --update`; proofs then hold for the new definitions only.")
    return len(now.splitlines())


if __name__ == "__main__":
    if sys.argv[1:] == ["--update"]:
        PINS.write_text(current())
        print(f"pinned {len(current().splitlines())} trusted files")
    else:
        print(f"trusted base: {check()} files match TCB.sha256")
