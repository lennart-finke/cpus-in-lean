#!/usr/bin/env python3
"""Is the model tested on the instructions the task images actually execute?

usage: python3 tools/encodings.py [N] [SEED]     (default 200000 vectors, seed 1)
       python3 tools/encodings.py --write        regenerate hw/encodings.txt

The executable checks (`sslcheck encodings`) record every instruction the four images execute and
reduce it to a class: opcode, ModRM `reg` for group opcodes, memory or register operand, operand
size, REP. `hw/encodings.txt` pins that list. This tool then generates N single-instruction vectors
with the model's differential fuzzer (`validation/test/gen.py`), classifies them the same way with
the model's own decoder, and requires every class the images use to occur among them. If QEMU and
the model's test runner are available it also runs the differential comparison on those vectors and
requires zero mismatches.

A class says which instruction form was tested, not which operand values; the complementary
evidence is `tools/hw.py`, which runs the images themselves on QEMU and on hardware.
"""
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VALIDATION = ROOT.parents[1] / "validation"
SSLCHECK = ROOT / ".lake/build/bin/sslcheck"
PIN = ROOT / "hw" / "encodings.txt"
MINIMUM = 5          # vectors required per class


def classes(*args):
    out = subprocess.run([SSLCHECK, *args], check=True, capture_output=True, text=True).stdout
    table = {}
    for line in out.splitlines():
        if line.startswith("op="):
            name, count = line.rsplit(" ", 1)
            table[name] = int(count)
    return table


def main(args):
    used = classes("encodings")
    listing = "".join(name + "\n" for name in sorted(used))
    if args == ["--write"]:
        PIN.write_text(listing)
        print(f"pinned {len(used)} instruction classes")
        return
    if PIN.read_text() != listing:
        raise SystemExit("hw/encodings.txt is out of date; run `python3 tools/encodings.py --write`")
    n = int(args[0]) if args else 200000
    seed = int(args[1]) if len(args) > 1 else 1
    out = ROOT / "out" / "fuzz"
    out.mkdir(parents=True, exist_ok=True)
    compared = shutil.which("qemu-system-i386") and (VALIDATION / ".lake/build/bin/x86test").is_file()
    if compared:
        result = subprocess.run([VALIDATION / "test/run.sh", str(n), str(seed)], check=True,
                                capture_output=True, text=True, env={**os.environ, "OUT": str(out)}).stdout
        summary = result.strip().splitlines()[-1]
        if ", 0 mismatches" not in summary:
            raise SystemExit(f"differential test against QEMU: {summary}")
    else:
        subprocess.run([sys.executable, VALIDATION / "test/gen.py", str(n), str(seed), out / f"v{seed}"],
                       check=True)
    fuzzed = classes("classify", str(out / f"v{seed}.bin"))
    thin = sorted((fuzzed.get(name, 0), name) for name in used if fuzzed.get(name, 0) < MINIMUM)
    if thin:
        raise SystemExit("instruction classes the images execute with too few fuzz vectors:\n" +
                         "\n".join(f"  {count:6}  {name}" for count, name in thin))
    covering = sum(fuzzed[name] for name in used)
    print(f"{len(used)} instruction classes executed by the images; each has at least "
          f"{min(fuzzed[name] for name in used)} of {n} fuzz vectors ({covering} in total)")
    print(f"differential test against QEMU: {summary}" if compared else
          "QEMU or validation/x86test not available: vectors classified but not compared")


if __name__ == "__main__":
    main(sys.argv[1:])
