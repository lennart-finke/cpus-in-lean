# Writes the `decode_shape` commands (Solutions/Exec/Shape.lean) for the instructions of a disassembly.
#
#   python3 shapes.py <Image.lean> <disassembly .dis> <lo hex> <hi hex> [<out.lean> <title>]
#
# <Image.lean> is a suite's image module (`def base`, `def chunkSize`, `def chunkN : Nat := 0x…`),
# <disassembly> the matching llvm-objdump listing (lines `  addr:  mnemonic operands`); the instructions
# whose address lies in [lo, hi) are read from the image bytes, their length from the next address.
# Without <out.lean> the commands are printed; with it, a complete Lean module is written.
# The literal bytes of a shape are the prefixes, the opcode (0F, 0F 38, 0F 3A maps) and the ModRM and
# SIB bytes; displacement and immediate bytes stay symbolic. Opcodes not listed in NOMODRM are taken
# to have a ModRM byte (true for everything else in the one-byte map except the rarely used ones
# below); 16-bit addressing (67 prefix) is not handled.
import re, sys

img, dis, lo, hi = sys.argv[1], sys.argv[2], int(sys.argv[3], 16), int(sys.argv[4], 16)
src = open(img).read()
base = int(re.search(r"def base : UInt32 := (0x[0-9A-Fa-f]+)", src).group(1), 16)
chunk = int(re.search(r"def chunkSize : Nat := (\d+)", src).group(1))
chunks = {int(m.group(1)): int(m.group(2), 16)
          for m in re.finditer(r"def chunk(\d+) : Nat := 0x([0-9A-Fa-f]+)", src)}


def byte(i):
    return (chunks[i // chunk] >> (8 * (i % chunk))) & 255


addrs = sorted({int(m.group(1), 16) for m in (re.match(r"\s+([0-9a-f]+):\s", l) for l in open(dis)) if m})
PREFIX = {0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x66, 0x67, 0xF0, 0xF2, 0xF3}
# one-byte opcodes without ModRM
NOMODRM = ({0x04, 0x05, 0x0C, 0x0D, 0x14, 0x15, 0x1C, 0x1D, 0x24, 0x25, 0x2C, 0x2D, 0x34, 0x35, 0x3C, 0x3D,
            0x06, 0x07, 0x0E, 0x16, 0x17, 0x1E, 0x1F, 0x27, 0x2F, 0x37, 0x3F, 0x60, 0x61, 0x68, 0x6A,
            0x6C, 0x6D, 0x6E, 0x6F, 0x9A, 0xC2, 0xC3, 0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,
            0xD4, 0xD5, 0xD6, 0xD7, 0xEA, 0xF1, 0xF4, 0xF5, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD}
           | set(range(0x40, 0x60)) | set(range(0x70, 0x80)) | set(range(0x90, 0xC0))
           | set(range(0xE0, 0xF0)))
# 0F-map opcodes without ModRM: jcc rel32, bswap, cpuid, rdtsc, push/pop fs/gs, …
NOMODRM_0F = (set(range(0x80, 0x90)) | set(range(0xC8, 0xD0))
              | {0x05, 0x06, 0x07, 0x08, 0x09, 0x0B, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x77,
                 0xA0, 0xA1, 0xA2, 0xA8, 0xA9, 0xAA})

shapes = set()
for a, b in zip(addrs, addrs[1:]):
    if not (lo <= a < hi):
        continue
    bs = [byte(a - base + k) for k in range(b - a)]
    k = 0
    while k < len(bs) and bs[k] in PREFIX:
        k += 1
    op = bs[k]
    if op == 0x0F:
        op2 = bs[k + 1]
        if op2 in (0x38, 0x3A):
            k += 3
        elif op2 in NOMODRM_0F:
            shapes.add((tuple(bs[:k + 2]), len(bs)))
            continue
        else:
            k += 2
    elif op in NOMODRM:
        shapes.add((tuple(bs[:k + 1]), len(bs)))
        continue
    else:
        k += 1
    modrm = bs[k]
    k += 1
    if (modrm >> 6) != 3 and (modrm & 7) == 4:
        k += 1
    shapes.add((tuple(bs[:k]), len(bs)))

lines = ["decode_shape [" + ", ".join(f"0x{x:02X}" for x in s) + f"] {n}"
         for s, n in sorted(shapes) if s != (0xCC,)]
if len(sys.argv) > 5:
    hdr = """import Solutions.Exec.Shape
/-!
# Decoded instruction shapes: %s

The `decode_shape` theorems (`Solutions.Exec.Shape`) for these instructions, written by
`Solutions/Exec/shapes.py` from the disassembly.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

""" % sys.argv[6]
    open(sys.argv[5], "w").write(hdr + "\n".join(lines) + "\n")
else:
    print("\n".join(lines))
