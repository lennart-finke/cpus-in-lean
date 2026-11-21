import Solutions.Exec.Shape
/-!
# Decoded instruction shapes of the Poly1305 image (3/4)

The `decode_shape` theorems (`Solutions.Exec.Shape`) for the instructions of the image
(`targets/openssl_poly1305`) that the X25519 shape modules (imported by `Solutions.OpensslPoly1305.Shapes`)
do not define; written by `gen/genshapes.py` from `Solutions/Exec/shapes.py`.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

decode_shape [0x83, 0xC5] 3
decode_shape [0x83, 0xC7] 3
decode_shape [0x83, 0xD0] 3
decode_shape [0x83, 0xE1] 3
decode_shape [0x83, 0xE3] 3
decode_shape [0x83, 0xE5] 3
decode_shape [0x83, 0xE7] 3
decode_shape [0x83, 0xF8] 3
decode_shape [0x83, 0xF9] 3
decode_shape [0x83, 0xFD] 3
decode_shape [0x85, 0xC0] 2
decode_shape [0x85, 0xC9] 2
decode_shape [0x85, 0xDB] 2
decode_shape [0x88, 0x16] 2
decode_shape [0x88, 0x1C, 0x30] 3
decode_shape [0x89, 0x08] 2
decode_shape [0x89, 0x11] 2
decode_shape [0x89, 0x86] 6
decode_shape [0x89, 0x9E] 6
decode_shape [0x89, 0xC5] 2
decode_shape [0x89, 0xC7] 2
decode_shape [0x89, 0xCB] 2
decode_shape [0x89, 0xDA] 2
decode_shape [0x89, 0xEB] 2
decode_shape [0x89, 0xF7] 2
decode_shape [0x8B, 0x01] 2
decode_shape [0x8B, 0x0C, 0x24] 3
decode_shape [0x8B, 0x31] 2
decode_shape [0x8B, 0x41] 3
decode_shape [0x8B, 0x59] 3
decode_shape [0x8B, 0x71] 3
decode_shape [0x8B, 0x79] 3
decode_shape [0x8B, 0x86] 6
decode_shape [0x8B, 0x9E] 6
