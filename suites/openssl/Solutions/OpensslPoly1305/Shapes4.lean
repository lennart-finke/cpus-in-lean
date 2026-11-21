import Solutions.Exec.Shape
/-!
# Decoded instruction shapes of the Poly1305 image (4/4)

The `decode_shape` theorems (`Solutions.Exec.Shape`) for the instructions of the image
(`targets/openssl_poly1305`) that the X25519 shape modules (imported by `Solutions.OpensslPoly1305.Shapes`)
do not define; written by `gen/genshapes.py` from `Solutions/Exec/shapes.py`.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

decode_shape [0x8D, 0x04, 0x0F] 3
decode_shape [0x8D, 0x1C, 0x29] 3
decode_shape [0x8D, 0x48] 3
decode_shape [0x8D, 0x4D] 3
decode_shape [0x8D, 0x4F] 3
decode_shape [0x8D, 0x84, 0x19] 7
decode_shape [0x8D, 0x86] 6
decode_shape [0x8D, 0x91] 6
decode_shape [0x8D, 0x96] 6
decode_shape [0x90] 1
decode_shape [0xA1] 5
decode_shape [0xBE] 5
decode_shape [0xC1, 0xE8] 3
decode_shape [0xC1, 0xE9] 3
decode_shape [0xC1, 0xEB] 3
decode_shape [0xC1, 0xEE] 3
decode_shape [0xC1, 0xEF] 3
decode_shape [0xC6, 0x84, 0x06] 8
decode_shape [0xC7, 0x01] 6
decode_shape [0xC7, 0x41] 7
decode_shape [0xC7, 0x86] 10
decode_shape [0xE8] 5
decode_shape [0xE9] 5
decode_shape [0xEB] 2
decode_shape [0xF7, 0x64, 0x24] 4
decode_shape [0xF7, 0xD1] 2
decode_shape [0xF7, 0xD6] 2
decode_shape [0xF7, 0xD8] 2
decode_shape [0xF7, 0xE3] 2
decode_shape [0xFF, 0x74, 0x24] 4
decode_shape [0xFF, 0xD0] 2
