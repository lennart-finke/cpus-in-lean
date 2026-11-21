import Solutions.Exec.Shape
/-!
# Decoded instruction shapes of the Poly1305 image (2/4)

The `decode_shape` theorems (`Solutions.Exec.Shape`) for the instructions of the image
(`targets/openssl_poly1305`) that the X25519 shape modules (imported by `Solutions.OpensslPoly1305.Shapes`)
do not define; written by `gen/genshapes.py` from `Solutions/Exec/shapes.py`.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

decode_shape [0x13, 0x78] 3
decode_shape [0x21, 0xC1] 2
decode_shape [0x21, 0xC2] 2
decode_shape [0x21, 0xC5] 2
decode_shape [0x21, 0xD9] 2
decode_shape [0x21, 0xEE] 2
decode_shape [0x21, 0xFA] 2
decode_shape [0x21, 0xFB] 2
decode_shape [0x21, 0xFE] 2
decode_shape [0x23, 0x44, 0x24] 4
decode_shape [0x23, 0x7C, 0x24] 4
decode_shape [0x29, 0xDE] 2
decode_shape [0x29, 0xF5] 2
decode_shape [0x31, 0xC1] 2
decode_shape [0x31, 0xCA] 2
decode_shape [0x31, 0xDB] 2
decode_shape [0x31, 0xF6] 2
decode_shape [0x31, 0xF9] 2
decode_shape [0x39, 0xF1] 2
decode_shape [0x40] 1
decode_shape [0x46] 1
decode_shape [0x49] 1
decode_shape [0x4F] 1
decode_shape [0x50] 1
decode_shape [0x52] 1
decode_shape [0x68] 5
decode_shape [0x6A] 2
decode_shape [0x72] 2
decode_shape [0x73] 2
decode_shape [0x74] 2
decode_shape [0x75] 2
decode_shape [0x77] 2
decode_shape [0x83, 0xC0] 3
decode_shape [0x83, 0xC2] 3
