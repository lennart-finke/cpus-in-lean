import Solutions.Exec.Shape
/-!
# Decoded instruction shapes: the rest of the X25519 image (part 4)

The `decode_shape` theorems (`Solutions.Exec.Shape`) of the instructions of `ossl_x25519`,
`fe_invert`, `fe_tobytes`, `fe_0`, `fe_1`, `fe_copy`, `fe_frombytes`,
`x25519_scalar_mult_generic`, `OPENSSL_cleanse`, `CRYPTO_memcmp`, `memcpy`, `memmove`, `memset`
not already in `Shapes*`/`I/ShapesM121`; written by `Solutions/Exec/shapes.py` (via
.lake/scratch/l/newshapes.py).
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

decode_shape [0x8D, 0x74, 0x24] 4
decode_shape [0x8D, 0x7C, 0x24] 4
decode_shape [0x8D, 0x84, 0x01] 7
decode_shape [0x8D, 0x84, 0x10] 7
decode_shape [0x8D, 0x84, 0x24] 7
decode_shape [0x8D, 0x84, 0x81] 7
decode_shape [0x8D, 0x88] 6
decode_shape [0x8D, 0x8C, 0x24] 7
decode_shape [0x8D, 0x8F] 6
decode_shape [0x8D, 0x94, 0x24] 7
decode_shape [0x8D, 0x94, 0x55] 7
decode_shape [0x8D, 0x9C, 0x24] 7
decode_shape [0x8D, 0xAC, 0x24] 7
decode_shape [0x8D, 0xB4, 0x24] 7
decode_shape [0x8D, 0xB5] 6
decode_shape [0x8D, 0xBC, 0x24] 7
decode_shape [0x90] 1
decode_shape [0xA1] 5
decode_shape [0xBE] 5
decode_shape [0xBF] 5
decode_shape [0xC1, 0xE0] 3
decode_shape [0xC1, 0xE2] 3
decode_shape [0xC1, 0xE3] 3
decode_shape [0xC1, 0xE7] 3
decode_shape [0xC1, 0xE8] 3
decode_shape [0xC1, 0xE9] 3
decode_shape [0xC1, 0xEA] 3
decode_shape [0xC1, 0xEB] 3
decode_shape [0xC1, 0xEE] 3
decode_shape [0xC1, 0xEF] 3
decode_shape [0xC1, 0xF8] 3
decode_shape [0xC7, 0x06] 6
decode_shape [0xE8] 5
decode_shape [0xE9] 5
decode_shape [0xEB] 2
decode_shape [0xFF, 0x74, 0x24] 4
decode_shape [0xFF, 0xB4, 0x24] 7
decode_shape [0xFF, 0xD0] 2
