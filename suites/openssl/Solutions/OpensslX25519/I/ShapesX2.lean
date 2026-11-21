import Solutions.Exec.Shape
/-!
# Decoded instruction shapes: the rest of the X25519 image (part 2)

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

decode_shape [0x31, 0xC7] 2
decode_shape [0x31, 0xC9] 2
decode_shape [0x31, 0xD2] 2
decode_shape [0x31, 0xDB] 2
decode_shape [0x31, 0xF6] 2
decode_shape [0x31, 0xFF] 2
decode_shape [0x32, 0x1C, 0x3A] 3
decode_shape [0x39, 0xC8] 2
decode_shape [0x39, 0xF1] 2
decode_shape [0x39, 0xF2] 2
decode_shape [0x39, 0xF9] 2
decode_shape [0x46] 1
decode_shape [0x47] 1
decode_shape [0x49] 1
decode_shape [0x4E] 1
decode_shape [0x4F] 1
decode_shape [0x50] 1
decode_shape [0x51] 1
decode_shape [0x52] 1
decode_shape [0x66, 0x89, 0x46] 4
decode_shape [0x66, 0x89, 0x56] 4
decode_shape [0x66, 0x89, 0x5E] 4
decode_shape [0x66, 0x89, 0x7E] 4
decode_shape [0x68] 5
decode_shape [0x6A] 2
decode_shape [0x74] 2
decode_shape [0x75] 2
decode_shape [0x76] 2
decode_shape [0x80, 0x24, 0x24] 4
decode_shape [0x80, 0x64, 0x24] 5
decode_shape [0x83, 0xC6] 3
decode_shape [0x83, 0xE0] 3
decode_shape [0x83, 0xE1] 3
decode_shape [0x83, 0xE2] 3
decode_shape [0x83, 0xE3] 3
decode_shape [0x83, 0xE7] 3
decode_shape [0x85, 0xC0] 2
decode_shape [0x85, 0xC9] 2
