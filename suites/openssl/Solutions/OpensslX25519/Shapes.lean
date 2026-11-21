import Solutions.Exec.Shape
/-!
# Decoded instruction shapes: fe_add, fe_sub

The `decode_shape` theorems (`Solutions.Exec.Shape`) for these instructions, written by
`Solutions/Exec/shapes.py` from the disassembly.
-/
open X86 Solutions.Logic Solutions.Exec Solutions.Exec.Shape

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 50000000

decode_shape [0x03, 0x32] 2
decode_shape [0x03, 0x42] 3
decode_shape [0x03, 0x72] 3
decode_shape [0x2B, 0x30] 2
decode_shape [0x2B, 0x50] 3
decode_shape [0x2B, 0x70] 3
decode_shape [0x56] 1
decode_shape [0x5E] 1
decode_shape [0x89, 0x31] 2
decode_shape [0x89, 0x41] 3
decode_shape [0x89, 0x51] 3
decode_shape [0x89, 0x71] 3
decode_shape [0x8B, 0x30] 2
decode_shape [0x8B, 0x32] 2
decode_shape [0x8B, 0x40] 3
decode_shape [0x8B, 0x44, 0x24] 4
decode_shape [0x8B, 0x52] 3
decode_shape [0x8B, 0x70] 3
decode_shape [0x8B, 0x72] 3
decode_shape [0xC3] 1
