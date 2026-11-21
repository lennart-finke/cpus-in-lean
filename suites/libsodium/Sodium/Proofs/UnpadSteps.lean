import Sodium.Proofs.PadRun
/-!
# `sodium_unpad`, in three straight-line pieces

```
100d30 push %ebp … sub $0x8,%esp      the prologue: saves four registers, pad_len = 0 at (%esp),
100d37 … 100d6f                        len - 1 at 4(%esp); block - 1 < len, so no early return
100d70 movzbl (%edi),%esi … jne        the loop body (20 instructions), one byte from the end each
100da0 dec %eax … ret                  the epilogue: stores len - 1 - pad_len, returns valid - 1
```

The stack pointer in the loop is `t`, 24 bytes below the entry stack pointer; the arguments are at
`t + 28` (`lenp`), `t + 32` (`buf`), `t + 36` (`len`), `t + 40` (`block`). Each piece is run by
`run_chain` on an abstract memory; the memory facts are hypotheses in `toNat` form.
-/
namespace Sodium.Proofs.Unpad
open X86 Ssl Solutions.Logic Solutions.Exec Solutions.Cbx Sodium.Proofs Sodium.Utils Sodium.Proofs.PadLib
  Sodium.Proofs.PadRun
attribute [local cbv_opaque] Image.bytes
attribute [-cbvSimprocAttr] Solutions.Cbx.cbvRdWr4 Solutions.Cbx.cbvRdWr

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000
set_option Elab.async false

def Lpre : List UInt32 :=
  [1051952, 1051953, 1051954, 1051955, 1051956, 1051959, 1051963, 1051967, 1051974, 1051977, 1051982, 1051984,
   1051986, 1051990, 1051994, 1051995, 1051999, 1052001, 1052003, 1052005, 1052006, 1052007, 1052008, 1052009,
   1052010, 1052011, 1052012, 1052013, 1052014, 1052015]

def Lbody : List UInt32 :=
  [1052016, 1052019, 1052022, 1052023, 1052026, 1052028, 1052030, 1052036, 1052037, 1052039, 1052043, 1052046,
   1052049, 1052051, 1052053, 1052055, 1052058, 1052059, 1052060, 1052062]

def Lexit : List UInt32 :=
  [1052016, 1052019, 1052022, 1052023, 1052026, 1052028, 1052030, 1052036, 1052037, 1052039, 1052043, 1052046,
   1052049, 1052051, 1052053, 1052055, 1052058, 1052059, 1052060, 1052062, 1052064, 1052065, 1052069, 1052072,
   1052076, 1052078, 1052081, 1052082, 1052083, 1052084, 1052085]

/-- The barrier bit of an iteration, as the machine computes it. -/
def ubit (c pl acc : UInt32) : UInt32 :=
  ((((c.xor 128).add 4294967295).land ((pl.add 4294967295).land (acc.add 4294967295))).shiftRight 8).land 1

/-- The padding length after an iteration. -/
def upl (c pl acc i : UInt32) : UInt32 := pl.lor ((UInt32.sub 0 (ubit c pl acc)).land i)

end Sodium.Proofs.Unpad
