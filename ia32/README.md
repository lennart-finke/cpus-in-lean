# IA-32

A model of 32-bit x86 as pure Lean definitions. The same definitions are what the proofs in `X86/Proofs/` are about and what gets compiled to boot Linux 6.12.111 (see [`../validation/`](../validation/README.md)). There is no separate emulator that could drift from the specification.

The CPU identifies as an i686-class Pentium Pro without x87. Linux emulates the FPU (`CONFIG_MATH_EMULATION`), so floating point still works in user space. Booting to the shell takes about 100M instructions (≈ 9 s on an Apple M5).

## What's modelled
- The integer instruction set (≈ 330 opcodes), including BCD, string instructions with REP, CMPXCHG8B, CMOV, CPUID, RDTSC and MSRs.
- Segmentation, protection rings, interrupts and exceptions through the IDT, far control flow, port I/O with the TSS permission bitmap.
- Two-level paging (4 KiB and 4 MiB pages, A/D bits, CR0.WP) with a 1024-entry TLB that software must flush, as on hardware.
- PIC, PIT, UART and CMOS RTC, and the Linux 32-bit boot protocol.
- Deterministic virtual time: a nominal 100M instructions per second, with HLT skipping to the next timer event.

Not modelled (execution stops with `Fault.unsupported`): hardware task switching, call gates, virtual-8086 mode, x87/MMX/SSE, PAE/NX, SMM, APIC, debug-register breakpoints and alignment checks.

## Files
- `X86/Word.lean`, `State.lean`: operand sizes, bit names, CPU state.
- `X86/Machine.lean`: memory, paging, TLB, segmentation checks, the semantic monad `M`.
- `X86/Decode.lean`, `Alu.lean`, `Exec.lean`: decoder, flags and arithmetic, instruction semantics.
- `X86/Sys.lean`, `Step.lean`: descriptors, interrupt delivery, one architectural step.
- `X86/Dev.lean`, `Io.lean`, `Boot.lean`: devices, port bus, Linux boot setup.

## Proofs
`lake build X86Proofs` (or `./verify.sh`, which also rejects `sorry`). The theorems cover ALU results and flags against `BitVec`, every condition code after `CMP`, shifts, IMUL overflow, DIV/IDIV including exactly when #DE is raised, register aliasing, segment and page permission checks, and the 15-byte instruction limit.

Most proofs use `bv_decide`, which adds one axiom per theorem that trusts Lean's compiled LRAT checker.
