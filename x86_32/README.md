# IA-32

A model of 32-bit x86 as pure Lean definitions. The same definitions are what the proofs in `X86/Proofs/` are about and what gets compiled to boot Linux 6.12.111 (see [`../validation/`](../validation/README.md)). There is no separate emulator that could drift from the specification.

The CPU identifies as an i686-class Pentium Pro with an x87 FPU, MMX, FXSAVE/FXRSTOR, SSE and SSE2, debugging extensions, PAE, NX and a local APIC. Linux uses the model's FPU and saves it with FXSAVE ("x87 FPU will use FXSAVE") instead of its math emulator. Booting to the shell takes about 62M instructions (≈ 12 s).

## What's modelled
- The integer instruction set (≈ 330 opcodes), including BCD, string instructions with REP, CMPXCHG8B, CMOV, CPUID, RDTSC and MSRs.
- Segmentation, protection rings, interrupts and exceptions through the IDT, far control flow, port I/O with the TSS permission bitmap.
- Call gates (16- and 32-bit; inner-privilege calls switch stacks and copy parameters) and hardware task switching: JMP/CALL to a TSS or task gate, task gates in the IDT (as Linux uses for #DF), IRET with NT, 32- and 16-bit TSSs, busy/NT/link bookkeeping and the TSS T flag. A fault after the switch has committed is delivered in the new task.
- Virtual-8086 mode (without CR4.VME): entry by IRET or task switch, interrupts and exceptions to ring-0 handlers, IOPL-sensitive instructions.
- Two-level paging (4 KiB and 4 MiB pages, A/D bits, CR0.WP) and PAE paging (PDPTE registers, 2 MiB pages, reserved-bit faults, execute-disable with EFER.NXE), with a 1024-entry TLB that software must flush, as on hardware.
- Debug registers: instruction, data and I/O breakpoints, single-step, general detect, RF, and debug traps held across MOV SS / POP SS (so `MOV SS; INT n` takes the #DB at the handler entry, the behaviour behind CVE-2018-8897).
- The x87 FPU (`X86/Float80.lean`, `X86/Fpu.lean`): exact 80-bit arithmetic with rounding and precision control, denormals, x87 NaN rules, masked and unmasked exception responses (wrapped exponents, #MF, FERR#), stack faults, loads/stores of all memory formats including BCD, compares, FPREM/FPREM1, FSCALE, FXTRACT, FRNDINT, constants, FCMOV/FCOMI, the environment and FNSAVE/FRSTOR formats, and FIP/FDP/FOP.
- The x87 transcendental instructions (`X86/Transcendental.lean`): F2XM1, FYL2X, FYL2XP1, FPATAN, FSIN, FCOS, FSINCOS and FPTAN return the correctly rounded value of the exact function in the current rounding mode, which is within the SDM's accuracy bounds (below 1 ulp, 1.5 ulps in directed modes; vol. 1, 8.3.10). The engine evaluates series in ball arithmetic (integer center and radius, each operation's error bound stated in the source) and rounds both ends of the enclosure, raising the working precision until they agree (Ziv's strategy); exactly representable results (2^±1 − 1, y·log2(2^k), the zero/infinity/π-multiple rows of the SDM tables) are computed directly, and exact elementary bounds (x − x³/6 < sin x < x, ...) keep tiny arguments cheap. FSIN, FCOS, FSINCOS and FPTAN reduce the argument exactly by Pi/2, where Pi is the SDM's 66-bit approximation 0.C90FDAA22168C234C·2^2 (vol. 1, 8.3.8), with the nearest quotient: |x| ≤ Pi/4 gives the correctly rounded sin x itself, larger arguments sin(x + k(π − Pi)/2), the behaviour the SDM describes as approximating sin(x·π/Pi). Operands with |x| ≥ 2^63 set C2 and leave ST(0) unchanged. Where the SDM leaves the result undefined (F2XM1 with |x| > 1, FYL2XP1 outside √2/2 − 1 ≤ x ≤ √2 − 1, AMD's documented range), the model follows QEMU: an invalid operation. FPTAN and FSINCOS put a NaN result in both destinations; FSINCOS sets C1 if either result was rounded up. An unmasked IE, DE or ZE stops any x87 instruction before the lower-priority overflow, underflow and precision exceptions are detected (vol. 1, 4.9.2).
- MMX, SSE and SSE2 (`X86/Simd.lean`, `X86/Float.lean`; Pentium 4 level without SSE3): MM0–7 aliased to the x87 registers (TOP = 0, tags valid, exponent word all ones; EMMS), XMM0–7 and MXCSR with exact binary32/binary64 arithmetic (rounding modes, DAZ, FTZ, all six exception flags, unmasked exceptions as #XM or #UD with the destination preserved), every packed-integer, move, shuffle, compare and conversion instruction, the mandatory-prefix decoding of the 0F map (undefined prefix combinations are #UD), 16-byte alignment checks, CR4.OSFXSR/OSXMMEXCPT, FXSAVE/FXRSTOR (MXCSR_MASK = 0xFFFF), LDMXCSR/STMXCSR, fences and non-temporal stores. RCPPS/RSQRTPS, whose exact results are implementation specific, are defined as the round-to-nearest values of 1/x and 1/√x with the SDM's special cases (see the module documentation).
- System-management mode: SMIs through the APM control port (0xB2), the 32-bit SMRAM state-save map, RSM and SMBASE relocation (SMRAM protection is the chipset's and is not modelled).
- PIC, PIT, UART, CMOS RTC, a local APIC (timer, self-IPIs, priorities; the PIC is wired through LINT0), and the Linux 32-bit boot protocol.
- Deterministic virtual time: a nominal 100M instructions per second, with HLT skipping to the next timer event.

Not modelled (execution stops with `Fault.unsupported`, or the feature is absent): SSE3 and later (#UD), CLFLUSH (#UD: CPUID does not report it), alignment checks, NMI, CR4.VME/PVI, the APIC's NMI/INIT/SIPI delivery modes, TSC-deadline and x2APIC modes, I/O APIC and multiprocessing.

## Files
- `X86/Word.lean`, `State.lean`: operand sizes, bit names, CPU state.
- `X86/Machine.lean`: physical memory and APIC decoding, paging (32-bit and PAE), TLB, breakpoint matching, segmentation checks, the semantic monad `M`.
- `X86/Decode.lean`, `Alu.lean`, `Exec.lean`: decoder (one-byte, 0F, 0F 38, 0F 3A maps and VEX), flags and arithmetic, instruction semantics.
- `X86/Cpuid.lean`: table-driven CPUID with the leaves of an EPYC 7742, reporting only the implemented features (`implemented`); the identity is still the former one (`identity := .legacy`).
- `X86/Dispatch.lean`, `X86/Ext/*.lean`: instruction dispatch with hooks into one module per extension workstream (stubs today); see [`EXTENDING.md`](EXTENDING.md).
- `X86/Float80.lean`, `Transcendental.lean`, `Fpu.lean`: extended-precision arithmetic, transcendental functions and x87 instructions.
- `X86/Float.lean`, `Simd.lean`: binary32/64 arithmetic, MMX, SSE, SSE2 and FXSAVE.
- `X86/Sys.lean`, `Step.lean`: descriptors, task switches, gates, interrupt delivery, virtual-8086 mode, one architectural step (including debug traps).
- `X86/Dev.lean`, `Io.lean`, `Boot.lean`: devices (including the local APIC), port bus, Linux boot setup.

## Proofs
`lake build X86Proofs` (or `./verify.sh`, which also rejects `sorry`). The theorems cover ALU results and flags against `BitVec`, every condition code after `CMP`, shifts, IMUL overflow, DIV/IDIV including exactly when #DE is raised, register aliasing, segment and page permission checks, execute-disable (`paeAllowed_nx`: with NXE, no fetch from a page with XD set at any level; `translate_hit_nx`: the TLB never satisfies such a fetch), that disabled breakpoints have no effect (`dbData_disabled`), that call gates enforce their DPL (`callGate_dpl`), that virtual-8086 code runs at CPL 3 (`cpl_vm86`), that RSM is #UD outside SMM (`rsm_outside_smm`), that CR0.EM/TS make every ESC instruction fault with #NM before touching state (`fpCheck_nm`), that FSIN/FCOS/FPTAN/FSINCOS with |x| ≥ 2^63 leave the register stack untouched and set C2 (`fpTrig_out_of_range`), the exact transcendental cases (`f2xm1_one`, `trigFinite_zero`) and that F2XM1 outside its domain is invalid (`f2xm1_out_of_domain`), that SSE instructions are #UD while CR4.OSFXSR is clear (`sseCheck_noosfxsr`) and MMX instructions #UD/#NM with CR0.EM/TS (`mmxPre_em`, `mmxPre_ts`), that every MMX instruction leaves TOP = 0 with all registers valid (`mmxCheck_ok`), that EMMS empties them (`emms_empty`) and that an MMX write sets the exponent word to all ones (`setMm_reg`), that the APIC only presents interrupts above the processor priority (`apic_pending_above_ppr`), and the 15-byte instruction limit.

These are selected properties; the floating-point engines do not yet have a complete proof of arithmetic and rounding correctness.

Most proofs use `bv_decide`, which adds one axiom per theorem that trusts Lean's compiled LRAT checker.

## Multiprocessor model

`X86/Tso.lean` retains the x86-TSO store-buffer model and its proofs. MFENCE drains the buffer;
non-temporal and masked stores, APIC MMIO, SMM, paging and I/O remain outside its supported scope.
The single-CPU model supports the system features described above.
Build the separate library with `lake build X86Tso`; [`../validation/litmus/`](../validation/litmus/README.md)
contains its concurrency tests.
