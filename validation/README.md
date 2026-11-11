# Validation

Evidence that the [IA-32 model](../x86_32/README.md) behaves like real x86, plus the hardware tests for both models. `x86run` boots Linux, `x86test` replays test vectors, `x86sys` runs the system tests, and `x86litmus` explores concurrent executions; nothing here is imported by the model or its proofs.

```
$ lake build
$ ./verify.sh [N]    # N random QEMU tests, the Linux boot and the workload comparison
```

`x86run` options: `--mem MB`, `--max N` (instruction limit), `--expect PAT --send TEXT` (scripted input; `@exit` stops) and `--trace-from N --trace-count K` (register trace on stderr).

## QEMU differential tests
`test/run.sh N SEED` generates N random single instructions with random prefixes, operands, registers, flags, segment selectors and page-table bits, including page-crossing operands and single-stepping. A small kernel (`test/harness/`) runs each one under `qemu-system-i386` in ring 3. `x86test` then runs the same instruction on the model and compares the exception, CR2, registers, flags, selectors, a memory hash and the page-table entries.

So far 800,000 tests have shown 0 mismatches, covering 226 one-byte and 106 two-byte opcodes.

QEMU deviates from the Intel manual in a few places, which are not generated: AAM/AAD with an immediate ≥ 0x80, INVD/WBINVD at CPL 3, REP INS/OUTS with a zero count, REP with TF, and the read order of CMPS. Where QEMU deviates from hardware, `x86test` accepts the hardware behaviour and counts the case separately: page faults on read-modify-write operands (QEMU drops the W bit and sets A instead of A and D), and PUSHA, which QEMU probes as a whole instead of pushing in order.

## System tests
`test/sys/run.sh` builds a small multiboot test kernel (`test/sys/*.c`, clang only) and runs it under `qemu-system-i386` and on the model (`x86sys`), then compares the two serial transcripts line by line. It exercises what the single-instruction tests cannot: legacy and PAE paging with NX, debug-register breakpoints and RF, call gates, hardware task switches (including #DF through a task gate), virtual-8086 mode, the local APIC system-management mode, and the x87 FPU: 2,500 random operations over every operand class (denormals, pseudo-denormals, unnormals, NaNs, extreme exponents) with random rounding and precision control are compared with QEMU's softfloat, and stack faults, unmasked responses, #MF/FERR#, FIP/FDP/FOP and the C1 round-up indicator, which TCG does not model, are model-only checks (the kernel opens SMRAM and enables APM SMIs through QEMU's i440FX/PIIX4 chipset; the model has no chipset and `x86sys` starts with the firmware's SMBASE). MMX/SSE/SSE2 (`t_simd.c`, `t_simdx.c`): 6,500 random instructions (every MMX, SSE and SSE2 opcode and prefix form, register and memory operands, binary32/64 operands from every class, random RC/DAZ/FTZ and sticky flags with all exceptions masked) compared with QEMU (`-cpu qemu32,...,+sse2,-pni`), plus the #UD/#NM rules (CR0.EM/TS, CR4.OSFXSR), 16-byte alignment, undefined prefix combinations, prefix precedence, LDMXCSR/FXRSTOR reserved bits, the FXSAVE image and FXRSTOR; unmasked SIMD exceptions (#XM/#UD and their MXCSR flags), #MF for MMX instructions, the MMX exponent word, the two-NaN rule, MIN/MAX with DAZ, RCP/RSQRT special cases and FXSAVE's FIP/FDP are model-only (TCG returns the larger-significand NaN like x87 instead of the first operand, so two-NaN lanes are not generated for the QEMU comparison).

The x87 transcendental instructions are checked against an exact reference, `test/sys/x87ref.py`, written independently of the model (Python's `decimal` module, whose exp, ln and sqrt are correctly rounded, atan by argument halving, a different interval-rounding test). F2XM1, FYL2X, FYL2XP1 and FPATAN, which QEMU implements carefully in softfloat, are fuzzed against QEMU (3,000 cases with random rounding and precision control and every operand class). For every line where QEMU's result differs, `x87ref.py qemu out/qemu.txt` decides it and writes a per-line rule with its reason to `test/sys/x87t-deviations.txt` (it also measures QEMU's error in ulps against the SDM bound of vol. 1, 8.3.10). All 3,000 values agreed; the 231 rules record that TCG never reports the denormal-operand exception for these instructions (#D is in their SDM exception lists) and two NaN choices (QEMU takes ST(0); the SDM's table 4-7 takes the larger significand). The model must then match the corrected transcript. QEMU computes FSIN, FCOS, FPTAN and FSINCOS with host doubles, so for them (and to check C1, C2 and the stack effects of all eight, which TCG does not model) `x87ref.py table x87t_cases.h` generates 1,540 inputs with expected results, including arguments next to multiples of π/2 up to 2^62, tiny, huge, out-of-range and special operands; the test kernel compares them in the MODEL-ONLY section. Regenerate both files with `x87ref.py` after changing `t_x87t.c`.

Two more fuzzers cover paging and debug breakpoints (400 cases each by default; `pgf=N`, `dbf=N` on the command line). The paging fuzzer (`t_pgfuzz.c`) builds fresh page tables in each case, in 32-bit paging with or without CR4.PSE or in PAE paging with EFER.NXE on or off, with CR0.WP at random. The tables map an eight-page window of 4 KiB pages and sometimes a 4 MiB or 2 MiB page, onto a pool of frames, with random P, R/W, U/S, PWT, PCD, A, D, G, PAT and XD bits and occasional reserved bits. It then makes 3 to 8 accesses: reads and writes of 1, 2 or 4 bytes and instruction fetches, from ring 0 and ring 3, often across a page boundary. Each access prints its vector, error code, CR2 and the value read, or the bytes written. Every case ends with the accessed and dirty flags of each entry. The breakpoint fuzzer (`t_dbfuzz.c`) programs DR0 to DR3 and DR7 at random, with every R/W type and length, L/G enables and CR4.DE, and sometimes sets EFLAGS.TF. It then runs one load, store, read-modify-write, MOVS, PUSH or POP (memory or register), IN or OUT in ring 0 or ring 3, and prints DR6, the EIP and the RF image of every #DB. TCG reports only the first watchpoint that matches, and it splits a single-step trap and a data breakpoint on the same instruction into two #DBs, the second at the handler's first instruction. So `dbf` keeps only one matching data or I/O breakpoint and drops TF in such cases. The model-only `dbfm` runs the same generator without these exclusions and checks every #DB against an expectation computed in C (SDM 17.2.3, 17.3.1). The paging fuzzer found that the model did not set the accessed flag of a page-directory entry when the walk used it but the page-table entry then faulted (SDM 4.8). It also showed that 4 MiB PDEs lacked the reserved-bit check for bits 21:13 (CPUID reports no PSE-36); TCG implements PSE-36 anyway, so bits 20:13 are model-only (`pgfm.pse.rsvd`).

Where QEMU's TCG deviates from the Intel SDM, the rules in `test/sys/qemu-deviations.txt` rewrite the QEMU line to the SDM-defined result before comparing; each rule states the SDM section. Examples: reserved-bit page faults have P = 1, MOV SS delays debug traps past the next instruction, data breakpoints in REP instructions trap after the matching iteration, and a fault after a task switch commits is raised in the new task. Behaviour that TCG cannot run at all (the TSS T flag) comes after a `MODEL-ONLY` marker and is checked against `test/sys/model-only.expected`.

Control transfers (`t_xfer.c`) are fuzzed too: `tsf=N` hardware task switches (JMP/CALL to a TSS or a GDT/LDT task gate, INT n through an IDT task gate and IRET with NT, from ring 0 or 3, to 32- and 16-bit TSSs with random limits, busy and present bits, DPLs, segment and LDT selectors, EFLAGS including NT and VM, EIPs beyond the limit and previous-task links), and `cgf=N` far CALL/JMP directly or through 16- and 32-bit call gates (random DPLs, parameter counts, targets and inner stacks in the TSS, from rings 0 to 3) and far RETs to outer levels with random CS/SS and data segment registers (default 300 cases each). Every exception and the end of each case go through IDT task gates to recovery tasks, so the outcome (vector, error code, the task it was raised in, the new task's registers as saved in its TSS, the inner-stack frame) is observed from a clean task even after TCG has delivered a fault with the old task's EIP. The fuzzers found six model bugs: JMP/CALL to a TSS descriptor in the LDT switched tasks instead of raising #GP; an IRET to the current task loaded the TSS contents from before the switch saved the state; null selectors with RPL > 0 survived returns to outer levels; RETF to a 16-bit stack cleared ESP[31:16]; an inner-stack selector beyond the table limit raised #GP instead of #TS; and a call gate whose inner stack had no room for the frame raised #SS(0) after the offset check instead of #SS(new SS) before it. TCG deviations handled by rules: #TS for TSS selectors with TI = 1, #NP/#TS for not-present stack segments, CS.RPL = DPL after a CALL through a gate to a conforming segment; by exclusion with model-only checks: conforming task CS with DPL < RPL, offset checks of far CALLs and RETs, JMP through a gate to a not-present segment, inner-stack limits and ESP[31:16] of 16-bit inner stacks (TCG keeps the caller's), null FS/GS on returns, RF in the EFLAGS image of faults through task gates and the EIP of faults after the task-switch commit point.

## TSO memory-model tests

`lake build x86litmus` builds the concurrent execution explorer. Run
`python3 litmus/litmus.py check-expected litmus/tests litmus/diy` to compare all final states with
the pinned expected sets. The [litmus documentation](litmus/README.md) describes their provenance
and how to compare directly with herd7. `verify.sh` also checks that enabling the TSO access log
preserves single-CPU execution and records all stores, using 20,000 generated instruction vectors
(only those with paging off are checked).

## Hardware tests
These run on an x86-64 Linux server without root or KVM. Each instruction executes in user mode, and Linux signal handlers capture the result, for both models:

```
$ python3 test/native.py prepare test/out/run --count 20000 --seed 1    # or --memory, --hunt, --focused-sse
$ bash test/native_remote.sh test/out/run.tar.gz user@host
$ python3 test/native.py compare test/out/run-returned --prepared test/out/run
```

`--memory` adds loads, stores and read-modify-write operations on pages that are writable, read-only or unmapped. `--hunt` targets areas earlier runs missed, and `test/native_hunt.py` groups its mismatches. For privileged and paging behaviour, `test/hardware.py` runs the QEMU harness under KVM (`-accel kvm -cpu host`).

On an AMD EPYC 7742, about 475,000 observations across four campaigns now all match. Bugs found this way and by the Linux boot:
- AAS ignored the borrow out of AL.
- LOCK on non-lockable instructions did not raise #UD.
- Read-modify-write instructions skipped the write-back for a zero shift count and for an unchanged ARPL.
- Read-modify-write operands were translated as reads, giving the wrong page-fault error code.
- PUSHA and POPA restored the wrong state after a fault, and ENTER did not check its final stack byte.
- The second immediate of far pointers and ENTER re-read the first (found by the Linux boot).
- x86-64 SSE: wrong MXCSR flags with unmasked exceptions, and flush-to-zero at the underflow boundary.

Regression tests: `python3 test/rmw_regression.py` and `python3 test/stack_regression.py`.

## Linux guest
`guest/build.sh` builds Linux 6.12.111 from `tinyconfig` plus `guest/kernel.fragment`: a 486SX-class kernel with math emulation, an 8250 console and no SMP, APIC, PCI or ACPI. It also builds an initramfs with Debian's static i386 BusyBox. Run it in a Linux VM, e.g. on macOS:

```
$ limactl start --name=kbuild template:debian
$ limactl shell kbuild -- sudo apt-get install -y build-essential flex bison bc libelf-dev cpio lz4 gcc-i686-linux-gnu
$ limactl shell kbuild -- bash guest/build.sh
```

`guest/workload.sh` runs hashing, sort, a gzip round trip, shell arithmetic, floating-point awk (on the model's x87 FPU, which CPUID advertises), tmpfs I/O and `/proc` reads. Debian's BusyBox awk is built without its math library, so the transcendental instructions were checked in the guest with a small static test program instead (all results bit-identical to `test/sys/x87ref.py`). Its output on the model is byte-for-byte identical to QEMU's (`guest/workload.qemu.txt`).
