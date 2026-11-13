# CPUs in Lean 4

Formal models of instruction sets and their implementations in Lean 4. The main one, [`x86_32/`](x86_32/README.md), models **32-bit mode on an AMD EPYC 7742** (Zen 2): the processor as 32-bit code sees it, in legacy protected, real and virtual-8086 mode and in compatibility mode under long mode. CPUID reports the 7742's identity and, of its feature bits, exactly the implemented ones ([`x86_32/CPUID.md`](x86_32/CPUID.md): 125 of the 162 feature bits of a real 7742's dump; the masked ones, such as the performance-counter extensions, IBS, SME/SEV, AVIC and scalable MCA, with their reasons). There is an experimental model of 64-bit mode, [`x86_64/`](x86_64/); the 32-bit model stops at the first 64-bit instruction and can hand its state to it.

What the IA-32 model covers:
- the integer instruction set, x87 (exact 80-bit arithmetic, correctly rounded transcendentals), MMX, SSE, SSE2;
- the Zen 2 extensions usable from 32-bit code: SSE3, SSSE3, SSE4.1, SSE4.2, SSE4a, MisalignSse, AES-NI, PCLMULQDQ, SHA, AVX, AVX2, FMA3, F16C, POPCNT, LZCNT, BMI1, BMI2, ADX, MOVBE, RDRAND/RDSEED, RDTSCP/RDPID, CLFLUSHOPT/CLWB/CLZERO, MONITOR/MWAIT(X), RDPRU, MCOMMIT, the XSAVE family;
- the system architecture: segmentation, paging (32-bit, PAE, 4-level with NX, global pages, PSE-36, SMEP, SMAP, UMIP), interrupts and exceptions with AMD's NMI and double-fault rules, task switches, call gates, virtual-8086 mode with VME/PVI, debug registers, alignment checking, SYSENTER/SYSCALL, SMM, MSRs, long-mode entry and compatibility mode, SVM with nested paging;
- a platform with up to 128 CPUs (local APICs and x2APIC, an I/O APIC, PIC, PIT, UART, RTC) under a deterministic scheduler, and a separate x86-TSO memory model.

Not modelled: 64-bit code, AVX-512 and other ISA the 7742 lacks, machine-check sources, caches and timing, and most devices (see [`x86_32/README.md`](x86_32/README.md)).

For example, to run Linux 6.12.111 on it (the guest images are built by `validation/guest/build.sh`, see [Requirements](#requirements)):
```
$ cd validation && lake build && ./.lake/build/bin/x86run guest/bzImage guest/initramfs.cpio
Linux version 6.12.111 ...
Run /init as init process
Hello from /init on the Lean x86 model
~ # echo $((6*7))
42
```

It can also run DOOM (slowly). On MacOS:

```
$ cd validation && doom/play.command # arrows to move, Ctrl to fire
```
<img width="400" height="225" alt="doom-small" src="https://github.com/user-attachments/assets/ed9fb555-24f2-4fb1-8819-8f20790c2bab" />

You can use the code from another Lean project with

```toml
[[require]]
name = "x86"
git = "https://github.com/lennart-finke/cpus-in-lean"
rev = "main"
subDir = "x86_32"
```

(`subDir = "x86_64"` and `name = "x86_64"` for the 64-bit model.)

## Why?
To prove correctness of binaries with respect to these formal models. This work is inspired by researchers like Nicholas Carlini and Keane Lucas, see [LLMs are making formal software verification feasible at a much larger scale](https://www.anthropic.com/research/formal-verification).


## Correctness
It's hard to know whether a formal model actually does what it's supposed to. The IA-32 model is tested by random differential testing against QEMU (an EPYC-Rome CPU under TCG; ten runs of 20,000 random instructions with 0 mismatches), a system-test kernel compared with QEMU (≈33,000 lines, plus model-only checks of what QEMU cannot run), independent Python references written from the manuals (crypto, FMA/F16C, PCMPxSTRx, XSAVE, VME, SVM, topology, ...), Linux (UP, and SMP with up to 16 CPUs, with transcripts identical to QEMU's), theorems about key properties, and native runs on a real EPYC 7742. Where QEMU deviates from the manuals (AMD's APM first, then Intel's SDM), the manual takes precedence, with every rule citing its section; where hardware differs from the manual and/or QEMU, the hardware gets precedence (though this is debatable).

The integer core matched the real 7742 on about 475,000 native observations. The self-contained user-mode bundle ran on a real 7742 (all 189,216 cases, in two runs: x87, MMX, SSE..SSE4a, AVX, AVX2/FMA/F16C, AES/PCLMULQDQ/SHA, XSAVE, the GPR extensions, alignment checking, compatibility mode and the open questions the manuals leave unsettled) and found 1,296 strict mismatches and 656 approximation observations; every one was traced to a root cause and the model now follows the hardware (x87 compare flags with unmasked exceptions, stack-fault priorities, FSCALE/FPREM/FST exception details, F2XM1/FYL2XP1 outside their documented domains, the x87 environment image, SHA alignment, EXTRQ/INSERTQ's upper half, HADD's NaN order, VEX encoding and #AC rules, RORX, RDPRU, undefined flags, a CPUID bit): 0 strict mismatches remained. An extended bundle (863,642 single instructions, every campaign run twice on two cores: an encoding fuzz over the whole opcode space, the integer set with every documented-undefined flag recorded, 16-bit code, FP depth, x87/XSAVE image and pointer rules, and a sweep of the RCPPS/RSQRTPS tables) then found 3,999 strict mismatches in 28 root causes, among them the lengths the processor decodes for undefined encodings (XOP, unknown VEX maps, 3DNow!), CMPS's read order, ARPL's write, ENTER, BSWAP r16, LOOPcc with REP prefixes, the 16-bit SHLD/SHRD rule, FSW.ES on x87 loads, which bytes FXSAVE/XSAVE write and where they fault, and a harness artifact (EFLAGS.ID/NT leaking between cases through Linux's sigreturn). The model now follows the hardware in all of them, also computes the 7742's value of every documented-undefined integer flag and its RCPPS/RSQRTPS tables (reconstructed from the sweep, all 52,794 lanes reproduced): 0 strict mismatches remain, and the 2,375 observations left are instructions whose results depend on the OS, the machine or time, 43 transcendental results within 1 ulp and 36 x87 pointers with bits an IA-32 model does not have. The KVM harness for the privileged features has not run on the processor yet; see [`validation/README.md`](validation/README.md). `./verify.sh` runs the gate (`--full` for everything).


## Requirements
- [elan](https://github.com/leanprover/elan) (Lean 4.34.1, from `lean-toolchain`) and Python 3
- QEMU 11.1.2 (`qemu-system-i386`, `qemu-system-x86_64`; older versions disagree with it) and clang for the differential tests
- For the Linux guest images: a Linux machine or VM with `build-essential` and an `i686-linux-gnu` cross toolchain (`validation/guest/build.sh`, `x86_64/guest/build.sh`)
