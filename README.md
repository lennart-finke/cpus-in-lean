# CPUs in Lean 4

Formal models of instruction sets and their implementations in Lean 4. The main one, [`x86_32/`](x86_32/README.md), models 32-bit mode on an AMD EPYC 7742. There is an experimental model of 64-bit mode as well.

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


## Requirements
- [elan](https://github.com/leanprover/elan) (Lean 4.34.1, from `lean-toolchain`) and Python 3
- QEMU 11.1.2 (`qemu-system-i386`, `qemu-system-x86_64`; older versions disagree with it) and clang for the differential tests
- For the Linux guest images: a Linux machine or VM with `build-essential` and an `i686-linux-gnu` cross toolchain (`validation/guest/build.sh`, `x86_64/guest/build.sh`)
