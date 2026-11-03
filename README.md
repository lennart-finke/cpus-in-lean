# CPUs in Lean 4

Formal models of instruction sets and their implementations in Lean 4. Currently, we mainly implement the behavior of the `x86-32` instruction set on the 32-bit mode in AMD EPYC 7742, but others are in scope as well. We have an experimental version of `x86-64`.

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
subDir = "ia32"
```

(`subDir = "x86_64"` and `name = "x86_64"` for the 64-bit model.)

## Why?
To prove correctness of binaries with respect to these formal models. This work is inspired by researchers like Nicholas Carlini and Keane Lucas, see [LLMs are making formal software verification feasible at a much larger scale](https://www.anthropic.com/research/formal-verification).


## Correctness
It's hard to know whether a formal model actually does what it's supposed to. The main ways we test for correctness are fuzzing against real hardware (`IA-32` using 32-bit mode on an AMD EPYC 7742) and QEMU. Sometimes QEMU deviates from Intel's manual, in which case the manual takes precedence. Sometimes the hardware test differs from either the manual and/or QEMU, in which case the hardware gets precedence (though this is highly debatable of course).

`./verify.sh` builds both models, checks the proofs, and runs a short QEMU differential test; `./verify.sh --full` also boots Linux on both models.

## Requirements
- [elan](https://github.com/leanprover/elan) (Lean 4.34.1, from `lean-toolchain`) and Python 3
- QEMU (`qemu-system-i386`, `qemu-system-x86_64`) and clang for the differential tests
- For the Linux guest images: a Linux machine or VM with `build-essential` and an `i686-linux-gnu` cross toolchain (`validation/guest/build.sh`, `x86_64/guest/build.sh`)
