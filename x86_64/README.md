# x86-64

An experimental model of 64-bit x86, independent of the IA-32 one (its own Lake package and namespace `X64`). It boots Linux 6.12.111 to a BusyBox 1.36.1 shell; kernel decompression, paging, interrupts and system calls all run in the model.

```
$ lake build && ./linux-shell.command    # boots in about a minute; exit with Ctrl-A x
```

Scripted sessions:

```
$ .lake/build/bin/x64run --expect '~ # ' --send 'uname -sm\n' --expect 'Linux x86_64' --send '@exit' \
    guest/bzImage guest/initramfs.cpio
```

## What's modelled
- 16 GPRs with partial-register aliases, REX prefixes, RIP-relative addressing, FS/GS bases, string and atomic instructions.
- Four-level paging (4 KiB, 2 MiB and 1 GiB pages, NX, A/D bits). There is no TLB; every access walks the page tables.
- Descriptor tables, TSS/IST stacks, IRETQ, SYSCALL/SYSRETQ and SWAPGS.
- SSE/SSE2, including binary32/binary64 arithmetic, MXCSR and FXSAVE/FXRSTOR. Floating point is computed with exact integer arithmetic, not the host FPU.
- x87 only as far as the kernel's FPU save/restore path needs.

Not yet modelled: general x87 arithmetic, MMX, parts of SSE/SSE2, compatibility mode, call gates and hardware breakpoints. Unsupported instructions stop execution.

## Testing
`./verify.sh [N] [SEED]` builds the model and proofs, runs `x64check` (targeted checks), N random instructions against QEMU, and the Linux boot. It then runs `../validation/guest/workload.sh` on both QEMU and the model and requires identical output (`guest/check.py`).

The QEMU test runs each instruction in ring 3 and compares registers, flags, exceptions, CR2, a memory hash, page-table entries, XMM registers and MXCSR. Cases where QEMU itself is wrong are not generated: REP with TF, unmasked SIMD exceptions ([QEMU issue 215](https://gitlab.com/qemu-project/qemu/-/issues/215)) and MIN/MAX with DAZ. Hardware tests are in [`../validation/`](../validation/README.md#hardware-tests).

## Proofs
`lake build X64Proofs`. The theorems cover ALU results and flags, comparisons and condition codes, shifts, division, register updates, canonical addresses, permission checks and decoder length. Floating-point rounding, the page walker and the full executor have no proofs yet. `Application.lean` composes finite executions of `step`.

## Guest images
`guest/build.sh` builds the kernel and a static BusyBox on Linux (on macOS, in a VM such as [Lima](https://lima-vm.io)):

```
$ sudo apt-get install -y build-essential gcc-x86-64-linux-gnu binutils-x86-64-linux-gnu \
    libc6-dev-amd64-cross flex bison bc libelf-dev libssl-dev lz4 cpio curl xz-utils bzip2 python3
$ bash guest/build.sh
```
