# x86-64

An experimental 64-bit model, separate from the IA-32 one (namespace `X64`), that boots Linux 6.12.111 to a BusyBox 1.36.1 shell.

```
$ lake build && ./linux-shell.command    # about a minute; exit with Ctrl-A x
$ .lake/build/bin/x64run --expect '~ # ' --send 'uname -sm\n' --expect 'Linux x86_64' --send '@exit' \
    guest/bzImage guest/initramfs.cpio   # scripted session
```

## What's modelled
- 16 GPRs, REX, RIP-relative addressing, FS/GS bases, string and atomic instructions.
- Four-level paging (4K/2M/1G pages, NX, A/D), no TLB; descriptor tables, TSS/IST, IRETQ, SYSCALL/SYSRETQ, SWAPGS.
- SSE/SSE2, MXCSR, FXSAVE/FXRSTOR in exact integer arithmetic; x87 only for the kernel's FPU save/restore.

Missing (execution stops): general x87, MMX, parts of SSE/SSE2, compatibility mode, call gates, hardware breakpoints.

## Testing
`./verify.sh [N] [SEED]`: `x64check`, N random ring-3 instructions against QEMU (registers, flags, exceptions, CR2, memory, PTEs, XMM, MXCSR), the Linux boot, and `../validation/guest/workload.sh` with identical output on QEMU and the model (`guest/check.py`). Skipped (QEMU is wrong): REP with TF, unmasked SIMD exceptions ([QEMU issue 215](https://gitlab.com/qemu-project/qemu/-/issues/215)), MIN/MAX with DAZ. Hardware tests: [`../validation/`](../validation/README.md#hardware-tests).

## Proofs
`lake build X64Proofs`: ALU flags, condition codes, shifts, division, register updates, canonical addresses, permissions, decoder length. Not yet: FP rounding, page walks, the executor. `Application.lean` composes finite runs of `step`.

## Guest images
`guest/build.sh`, on Linux (on macOS in a VM such as [Lima](https://lima-vm.io)):

```
$ sudo apt-get install -y build-essential gcc-x86-64-linux-gnu binutils-x86-64-linux-gnu \
    libc6-dev-amd64-cross flex bison bc libelf-dev libssl-dev lz4 cpio curl xz-utils bzip2 python3
$ bash guest/build.sh
```
