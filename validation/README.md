# Validation

Evidence that the [IA-32 model](../ia32/README.md) behaves like real x86, plus the hardware tests for both models. `x86run` boots Linux on the model and `x86test` replays test vectors; nothing here is imported by the model or its proofs.

```
$ lake build
$ ./verify.sh [N]    # N random QEMU tests, the Linux boot and the workload comparison
```

`x86run` options: `--mem MB`, `--max N` (instruction limit), `--expect PAT --send TEXT` (scripted input; `@exit` stops) and `--trace-from N --trace-count K` (register trace on stderr).

## QEMU differential tests
`test/run.sh N SEED` generates N random single instructions with random prefixes, operands, registers, flags, segment selectors and page-table bits, including page-crossing operands and single-stepping. A small kernel (`test/harness/`) runs each one under `qemu-system-i386` in ring 3. `x86test` then runs the same instruction on the model and compares the exception, CR2, registers, flags, selectors, a memory hash and the page-table entries.

So far 800,000 tests have shown 0 mismatches, covering 226 one-byte and 106 two-byte opcodes.

QEMU deviates from the Intel manual in a few places, which are not generated: AAM/AAD with an immediate ≥ 0x80, INVD/WBINVD at CPL 3, REP INS/OUTS with a zero count, REP with TF, and the read order of CMPS. Where QEMU deviates from hardware, `x86test` accepts the hardware behaviour and counts the case separately: page faults on read-modify-write operands (QEMU drops the W bit and sets A instead of A and D), and PUSHA, which QEMU probes as a whole instead of pushing in order.

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

`guest/workload.sh` runs hashing, sort, a gzip round trip, shell arithmetic, floating-point awk (through the kernel's x87 emulator), tmpfs I/O and `/proc` reads. Its output on the model is byte-for-byte identical to QEMU's (`guest/workload.qemu.txt`).
