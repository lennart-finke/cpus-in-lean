/* Input validation of one native FP record, shared by the oracle (signal_oracle.c: before every case,
 * and `oracle check`, a dry run over a whole campaign on the target) and the host checker
 * (check_records.c, run by `native_fp.py prepare` on every campaign it writes). One source, so a record
 * the oracle would refuse is refused when the bundle is prepared, not halfway through a hardware run.
 *
 * `base` is the 440-byte record (struct vector), `fp` the 208-byte FP extension (struct fp_input) or 0.
 * `target` describes the machine: RC_AMD (CPUID vendor AuthenticAMD), RC_MISALIGN_SSE (CPUID
 * 8000_0001h:ECX[7]). Returns 0 when the oracle can run the record as the model runs it, else the reason;
 * *value gets the offending value. Rules:
 *  - instruction length 1..15 (the oracle copies the bytes to its code page; 0xCC fills the rest);
 *  - data-page PTEs: 0 (unmapped), 0x65 (present, user, read-only, accessed, dirty), 0x67 (writable). The
 *    oracle realises them with munmap/mprotect; an accessed or dirty bit cannot be set from user mode, so
 *    no other value has a native equivalent;
 *  - EFLAGS: only CF PF AF ZF SF TF DF OF and AC are installed from the record (set_regs); every other bit
 *    is the runner's (IF and bit 1 set), so the record must have exactly those;
 *  - MXCSR bits 31:16 are reserved (rt_sigreturn's XRSTOR would fault and kill the process), except MM
 *    (bit 17) on a processor with MisalignSse;
 *  - FTW is the 8-bit abridged tag word; memory kinds 0..4 (signal_oracle.c memory_byte);
 *  - instructions that would leave the process's sandbox: INT 80h and SYSCALL (real Linux system calls
 *    with whatever EAX holds), SYSENTER unless the processor is AMD (#UD in long mode on AMD, APM vol. 3;
 *    a system call on Intel), far transfers and IRET (they leave the instruction page or load CS), and
 *    loads of DS/ES/FS/GS (64-bit rt_sigreturn does not restore them, so they would leak into later cases).
 */
#define RC_AMD 1u
#define RC_MISALIGN_SSE 2u
static unsigned long long rc_le(const unsigned char *p, int n) {
 unsigned long long v = 0;
 for (int i = n - 1; i >= 0; i--) v = v << 8 | p[i];
 return v;
}
static const char *record_check(const unsigned char *base, const unsigned char *fp, unsigned target,
                                unsigned long long *value) {
 unsigned len = base[0];
 *value = len;
 if (len < 1 || len > 15) return "bad instruction length";
 for (int p = 0; p < 2; p++) {
  unsigned long long pte = rc_le(base + 160 + 8 * p, 8);
  *value = pte;
  if (pte != 0 && pte != 0x65 && pte != 0x67) return "unsupported data permission";
 }
 unsigned long long flags = rc_le(base + 144, 8);
 *value = flags;
 if ((flags & ~0x40dd5ull) != 0x202) return "EFLAGS bits the oracle cannot install";
 unsigned long long mxcsr = rc_le(base + 432, 4);
 *value = mxcsr;
 if (mxcsr & ~(0xffffull | (target & RC_MISALIGN_SSE ? 0x20000ull : 0))) return "reserved MXCSR bits";
 *value = rc_le(base + 436, 4);
 if (*value > 4) return "unknown memory kind";
 if (fp) {
  *value = rc_le(fp + 4, 2);
  if (*value > 0xff) return "FTW wider than the abridged tag byte";
 }
 /* the bytes the processor decodes: the instruction, then the 0xCC filling of the code page */
 unsigned char b[17];
 for (unsigned i = 0; i < 17; i++) b[i] = i < len ? base[1 + i] : 0xcc;
 unsigned k = 0;
 while (k < len && (b[k] == 0x26 || b[k] == 0x2e || b[k] == 0x36 || b[k] == 0x3e || b[k] == 0x64 ||
                    b[k] == 0x65 || b[k] == 0x66 || b[k] == 0x67 || b[k] == 0xf0 || b[k] == 0xf2 ||
                    b[k] == 0xf3)) k++;
 unsigned op = b[k], next = b[k + 1], reg = next >> 3 & 7;
 *value = op << 8 | next;
 if (op == 0xcd && next == 0x80) return "INT 80h: a Linux system call";
 if (op == 0x0f && next == 0x05) return "SYSCALL: a Linux system call from compatibility mode";
 if (op == 0x0f && next == 0x34 && !(target & RC_AMD)) return "SYSENTER: a system call outside AMD long mode";
 if (op == 0xea || op == 0x9a || op == 0xca || op == 0xcb || op == 0xcf || (op == 0xff && (reg == 3 || reg == 5)))
  return "far transfer or IRET";
 if (op == 0x07 || op == 0x1f || (op == 0x0f && (next == 0xa1 || next == 0xa9 || next == 0xb4 || next == 0xb5)) ||
     (op == 0x8e && (reg == 0 || reg == 3 || reg == 4 || reg == 5)) || ((op == 0xc4 || op == 0xc5) && next >> 6 != 3))
  return "loads DS/ES/FS/GS (not restored between cases)";
 return 0;
}
