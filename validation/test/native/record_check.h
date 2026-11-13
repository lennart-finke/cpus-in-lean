/* Input validation of one native FP record, shared by the oracle (signal_oracle.c: before every case,
 * and `oracle check`, a dry run over a whole campaign on the target) and the host checker
 * (check_records.c, run by `native_fp.py prepare` on every campaign it writes). One source, so a record
 * the oracle would refuse is refused when the bundle is prepared, not halfway through a hardware run.
 *
 * `base` is the 440-byte record (struct vector), `fp` the 208-byte FP extension (struct fp_input) or 0,
 * `ext` the 128-byte v3 extension or 0.
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
 *  - v3 extension: flags bits 0..1 only, the dump window inside the arena, at most eight arena patches,
 *    each inside the arena (offset + 4 x count), reserved bytes zero;
 *  - instructions that would leave the process's sandbox: INT 80h and SYSCALL (real Linux system calls
 *    with whatever EAX holds), SYSENTER unless the processor is AMD (#UD in long mode on AMD, APM vol. 3;
 *    a system call on Intel), far transfers and IRET (they leave the instruction page or load CS), and
 *    loads of DS/ES/FS/GS (64-bit rt_sigreturn does not restore them, so they would leak into later cases);
 *  - every other software interrupt (INT n, INT3, INTO, INT1/ICEBP): they enter the kernel through its IDT
 *    (a DPL-0 gate is #GP, but which vectors have DPL-3 gates is the kernel's business) and the model has
 *    no IDT to compare with;
 *  - near transfers whose target is not in the oracle's code page, outside the instruction (the 0xCC
 *    filling, where the next INT3 ends the case): relative JMP/CALL/Jcc/LOOP/JCXZ (target from the
 *    instruction), RET (target from the stack: the arena content is computed from the record) and indirect
 *    JMP/CALL r/m (register or arena operand). A target elsewhere could be the oracle's own image at 1 MiB
 *    (executed as 32-bit code), a target inside the instruction an endless loop. An operand that is
 *    certain to fault (in an unmapped arena page or below the arena, where nothing is mapped) is accepted;
 *  - bytes after the instruction (the record is longer than the instruction, decoded with the model's
 *    layout, `rc_decode`): they would run as further instructions unless EFLAGS.TF = 1 (the single-step
 *    trap after the first instruction ends the case), and even then not after MOV SS / POP SS, which
 *    hold the trap past the next instruction (exceptions: MOVBE with a register operand, VEX gathers with
 *    16-bit addressing and XOP-space 8F encodings, which are #UD, or decoded whole, on every processor);
 *  - mode 1 (v3, a 16-bit code segment based at the code page, DS/ES based at the arena): the same rules
 *    with 16-bit default operand and address size, IP 0100h and the segment bases;
 *  - MOV SS / POP SS with EFLAGS.TF = 1 at all: the held single-step trap would be taken on the kernel's
 *    entry of the INT3 that ends the case (the CVE-2018-8897 pattern: Linux copes, but logs a warning).
 * The decoder (`rc_decode`) is the model's layout (Decode.lean); the tests check it against the model's
 * decoded lengths. Every rule is a property of the record alone; the oracle protects its own image as well
 * (signal_oracle.c), so a mistranslated access cannot change it either.
 */
#define RC_AMD 1u
#define RC_MISALIGN_SSE 2u
#define RC_ARENA 0x10000ull
#define RC_CODE 0x20000ull
#define RC_IP 0x20100ull
static unsigned long long rc_le(const unsigned char *p, int n) {
 unsigned long long v = 0;
 for (int i = n - 1; i >= 0; i--) v = v << 8 | p[i];
 return v;
}
/* The instruction's layout as the model decodes it (x86_32/X86/Decode.lean, decodeRaw/opInfo), in a
 * 32-bit code segment: prefixes, opcode map, ModRM/SIB/displacement, immediates. */
struct rc_insn {
 unsigned len, prefixes, op, modrm, has_modrm, is_mem, vex, opsz, adsz, rep, seg;
 unsigned base, index, scale; /* 8 = none */
 unsigned long long disp, imm;
};
static unsigned rc_info(unsigned op) {
 if (op >= 0x300) return 0x11;
 if (op >= 0x200) return 0x01;
 if (op < 0x100) {
  unsigned b = op;
  if (b < 0x40) { unsigned lo = b & 7; return lo < 4 ? 0x01 : lo == 4 ? 0x10 : lo == 5 ? 0x30 : 0; }
  if (b < 0x60) return 0;
  if (b >= 0x70 && b <= 0x7f) return 0x10;
  if (b >= 0x84 && b <= 0x8f) return 0x01;
  if (b >= 0xb0 && b <= 0xb7) return 0x10;
  if (b >= 0xb8 && b <= 0xbf) return 0x30;
  if ((b >= 0xd0 && b <= 0xd3) || (b >= 0xd8 && b <= 0xdf)) return 0x01;
  if (b >= 0xe0 && b <= 0xe7) return 0x10;
  switch (b) {
  case 0x62: case 0x63: return 0x01;
  case 0x68: return 0x30; case 0x69: return 0x31; case 0x6a: return 0x10; case 0x6b: return 0x11;
  case 0x80: case 0x82: case 0x83: return 0x11; case 0x81: return 0x31;
  case 0x9a: case 0xea: return 0x50;
  case 0xa0: case 0xa1: case 0xa2: case 0xa3: return 0x40;
  case 0xa8: return 0x10; case 0xa9: return 0x30;
  case 0xc0: case 0xc1: case 0xc6: return 0x11; case 0xc7: return 0x31;
  case 0xc2: case 0xca: return 0x20;
  case 0xc4: case 0xc5: return 0x01;
  case 0xc8: return 0x60;
  case 0xcd: case 0xd4: case 0xd5: case 0xeb: return 0x10;
  case 0xe8: case 0xe9: return 0x30;
  case 0xf6: return 0x71; case 0xf7: return 0x81;
  case 0xfe: case 0xff: return 0x01;
  default: return 0;
  }
 }
 unsigned b = op - 0x100;
 if (b <= 3 || b == 0x0d || (b >= 0x18 && b <= 0x1f) || (b >= 0x20 && b <= 0x23) || (b >= 0x40 && b <= 0x4f) ||
     (b >= 0x90 && b <= 0x9f)) return 0x01;
 if (b >= 0x80 && b <= 0x8f) return 0x30;
 if ((b >= 0x10 && b <= 0x17) || (b >= 0x28 && b <= 0x2f) || (b >= 0x50 && b <= 0x6f) || (b >= 0x74 && b <= 0x76) ||
     b == 0x79 || (b >= 0x7c && b <= 0x7f) || (b >= 0xd0 && b <= 0xfe)) return 0x01;
 if ((b >= 0x70 && b <= 0x73) || b == 0xc2 || (b >= 0xc4 && b <= 0xc6)) return 0x11;
 if (b == 0x78) return 0x91;
 if (b == 0x0f) return 0x11;   /* 3DNow! layout (EPYC 7742: Decode.lean) */
 switch (b) {
 case 0xa3: case 0xa5: case 0xab: case 0xad: case 0xae: case 0xaf: return 0x01;
 case 0xa4: case 0xac: case 0xba: return 0x11;
 case 0xb0: case 0xb1: case 0xb2: case 0xb3: case 0xb4: case 0xb5: case 0xb6: case 0xb7: return 0x01;
 case 0xb8: case 0xbb: case 0xbc: case 0xbd: case 0xbe: case 0xbf: return 0x01;   /* 0F B9, 0F FF: no ModRM */
 case 0xc0: case 0xc1: case 0xc3: case 0xc7: return 0x01;
 default: return 0;
 }
}
/* b: the 32 bytes at 0x20100 (instruction, then 0xCC). Returns the length (16 and more: #GP). */
static void rc_decode16(const unsigned char *b, struct rc_insn *d, int d16) {
 unsigned n = 0, opsz = d16 ? 2 : 4, adsz = d16 ? 2 : 4, rep = 0, seg = 0xff, pre = 0x100, vx = 0, xopimm = 0;
 while (n < 15 && (b[n] == 0x26 || b[n] == 0x2e || b[n] == 0x36 || b[n] == 0x3e || b[n] == 0x64 || b[n] == 0x65 ||
                   b[n] == 0x66 || b[n] == 0x67 || b[n] == 0xf0 || b[n] == 0xf2 || b[n] == 0xf3)) {
  if (b[n] == 0x66) opsz = d16 ? 4 : 2;
  else if (b[n] == 0x67) adsz = d16 ? 4 : 2;
  else if (b[n] == 0xf2 || b[n] == 0xf3) rep = b[n];
  else if (b[n] != 0xf0) seg = b[n];
  n++;
 }
 d->prefixes = n;
 if (n >= 15) { d->len = 16; d->op = 0x1000; return; }
 unsigned op = b[n++];
 if (op == 0x0f) {
  unsigned b1 = b[n++];
  if (b1 == 0x38 || b1 == 0x3a) op = (b1 == 0x38 ? 0x200 : 0x300) + b[n++];
  else op = 0x100 + b1;
 } else if (op == 0xc4 || op == 0xc5) {
  unsigned v1 = b[n++];
  if ((v1 & 0xc0) == 0xc0) {
   if (op == 0xc5) { vx = 0x10000 | v1; op = 0x100 + b[n++]; }
   else {
    unsigned v2 = b[n], ob = b[n + 1], map = v1 & 0x1f;
    n += 2; vx = 0x18000 | v2;
    op = map >= 1 && map <= 3 ? map * 0x100 + ob : ob;
   }
  } else pre = v1;
 } else if (op == 0x8f && (b[n] >> 3 & 7)) {
  /* XOP layout (EPYC 7742; Decode.lean): 8F, two XOP bytes, opcode, ModRM, imm32 in map 0Ah */
  unsigned x1 = b[n];
  vx = 0x18000 | b[n + 1]; op = b[n + 2]; n += 3;
  if ((x1 & 0x1f) == 0x0a) xopimm = 4;
 }
 unsigned info = vx && op < 0x100 ? 0x01 : rc_info(op);
 d->op = op; d->vex = vx != 0; d->opsz = opsz; d->adsz = adsz; d->rep = rep; d->seg = seg;
 d->modrm = 0; d->has_modrm = info & 1; d->is_mem = 0; d->base = d->index = 8; d->scale = 0; d->disp = 0; d->imm = 0;
 unsigned reg = 0;
 if (info & 1) {
  unsigned modrm = pre < 0x100 ? pre : b[n++], md = modrm >> 6, rm = modrm & 7;
  d->modrm = modrm; reg = modrm >> 3 & 7;
  if (md != 3 && !(op >= 0x120 && op <= 0x123)) {
   d->is_mem = 1;
   if (adsz == 4) {
    if (rm == 4) {
     unsigned sib = b[n++];
     d->scale = sib >> 6;
     if ((sib >> 3 & 7) != 4) d->index = sib >> 3 & 7;
     if ((sib & 7) == 5 && md == 0) { d->disp = rc_le(b + n, 4); n += 4; }
     else d->base = sib & 7;
    } else if (rm == 5 && md == 0) { d->disp = rc_le(b + n, 4); n += 4; }
    else d->base = rm;
    if (md == 1) { d->disp = (unsigned long long)(long long)(signed char)b[n]; n++; }
    else if (md == 2) { d->disp = rc_le(b + n, 4); n += 4; }
   } else {
    static const unsigned char bases[8] = {3, 3, 5, 5, 6, 7, 5, 3}, indices[8] = {6, 7, 6, 7, 8, 8, 8, 8};
    d->base = bases[rm]; d->index = indices[rm];
    if (md == 0 && rm == 6) { d->base = 8; d->disp = rc_le(b + n, 2); n += 2; }
    else if (md == 1) { d->disp = (unsigned long long)(long long)(signed char)b[n]; n++; }
    else if (md == 2) { d->disp = rc_le(b + n, 2); n += 2; }
   }
  }
 }
 unsigned kind = info >> 4, k = 0;
 if (kind) {
  unsigned pp = vx ? (vx & 3) : rep == 0xf3 ? 2 : rep == 0xf2 ? 3 : opsz == 2 ? 1 : 0;
  k = kind == 1 ? 1 : kind == 2 ? 2 : kind == 3 ? (vx ? 4 : opsz) : kind == 4 ? adsz : kind == 5 ? opsz : kind == 6 ? 2 :
      kind == 7 ? (reg < 2 ? 1 : 0) : kind == 8 ? (reg < 2 ? opsz : 0) :
      kind == 9 ? (!vx || pp == 1 || pp == 3 ? 1 : 0) : 0;
  if (k) { d->imm = rc_le(b + n, k); n += k; }
  if (kind == 5) n += 2;
  else if (kind == 6 || (kind == 9 && k)) n += 1;
 }
 if (xopimm) { d->imm = rc_le(b + n, xopimm); n += xopimm; }
 d->len = n;
}
__attribute__((unused)) static void rc_decode(const unsigned char *b, struct rc_insn *d) { rc_decode16(b, d, 0); }
/* The initial content of the 8 KiB arena (signal_oracle.c memory_prepare): xorshift from the record's
 * seed, then the 64-byte patch of the FP extension. */
static unsigned long long rc_arena(const unsigned char *base, const unsigned char *fp, const unsigned char *ext,
                                   unsigned long long a, unsigned n) {
 unsigned long long v = 0;
 for (unsigned i = 0; i < n; i++) {
  unsigned long long off = a + i - RC_ARENA;
  unsigned byte;
  int patched = -1;
  for (unsigned k = 0; ext && k < ext[24]; k++) {
   unsigned long long p = rc_le(ext + 32 + 8 * k, 2), cnt = rc_le(ext + 34 + 8 * k, 2);
   if (!cnt) cnt = 1;
   if (off >= p && off < p + 4 * cnt) patched = (int)ext[36 + 8 * k + (off - p) % 4];
  }
  if (patched >= 0) byte = (unsigned)patched;
  else if (fp && off < 64) byte = fp[144 + off];
  else {
   unsigned seed = (unsigned)rc_le(base + 152, 4), word = 0;
   for (unsigned k = 0; k <= off / 4; k++) { seed ^= seed << 13; seed ^= seed >> 17; seed ^= seed << 5; word = seed; }
   byte = word >> (8 * (off % 4)) & 0xff;
  }
  v |= (unsigned long long)byte << (8 * i);
 }
 return v;
}
/* 0: the target is computed (*t); 1: the operand access certainly faults; 2: unknown. */
static int rc_load(const unsigned char *base, const unsigned char *fp, const unsigned char *ext,
                   unsigned long long a, unsigned n, unsigned long long *t) {
 if (a + n <= RC_ARENA) return 1; /* below the arena: nothing is mapped there (mmap_min_addr) */
 if (a >= RC_ARENA && a + n <= RC_ARENA + 8192) {
  int p0 = (int)((a - RC_ARENA) / 4096), p1 = (int)((a + n - 1 - RC_ARENA) / 4096);
  if (!rc_le(base + 160 + 8 * p0, 8) || !rc_le(base + 160 + 8 * p1, 8)) return 1;
  *t = rc_arena(base, fp, ext, a, n);
  return 0;
 }
 return 2;
}
static unsigned long long rc_reg(const unsigned char *base, unsigned r) { return r < 8 ? rc_le(base + 16 + 8 * r, 4) : 0; }
/* The segment base of a memory operand: 0 for the flat 32-bit segments; in mode 1 (16-bit code) CS is
 * based at the code page and DS/ES at the arena (the oracle's LDT); SS, FS, GS stay flat. */
static unsigned long long rc_segbase(const struct rc_insn *d, int mode) {
 if (mode != 1) return 0;
 unsigned seg = d->seg;
 if (seg == 0xff) seg = (d->base == 4 || d->base == 5) && d->is_mem ? 0x36 : 0x3e;
 return seg == 0x2e ? RC_CODE : seg == 0x26 || seg == 0x3e ? RC_ARENA : 0;
}
static const char *record_check(const unsigned char *base, const unsigned char *fp, const unsigned char *ext,
                                unsigned target, unsigned long long *value) {
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
 if (ext) {
  *value = rc_le(ext, 4);
  if (*value & ~3ull) return "unknown v3 extension flags";
  *value = rc_le(ext + 6, 2);
  if (*value > 8192 - 64) return "dump window outside the arena";
  *value = ext[24];
  if (*value > 8) return "more than eight arena patches";
  for (unsigned k = 0; k < 8; k++) {
   unsigned long long cnt = rc_le(ext + 34 + 8 * k, 2);
   *value = rc_le(ext + 32 + 8 * k, 2) + 4 * (cnt ? cnt : 1);
   if (k < ext[24] && *value > 8192) return "arena patch outside the arena";
   if (k >= ext[24] && rc_le(ext + 32 + 8 * k, 8)) return "unused arena patch not zero";
  }
  *value = ext[28];
  if (ext[28] > 1) return "unknown v3 mode";
  for (unsigned i = 25; i < 32; i++) if (ext[i] && i != 28) { *value = i; return "reserved v3 extension byte not zero"; }
  for (unsigned i = 96; i < 128; i++) if (ext[i]) { *value = i; return "reserved v3 extension byte not zero"; }
 }
 /* the bytes the processor decodes: the instruction, then the 0xCC filling of the code page */
 unsigned char b[40];
 for (unsigned i = 0; i < 40; i++) b[i] = i < len ? base[1 + i] : 0xcc;
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
 if (op == 0xcd || op == 0xcc || op == 0xce || op == 0xf1)
  return "software interrupt (through the kernel's IDT; the model has none)";
 struct rc_insn d;
 int mode = ext ? ext[28] : 0;   /* 1: a 16-bit code segment, IP 0100h (code page offset) */
 rc_decode16(b, &d, mode == 1);
 int tf = (flags & 0x100) != 0;
 *value = d.len;
 /* MOVBE with a register operand (0F 38 F0/F1, mod = 11, no F2: not CRC32) is #UD on every processor
  * (gpr_movbe has such records with a byte after them, which never runs) */
 int always_ud = (!d.vex && (d.op == 0x2f0 || d.op == 0x2f1) && !d.is_mem && d.rep != 0xf2) ||
  /* and a VEX gather (VEX.0F38 90..93) with 16-bit addressing, which has no VSIB (avx2_gather a16) */
  (d.vex && d.op >= 0x290 && d.op <= 0x293 && d.adsz == 2);
 /* 8F with ModRM.reg != 0: POP r/m is #UD; with mmmmm >= 8 it is the XOP escape on processors with XOP
  * (Zen 2 has none: #UD), which then decodes the whole XOP instruction: count its layout */
 unsigned run_len = d.len;
 if (!d.vex && d.op == 0x8f && (d.modrm >> 3 & 7)) {
  unsigned p = d.prefixes, map = b[p + 1] & 0x1f;
  if (map < 8) always_ud = 1;
  else {
   unsigned modrm = b[p + 4], md = modrm >> 6, rm = modrm & 7, n = p + 5;
   if (md != 3 && rm == 4) { if (md == 0 && (b[n] & 7) == 5) n += 4; n++; }
   else if (md == 0 && rm == 5) n += 4;
   n += md == 1 ? 1 : md == 2 ? 4 : 0;
   n += map == 8 ? 1 : map == 10 ? 4 : 0;
   run_len = n;
  }
 }
 if (run_len < len && !tf && !always_ud) return "bytes after the instruction would run as further instructions (EFLAGS.TF = 0)";
 if (d.len < len && (op == 0x17 || (op == 0x8e && reg == 2)))
  return "MOV/POP SS holds the single-step trap past the bytes after the instruction";
 /* MOV/POP SS with TF: the held #DB would be taken on the kernel's entry of the INT3 that follows (the
  * CVE-2018-8897 pattern; Linux survives it but warns) */
 if (tf && (op == 0x17 || (op == 0x8e && reg == 2)))
  return "MOV/POP SS with EFLAGS.TF (the single-step trap would hit the kernel's INT3 entry)";
 if (d.len > 15) return 0; /* #GP(0) at decode: nothing executes */
 /* near transfers: the target must be the INT3 filling of the code page */
 unsigned long long mask = d.opsz == 2 ? 0xffff : 0xffffffffull, t = 0;
 unsigned long long ip = mode == 1 ? RC_IP - RC_CODE : RC_IP, page = mode == 1 ? 0 : RC_CODE;
 unsigned long long next_ip = ip + d.len;
 int have = -1; /* -1: not a transfer */
 if (!d.vex && ((d.op >= 0x70 && d.op <= 0x7f) || (d.op >= 0xe0 && d.op <= 0xe3) || d.op == 0xeb)) {
  t = (next_ip + (unsigned long long)(long long)(signed char)d.imm) & mask; have = 0;
 } else if (!d.vex && (d.op == 0xe8 || d.op == 0xe9 || (d.op >= 0x180 && d.op <= 0x18f))) {
  unsigned long long rel = d.opsz == 2 ? (unsigned long long)(long long)(short)d.imm : (unsigned long long)(long long)(int)d.imm;
  t = (next_ip + rel) & mask; have = 0;
 } else if (!d.vex && (d.op == 0xc2 || d.op == 0xc3)) {
  have = rc_load(base, fp, ext, rc_reg(base, 4) & 0xffffffffull, d.opsz, &t);
 } else if (!d.vex && d.op == 0xff && ((d.modrm >> 3 & 7) == 2 || (d.modrm >> 3 & 7) == 4)) {
  if (!d.is_mem) { t = rc_reg(base, d.modrm & 7) & mask; have = 0; }
  else {
   unsigned long long a = d.disp;
   if (d.base < 8) a += rc_reg(base, d.base);
   if (d.index < 8) a += rc_reg(base, d.index) << d.scale;
   a &= d.adsz == 2 ? 0xffff : 0xffffffffull;
   a = (a + rc_segbase(&d, mode)) & 0xffffffffull;
   have = rc_load(base, fp, ext, a, d.opsz, &t);
  }
 }
 if (have == 2) { *value = op << 8 | next; return "near transfer through an operand outside the arena"; }
 if (have == 0) {
  *value = t;
  if (t < page || t >= page + 4096 || (t >= ip && t < next_ip))
   return "near transfer target outside the INT3 filling of the code page";
 }
 return 0;
}
