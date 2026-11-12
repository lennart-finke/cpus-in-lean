/* AES-NI, PCLMULQDQ and SHA (x86_32/X86/Ext/Crypto.lean).

   test_crypto (compared with QEMU):
   - crypto.exc: for every instruction, the register and aligned memory forms, CR4.OSFXSR = 0 (#UD),
     CR0.EM (#UD), CR0.TS (#NM), a misaligned memory operand (#GP(0); the SHA instructions execute
     it, as on the EPYC 7742), LOCK and every wrong mandatory prefix (#UD). TCG runs the SHA
     instructions with a 66/F2/F3 prefix; qemu-deviations.txt rewrites those fields ("NP").
   - crypto.fips: FIPS-197 C.1-C.3 (AES-128/192/256, key expansion by AESKEYGENASSIST, encryption
     by AESENC/AESENCLAST, decryption by AESIMC/AESDEC/AESDECLAST), the FIPS 180-4 "abc" digests by
     the SHA instructions, and GCM test case 2 (H, ciphertext, tag; GHASH by PCLMULQDQ), each
     checked against the published value.
   test_crypto_model (MODEL-ONLY): the random cases of crypto_cases.h with the results of the
   independent reference test/cryptoref.py (regenerate: cryptoref.py table sys/crypto_cases.h).
   The instructions are written as bytes (this file is compiled without SSE). */
#include "sys.h"
#include "crypto_cases.h"

static u8 cc[32] __attribute__((aligned(16)));
void (*volatile crypto_codep)(void) = (void (*)(void))cc;
__attribute__((used, aligned(16))) u32 CX[12];   /* XMM0, XMM1 (destination), XMM2 (source) */
__attribute__((used, aligned(16))) u8 CM[48];    /* memory operand */

/* Run the bytes with XMM0..2 from CX (stored back afterwards) and ESI = `mem`; the vector or 0xFFFF. */
static int crun(const u8 *b, int n, void *mem) {
	for (int k = 0; k < n; k++) cc[k] = b[k];
	cc[n] = 0xC3;
	return TRY(__asm__ volatile(
		"movdqu CX, %%xmm0\n movdqu CX+16, %%xmm1\n movdqu CX+32, %%xmm2\n call *crypto_codep\n"
		"movdqu %%xmm0, CX\n movdqu %%xmm1, CX+16\n movdqu %%xmm2, CX+32"
		:: "S"(mem) : "memory", "eax", "ecx", "edx", "cc"));
}

/* [prefixes] 0F 38|3A op modrm [imm8]; modrm 0xCA = xmm1, xmm2; 0x0E = xmm1, [esi] */
static int enc(u8 *b, const u8 *pre, int npre, int map, u8 op, u8 modrm, u8 imm) {
	int n = 0;
	for (int k = 0; k < npre; k++) b[n++] = pre[k];
	b[n++] = 0x0F; b[n++] = map == 2 ? 0x38 : 0x3A; b[n++] = op; b[n++] = modrm;
	if (map == 3) b[n++] = imm;
	return n;
}

/* xmm1 := op(xmm1 = d, xmm2 = s) with XMM0 = CX[0..3]; mandatory prefix pfx (0 or 0x66) */
static void xop(int map, u8 pfx, u8 op, u8 imm, u32 *d, const u32 *s) {
	u8 b[16];
	int n = enc(b, &pfx, pfx ? 1 : 0, map, op, 0xCA, imm);
	for (int k = 0; k < 4; k++) { CX[4 + k] = d[k]; CX[8 + k] = s[k]; }
	crun(b, n, CM);
	for (int k = 0; k < 4; k++) d[k] = CX[4 + k];
}

static void cr0set(u32 em_ts) { WRCR(0, (RDCR(0) & ~0xC) | 0x22 | em_ts); }
static void cr4sse(int on) { WRCR(4, on ? RDCR(4) | 0x600 : RDCR(4) & ~0x600); }

static const struct cform { const char *name; u8 map, pfx, op; } cforms[] = {
	{ "aesimc", 2, 0x66, 0xDB }, { "aesenc", 2, 0x66, 0xDC }, { "aesenclast", 2, 0x66, 0xDD },
	{ "aesdec", 2, 0x66, 0xDE }, { "aesdeclast", 2, 0x66, 0xDF }, { "aeskeygenassist", 3, 0x66, 0xDF },
	{ "pclmulqdq", 3, 0x66, 0x44 },
	{ "sha1nexte", 2, 0, 0xC8 }, { "sha1msg1", 2, 0, 0xC9 }, { "sha1msg2", 2, 0, 0xCA },
	{ "sha256rnds2", 2, 0, 0xCB }, { "sha256msg1", 2, 0, 0xCC }, { "sha256msg2", 2, 0, 0xCD },
	{ "sha1rnds4", 3, 0, 0xCC },
};
#define NCFORMS (sizeof cforms / sizeof cforms[0])

static void exc_line(const struct cform *f) {
	u8 b[16], pre[2];
	int n, np = f->pfx ? 1 : 0;
	pre[0] = f->pfx;
	kprintf("crypto.exc %s:", f->name);
	n = enc(b, pre, np, f->map, f->op, 0xCA, 0x11);
	kprintf(" reg=%x", crun(b, n, CM));
	n = enc(b, pre, np, f->map, f->op, 0x0E, 0x11);
	kprintf(" mem=%x", crun(b, n, CM));
	kprintf(" align=%x", crun(b, n, CM + 8));
	cr4sse(0);
	kprintf(" noosfxsr=%x", crun(b, n, CM));
	cr4sse(1);
	cr0set(4);
	kprintf(" em=%x", crun(b, n, CM));
	cr0set(8);
	kprintf(" ts=%x", crun(b, n, CM));
	cr0set(0);
	/* LOCK, then the other mandatory prefixes (the last F2/F3 counts; F2/F3 take precedence over 66) */
	u8 lk[2] = { 0xF0, f->pfx };
	n = enc(b, lk, np + 1, f->map, f->op, 0x0E, 0x11);
	kprintf(" lock=%x", crun(b, n, CM));
	static const u8 others[4][2] = { { 0, 0 }, { 0x66, 0 }, { 0xF3, 0 }, { 0xF2, 0 } };
	static const char *on[4] = { "np", "p66", "pf3", "pf2" };
	for (int k = 0; k < 4; k++) {
		if (others[k][0] == f->pfx) continue;
		n = enc(b, others[k], others[k][0] ? 1 : 0, f->map, f->op, 0xCA, 0x11);
		kprintf(" %s=%x", on[k], crun(b, n, CM));
	}
	if (f->pfx == 0x66) {   /* 66 F3: F3 wins */
		static const u8 p2[2] = { 0x66, 0xF3 };
		n = enc(b, p2, 2, f->map, f->op, 0xCA, 0x11);
		kprintf(" p66f3=%x", crun(b, n, CM));
	}
	kputc('\n');
}

/* AES with the key expansion's SubWord/RotWord/Rcon from AESKEYGENASSIST (FIPS-197 5.2) */
static void aes_keys(const u8 *key, int nk, u32 rk[15][4]) {
	u32 w[60];
	int nr = nk + 6;
	u8 rcon = 1;
	for (int i = 0; i < nk; i++) w[i] = key[4 * i] | key[4 * i + 1] << 8 | key[4 * i + 2] << 16 | (u32)key[4 * i + 3] << 24;
	for (int i = nk; i < 4 * (nr + 1); i++) {
		u32 t = w[i - 1];
		if (i % nk == 0 || (nk > 6 && i % nk == 4)) {
			u32 d[4] = { 0, 0, 0, 0 }, s[4] = { 0, 0, 0, t };
			xop(3, 0x66, 0xDF, i % nk == 0 ? rcon : 0, d, s);
			t = i % nk == 0 ? d[3] : d[2];
			if (i % nk == 0) rcon = (u8)((rcon << 1) ^ (rcon & 0x80 ? 0x1B : 0));
		}
		w[i] = w[i - nk] ^ t;
	}
	for (int r = 0; r <= nr; r++) for (int k = 0; k < 4; k++) rk[r][k] = w[4 * r + k];
}

static void ldblock(u32 *v, const u8 *p) { for (int k = 0; k < 4; k++) v[k] = p[4 * k] | p[4 * k + 1] << 8 | p[4 * k + 2] << 16 | (u32)p[4 * k + 3] << 24; }
static int eq4(const u32 *a, const u32 *b) { return a[0] == b[0] && a[1] == b[1] && a[2] == b[2] && a[3] == b[3]; }

static void aes_encrypt(u32 rk[15][4], int nr, const u32 *pt, u32 *ct) {
	u32 s[4];
	for (int k = 0; k < 4; k++) s[k] = pt[k] ^ rk[0][k];
	for (int r = 1; r < nr; r++) xop(2, 0x66, 0xDC, 0, s, rk[r]);
	xop(2, 0x66, 0xDD, 0, s, rk[nr]);
	for (int k = 0; k < 4; k++) ct[k] = s[k];
}

static void aes_decrypt(u32 rk[15][4], int nr, const u32 *ct, u32 *pt) {
	u32 s[4];
	for (int k = 0; k < 4; k++) s[k] = ct[k] ^ rk[nr][k];
	for (int r = nr - 1; r >= 1; r--) {
		u32 imc[4] = { 0, 0, 0, 0 };
		xop(2, 0x66, 0xDB, 0, imc, rk[r]);
		xop(2, 0x66, 0xDE, 0, s, imc);
	}
	xop(2, 0x66, 0xDF, 0, s, rk[0]);
	for (int k = 0; k < 4; k++) pt[k] = s[k];
}

static const u8 fips_pt[16] = { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff };
static const u8 fips_ct[3][16] = {
	{ 0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a },
	{ 0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0, 0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d, 0x71, 0x91 },
	{ 0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89 },
};

static void add4(u32 *a, const u32 *b) { for (int k = 0; k < 4; k++) a[k] += b[k]; }

/* SHA-1 of a one-block message (padded words m[16]), by SHA1RNDS4/SHA1NEXTE/SHA1MSG1/SHA1MSG2 */
static void sha1_block(u32 *abcd, u32 *e, const u32 *m) {
	u32 g[20][4], prev[4], cur[4], x[4], abcd0[4];
	for (int j = 0; j < 4; j++) { g[j][0] = m[4 * j + 3]; g[j][1] = m[4 * j + 2]; g[j][2] = m[4 * j + 1]; g[j][3] = m[4 * j]; }
	for (int j = 4; j < 20; j++) {
		u32 t[4];
		for (int k = 0; k < 4; k++) t[k] = g[j - 4][k];
		xop(2, 0, 0xC9, 0, t, g[j - 3]);
		for (int k = 0; k < 4; k++) t[k] ^= g[j - 2][k];
		xop(2, 0, 0xCA, 0, t, g[j - 1]);
		for (int k = 0; k < 4; k++) g[j][k] = t[k];
	}
	for (int k = 0; k < 4; k++) { abcd0[k] = prev[k] = cur[k] = abcd[k]; x[k] = g[0][k]; }
	x[3] += *e;
	xop(3, 0, 0xCC, 0, cur, x);
	for (int j = 1; j < 20; j++) {
		for (int k = 0; k < 4; k++) x[k] = prev[k];
		xop(2, 0, 0xC8, 0, x, g[j]);
		for (int k = 0; k < 4; k++) prev[k] = cur[k];
		xop(3, 0, 0xCC, (u8)(j / 5), cur, x);
	}
	u32 ev[4] = { 0, 0, 0, *e };
	xop(2, 0, 0xC8, 0, prev, ev);
	*e = prev[3];
	add4(cur, abcd0);
	for (int k = 0; k < 4; k++) abcd[k] = cur[k];
}

static const u32 K256[64] = {
	0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
	0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
	0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
	0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
	0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
	0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
	0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
	0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208, 0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
};

/* SHA-256 of a one-block message, by SHA256RNDS2/SHA256MSG1/SHA256MSG2 (st0 = ABEF, st1 = CDGH) */
static void sha256_block(u32 *st0, u32 *st1, const u32 *m) {
	u32 g[16][4], a[4], b[4];
	for (int j = 0; j < 4; j++) for (int k = 0; k < 4; k++) g[j][k] = m[4 * j + k];
	for (int j = 4; j < 16; j++) {
		u32 t[4], al[4] = { g[j - 2][1], g[j - 2][2], g[j - 2][3], g[j - 1][0] };
		for (int k = 0; k < 4; k++) t[k] = g[j - 4][k];
		xop(2, 0, 0xCC, 0, t, g[j - 3]);
		add4(t, al);
		xop(2, 0, 0xCD, 0, t, g[j - 1]);
		for (int k = 0; k < 4; k++) g[j][k] = t[k];
	}
	for (int k = 0; k < 4; k++) { a[k] = st0[k]; b[k] = st1[k]; }
	for (int j = 0; j < 16; j++) {
		u32 wk[4];
		for (int k = 0; k < 4; k++) wk[k] = g[j][k] + K256[4 * j + k];
		for (int k = 0; k < 4; k++) CX[k] = wk[k];
		xop(2, 0, 0xCB, 0, b, a);
		CX[0] = wk[2]; CX[1] = wk[3];
		xop(2, 0, 0xCB, 0, a, b);
	}
	add4(st0, a);
	add4(st1, b);
}

/* GCM multiplication (blocks as loaded from memory) by four PCLMULQDQ and a PCLMULQDQ reduction */
static u32 brev8x4(u32 v) {
	u32 r = 0;
	for (int k = 0; k < 32; k++) if (v >> k & 1) r |= 1u << ((k & ~7) | (7 - (k & 7)));
	return r;
}
static void gfmul(u32 *x, const u32 *h) {
	u32 a[4], b[4], p[4][4], r87[4] = { 0x87, 0, 0, 0 }, lo[4], hi[4], t0[4], t1[4], t2[4];
	static const u8 sel[4] = { 0x00, 0x01, 0x10, 0x11 };
	for (int k = 0; k < 4; k++) { a[k] = brev8x4(x[k]); b[k] = brev8x4(h[k]); }
	for (int s = 0; s < 4; s++) { for (int k = 0; k < 4; k++) p[s][k] = a[k]; xop(3, 0x66, 0x44, sel[s], p[s], b); }
	/* mid = p01 ^ p10; lo = p00 ^ mid << 64; hi = p11 ^ mid >> 64 */
	for (int k = 0; k < 4; k++) { lo[k] = p[0][k]; hi[k] = p[3][k]; }
	lo[2] ^= p[1][0] ^ p[2][0]; lo[3] ^= p[1][1] ^ p[2][1];
	hi[0] ^= p[1][2] ^ p[2][2]; hi[1] ^= p[1][3] ^ p[2][3];
	for (int k = 0; k < 4; k++) { t0[k] = hi[k]; t1[k] = hi[k]; }
	xop(3, 0x66, 0x44, 0x00, t0, r87);
	xop(3, 0x66, 0x44, 0x01, t1, r87);
	t2[0] = t1[2]; t2[1] = t1[3]; t2[2] = t2[3] = 0;
	xop(3, 0x66, 0x44, 0x00, t2, r87);
	lo[0] ^= t0[0] ^ t2[0]; lo[1] ^= t0[1] ^ t2[1]; lo[2] ^= t0[2] ^ t1[0] ^ t2[2]; lo[3] ^= t0[3] ^ t1[1] ^ t2[3];
	for (int k = 0; k < 4; k++) x[k] = brev8x4(lo[k]);
}

static void fips_line(void) {
	static const u8 key[32] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
	                            24, 25, 26, 27, 28, 29, 30, 31 };
	u32 rk[15][4], pt[4], ct[4], out[4], want[4];
	kputs("crypto.fips:");
	for (int v = 0; v < 3; v++) {
		int nk = 4 + 2 * v;
		aes_keys(key, nk, rk);
		ldblock(pt, fips_pt);
		ldblock(want, fips_ct[v]);
		aes_encrypt(rk, nk + 6, pt, ct);
		aes_decrypt(rk, nk + 6, ct, out);
		kprintf(" aes%d=%s", 128 + 64 * v, eq4(ct, want) && eq4(out, pt) ? "ok" : "bad");
	}
	/* "abc", padded: 61626380 0 .. 0 00000018 */
	u32 m[16] = { 0x61626380 };
	m[15] = 24;
	u32 abcd[4] = { 0x10325476, 0x98BADCFE, 0xEFCDAB89, 0x67452301 }, e = 0xC3D2E1F0;
	sha1_block(abcd, &e, m);
	kprintf(" sha1=%x%x%x%x%x", abcd[3], abcd[2], abcd[1], abcd[0], e);
	kprintf(" (%s)", abcd[3] == 0xa9993e36 && abcd[2] == 0x4706816a && abcd[1] == 0xba3e2571 && abcd[0] == 0x7850c26c &&
	        e == 0x9cd0d89d ? "ok" : "bad");
	u32 st0[4] = { 0x9B05688C, 0x510E527F, 0xBB67AE85, 0x6A09E667 }, st1[4] = { 0x5BE0CD19, 0x1F83D9AB, 0xA54FF53A, 0x3C6EF372 };
	sha256_block(st0, st1, m);
	kprintf(" sha256=%x%x%x%x%x%x%x%x", st0[3], st0[2], st1[3], st1[2], st0[1], st0[0], st1[1], st1[0]);
	kprintf(" (%s)", st0[3] == 0xba7816bf && st0[2] == 0x8f01cfea && st1[3] == 0x414140de && st1[2] == 0x5dae2223 &&
	        st0[1] == 0xb00361a3 && st0[0] == 0x96177a9c && st1[1] == 0xb410ff61 && st1[0] == 0xf20015ad ? "ok" : "bad");
	/* GCM test case 2: K = 0, IV = 0, P = 0 (one block) */
	static const u8 zk[16];
	static const u8 hb[16] = { 0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b, 0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34, 0x2b, 0x2e };
	static const u8 cb[16] = { 0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92, 0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe, 0x78 };
	static const u8 tb[16] = { 0xab, 0x6e, 0x47, 0xd4, 0x2c, 0xec, 0x13, 0xbd, 0xf5, 0x3a, 0x67, 0xb2, 0x12, 0x57, 0xbd, 0xdf };
	u32 zero[4] = { 0, 0, 0, 0 }, j0[4] = { 0, 0, 0, 0x01000000 }, j1[4] = { 0, 0, 0, 0x02000000 };
	u32 h[4], c[4], y[4], tag[4], w1[4], w2[4], w3[4], len[4] = { 0, 0, 0, 0x80000000 };
	aes_keys(zk, 4, rk);
	aes_encrypt(rk, 10, zero, h);
	aes_encrypt(rk, 10, j1, c);
	for (int k = 0; k < 4; k++) y[k] = c[k];
	gfmul(y, h);
	for (int k = 0; k < 4; k++) y[k] ^= len[k];
	gfmul(y, h);
	aes_encrypt(rk, 10, j0, tag);
	for (int k = 0; k < 4; k++) tag[k] ^= y[k];
	ldblock(w1, hb); ldblock(w2, cb); ldblock(w3, tb);
	kprintf(" gcm=%s\n", eq4(h, w1) && eq4(c, w2) && eq4(tag, w3) ? "ok" : "bad");
}

void test_crypto(void) {
	cr0set(0);
	cr4sse(1);
	/* the model does not report SHA yet (it waits for SSSE3, X86/Ext/Crypto.lean shaAvail) but
	   executes the SHA instructions; QEMU's EPYC-Rome reports and executes them */
	int aes = has_feature(1, 0, 2, 25), pcl = has_feature(1, 0, 2, 1);
	kprintf("crypto.cpuid: aes=%d pclmulqdq=%d\n", aes, pcl);
	if (!aes || !pcl) return;
	for (int k = 0; k < 48; k++) CM[k] = (u8)(k * 37 + 11);
	for (int k = 0; k < 12; k++) CX[k] = 0x01010101u * (u32)(k + 1);
	for (u32 f = 0; f < NCFORMS; f++) exc_line(&cforms[f]);
	fips_line();
}

void test_crypto_model(void) {
	cr0set(0);
	cr4sse(1);
	u32 bad = 0, n = sizeof ccases / sizeof ccases[0];
	for (u32 i = 0; i < n; i++) {
		const struct ccase *c = &ccases[i];
		u8 b[16], pre = c->pfx;
		int mem = i % 3 == 2;
		int len = enc(b, &pre, pre ? 1 : 0, c->map, c->op, mem ? 0x0E : 0xCA, c->imm);
		for (int k = 0; k < 4; k++) { CX[k] = c->x0[k]; CX[4 + k] = c->a[k]; CX[8 + k] = c->b[k]; }
		u8 *m = CM + 16;
		for (int k = 0; k < 16; k++) m[k] = (u8)(c->b[k / 4] >> (8 * (k % 4)));
		int v = crun(b, len, m);
		if (v != 0xFFFF || !eq4(CX + 4, c->r)) {
			if (bad < 4) kprintf("cryptom.bad: %d vec=%x %x%x%x%x\n", i, v, CX[7], CX[6], CX[5], CX[4]);
			bad++;
		}
	}
	kprintf("cryptom.table: n=%d bad=%d\n", n, bad);
}
