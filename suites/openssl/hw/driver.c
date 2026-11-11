/* Calls every task entry point of one image on pseudo-random and edge-case inputs and prints each
   result as a line `sslcheck spec` understands, so a transcript from any CPU can be compared with
   the Lean model's and evaluated against the Lean specifications. TARGET selects the image. */
#include "driver.h"
#include "syms.h"

static u32 seed = 0x2545F491u;
u32 rnd(void) { seed ^= seed << 13; seed ^= seed >> 17; seed ^= seed << 5; return seed; }
void rnd_bytes(u8 *p, u32 n) { for (u32 i = 0; i < n; i++) p[i] = (u8)(rnd() >> 11); }
void put(const char *s) { while (*s) plat_putc(*s++); }
void put_hex(const u8 *p, u32 n) {
	if (!n) plat_putc('-');
	for (u32 i = 0; i < n; i++) { plat_putc("0123456789abcdef"[p[i] >> 4]); plat_putc("0123456789abcdef"[p[i] & 15]); }
}
void put_u32(u32 v) { for (int i = 28; i >= 0; i -= 4) plat_putc("0123456789abcdef"[(v >> i) & 15]); }
static void sp(void) { plat_putc(' '); }
static void nl(void) { plat_putc('\n'); }
static u32 cdecl(u32 fn, u32 nargs, const u32 *args) { return call_fn(fn, rnd(), rnd(), nargs, args); }
#define A(...) (const u32[]){ __VA_ARGS__ }
#define P(x) ((u32)(x))

/* not every target uses every buffer */
__attribute__((unused)) static u8 msg[1024], out[64], ctx[256], ctx2[256];

#if TARGET == 1 /* ---- openssl_sha256 ---- */
static void digest(const char *name, u32 ini, u32 upd, u32 fin, u32 n, u32 len, u32 cut) {
	rnd_bytes(msg, len);
	if (cdecl(ini, 1, A(P(ctx))) != 1) put("!init\n");
	/* three chunks, the middle one empty; the context is moved between calls */
	if (cdecl(upd, 3, A(P(ctx), P(msg), cut)) != 1) put("!update\n");
	for (u32 i = 0; i < 112; i++) ctx2[i] = ctx[i];
	if (cdecl(upd, 3, A(P(ctx2), 0xFFFFFFF1u, 0)) != 1) put("!update\n");
	if (cdecl(upd, 3, A(P(ctx2), P(msg + cut), len - cut)) != 1) put("!update\n");
	if (cdecl(fin, 2, A(P(out), P(ctx2))) != 1) put("!final\n");
	for (u32 i = 40; i < 108; i++) if (ctx2[i]) { put("!wipe\n"); break; }
	put(name); sp(); put_hex(msg, len); sp(); put_hex(out, n); nl();
}
void run(void) {
	static const u32 lens[] = { 0, 1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 200, 1000 };
	for (u32 i = 0; i < sizeof lens / sizeof *lens; i++) {
		u32 cut = lens[i] ? rnd() % (lens[i] + 1) : 0;
		digest("sha256", SYM_SHA256_Init, SYM_SHA256_Update, SYM_SHA256_Final, 32, lens[i], cut);
		digest("sha224", SYM_SHA224_Init, SYM_SHA224_Update, SYM_SHA224_Final, 28, lens[i], cut);
	}
	for (u32 i = 0; i < 8; i++) {
		rnd_bytes(ctx, 32); rnd_bytes(msg, 64);
		put("sha256_transform "); put_hex(ctx, 32); sp(); put_hex(msg, 64); sp();
		cdecl(SYM_SHA256_Transform, 2, A(P(ctx), P(msg)));
		put_hex(ctx, 32); nl();
	}
}
#elif TARGET == 2 /* ---- openssl_chacha20 ---- */
static u8 key[32], ctr[16], ct[1024];
void run(void) {
	static const u32 lens[] = { 0, 1, 63, 64, 65, 127, 128, 129, 300, 1000 };
	for (u32 i = 0; i < sizeof lens / sizeof *lens; i++)
		for (u32 k = 0; k < 4; k++) {
			u32 len = lens[i];
			rnd_bytes(key, 32); rnd_bytes(ctr, 16); rnd_bytes(msg, len);
			/* k = 1: the 32-bit block counter wraps during the call; k = 3: in place */
			u32 counter = k == 0 ? 1 : k == 1 ? 0xFFFFFFFFu : rnd();
			*(u32 *)ctr = counter;
			put("chacha20 "); put_hex(key, 32); sp(); put_u32(counter); sp(); put_hex(ctr + 4, 12); sp();
			put_hex(msg, len); sp();
			if (k == 3) { cdecl(SYM_ChaCha20_ctr32, 5, A(P(msg), P(msg), len, P(key), P(ctr))); put_hex(msg, len); }
			else { cdecl(SYM_ChaCha20_ctr32, 5, A(P(ct), P(msg), len, P(key), P(ctr))); put_hex(ct, len); }
			nl();
		}
}
#elif TARGET == 3 /* ---- openssl_poly1305 ---- */
static u8 key[32];
void run(void) {
	put("poly1305_ctx_size "); put_u32(cdecl(SYM_Poly1305_ctx_size, 0, A(0))); nl();
	for (u32 len = 0; len <= 1000; len = len < 50 ? len + 1 : len * 2 + 7) {
		u32 cut = len ? rnd() % (len + 1) : 0;
		rnd_bytes(key, 32); rnd_bytes(msg, len);
		if ((len & 7) == 3) for (u32 i = 0; i < 32; i++) key[i] = 0xff;      /* maximal r and s */
		if ((len & 7) == 5) for (u32 i = 0; i < len; i++) msg[i] = 0xff;     /* all-ones blocks */
		rnd_bytes(ctx, 236);                                                 /* Init need not find zeros */
		cdecl(SYM_Poly1305_Init, 2, A(P(ctx), P(key)));
		cdecl(SYM_Poly1305_Update, 3, A(P(ctx), P(msg), cut));
		for (u32 i = 0; i < 236; i++) ctx2[i] = ctx[i];
		cdecl(SYM_Poly1305_Update, 3, A(P(ctx2), 0xFFFFFFF1u, 0));
		cdecl(SYM_Poly1305_Update, 3, A(P(ctx2), P(msg + cut), len - cut));
		cdecl(SYM_Poly1305_Final, 2, A(P(ctx2), P(out)));
		for (u32 i = 0; i < 236; i++) if (ctx2[i]) { put("!wipe\n"); break; }
		put("poly1305 "); put_hex(key, 32); sp(); put_hex(msg, len); sp(); put_hex(out, 16); nl();
	}
}
#elif TARGET == 4 /* ---- openssl_x25519 ---- */
static u32 f[10], g[10], h[10];
/* limbs within |t| <= num/100 * 2^(e - i%2), at the bound when `edge` */
static void limbs(u32 *t, u32 num, u32 e, int edge) {
	for (u32 i = 0; i < 10; i++) {
		u32 bound = (u32)(((uint64_t)num << (e - (i & 1))) / 100);
		u32 mag = edge ? bound : rnd() % (bound + 1);
		t[i] = (rnd() & 1) ? (u32)-(int32_t)mag : mag;
	}
}
static void field(const char *name, u32 fn, int two, u32 num, u32 e) {
	for (u32 k = 0; k < 40; k++) {
		limbs(f, num, e, k < 8); limbs(g, num, e, k < 8);
		u32 alias = k % 5;                  /* 0, 1: none; 2: h = f; 3: h = g; 4: f = g */
		u32 *gp = (two && alias == 4) ? f : g;
		u32 *hp = alias == 2 ? f : (two && alias == 3) ? g : h;
		put(name); sp(); put_hex((u8 *)f, 40); sp();
		if (two) { put_hex((u8 *)gp, 40); sp(); }
		call_fn(fn, P(hp), P(f), two ? 1 : 0, A(P(gp)));
		put_hex((u8 *)hp, 40); nl();
	}
}
static u8 k[32], u[32];
void run(void) {
	field("fe_mul", SYM_fe_mul, 1, 165, 26);
	field("fe_sq", SYM_fe_sq, 0, 165, 26);
	field("fe_add", SYM_fe_add, 1, 110, 25);
	field("fe_sub", SYM_fe_sub, 1, 110, 25);
	for (u32 i = 0; i < 12; i++) {
		rnd_bytes(k, 32); rnd_bytes(u, 32);
		if (i == 0) for (u32 j = 0; j < 32; j++) u[j] = 0;        /* small order: all-zero result */
		if (i == 1) for (u32 j = 0; j < 32; j++) u[j] = 0xff;     /* non-canonical u */
		if (i == 2) for (u32 j = 0; j < 32; j++) k[j] = 0xff;
		put("x25519 "); put_hex(k, 32); sp(); put_hex(u, 32); sp();
		u8 *o = i % 3 == 1 ? u : out;                              /* the output may be an input */
		u32 r = cdecl(SYM_ossl_x25519, 3, A(P(o), P(k), P(u)));
		u32 nonzero = 0;
		for (u32 j = 0; j < 32; j++) nonzero |= o[j];
		if (r != (nonzero ? 1u : 0u)) put("!x25519 return value ");
		put_hex(o, 32); nl();
	}
	for (u32 i = 0; i < 6; i++) {
		rnd_bytes(k, 32);
		put("x25519_public "); put_hex(k, 32); sp();
		cdecl(SYM_ossl_x25519_public_from_private, 2, A(P(out), P(k)));
		put_hex(out, 32); nl();
	}
}
#else
#error "TARGET must be 1..4"
#endif

void main(void) {
	plat_init();
	run();
	if (call_violations) put("!a call did not restore the callee-saved registers, the stack pointer or the direction flag\n");
	put("END\n");
	plat_exit();
}
