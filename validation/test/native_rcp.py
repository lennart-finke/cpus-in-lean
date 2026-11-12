"""Native family `sse_rcp_sweep`: the RCPPS/RSQRTPS results of the EPYC 7742, swept so that a later round
can reproduce them exactly (validation/README.md, "Hardware tests", open question S5).

The first hardware run (338 sse_random cases) showed AMD's results to be table-based: every result has
at most 12 significant fraction bits (bits 10..0 are zero), and in the samples the result depends only
on the top 12 fraction bits of the operand (and, for RSQRT, the exponent's parity); a simple
"round 1/x or 1/sqrt(x) of the interval midpoint to 12 bits" rule matches only 210 of 314 RCP and 259 of
287 RSQRT lanes, so the table cannot be derived from the samples. This family measures it: for each of
the 4096 values of fraction bits 22..11, one packed instruction on four operands in [1, 2) (RSQRT also
in [2, 4)) whose bits 10..0 are 0, all ones and two random patterns, so that the table is read and the
"top 12 bits only" hypothesis is tested at four points per entry; plus operands at extreme exponents
(results near the overflow and denormal boundaries). 12,400 cases; every case is 'observe' (the model
returns the correctly rounded value, a documented deviation)."""

REASON = 'RCP/RSQRT table sweep: implementation-specific approximations (open question S5)'


def _case(code, name, lanes, **kw):
    from fp_cases import record, meta   # (fp_cases imports this module)
    xmm = [0x0123456789abcdef ^ (k * 0x101010101010101) for k in range(32)]
    xmm[2] = lanes[0] | lanes[1] << 32
    xmm[3] = lanes[2] | lanes[3] << 32
    return record(code, xmm=xmm), meta('sse_rcp_sweep', name, code, policy='observe', reason=REASON, **kw)


def rcp_sweep(rng, count):
    for name, code, exps in (('rcpps', '0f53c1', (127,)), ('rsqrtps', '0f52c1', (127, 128))):
        for e in exps:
            for t in range(4096):
                lows = (0, 0x7FF, rng.getrandbits(11), rng.getrandbits(11))
                lanes = [e << 23 | t << 11 | lo for lo in lows]
                yield _case(code, name, lanes, table=t, exponent=e)
        # extreme exponents: results near the overflow and denormal boundaries, both signs (RCP)
        for e in (1, 2, 3, 124, 125, 126, 128, 129, 130, 250, 251, 252, 253, 254):
            for _ in range(4):
                lanes = [(rng.getrandbits(1) << 31 if name == 'rcpps' else 0) | e << 23 | rng.getrandbits(23)
                         for _ in range(4)]
                yield _case(code, name, lanes, exponent=e)
