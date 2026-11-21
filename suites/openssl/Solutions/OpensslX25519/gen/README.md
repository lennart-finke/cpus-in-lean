Generators of the fe_sq proof (SqRun01-14, SqMath, Sq). From this directory:

    python3 -c "import gensq"                          # (modules: asm, symx, sem, genmath)
    python3 genmain.py sq.txt ..                      # writes ../SqMath.lean and ../Sq.lean

The SqRun modules were written by gensq.lemma over the pieces of gensq.run (6 per file).
sq.txt is the fe_sq part of targets/openssl_x25519/image/openssl_x25519.dis, one instruction per
line (`addr mnemonic operands`).

fe_mul: `python3 genmulmain.py .. runs` writes ../MulRun*.lean; `python3 genmulmain.py ..` writes
../MulArith.lean and ../Mul.lean (configuration in mulcfg.py; mul.txt is the fe_mul listing).
