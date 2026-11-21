"""The facts of `blkF` as natural-number equations (`BlkFacts.lean`): `blkF_facts` turns each
definition of the let-chain into an equation over `toNat` (Sem.lean) and hands them to `blk_arith`
(BlkArith.lean, hand-written), whose statement is generated here (`blk_arith_stmt`).

    python3 genmath.py      (from this directory)
"""
import os, re
import genblk
from pchain import names_in

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')

sb, pb = genblk.body()
defs = list(sb.defs.items())
dd = dict(defs)
free = []
for nm, t in defs:
    for x in names_in(t):
        if x not in dd and x not in free:
            free.append(x)
outs = [sb.slots[4].term(), sb.slots[12].term(), sb.slots[8].term(), sb.regs['ebx'].term(), sb.regs['esi'].term()]

# facts: (name, nat statement, proof lines)
facts = []
cvars = []      # carry bits cN (from cfBit gN)
used_vals = []  # the SSA values with a fact (Nat variables)


def nat(t):
    """Nat form of a simple term (a name or literal)"""
    if re.match(r'^\d+$', t):
        return t
    return t


def carry_of(cin):
    m = re.match(r'^\(cfBit (g\d+)\)$', cin)
    return ('c' + m.group(1)[1:]) if m else None


partner = {}
for nm, t in defs:
    m = re.match(r'^\((addF|subF) 4 (\S+) (\S+) (0|\(cfBit g\d+\))\)\.([12])$', t)
    if m:
        key = (m.group(1), m.group(2), m.group(3), m.group(4))
        partner.setdefault(key, {})[m.group(5)] = nm

order = {nm: i for i, (nm, _) in enumerate(defs)}


def rw_list(names):
    names = sorted(set(names), key=lambda n: order[n])
    return ", ".join(f"← e_{n}" for n in names)


done = set()
for nm, t in defs:
    if nm in done:
        continue
    m = re.match(r'^\(addF 4 (\S+) (\S+) (0|\(cfBit g\d+\))\)\.1$', t)
    if m:
        a, b, cin = m.groups()
        g = partner[('addF', a, b, cin)].get('2')
        c = carry_of(cin)
        if g in [n for n, _ in defs] and any(g in t2 for n2, t2 in defs if n2 != g):
            cg = 'c' + g[1:]
            cvars.append(cg)
            st = f"{nm} + 2 ^ 32 * {cg} = {a} + {b} + {c if c else 0}"
            hc = f"(cfBit_le {cin[7:-1]})" if c else "(by decide)"
            pf = [f"have f_{nm} := add_sem {a} {b} {cin} {hc}", f"rw [{rw_list([nm, g])}] at f_{nm}"]
            facts.append((nm, st, pf, [nm, g]))
        else:
            st = f"{nm} = ({a} + {b} + {c if c else 0}) % 2 ^ 32"
            pf = [f"have f_{nm} := add_lo {a} {b} {cin}", f"rw [{rw_list([nm])}] at f_{nm}"]
            facts.append((nm, st, pf, [nm]))
        used_vals.append(nm)
        done.add(nm)
        continue
    m = re.match(r'^UInt64\.toUInt32 \(UInt64\.mul \(UInt32\.toUInt64 (\S+)\) \(UInt32\.toUInt64 (\S+)\)\)$', t)
    if m:
        a, b = m.groups()
        hi = [n for n, t2 in defs if t2 == f"UInt64.toUInt32 (UInt64.shiftRight ({t[len('UInt64.toUInt32 '):][1:-1]}) 32)"][0]
        st = f"{nm} + 2 ^ 32 * {hi} = {a} * {b}"
        pf = [f"have f_{nm} := mul_sem {a} {b}", f"rw [{rw_list([nm, hi])}] at f_{nm}"]
        facts.append((nm, st, pf, [nm, hi]))
        used_vals += [nm, hi]
        done |= {nm, hi}
        continue
    m = re.match(r'^UInt32\.land \(UInt64\.toUInt32 \(imulCore 4 (\S+) (\S+)\)\.1\) 4294967295$', t)
    if m:
        a, b = m.groups()
        facts.append((nm, f"{nm} = {a} * {b} % 2 ^ 32", [f"have f_{nm} := imul_sem {a} {b}",
                                                          f"rw [{rw_list([nm])}] at f_{nm}"], [nm]))
        used_vals.append(nm)
        continue
    m = re.match(r'^UInt32\.shiftRight (\S+) (\d+)$', t)
    if m:
        a, k = m.groups()
        # the carry tricks
        if k == '31':
            src = dd[a]
            if src.startswith('(logicF 4 (UInt32.xor'):
                # v156 = (logicF (xor v154 s)).1 ... with s = UInt32.add x c
                s_ = re.match(r'^\(logicF 4 \(UInt32\.xor (\S+) (\S+)\)\)\.1$', src).group(2)
                x, c = re.match(r'^UInt32\.add (\S+) (\S+)$', dd[s_]).groups()
                chain = [a, s_]
                v154 = re.match(r'^\(logicF 4 \(UInt32\.xor (\S+) (\S+)\)\)\.1$', src).group(1)
                v152, v150 = re.match(r'^\(logicF 4 \(UInt32\.lor (\S+) (\S+)\)\)\.1$', dd[v154]).groups()
                chain += [v154, v152, v150, nm]
                st = f"{nm} = if 2 ^ 32 ≤ {x} + {c} then 1 else 0"
                pf = [f"have f_{nm} := carry_xor {x} {c}", f"rw [{rw_list(chain)}] at f_{nm}"]
                facts.append((nm, st, pf, [nm]))
            else:
                # (~(b + a) & a) >> 31
                m2 = re.match(r'^UInt32\.land (\S+) (\S+)$', src)
                v162, a_ = m2.groups()
                v160 = re.match(r'^UInt32\.land \(UInt32\.complement (\S+)\) 4294967295$', dd[v162]).group(1)
                t160 = dd[v160]
                m3 = re.match(r'^\(addF 4 (\S+) (\S+) 0\)\.1$', t160)
                if m3:
                    b_, a2 = m3.groups()
                    lem = 'carry_not'
                else:
                    b_, a2 = re.match(r'^UInt32\.add (\S+) (\S+)$', t160).groups()
                    lem = "carry_not'"
                assert a2 == a_
                st = f"{nm} = if 2 ^ 32 ≤ {a_} + {b_} then 1 else 0"
                pf = [f"have f_{nm} := {lem} {a_} {b_} (by rw [f_{b_}]; split <;> decide)",
                      f"rw [{rw_list([v160, v162, a, nm])}] at f_{nm}"]
                facts.append((nm, st, pf, [nm]))
        else:
            st = f"{nm} = {a} / 2 ^ {k}"
            pf = [f"have f_{nm} := shr_sem {a} {k} (by decide)", f"rw [{rw_list([nm])}] at f_{nm}"]
            facts.append((nm, st, pf, [nm]))
        used_vals.append(nm)
        continue
    m = re.match(r'^UInt32\.land (\S+) (4294967292|3)$', t)
    if m:
        a, k = m.groups()
        if k == '3':
            st, lem = f"{nm} = {a} % 4", 'land3_sem'
        else:
            st, lem = f"{nm} = 4 * ({a} / 4)", 'landm4_sem'
        facts.append((nm, st, [f"have f_{nm} := {lem} {a}", f"rw [{rw_list([nm])}] at f_{nm}"], [nm]))
        used_vals.append(nm)
        continue
    m = re.match(r'^UInt32\.add (\S+) (\S+)$', t)
    if m:
        a, b = m.groups()
        facts.append((nm, f"{nm} = ({a} + {b}) % 2 ^ 32", [f"have f_{nm} := uadd_sem {a} {b}",
                                                         f"rw [{rw_list([nm])}] at f_{nm}"], [nm]))
        used_vals.append(nm)
        continue

# keep the facts the arithmetic needs: those of values reachable from the outputs
need = set()
stack = list(outs)
while stack:
    v = stack.pop()
    if v in need or v not in dd:
        continue
    need.add(v)
    for x in names_in(dd[v]):
        stack.append(x)
facts = [f for f in facts if any(v in need for v in f[3]) or f[0] in need]

nat_vars = [x for x in free if x not in ('len', 'inp')]
vals = []
for (nm, st, _, _) in facts:
    for x in names_in(st):
        if x not in vals and x not in nat_vars:
            vals.append(x)

def T(s):
    """the Nat statement as a UInt32 statement over toNat"""
    return re.sub(r'(?<![\w.])([a-z]\d+|[a-z]+\d*)(?![\w.])',
                  lambda m: (f"(cfBit g{m.group(1)[1:]}).toNat" if re.match(r'^c\d+$', m.group(1))
                             else (m.group(1) if m.group(1) in ('if', 'then', 'else') else f"{m.group(1)}.toNat")), s)

stmt_args = " ".join(nat_vars + vals)
hyps = []
for x in nat_vars + vals:
    if not re.match(r'^c\d+$', x):
        hyps.append(f"(b_{x} : {x} < 2 ^ 32)")
    else:
        hyps.append(f"(b_{x} : {x} ≤ 1)")
hyps += [f"(f_{nm} : {st})" for (nm, st, _, _) in facts]
hyps += ["(hr0 : r0 < 2 ^ 28)", "(hr1 : r1 < 2 ^ 28)", "(hr2 : r2 < 2 ^ 28)", "(hr3 : r3 < 2 ^ 28)",
         "(hq1 : r1 % 4 = 0)", "(hq2 : r2 % 4 = 0)", "(hq3 : r3 % 4 = 0)",
         "(hs1 : s1 = r1 + r1 / 4)", "(hs2 : s2 = r2 + r2 / 4)", "(hs3 : s3 = r3 + r3 / 4)",
         "(hh4 : h4 ≤ 4)", "(hpad : pad ≤ 1)"]
o = outs
concl = (f"{o[4]} ≤ 4 ∧ ({o[0]} + 2 ^ 32 * {o[1]} + 2 ^ 64 * {o[2]} + 2 ^ 96 * {o[3]} + 2 ^ 128 * {o[4]}) % p = "
         f"((h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4) + "
         f"(x1 + 2 ^ 32 * x2 + 2 ^ 64 * x3 + 2 ^ 96 * x4) + 2 ^ 128 * pad) * "
         f"(r0 + 2 ^ 32 * r1 + 2 ^ 64 * r2 + 2 ^ 96 * r3) % p")
arith_stmt = (f"theorem blk_arith ({stmt_args} : Nat)\n    " + "\n    ".join(hyps) + f" :\n    {concl}")
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'blk_arith_stmt.txt'), 'w').write(arith_stmt + "\n")

# the UInt32-level theorem
u_hyps = ["(hr0 : r0.toNat < 2 ^ 28)", "(hr1 : r1.toNat < 2 ^ 28)", "(hr2 : r2.toNat < 2 ^ 28)",
          "(hr3 : r3.toNat < 2 ^ 28)", "(hq1 : r1.toNat % 4 = 0)", "(hq2 : r2.toNat % 4 = 0)",
          "(hq3 : r3.toNat % 4 = 0)", "(hs1 : s1.toNat = r1.toNat + r1.toNat / 4)",
          "(hs2 : s2.toNat = r2.toNat + r2.toNat / 4)", "(hs3 : s3.toNat = r3.toNat + r3.toNat / 4)",
          "(hh4 : h4.toNat ≤ 4)", "(hpad : pad.toNat ≤ 1)"]
lines = []
for nm, t in defs:
    lines.append(f"obtain ⟨{nm}, e_{nm}⟩ : ∃ y : UInt32, y = {t} := ⟨_, rfl⟩")
lines.append(f"have hF : blkF {' '.join(free)} = ({', '.join(outs)}) := by")
lines.append("  " + "; ".join(f"subst e_{nm}" for nm, _ in reversed(defs)))
lines.append("  rfl")
lines.append("rw [hF]")
for (nm, st, pf, _) in facts:
    lines += pf
args = []
for x in nat_vars + vals:
    args.append(f"(cfBit g{x[1:]}).toNat" if re.match(r'^c\d+$', x) else f"{x}.toNat")
bargs = []
for x in nat_vars + vals:
    bargs.append(f"(cfBit_le g{x[1:]})" if re.match(r'^c\d+$', x) else f"{x}.toNat_lt")
lines.append("exact blk_arith " + " ".join(f"({a})" for a in args) + " " + " ".join(bargs) + " "
             + " ".join(f"f_{nm}" for (nm, _, _, _) in facts) + " hr0 hr1 hr2 hr3 hq1 hq2 hq3 hs1 hs2 hs3 hh4 hpad")
spec = f"""
/-- One block as the code computes it: `h4 ≤ 4` is kept and the value is `(h + m + pad·2^128)·r`
modulo `p`. -/
theorem blkF_spec ({' '.join(free)} : UInt32)
    {chr(10).join('    ' + h for h in u_hyps)} :
    (blkF {' '.join(free)}).2.2.2.2.toNat ≤ 4 ∧
      ((blkF {' '.join(free)}).1.toNat + 2 ^ 32 * (blkF {' '.join(free)}).2.1.toNat +
        2 ^ 64 * (blkF {' '.join(free)}).2.2.1.toNat + 2 ^ 96 * (blkF {' '.join(free)}).2.2.2.1.toNat +
        2 ^ 128 * (blkF {' '.join(free)}).2.2.2.2.toNat) % p =
      ((h0.toNat + 2 ^ 32 * h1.toNat + 2 ^ 64 * h2.toNat + 2 ^ 96 * h3.toNat + 2 ^ 128 * h4.toNat) +
        (x1.toNat + 2 ^ 32 * x2.toNat + 2 ^ 64 * x3.toNat + 2 ^ 96 * x4.toNat) + 2 ^ 128 * pad.toNat) *
        (r0.toNat + 2 ^ 32 * r1.toNat + 2 ^ 64 * r2.toNat + 2 ^ 96 * r3.toNat) % p := by
"""
spec += "".join("  " + l + "\n" for l in lines)
hdr = """import Solutions.OpensslPoly1305.BlkIter
import Solutions.OpensslPoly1305.BlkArith
import Solutions.OpensslPoly1305.Sem
/-!
# The arithmetic of one block (`blkF_spec`)

Generated by `gen/genmath.py`: each definition of `blkF` becomes an equation over `toNat`
(`Sem.lean`), and `blk_arith` (BlkArith.lean) does the arithmetic.
-/
namespace Solutions.OpensslPoly1305
open X86 Solutions.Exec Solutions.Exec.Mul Ssl.Spec.Poly1305

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
"""
open(os.path.join(D, 'BlkFacts.lean'), 'w').write(hdr + spec + "\nend Solutions.OpensslPoly1305\n")
print(len(facts), 'facts;', len(vals), 'values')
