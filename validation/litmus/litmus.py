#!/usr/bin/env python3
"""Litmus tests on the x86-TSO multiprocessor (`X86.Tso`) against herd7's x86-TSO model.

usage: litmus.py run TEST.litmus...        print both outcome sets and the verdict per test
       litmus.py check DIR|FILE...         one line per test; exit 1 on any mismatch
       litmus.py expect DIR|FILE...        write herd7's outcome sets to expected/<name>.states
       litmus.py check-expected DIR|FILE   compare against expected/ (no herd7 needed)

A herd X86 test (`X86 NAME`, init block, thread table, `locations`, final condition) is turned into
one i386 code image per thread: herd's syntax (`MOV [x],$1`, `MOV EAX,[y]`, `LOCK XADD`, labels and
jumps) is rewritten to Intel syntax with absolute data addresses, assembled with clang and ended with
HLT. `x86litmus` (validation/LitmusMain.lean) explores every interleaving and prints the final
states over the observed locations (the condition's and `locations`). herd7 is run with
`-model x86tso.cat`. The sets must be equal.

MFENCE drains the TSO store buffer; LFENCE/SFENCE preserve ordinary write-back ordering.
"""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
VALIDATION = os.path.dirname(HERE)
EXPLORER = os.path.join(VALIDATION, '.lake', 'build', 'bin', 'x86litmus')
HERD = os.environ.get('HERD7', os.path.expanduser('~/.opam-verify/herd/bin/herd7'))
EXPECTED = os.path.join(HERE, 'expected')
REGS = ['EAX', 'ECX', 'EDX', 'EBX', 'ESP', 'EBP', 'ESI', 'EDI']
DATA = 0x2000


class Skip(Exception):
    pass


def parse(path):
    src = open(path).read()
    src = re.sub(r'\(\*.*?\*\)', '', src, flags=re.S)
    lines = src.split('\n')
    head = lines[0].split()
    if not head or head[0] != 'X86':
        raise Skip('not an X86 test')
    name = head[1]
    body = '\n'.join(lines[1:])
    m = re.search(r'\{(.*?)\}', body, re.S)
    if not m:
        raise Skip('no init block')
    init = [s.strip() for s in m.group(1).split(';') if s.strip()]
    rest = body[m.end():]
    # thread table: lines up to the first line starting with exists/forall/~exists/locations/filter
    tail_re = re.compile(r'^\s*(exists|~exists|forall|locations|filter)\b', re.M)
    t = tail_re.search(rest)
    if not t:
        raise Skip('no final condition')
    table, tail = rest[:t.start()], rest[t.start():]
    rows = [r.strip() for r in table.split(';') if r.strip()]
    header = [c.strip() for c in rows[0].split('|')]
    if not all(re.fullmatch(r'P\d+', h) for h in header):
        raise Skip(f'bad thread header {rows[0]!r}')
    threads = [[] for _ in header]
    for r in rows[1:]:
        cols = r.split('|')
        for k, c in enumerate(cols):
            c = c.strip()
            if c:
                threads[k].append(c)
    locs = []
    lm = re.search(r'locations\s*\[(.*?)\]', tail, re.S)
    if lm:
        locs += [s.strip() for s in lm.group(1).split(';') if s.strip()]
    cm = re.search(r'(~?exists|forall)\s*(.*)', tail, re.S)
    cond = cm.group(2) if cm else ''
    obs = []
    for x in locs + re.findall(r'(\d+:[A-Z]+|\[?[a-z][a-z0-9_]*\]?)\s*=', cond):
        x = x.strip('[]')
        if x not in obs:
            obs.append(x)
    return name, init, threads, obs


def translate(name, init, threads, obs):
    """Return the explorer input and the list of variables."""
    vars_ = []

    def var(v):
        if v not in vars_:
            vars_.append(v)
        return DATA + 0x40 * vars_.index(v)

    regs, mems = [], []
    for item in init:
        lhs, _, rhs = item.partition('=')
        lhs, rhs = lhs.strip(), rhs.strip()
        if lhs.startswith('int '):
            lhs = lhs[4:].strip()
        if ':' in lhs:
            k, r = lhs.split(':')
            if r not in REGS:
                raise Skip(f'register {r}')
            val = var(rhs) if re.fullmatch(r'[a-z]\w*', rhs) else int(rhs, 0)
            regs.append((int(k), REGS.index(r), val))
        else:
            mems.append((var(lhs), int(rhs, 0) if rhs else 0))
    for o in obs:
        if ':' not in o:
            var(o)
    codes = []
    for k, ins in enumerate(threads):
        asm = ['.intel_syntax noprefix', '.code32']
        for i in ins:
            i = re.sub(r'\$(-?\w+)', r'\1', i)
            i = re.sub(r'\[([a-z]\w*)\]', lambda m: f'dword ptr [{var(m.group(1)):#x}]', i)
            i = re.sub(r'\[([A-Z]{3})\]', r'dword ptr [\1]', i)
            asm.append(i.lower())  # clang rejects an upper-case mnemonic after LOCK
        asm.append('hlt')
        codes.append(assemble('\n'.join(asm) + '\n', f'{name} P{k}'))
    out = [f'thread {k} {c.hex()}' for k, c in enumerate(codes)]
    out += [f'mem {a:#x} {v}' for a, v in mems]
    out += [f'reg {k} {r} {v}' for k, r, v in regs]
    for o in obs:
        if ':' in o:
            k, r = o.split(':')
            out.append(f'obsreg {k} {r} {REGS.index(r)}')
        else:
            out.append(f'obsmem {o} {var(o):#x}')
    return '\n'.join(out) + '\n'


def assemble(src, what):
    with tempfile.TemporaryDirectory() as d:
        s, o = os.path.join(d, 't.s'), os.path.join(d, 't.o')
        open(s, 'w').write(src)
        r = subprocess.run(['clang', '-target', 'i386-unknown-none-elf', '-c', s, '-o', o],
                           capture_output=True, text=True)
        if r.returncode:
            raise Skip(f'{what}: assembler: {r.stderr.strip().splitlines()[0]}')
        dis = subprocess.run(['objdump', '-d', o], capture_output=True, text=True, check=True).stdout
    code = bytearray()
    # objdump: `   a: a1 40 20 00 00 <TAB> movl ...` (continuation lines carry only bytes)
    for line in dis.splitlines():
        m = re.fullmatch(r'\s*[0-9a-f]+:((?: [0-9a-f]{2})+)\s*', line.split('\t')[0])
        if m:
            code += bytes.fromhex(m.group(1).replace(' ', ''))
    if len(code) > 0x200:
        raise Skip('thread code too long')
    return bytes(code)


def norm(lines):
    """Outcome lines to a set of frozensets of `loc=value` (herd prints `[x]=1` or `x=1`)."""
    out = set()
    for l in lines:
        l = l.strip()
        if not l:
            continue
        if l.startswith('STOP'):
            out.add(frozenset([l]))
            continue
        items = [s.strip().replace('[', '').replace(']', '') for s in l.split(';') if s.strip()]
        out.add(frozenset(items))
    return out


def model_states(path):
    name, init, threads, obs = parse(path)
    text = translate(name, init, threads, obs)
    with tempfile.NamedTemporaryFile('w', suffix='.lit', delete=False) as f:
        f.write(text)
    try:
        r = subprocess.run([EXPLORER, f.name], capture_output=True, text=True, timeout=3600)
    finally:
        os.unlink(f.name)
    if r.returncode:
        raise RuntimeError(f'x86litmus failed: {r.stderr.strip()}')
    lines = r.stdout.splitlines()
    return name, norm(lines[1:]), r.stderr.strip()


def herd_states(path, name):
    """herd7's outcome set; for a test herd7 cannot run (its X86 dialect has no XADD/CMPXCHG), the
    hand-derived set in expected/<name>.states (first line `# hand: <reason>`), else Skip."""
    r = subprocess.run([HERD, '-model', 'x86tso.cat', path], capture_output=True, text=True, timeout=3600)
    lines = r.stdout.splitlines()
    i = next((k for k, l in enumerate(lines) if l.startswith('States')), None)
    if r.returncode == 0 and i is not None:
        n = int(lines[i].split()[1])
        return norm(lines[i + 1:i + 1 + n])
    hand = os.path.join(EXPECTED, name + '.states')
    if os.path.exists(hand) and open(hand).readline().startswith('# hand'):
        return norm(l for l in open(hand) if not l.startswith('#'))
    raise Skip('herd7: ' + (r.stderr.strip().splitlines() or ['no output'])[0])


def show(states):
    return sorted('; '.join(sorted(s)) + ';' for s in states)


def files(args):
    for a in args:
        if os.path.isdir(a):
            for root, _, fs in os.walk(a):
                for f in sorted(fs):
                    if f.endswith('.litmus'):
                        yield os.path.join(root, f)
        else:
            yield a


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    mode, args = sys.argv[1], sys.argv[2:]
    bad = ok = skipped = 0
    for path in files(args):
        try:
            if mode == 'expect':
                name = parse(path)[0]
                p = os.path.join(EXPECTED, name + '.states')
                if os.path.exists(p) and open(p).readline().startswith('# hand'):
                    print(f'{name}: hand-written expectation kept')
                    continue
                theirs = herd_states(path, name)
                os.makedirs(EXPECTED, exist_ok=True)
                open(p, 'w').write('\n'.join(show(theirs)) + '\n')
                print(f'{name}: {len(theirs)} states recorded')
                continue
            name, ours, info = model_states(path)
            if mode == 'check-expected':
                p = os.path.join(EXPECTED, name + '.states')
                if not os.path.exists(p):
                    print(f'MISSING expectation for {name}')
                    bad += 1
                    continue
                theirs = norm(l for l in open(p) if not l.startswith('#'))
            else:
                theirs = herd_states(path, name)
        except Skip as e:
            skipped += 1
            print(f'SKIP {os.path.basename(path)}: {e}')
            continue
        same = ours == theirs
        ok += same
        bad += not same
        if mode == 'run' or not same:
            print(f'{"OK  " if same else "DIFF"} {name} ({info})')
            print('  model only: ' + '; '.join(show(ours - theirs)) if ours - theirs else '', end='')
            print('\n  herd only:  ' + '; '.join(show(theirs - ours)) if theirs - ours else '', end='')
            if mode == 'run':
                print('\n  states: ' + ' | '.join(show(ours)))
            else:
                print()
        else:
            print(f'OK   {name} ({len(ours)} states)')
    if mode != 'expect':
        print(f'== {ok} equal, {bad} different, {skipped} skipped')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
