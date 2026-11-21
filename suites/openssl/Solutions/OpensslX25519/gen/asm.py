# Parsing the llvm-objdump AT&T listing of a function into instructions.
import re

REGS = ['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi']


class Op:
    def __init__(self, kind, **kw):
        self.kind = kind  # 'reg' | 'imm' | 'mem'
        self.__dict__.update(kw)

    def __repr__(self):
        return f"Op({self.kind},{self.__dict__})"


def parse_op(s):
    s = s.strip()
    if s.startswith('%'):
        return Op('reg', r=s[1:])
    if s.startswith('$'):
        return Op('imm', v=int(s[1:], 0) & 0xFFFFFFFF)
    m = re.match(r'^(-?0x[0-9a-f]+|-?\d+)?\((%\w+)?(?:,(%\w+)(?:,(\d))?)?\)$', s)
    assert m, s
    disp = int(m.group(1), 0) if m.group(1) else 0
    base = m.group(2)[1:] if m.group(2) else None
    idx = m.group(3)[1:] if m.group(3) else None
    sc = int(m.group(4)) if m.group(4) else 1
    return Op('mem', disp=disp, base=base, idx=idx, sc=sc)


def split_ops(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            depth += 1
        if ch == ')':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [parse_op(x) for x in out]


class Ins:
    def __init__(self, addr, mn, ops, nxt):
        self.addr, self.mn, self.ops, self.nxt = addr, mn, ops, nxt

    def __repr__(self):
        return f"{self.addr:x} {self.mn} {self.ops}"


def read(path):
    """lines `addr mnemonic operands` (as written by the sed in the notes)"""
    rows = []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        parts = line.split(' ', 2)
        addr = int(parts[0], 16)
        mn = parts[1]
        ops = split_ops(parts[2]) if len(parts) > 2 else []
        rows.append((addr, mn, ops))
    ins = []
    for i, (a, mn, ops) in enumerate(rows):
        nxt = rows[i + 1][0] if i + 1 < len(rows) else None
        ins.append(Ins(a, mn, ops, nxt))
    return ins
