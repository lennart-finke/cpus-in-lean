# fe_mul configuration of gensq
import gensq
gensq.FS = 836
gensq.WS = 828
gensq.PRE = 'mul'
gensq.BODY = (0x100c2a, 0x101be2)
gensq.SLOTS = {0x338: 'ebp0', 0x334: 'ebx0', 0x330: 'edi0', 0x32c: 'esi0', 0x340: 'gp'}
gensq.PTRS = ['fp', 'gp']
gensq.HDR = gensq.HDR.replace("import Solutions.OpensslX25519.ShapesSq4\n",
                              "import Solutions.OpensslX25519.ShapesSq4\nimport Solutions.OpensslX25519.ShapesMul1\n"
                              "import Solutions.OpensslX25519.ShapesMul2\n")


def run():
    return gensq.run('mul.txt' if __import__('os').path.exists('mul.txt') else '../mul.txt')


if __name__ == '__main__':
    out, m = run()
    print(len(out), out[-1]['ic1'])
    ext = [(p['k'], key, nm) for p in out for (kind, key, nm) in p['loads'] if kind == 'ext']
    print(ext)
    print(m.regs, {k: m.slots.get(k) for k in (0x34, 0x20, 0x10, 0, 0x18)})
