def chain(n):
    out = []
    for i in range(n):
        pf = "lk_here"
        for _ in range(i):
            pf = f"lk_skip ({pf}) rfl" if pf != "lk_here" else "lk_skip lk_here rfl"
        out.append(pf)
    return "⟨" + ", ".join(out + ["trivial"]) + "⟩"
import sys
