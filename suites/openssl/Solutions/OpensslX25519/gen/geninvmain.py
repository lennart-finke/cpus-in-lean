"""The main proof of fe_invert as a callee (I/InvCall.lean), from the pieces of geninv.py.

    python3 geninvmain.py          (from this directory)
"""
import os, re
import geninv
from geninv import main_pieces, REGS, SQ, D

MAINHDR = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'invmain.lean.in')).read()


def main_proof(calls):
    out = []
    a = out.append
    reg = dict(eax='a0', ecx='(UInt32.add L 52)', edx='fp', ebx='ebx0', ebp='ebp0', esi='fp', edi='(UInt32.add L 52)',
               fl='(subF 4 (UInt32.add L 172) 164 0).2')
    cnt = 4 + 1 + 4
    mem, C, RR = 'M2', 'C0', 'RR0'
    buf = {}
    k = 0
    final = None
    for c in calls:
        if c.get('addl'):
            k += 1
            a(f"  have A{k} := {c['addl']} (icAdd ic0 {cnt}) (icAdd_lt hic (by decide)) {mem} L (hS.size_eq {C}.pres.1) "
              f"{reg['eax']} {reg['ecx']} {reg['edx']} {reg['ebx']} {reg['ebp']} {reg['esi']} {reg['edi']} {reg['fl']}")
            a(f"  simp only [icAdd_add] at A{k}")
            a(f"  have RRa{k} := {RR}.trans A{k}")
            RR = f'RRa{k}'
            reg['fl'] = '(addF 4 (UInt32.add L 4) 4 0).2'
            cnt += 1
        k += 1
        if c.get('loop'):
            a(f"  have P{k} := inv_l0 (icAdd ic0 {cnt}) (icAdd_lt hic (by decide)) {mem} L (hS.size_eq {C}.pres.1) "
              f"{reg['eax']} {reg['ecx']} {reg['edx']} {reg['ebx']} {reg['ebp']} {reg['esi']} {reg['edi']} {reg['fl']}")
            a(f"  simp only [icAdd_add] at P{k}")
            cnt += 3
            (j, e, mo, en) = buf[12]
            a(f"  obtain ⟨N{k}, a{k}, c{k}, d{k}, i{k}, f{k}, RR{k}, C{k}, Mo{k}, E{k}'⟩ := inv_loop G L {reg['ebx']} "
              f"{reg['ebp']} hS _ (feValI fv) ic0 _ 99 {mem} _ _ {e} {cnt} {reg['eax']} {reg['ecx']} {reg['edx']} 0x63 {reg['fl']} "
              f"(by decide) (by decide) {C} rfl {mo} {en} (ic_lt hic (by decide)) ({RR}.trans P{k})")
            e2 = e * 2 ** 99
            a(f"  have E{k} : feValI (memWords N{k}.get (UInt32.add L (12 : Nat).toUInt32) 10) % pI = "
              f"feValI fv ^ {e2} % pI := E{k}'")
            cnt += 579 * 99
            buf[12] = (k, e2, f'Mo{k}', f'E{k}')
            reg.update(eax=f'a{k}', ecx=f'c{k}', edx=f'd{k}', edi=f'i{k}', fl=f'f{k}')
            a(f"  have C{k}' := C{k}.set4 12 52 92 132 _ _ _ _ (by simp [keys_upd]) rfl rfl rfl rfl")
            mem, C, RR = f'N{k}', f"C{k}'", f'RR{k}'
            continue
        info = c['info']
        r = info['regs']
        args = f"{reg['eax']} {reg['ecx']} {reg['edx']} {reg['ebx']} {reg['ebp']} {reg['esi']} {reg['edi']} {reg['fl']}"
        lo = ''
        if info['loads']:
            args += ' hp'
            lo = f" ({C}.slot 8 hp rfl)"
        a(f"  have P{k} := {c['piece']} (icAdd ic0 {cnt}) (icAdd_lt hic (by decide)) {mem} L (hS.size_eq {C}.pres.1) "
          f"{args}{lo}")
        a(f"  simp only [icAdd_add] at P{k}")
        cnt += info['n']

        def val(v):
            if isinstance(v, str):
                return 'hp' if v == 'o' else reg[v]
            if v[0] == 'L':
                return f'(UInt32.add L {v[1]})'
            return '0x%x' % v[1]

        def off(v):
            s = val(v)
            m = re.match(r'\(UInt32\.add L (\d+)\)', s)
            return int(m.group(1)) if m else s
        new = {x: val(r[x]) for x in REGS}
        ret = info['stores'][-1][1][1]
        kd = off(r['ecx'])
        kf = off(r['edx'])
        ent = ' '.join((new['eax'], new['ebx'], new['ebp'], new['esi'], new['edi']))
        if info['target'] == SQ:
            if kf == 'fp':
                a(f"  obtain ⟨N{k}, a{k}, c{k}, d{k}, f{k}, RR{k}, C{k}, Mo{k}, Va{k}⟩ := {C}.sq_x (by decide) (by decide) "
                  f"{kd} (by simp [keys_upd]) fp hfm hfi hfs' hfv hin 0x{ret:x} {ent} {reg['fl']} ic0 {cnt} (ic_lt hic (by decide)) _ "
                  f"(by decide) ({RR}.trans P{k})")
                e, src = 2, 'E0'
            else:
                (j, es, mo, en) = buf[kf]
                a(f"  obtain ⟨N{k}, a{k}, c{k}, d{k}, f{k}, RR{k}, C{k}, Mo{k}, Va{k}⟩ := {C}.sq (by decide) (by decide) "
                  f"{kd} {kf} (by simp [keys_upd]) rfl (mulIn_of_mulOut {mo}) 0x{ret:x} {ent} {reg['fl']} ic0 {cnt} (ic_lt hic (by decide)) _ "
                  f"(by decide) ({RR}.trans P{k})")
                e, src = 2 * es, en
            a(f"  have E{k} : feValI (memWords N{k}.get (UInt32.add L ({kd} : Nat).toUInt32) 10) % pI = "
              f"feValI fv ^ {e} % pI := pow_sq_emod {src} Va{k}")
            cnt += 574
        else:
            kg = off(info['stores'][0][1])
            (jg, eg, mog, eng) = buf[kg]
            if kd == 'hp':
                (jf, ef, mof, enf) = buf[kf]
                a(f"  obtain ⟨Nf, af, cf, df, ff, RRf, Pf, Sf, Mof, Vaf⟩ := {C}.mul_out (by decide) (by decide) hp {kf} {kg} "
                  f"hhm hhi hhs' rfl rfl (mulIn_of_mulOut {mof}) (mulIn_of_mulOut {mog}) 0x{ret:x} {ent} "
                  f"{reg['fl']} ic0 {cnt} (ic_lt hic (by decide)) _ (by decide) (by decide) ({RR}.trans P{k})")
                cnt += 891
                final = (ef + eg, enf, eng, cnt, new)
                break
            if kf == 'fp':
                a(f"  obtain ⟨N{k}, a{k}, c{k}, d{k}, f{k}, RR{k}, C{k}, Mo{k}, Va{k}⟩ := {C}.mul_xf (by decide) (by decide) "
                  f"{kd} {kg} (by simp [keys_upd]) fp hfm hfi hfs' hfv rfl hin (mulIn_of_mulOut {mog}) 0x{ret:x} {ent} "
                  f"{reg['fl']} ic0 {cnt} (ic_lt hic (by decide)) _ (by decide) (by decide) ({RR}.trans P{k})")
                (ef, enf) = (1, 'E0')
            else:
                (jf, ef, mof, enf) = buf[kf]
                a(f"  obtain ⟨N{k}, a{k}, c{k}, d{k}, f{k}, RR{k}, C{k}, Mo{k}, Va{k}⟩ := {C}.mul (by decide) (by decide) "
                  f"{kd} {kf} {kg} (by simp [keys_upd]) rfl rfl (mulIn_of_mulOut {mof}) (mulIn_of_mulOut {mog}) 0x{ret:x} {ent} "
                  f"{reg['fl']} ic0 {cnt} (ic_lt hic (by decide)) _ (by decide) (by decide) ({RR}.trans P{k})")
            e = ef + eg
            a(f"  have E{k} : feValI (memWords N{k}.get (UInt32.add L ({kd} : Nat).toUInt32) 10) % pI = "
              f"feValI fv ^ {e} % pI := pow_mul_emod {enf} {eng} Va{k}")
            cnt += 891
        buf[kd] = (k, e, f'Mo{k}', f'E{k}')
        reg = dict(eax=f'a{k}', ecx=f'c{k}', edx=f'd{k}', ebx=new['ebx'], ebp=new['ebp'], esi=new['esi'],
                   edi=new['edi'], fl=f'f{k}')
        a(f"  have C{k}' := C{k}.set4 12 52 92 132 _ _ _ _ (by simp [keys_upd]) rfl rfl rfl rfl")
        mem, C, RR = f'N{k}', f"C{k}'", f'RR{k}'
    (ef, enf, eng, cnt, new) = final
    assert ef == 2 ** 255 - 21, ef
    K = cnt + 1 + 5
    a(f"""  have hsz : Nf.get.size = G.get.size := Pf.1
  have hSf : FB Nf.get.size L 192 := ⟨by rw [hsz]; exact htop, by rw [hsz]; exact hSpre, himgL⟩
  have A9 := inv_add (icAdd ic0 {cnt}) (icAdd_lt hic (by decide)) Nf L hSf af cf df {new['ebx']}
    {new['ebp']} {new['esi']} {new['edi']} ff
  simp only [icAdd_add] at A9
  have A10 := inv_epi (icAdd ic0 {cnt + 1}) (icAdd_lt hic (by decide)) Nf L hSf af cf df {new['ebx']}
    {new['ebp']} {new['esi']} {new['edi']} (addF 4 (UInt32.add L 4) 168 0).2 esi0 edi0 ebx0 ebp0 ret (Sf 172 esi0 rfl)
    (Sf 176 edi0 rfl) (Sf 180 ebx0 rfl) (Sf 184 ebp0 rfl) ((Pf.rd htop hr1 hr2).trans hret188)
  simp only [icAdd_add] at A10
  rw [hesp] at A10
  refine ⟨Nf, _, _, _, _, RRf.trans (A9.trans A10), Pf.mono fun x hx => ?_, Mof, ?_⟩
  · exact hkey x hx
  · rw [pow_mul_emod {enf} {eng} Vaf]

end Solutions.OpensslX25519.I
""")
    return out, K


if __name__ == '__main__':
    pieces, calls = main_pieces()
    body, K = main_proof(calls)
    txt = MAINHDR.replace('{K}', str(K)) + '\n'.join(body)
    open(os.path.join(D, 'I', 'InvCall.lean'), 'w').write(txt)
    print('K', K)
