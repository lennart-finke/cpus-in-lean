import Curl.Proofs.Xrun
import Curl.Proofs.Toupper
/-!
# `Curl_raw_toupper` (`0x1006E0`)

```
1006e0 movzbl %cl,%eax
1006e3 movzbl 0x100e4c(%eax),%eax
1006ea ret
```

The byte `cl` looked up in `Curl_touppermap`: the result is `upper (ecx % 256)` (`touppermap_eq`).
Nothing is written; the stack pointer is the caller's plus 4 at the return.
-/
namespace Curl.Proofs.RawToupper
open X86 Ssl Solutions.Logic Solutions.Exec Curl.Proofs Curl.Proofs.Sym Curl.Hostcheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 5000000

theorem codeB_table (c : UInt32) :
    (codeB ((c.land 255).add 1052236)).toUInt32.toNat = upper (c.toNat % 256) := by
  have ha : ((c.land 255).add 1052236).toNat - 0x100000 = 0xE4C + c.toNat % 256 := by xomega
  rw [UInt8.toNat_toUInt32]
  unfold codeB
  rw [ha]
  exact touppermap_eq _ (by omega)

theorem toupper_spec (G : CMem) (eax ecx edx ebx t ebp esi edi f : UInt32) (x : UInt64) (Q : Machine → Prop)
    (hsz : G.get.size ≤ ramTop) (hcode : 0x100000 + 3971 ≤ G.get.size) (hts : t.toNat + 4 ≤ G.get.size) (hx : x.toNat + 10 < 2 ^ 64)
    (k : ∀ (r : UInt32) (x' : UInt64), r.toNat = upper (ecx.toNat % 256) → x'.toNat ≤ x.toNat + 3 →
      Reaches img (St.m ⟨G.get, r, ecx, edx, ebx, t.add 4, ebp, esi, edi, rdRaw G.get t 4, efl f, x'⟩) Q) :
    Reaches img (St.m ⟨G.get, eax, ecx, edx, ebx, t, ebp, esi, edi, 0x1006E0, efl f, x⟩) Q := by
  xrun []
  refine k _ _ ?_ (by xomega)
  exact codeB_table ecx
