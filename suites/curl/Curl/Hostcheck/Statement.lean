import Ssl.Harness
import Curl.Spec.Hostcheck
import Curl.Hostcheck.Image
/-!
# curl 8.23.0 `lib/vtls/hostcheck.c`: certificate name matching (RFC 2818 §3.1)

Image: `targets/hostcheck`. `Curl_cert_hostcheck(match, matchlen, hostname, hostlen)` decides whether
a name presented in a server certificate (`match`, not NUL-terminated) is acceptable for the host
name the user asked for (`hostname`, a C string of `hostlen` bytes). It returns a `bool` in `al`.
The image also holds what it calls, all unchanged: `hostmatch` and `pmatch` of the same file,
`Curl_host_is_ipnum` (`lib/vdns/hostip.c`), `curlx_inet_pton` (`lib/curlx/inet_pton.c`),
`curl_strnequal` (`lib/strequal.c`), `Curl_raw_toupper` (`lib/strcase.c`) and `Curl_memrchr`.

Statements, for every caller (`Ssl.Harness`), every placement of the two names and every content of
the rest of memory:

* `match_sound`: a name is accepted only if RFC 2818 §3.1 lets it match: component by component,
  `*` standing for a non-empty component or a fragment of one, letters compared without regard to
  case. So `*.a.com` is never accepted for `bar.foo.a.com`, whatever else memory holds.
* `match_leftmost_wildcard`: the wildcard form curl implements is accepted: `*.S` matches `L.S'`
  when `L` is one non-empty component and `S'` equals `S` up to case.
* `ip_host_exact`: when the host name is an IP address, a name is accepted only if it is that
  address, character for character: no wildcard matches an IP address.

RFC 2818 also allows fragments (`f*.com`) and `*.com`. curl refuses both on purpose, following
RFC 6125 §6.4.3, so only soundness is stated for every input and completeness for the form curl
documents. Security history of this function: CVE-2014-0139 (a wildcard matched an IP-address
host; fixed by the `Curl_host_is_ipnum` test) and CVE-2023-28321 (partial wildcards such as `x*`
matched internationalised `xn--` hosts; fixed by removing partial wildcards).

Not stated: names ending in `.` (RFC 2818 does not speak of absolute names; curl removes one
trailing dot from each name before comparing), and the zero-length cases (curl returns FALSE).
-/
namespace Curl.Hostcheck
open X86 Ssl Curl.Spec

def img : Img := ⟨Image.base, Image.bytes, Image.sym_halt⟩
/-- Stack the call may use below its entry stack pointer. -/
def stackBound : Nat := 256

/-- The stack arguments of `Curl_cert_hostcheck(match, |p|, hostname, |h|)`. -/
def args (matchp hostp : UInt32) (p h : List UInt8) : List UInt32 :=
  [matchp, p.length.toUInt32, hostp, h.length.toUInt32]

/-- The names the statements are about: both non-empty, the host name without a NUL byte (it is a C
string), neither ending in `.`. -/
def Admissible (p h : List UInt8) : Prop :=
  0 < p.length ∧ 0 < h.length ∧ (0 : UInt8) ∉ h ∧ p.getLast? ≠ some 0x2E ∧ h.getLast? ≠ some 0x2E

/-- A call with the presented name `p` at `matchp` and the host name `h`, NUL-terminated, at `hostp`.
The two buffers are only read and may be anywhere, also overlapping. -/
def Pre (c : Caller) (matchp hostp : UInt32) (p h : List UInt8) : Prop :=
  Calls img c stackBound (args matchp hostp p h) ∧
  Buffer img c stackBound 4 matchp p.length ∧ Buffer img c stackBound 4 hostp (h.length + 1) ∧
  memBytes c.mem matchp p.length = p ∧ memBytes c.mem hostp (h.length + 1) = h ++ [0] ∧
  Admissible p h

instance (c : Caller) (matchp hostp : UInt32) (p h : List UInt8) : Decidable (Pre c matchp hostp p h) := by
  unfold Pre Admissible; infer_instance

/-- The `bool` result: the presented name was accepted. -/
def accepted (m : Machine) : Prop := m.cpu.eax.toUInt8 ≠ 0

instance (m : Machine) : Decidable (accepted m) := by unfold accepted; infer_instance

/-- The call returns having written nothing but its own stack, and its result satisfies `Q`. -/
def Decides (c : Caller) (Q : Machine → Prop) : Prop :=
  Returns img (c.enter Image.sym_Curl_cert_hostcheck) stackBound NoWrites Q

/-- **Soundness.** RFC 2818 §3.1: "Names may contain the wildcard character * which is considered
to match any single domain name component or component fragment. E.g., *.a.com matches foo.a.com
but not bar.foo.a.com. f*.com matches foo.com but not bar.com." RFC 2459 §4.2.1.7: "no
signifigance is attached to the case". A name is accepted only if it matches under these rules
(`Hostcheck.nameMatch`). -/
def match_sound : Prop :=
  ∀ (c : Caller) (matchp hostp : UInt32) (p h : List UInt8), Pre c matchp hostp p h →
    Decides c fun m => accepted m → Hostcheck.nameMatch p h = true

/-- **A wildcard leftmost component matches any single host component.** The name `*.S`, where `S`
has a further dot (curl does not let `*.com` cover a whole top-level domain), is accepted for
every host name `L.S'` with `L` non-empty and dot-free and `S'` equal to `S` up to case, unless
the host name is an IP address (`ip_host_exact`). -/
def match_leftmost_wildcard : Prop :=
  ∀ (c : Caller) (matchp hostp : UInt32) (s l s' : List UInt8),
    Pre c matchp hostp (0x2A :: 0x2E :: s) (l ++ 0x2E :: s') →
    0x2E ∈ s → l ≠ [] → 0x2E ∉ l → Hostcheck.ciEq s' s = true →
    Hostcheck.isIP (l ++ 0x2E :: s') = false →
    Decides c accepted

/-- **An IP-address host matches only its own text.** RFC 2818 §3.1: "In some cases, the URI is
specified as an IP address rather than a hostname. In this case, the iPAddress subjectAltName must
be present in the certificate and must exactly match the IP in the URI." When the host name is an
`IPv4address` or `IPv6address` of RFC 3986 §3.2.2 (`Hostcheck.isIP`), a name is accepted only if
it equals the host name; case is ignored because `A`–`F` and `a`–`f` are the same hexadecimal
digits. -/
def ip_host_exact : Prop :=
  ∀ (c : Caller) (matchp hostp : UInt32) (p h : List UInt8), Pre c matchp hostp p h →
    Hostcheck.isIP h = true →
    Decides c fun m => accepted m → Hostcheck.ciEq p h = true

end Curl.Hostcheck
