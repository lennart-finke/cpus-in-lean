import Curl.Hostcheck.Statement
import Check.Support
/-! Executable checks of the pinned machine code against the statements, on the CPU model: each
case is run in the OpenSSL suite's four memory placements (`Check.Support`), the precondition is
evaluated, every clause of `Returns` is checked, and the result is compared with what the three
tasks say about it. These finite examples do not discharge the tasks. -/
open X86 Ssl Check Curl.Hostcheck Curl.Spec

def ascii (s : String) : List UInt8 := s.toUTF8.toList

/-- (presented name, host name). -/
def cases : List (String × String) :=
  [("*.a.com", "foo.a.com"), ("*.a.com", "bar.foo.a.com"), ("*.a.com", ".a.com"), ("*.a.com", "a.com"),
   ("f*.com", "foo.com"), ("f*.a.com", "foo.a.com"), ("*.com", "foo.com"), ("*", "foo"),
   ("WWW.Example.COM", "www.example.com"), ("www.example.com", "www.example.org"),
   ("*.Example.COM", "WwW.eXample.com"), ("a.*.com", "a.b.com"), ("*.*.com", "a.b.com"),
   ("x*.example.com", "xn--l8j.example.com"), ("*.example.com", "xn--l8j.example.com"),
   ("192.0.2.1", "192.0.2.1"), ("*.0.2.1", "192.0.2.1"), ("*.2.1", "192.0.2.1"),
   ("*.b.c", "1.2.3.4"), ("::1", "::1"), ("*.b.c", "2001:db8::7"), ("2001:DB8::7", "2001:db8::7"),
   ("*.b.c", "1.b.c"), ("*.b.c", "01.b.c"), ("*.b.c", "a.b.c.d"), ("*.b.c", "a..b.c"),
   ("a.b.c", "a.b.c"), ("a.b.c", "a.b.cc"), ("a.b.cc", "a.b.c"), ("**.b.c", "a.b.c"),
   ("*.b.c", "a*.b.c"), ("*.b.c", "*.b.c"), ("*.bücher.example", "a.bücher.example")]

def main : IO Unit := do
  let t ← T.new
  let fn := Image.sym_Curl_cert_hostcheck
  let mut accepts := 0
  for (ps, hs) in cases do for L in t.layouts img stackBound do
    let (p, h) := (ascii ps, ascii hs)
    let (matchp, hostp) := (L.slot 0, L.slot 1)
    let c ← t.caller img L (args matchp hostp p h) [(matchp, p), (hostp, h ++ [0])]
    ensure s!"precondition: {ps} / {hs}" (decide (Pre c matchp hostp p h))
    let m ← t.call "hostcheck" img c fn stackBound []
    let acc := decide (accepted m)
    if acc then accepts := accepts + 1
    ensure s!"match_sound: {ps} accepted for {hs}" (!acc || Hostcheck.nameMatch p h)
    ensure s!"ip_host_exact: {ps} accepted for {hs}" (!(acc && Hostcheck.isIP h) || Hostcheck.ciEq p h)
    -- the wildcard form: `*.S` with a dot in `S`, against `L.S'`
    if let (0x2A :: 0x2E :: s, some i) := (p, h.idxOf? 0x2E) then
      let (l, s') := (h.take i, h.drop (i + 1))
      if s.contains 0x2E && !l.isEmpty && Hostcheck.ciEq s' s && !Hostcheck.isIP h then
        ensure s!"match_leftmost_wildcard: {ps} refused for {hs}" acc
  ensure "some names are accepted and some refused" (0 < accepts && accepts < 4 * cases.length)
  t.report [("hostcheck", stackBound)]
