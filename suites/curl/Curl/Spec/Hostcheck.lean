/-!
# Server identity names: RFC 2818 §3.1 matching, RFC 2459 §4.2.1.7 case, RFC 3986 §3.2.2 IP literals

Written from the RFCs alone, not from curl's code.

* RFC 2818 §3.1: "Names may contain the wildcard character * which is considered to match any single
  domain name component or component fragment. E.g., *.a.com matches foo.a.com but not bar.foo.a.com.
  f*.com matches foo.com but not bar.com." `nameMatch pattern host`: both names split at `.` into
  components; there are equally many, and each pattern component matches the host component at the same
  position. A component without `*` matches a component equal to it; in a component with `*`, each `*`
  stands for any sequence of characters within the component (a "component fragment"), and the host
  component — a domain name component — is not empty.
* RFC 2459 §4.2.1.7: "no signifigance is attached to the case": characters are compared ignoring ASCII
  case (`ciEq`, `lower`).
* RFC 3986 §3.2.2: the `IPv4address` and `IPv6address` grammars (`isIPv4`, `isIPv6`): a host given as
  an IP address rather than a hostname.
-/
namespace Curl.Spec.Hostcheck

/-- ASCII lower case (RFC 2459 §4.2.1.7: the case of letters carries no significance). -/
def lower (c : UInt8) : UInt8 := if 0x41 ≤ c && c ≤ 0x5A then c + 0x20 else c

/-- Equality ignoring ASCII case. -/
def ciEq (a b : List UInt8) : Bool := a.map lower == b.map lower

/-- The components of a name, split at `.` (`"a.b"` ↦ `["a", "b"]`; `""` ↦ `[""]`). -/
def labels (s : List UInt8) : List (List UInt8) := s.splitOn 0x2E

/-- A pattern component with `*` against a host component: each `*` matches any sequence of characters,
the other characters match ignoring case. -/
def glob : List UInt8 → List UInt8 → Bool
  | [], h => h.isEmpty
  | 0x2A :: p, h => glob p h || (match h with | [] => false | _ :: h' => glob (0x2A :: p) h')
  | c :: p, d :: h => lower c == lower d && glob p h
  | _ :: _, [] => false
termination_by p h => (p.length, h.length)

/-- One pattern component against one host component. -/
def labelMatch (p h : List UInt8) : Bool :=
  if p.contains 0x2A then !h.isEmpty && glob p h else ciEq p h

/-- RFC 2818 §3.1: the presented name `pattern` matches `host`. -/
def nameMatch (pattern host : List UInt8) : Bool :=
  let ps := labels pattern
  let hs := labels host
  ps.length == hs.length && (ps.zip hs).all fun (p, h) => labelMatch p h

/-- RFC 3986 §3.2.2 `dec-octet`: `0`–`255` without leading zeros. -/
def isDecOctet (s : List UInt8) : Bool :=
  let digit (c : UInt8) : Bool := 0x30 ≤ c && c ≤ 0x39
  let v := s.foldl (fun a c => a * 10 + (c.toNat - 0x30)) 0
  1 ≤ s.length && s.length ≤ 3 && s.all digit && (s.length == 1 || s.head! != 0x30) && v ≤ 255

/-- RFC 3986 §3.2.2 `IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet`. -/
def isIPv4 (s : List UInt8) : Bool :=
  let parts := s.splitOn 0x2E
  parts.length == 4 && parts.all isDecOctet

/-- `h16 = 1*4HEXDIG`. -/
def isH16 (s : List UInt8) : Bool :=
  let hex (c : UInt8) : Bool := (0x30 ≤ c && c ≤ 0x39) || (0x41 ≤ c && c ≤ 0x46) || (0x61 ≤ c && c ≤ 0x66)
  1 ≤ s.length && s.length ≤ 4 && s.all hex

/-- The number of 16-bit pieces of `h16 *( ":" h16 )`, optionally ending in an `IPv4address` (two
pieces) when `v4` holds; `none` if `s` has another form. -/
def pieces (v4 : Bool) (s : List UInt8) : Option Nat :=
  let fs := s.splitOn 0x3A
  let init := fs.dropLast
  let last := fs.getLast!
  if !init.all isH16 then none
  else if isH16 last then some fs.length
  else if v4 && isIPv4 last then some (fs.length + 1)
  else none

/-- The first occurrence of `"::"`: the parts before and after it. -/
def splitElision : List UInt8 → Option (List UInt8 × List UInt8)
  | 0x3A :: 0x3A :: r => some ([], r)
  | c :: r => (splitElision r).map fun (a, b) => (c :: a, b)
  | [] => none

/-- RFC 3986 §3.2.2 `IPv6address`: without `"::"`, `6( h16 ":" ) ls32` (eight pieces, `ls32` either
`h16 ":" h16` or an `IPv4address`); with `"::"`, at most seven pieces on its two sides together, the
left side `h16` pieces only, the right side ending in `h16` or (if at least two pieces) in `ls32`. -/
def isIPv6 (s : List UInt8) : Bool :=
  match splitElision s with
  | none => pieces true s == some 8
  | some (l, r) =>
    let nl := if l.isEmpty then some 0 else pieces false l
    let nr := if r.isEmpty then some 0 else pieces true r
    match nl, nr with
    | some a, some b => a + b ≤ 7
    | _, _ => false

/-- A host given as an IP address (RFC 3986 §3.2.2). -/
def isIP (s : List UInt8) : Bool := isIPv4 s || isIPv6 s

private def ascii (s : String) : List UInt8 := s.toUTF8.toList

-- RFC 2818 §3.1's examples.
#guard nameMatch (ascii "*.a.com") (ascii "foo.a.com")
#guard !nameMatch (ascii "*.a.com") (ascii "bar.foo.a.com")
#guard nameMatch (ascii "f*.com") (ascii "foo.com")
#guard !nameMatch (ascii "f*.com") (ascii "bar.com")
-- RFC 2459 §4.2.1.7: case carries no significance.
#guard nameMatch (ascii "WWW.Example.COM") (ascii "www.example.com")
#guard !nameMatch (ascii "*.a.com") (ascii ".a.com") && !nameMatch (ascii "a.com") (ascii "a.com.x")
-- RFC 3986 §3.2.2's address forms.
#guard isIPv4 (ascii "192.0.2.255") && !isIPv4 (ascii "192.0.2.256") && !isIPv4 (ascii "01.2.3.4")
#guard !isIPv4 (ascii "1.2.3") && !isIPv4 (ascii "1.2.3.4.")
#guard isIPv6 (ascii "::") && isIPv6 (ascii "::1") && isIPv6 (ascii "2001:db8::7")
#guard isIPv6 (ascii "1:2:3:4:5:6:7:8") && isIPv6 (ascii "::ffff:192.0.2.1") && isIPv6 (ascii "1:2:3:4:5:6:1.2.3.4")
#guard isIPv6 (ascii "1:2:3:4:5:6:7::") && isIPv6 (ascii "::2:3:4:5:6:7:8") && isIPv6 (ascii "1::")
#guard !isIPv6 (ascii "1:2:3:4:5:6:7:8:9") && !isIPv6 (ascii "1::2::3") && !isIPv6 (ascii ":1::")
#guard !isIPv6 (ascii "1:2:3:4:5:6:7:1.2.3.4") && !isIPv6 (ascii "::1:2:3:4:5:6:1.2.3.4")
#guard !isIPv6 (ascii "12345::") && !isIPv6 (ascii "1:2:3:4:5:6:7") && !isIPv6 (ascii "1.2.3.4::")
#guard isIPv6 (ascii "1::2:3:4:5:6:7") && !isIPv6 (ascii "1::2:3:4:5:6:7:8")

end Curl.Spec.Hostcheck
