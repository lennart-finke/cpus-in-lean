/-!
# Byte encodings for specifications

Model-free helpers that specifications may use: a `Spec` module imports neither the model nor the
harness, only this file. `Ssl.Harness` imports it, so statements see the same names.
-/
namespace Ssl

/-- Bytes of a 32-bit value, little-endian. -/
def le32 (v : UInt32) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
def le16 (v : UInt16) : List UInt8 := [v.toUInt8, (v >>> 8).toUInt8]
def le64 (v : UInt64) : List UInt8 := le32 v.toUInt32 ++ le32 (v >>> 32).toUInt32
def be32 (v : UInt32) : List UInt8 := (le32 v).reverse
def be64 (v : UInt64) : List UInt8 := (le64 v).reverse

end Ssl
