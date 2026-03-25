import Radix.UTF8

/-!
# Example: UTF-8
-/

namespace Examples.UTF8Demo

private def scalar (n : Nat) : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? n with
  | some s => pure s
  | none => throw (IO.userError s!"invalid scalar {n}")

def main : IO Unit := do
  IO.println "━━━ UTF-8 Example ━━━"
  let ascii ← scalar 0x41
  let euro ← scalar 0x20AC
  let smile ← scalar 0x1F642
  let encoded := Radix.UTF8.encodeScalars [ascii, euro, smile]
  IO.println s!"  Encoded bytes: {encoded.toList}"
  IO.println s!"  Well formed: {Radix.UTF8.isWellFormed encoded}"
  match Radix.UTF8.decodeBytes? encoded with
  | some scalars => IO.println s!"  Decoded scalars: {scalars.map (·.val)}"
  | none => throw (IO.userError "decode failed")

  let malformed := ByteArray.mk #[0xE1, 0x80, 0x41]
  let detailedStep := Radix.UTF8.decodeNextBytesStep? malformed
  IO.println s!"  Malformed bytes: {malformed.toList}"
  IO.println s!"  Detailed step: {reprStr detailedStep}"
  IO.println s!"  Legacy replacement: {Radix.UTF8.decodeBytesReplacing malformed |>.map (·.val)}"
  IO.println s!"  Strict replacement: {Radix.UTF8.decodeBytesReplacingMaximalSubparts malformed |>.map (·.val)}"

end Examples.UTF8Demo
