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

  let chunk1 := ByteArray.mk #[0xF0, 0x9F]
  let chunk2 := ByteArray.mk #[0x99, 0x82, 0x21]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init chunk1 with
  | Except.ok step1 =>
    IO.println s!"  Streaming pending bytes after chunk1: {step1.decoder.pendingByteCount}"
    match Radix.UTF8.StreamDecoder.feed? step1.decoder chunk2 with
    | Except.ok step2 =>
      IO.println s!"  Streaming decoded scalars: {step2.scalars.map (·.val)}"
      IO.println s!"  Streaming finish: {reprStr (Radix.UTF8.StreamDecoder.finish? step2.decoder)}"
    | Except.error err =>
      throw (IO.userError s!"streaming decode failed on chunk2: {reprStr err}")
  | Except.error err =>
    throw (IO.userError s!"streaming decode failed on chunk1: {reprStr err}")

  let cursorInput := Radix.UTF8.encodeScalars [ascii, euro, smile]
  let cursor := Radix.UTF8.Cursor.init cursorInput
  IO.println s!"  Cursor start offset: {cursor.byteOffset}"
  match Radix.UTF8.Cursor.advance? cursor with
  | some (firstScalar, cursor1) =>
    IO.println s!"  Cursor first scalar: {firstScalar.val}"
    IO.println s!"  Cursor next offset: {cursor1.byteOffset}"
    IO.println s!"  Cursor remaining strict decode: {reprStr (cursor1.decodeRemaining?)}"
  | none =>
    throw (IO.userError "cursor failed on valid UTF-8 input")

  let acute ← scalar 0x0301
  let graphemeInput := Radix.UTF8.encodeScalars [ascii, acute, smile]
  match Radix.UTF8.decodeGraphemes? graphemeInput with
  | some graphemes =>
    IO.println s!"  Grapheme clusters: {graphemes.map (fun grapheme => grapheme.scalars.map (·.val))}"
    IO.println s!"  Grapheme count: {graphemes.length}"
  | none =>
    throw (IO.userError "grapheme decode failed on valid UTF-8 input")

  let utf16Units := Radix.UTF8.encodeScalarsToUTF16 [ascii, smile]
  IO.println s!"  UTF-16 units: {utf16Units.toList.map UInt16.toNat}"
  match Radix.UTF8.decodeUTF16? utf16Units with
  | some scalars =>
    IO.println s!"  UTF-16 decoded scalars: {scalars.map (·.val)}"
  | none =>
    throw (IO.userError "UTF-16 decode failed on valid input")

end Examples.UTF8Demo
