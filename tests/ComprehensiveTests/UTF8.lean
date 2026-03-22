import tests.ComprehensiveTests.Framework
import Radix.UTF8

/-!
# UTF-8 Tests
-/

open ComprehensiveTests

namespace UTF8Test

private def scalar (n : Nat) : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? n with
  | some s => pure s
  | none => throw (IO.userError s!"invalid scalar {n}")

end UTF8Test

def runUTF8Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UTF8 tests..."

  let ascii ← UTF8Test.scalar 0x41
  let twoByte ← UTF8Test.scalar 0x00A2
  let threeByte ← UTF8Test.scalar 0x20AC
  let fourByte ← UTF8Test.scalar 0x1F642

  assert (Radix.UTF8.encodedLength ascii == 1) "ASCII length"
  assert (Radix.UTF8.encodedLength twoByte == 2) "2-byte length"
  assert (Radix.UTF8.encodedLength threeByte == 3) "3-byte length"
  assert (Radix.UTF8.encodedLength fourByte == 4) "4-byte length"

  let encoded := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  assert (Radix.UTF8.isWellFormed encoded) "encoded scalars well formed"
  match Radix.UTF8.decodeBytes? encoded with
  | some scalars =>
    assert (scalars.map (·.val) == [0x41, 0x00A2, 0x20AC, 0x1F642]) "decode encoded scalars"
  | none => assert false "decode encoded scalars failed"

  let malformed1 := ByteArray.mk #[0xC0, 0xAF]
  let malformed2 := ByteArray.mk #[0xED, 0xA0, 0x80]
  assert (!Radix.UTF8.isWellFormed malformed1) "reject overlong"
  assert (!Radix.UTF8.isWellFormed malformed2) "reject surrogate"

  c.get
