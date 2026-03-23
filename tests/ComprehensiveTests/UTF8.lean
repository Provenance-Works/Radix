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
  let maxScalar ← UTF8Test.scalar 0x10FFFF

  assert (Radix.UTF8.encodedLength ascii == 1) "ASCII length"
  assert (Radix.UTF8.encodedLength twoByte == 2) "2-byte length"
  assert (Radix.UTF8.encodedLength threeByte == 3) "3-byte length"
  assert (Radix.UTF8.encodedLength fourByte == 4) "4-byte length"
  assert (Radix.UTF8.encodedLength maxScalar == 4) "max scalar length"

  let encoded := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  assert (Radix.UTF8.isWellFormed encoded) "encoded scalars well formed"
  match Radix.UTF8.decodeBytes? encoded with
  | some scalars =>
    assert (scalars.map (·.val) == [0x41, 0x00A2, 0x20AC, 0x1F642]) "decode encoded scalars"
  | none => assert false "decode encoded scalars failed"

  match Radix.UTF8.decodeNextBytes? (Radix.UTF8.encodeScalar fourByte) with
  | some (decoded, consumed) =>
    assert (decoded.val == 0x1F642) "decodeNext returns scalar"
    assert (consumed == 4) "decodeNext consumed four bytes"
  | none => assert false "decodeNext four-byte scalar failed"

  let boundaryScalars := [ascii, (← UTF8Test.scalar 0x7F), (← UTF8Test.scalar 0x80), (← UTF8Test.scalar 0x7FF), (← UTF8Test.scalar 0x800), (← UTF8Test.scalar 0xD7FF), (← UTF8Test.scalar 0xE000), (← UTF8Test.scalar 0xFFFF), (← UTF8Test.scalar 0x10000), maxScalar]
  let boundaryEncoded := Radix.UTF8.encodeScalars boundaryScalars
  match Radix.UTF8.decodeBytes? boundaryEncoded with
  | some scalars =>
    assert (scalars.map (·.val) == boundaryScalars.map (·.val)) "boundary scalar round-trip"
  | none => assert false "boundary scalar round-trip failed"

  assert (Radix.UTF8.scalarCount? boundaryEncoded == some boundaryScalars.length) "scalar count round-trip"

  let malformed1 := ByteArray.mk #[0xC0, 0xAF]
  let malformed2 := ByteArray.mk #[0xED, 0xA0, 0x80]
  let malformed3 := ByteArray.mk #[0xF0, 0x9F, 0x99]
  assert (!Radix.UTF8.isWellFormed malformed1) "reject overlong"
  assert (!Radix.UTF8.isWellFormed malformed2) "reject surrogate"
  assert (!Radix.UTF8.isWellFormed malformed3) "reject truncated four-byte sequence"
  assert (Radix.UTF8.ofNat? 0xD800 == none) "reject surrogate constructor"

  -- ── Spec-level scalar predicates ──
  assert (Radix.UTF8.Spec.Scalar.isAscii ascii) "ASCII scalar isAscii"
  assert (!Radix.UTF8.Spec.Scalar.isAscii fourByte) "four-byte scalar not isAscii"
  assert (Radix.UTF8.Spec.Scalar.isBMP threeByte) "3-byte scalar isBMP"
  assert (!Radix.UTF8.Spec.Scalar.isBMP fourByte) "four-byte scalar not isBMP"
  assert (Radix.UTF8.Spec.Scalar.isSupplementary fourByte) "four-byte scalar isSupplementary"
  assert (!Radix.UTF8.Spec.Scalar.isSupplementary ascii) "ASCII not isSupplementary"
  assert (Radix.UTF8.Spec.Scalar.plane ascii == 0) "ASCII on plane 0"
  assert (Radix.UTF8.Spec.Scalar.plane fourByte == 1) "emoji on plane 1"

  -- ── Ops-level helpers ──
  let encodedList := Radix.UTF8.encodeAllToList [ascii, twoByte]
  assert (encodedList.length > 0) "encodeAllToList produces bytes"
  let decodedList := Radix.UTF8.decodeList? encodedList
  match decodedList with
  | some scalars => assert (scalars.length == 2) "decodeList? round-trip count"
  | none => assert false "decodeList? round-trip failed"
  assert (Radix.UTF8.isWellFormedList encodedList) "encodeAllToList is well-formed"
  let byteCounts := Radix.UTF8.totalByteLength [ascii, twoByte, threeByte, fourByte]
  assert (byteCounts == 10) "totalByteLength 1+2+3+4=10"
  let nats := Radix.UTF8.scalarsToNats [ascii, twoByte]
  assert (nats == [0x41, 0x00A2]) "scalarsToNats"

  -- ── BOM tests ──
  let bomBytes := Radix.UTF8.Spec.bom
  assert (bomBytes == [0xEF, 0xBB, 0xBF]) "BOM bytes"
  assert (Radix.UTF8.Spec.hasBOM [0xEF, 0xBB, 0xBF, 0x41]) "hasBOM true"
  assert (!Radix.UTF8.Spec.hasBOM [0x41, 0x42]) "hasBOM false"
  assert (Radix.UTF8.Spec.stripBOM [0xEF, 0xBB, 0xBF, 0x41] == [0x41]) "stripBOM"
  assert (Radix.UTF8.Spec.stripBOM [0x41] == [0x41]) "stripBOM no BOM"

  -- ── Byte classification ──
  let classes := Radix.UTF8.classifyBytes (ByteArray.mk #[0x41, 0xC2, 0xA2, 0x80])
  assert (classes.length == 4) "classifyBytes length"

  c.get
