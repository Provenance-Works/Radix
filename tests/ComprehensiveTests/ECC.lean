import tests.ComprehensiveTests.Framework
import Radix.ECC

/-!
# ECC Tests
-/

open ComprehensiveTests

def runECCTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    ECC tests..."

  let nibble : Radix.ECC.Nibble := ⟨0xB, by decide⟩
  let encoded := Radix.ECC.encodeNibble nibble
  assert (Radix.ECC.decode encoded == (some (0x0B : UInt8))) "decode(encode)"
  assert (Radix.ECC.check encoded) "encoded word parity"
  assert (Radix.ECC.status? encoded == some .clean) "encoded word classified as clean"
  assert (Radix.ECC.errorIndex? encoded == none) "clean codeword has no error index"
  assert (Radix.ECC.encodeByte? 0x0B == some encoded) "encodeByte? accepts low nibble"
  assert (Radix.ECC.encodeByte? 0xF0 == none) "encodeByte? rejects wide byte"

  for (mask, expectedIdx) in ([
      ((0x01 : UInt8), 0),
      ((0x02 : UInt8), 1),
      ((0x04 : UInt8), 2),
      ((0x08 : UInt8), 3),
      ((0x10 : UInt8), 4),
      ((0x20 : UInt8), 5),
      ((0x40 : UInt8), 6)
    ] : List (UInt8 × Nat)) do
    let corrupted := encoded ^^^ mask
    assert (Radix.ECC.check corrupted == false) s!"single-bit corruption detected: {mask}"
    assert (Radix.ECC.decode corrupted == none) s!"single-bit corruption rejected by decode: {mask}"
    match Radix.ECC.errorIndex? corrupted with
    | some idx =>
      assert (idx.val == expectedIdx) s!"syndrome classified error bit: {mask}"
    | none =>
      assert false s!"single-bit corruption should produce an error index: {mask}"
    match Radix.ECC.status? corrupted with
    | some (.corrected idx) =>
      assert (idx.val == expectedIdx) s!"status records corrected index: {mask}"
    | _ =>
      assert false s!"single-bit corruption should be classified as corrected: {mask}"
    assert (Radix.ECC.decodeAfterCorrect corrupted == (some (0x0B : UInt8)))
      s!"decodeAfterCorrect repairs single-bit corruption: {mask}"
    match (Radix.ECC.correct corrupted : Option UInt8) with
    | some corrected =>
      assert (Radix.ECC.decode corrected == (some (0x0B : UInt8))) s!"single-bit correction: {mask}"
      assert (Radix.ECC.check corrected) s!"corrected parity restored: {mask}"
    | none => assert false s!"single-bit correction unexpectedly failed: {mask}"

  let invalid : UInt8 := 0x80
  assert (!Radix.ECC.check invalid) "reject high-bit invalid word"
  match (Radix.ECC.decode invalid : Option UInt8) with
  | none => assert true "decode invalid word"
  | some _ => assert false "decode invalid word"
  match (Radix.ECC.correct invalid : Option UInt8) with
  | none => assert true "correct invalid word"
  | some _ => assert false "correct invalid word"

  assert (Radix.ECC.evenParity 0x00) "zero has even parity"
  assert (!Radix.ECC.evenParity 0x01) "one has odd parity"

  c.get
