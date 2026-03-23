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

  for mask in ([0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40] : List UInt8) do
    let corrupted := encoded ^^^ mask
    assert (Radix.ECC.check corrupted == false) s!"single-bit corruption detected: {mask}"
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
