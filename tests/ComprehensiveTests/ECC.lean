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
  assert (Radix.ECC.decode encoded == 0x0B) "decode(encode)"
  assert (Radix.ECC.check encoded) "encoded word parity"

  let corrupted := encoded ^^^ 0x04
  assert (Radix.ECC.check corrupted == false) "single-bit corruption detected"
  let corrected := Radix.ECC.correct corrupted
  assert (Radix.ECC.decode corrected == 0x0B) "single-bit correction"

  assert (Radix.ECC.evenParity 0x00) "zero has even parity"
  assert (!Radix.ECC.evenParity 0x01) "one has odd parity"

  c.get
