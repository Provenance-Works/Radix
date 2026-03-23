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

  -- ── Spec-level SECDED tests ──
  let specNib : Radix.ECC.Spec.Nibble := ⟨0xA, by decide⟩
  let cw := Radix.ECC.Spec.ofNibbleSECDED specNib
  assert (Radix.ECC.Spec.classifySECDED cw == .noError) "Spec SECDED clean classification"
  -- Flip a data bit in the inner Codeword74, then re-wrap
  let innerFlipped := Radix.ECC.Spec.flipAt cw.inner ⟨2, by omega⟩
  let cwFlipped : Radix.ECC.Spec.Codeword84 := { cw with inner := innerFlipped }
  assert (Radix.ECC.Spec.classifySECDED cwFlipped != .noError) "Spec SECDED detects single-bit flip"

  -- ── Ops-level batch encode/decode ──
  let nibbles : List Radix.ECC.Nibble := [
    ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩
  ]
  let encoded_batch := Radix.ECC.encodeNibbles nibbles
  let decoded_batch := Radix.ECC.decodeNibbles encoded_batch
  assert (decoded_batch == nibbles.map (fun n => some (n.val.toUInt8)))
    "batch encode/decode round-trip"
  let corrected_batch := Radix.ECC.correctAll encoded_batch
  assert (corrected_batch == encoded_batch.map some) "correctAll on clean data is identity"
  assert (Radix.ECC.countClean encoded_batch == encoded_batch.length) "all clean codewords"
  assert (Radix.ECC.countCorrected encoded_batch == 0) "no corrected codewords in clean data"

  -- ── Hamming weight/distance ──
  let cw_zero := Radix.ECC.Spec.ofNibbleSECDED ⟨0, by decide⟩
  assert (Radix.ECC.codewordWeight cw_zero.inner == 0) "hamming weight of zero codeword"
  assert (Radix.ECC.codewordDist cw.inner cw.inner == 0) "hamming distance of same codewords"
  assert (Radix.ECC.codewordDist cw.inner cw_zero.inner > 0) "hamming distance of different codewords"
  assert (Radix.ECC.popcount 0xFF == 8) "popcount 0xFF"
  assert (Radix.ECC.popcount 0x00 == 0) "popcount 0x00"
  assert (Radix.ECC.byteHammingDist 0xFF 0x00 == 8) "byte hamming distance 0xFF/0x00"

  c.get
