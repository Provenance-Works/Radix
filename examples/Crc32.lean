import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Example: CRC-32 Checksum

Implements the CRC-32/ISO-HDLC algorithm (used in Ethernet, gzip, PNG)
using Radix's bitwise primitives. Demonstrates:

- `Radix.UInt32` wrapping arithmetic and bitwise operations
- Bit manipulation: XOR, shifts, complement
- Table-driven optimization pattern
-/

namespace Examples.Crc32

/-- CRC-32 polynomial in reversed (LSB-first) representation. -/
private def crc32Poly : Radix.UInt32 := ⟨0xEDB88320⟩

/-- Compute CRC-32 of a single byte against a running CRC value (bit-by-bit). -/
private def crc32UpdateByte (crc : Radix.UInt32) (byte : UInt8) : Radix.UInt32 :=
  let init := Radix.UInt32.bxor crc (Radix.UInt32.fromBuiltin byte.toUInt32)
  let step (c : Radix.UInt32) : Radix.UInt32 :=
    if Radix.UInt32.testBit c 0 then
      Radix.UInt32.bxor (Radix.UInt32.shrLogical c ⟨1⟩) crc32Poly
    else
      Radix.UInt32.shrLogical c ⟨1⟩
  step (step (step (step (step (step (step (step init)))))))

/-- Compute CRC-32 of a byte array (bit-by-bit reference). -/
private def crc32Naive (data : ByteArray) : Radix.UInt32 :=
  let init := Radix.UInt32.bnot ⟨0⟩
  let result := data.foldl (init := init) fun crc byte =>
    crc32UpdateByte crc byte
  Radix.UInt32.bnot result

/-- Build the CRC-32 lookup table (256 entries). -/
private def buildCrc32Table : Array Radix.UInt32 := Id.run do
  let mut table : Array Radix.UInt32 := Array.mkEmpty 256
  for i in [:256] do
    let mut crc : Radix.UInt32 := ⟨i.toUInt32⟩
    for _ in [:8] do
      if Radix.UInt32.testBit crc 0 then
        crc := Radix.UInt32.bxor (Radix.UInt32.shrLogical crc ⟨1⟩) crc32Poly
      else
        crc := Radix.UInt32.shrLogical crc ⟨1⟩
    table := table.push crc
  return table

/-- Precomputed CRC-32 table. -/
private def crc32Table : Array Radix.UInt32 := buildCrc32Table

/-- Compute CRC-32 using the precomputed lookup table. -/
def crc32 (data : ByteArray) : Radix.UInt32 :=
  let init := Radix.UInt32.bnot ⟨0⟩
  let result := data.foldl (init := init) fun crc byte =>
    let index := Radix.UInt32.bxor crc (Radix.UInt32.fromBuiltin byte.toUInt32)
    let tableIdx := index.toNat % 256
    match crc32Table[tableIdx]? with
    | some entry => Radix.UInt32.bxor entry (Radix.UInt32.shrLogical crc ⟨8⟩)
    | none => crc
  Radix.UInt32.bnot result

/-- Format a Radix.UInt32 as 0x-prefixed hex string. -/
private def toHex32 (v : Radix.UInt32) : String :=
  let digits := Nat.toDigits 16 v.toNat
  let padded := List.replicate (8 - digits.length) '0' ++ digits
  "0x" ++ String.ofList padded

def run : IO Unit := do
  IO.println "=== CRC-32 Checksum Calculator ==="
  IO.println ""

  -- Test vector: ASCII "123456789" -> 0xCBF43926
  let testData := "123456789".toUTF8
  let crcTable := crc32 testData
  IO.println s!"  CRC-32(\"123456789\") = {toHex32 crcTable}"
  if crcTable.toNat != 0xCBF43926 then
    throw (IO.userError s!"FAIL: expected 0xCBF43926, got {toHex32 crcTable}")
  IO.println "  ✓ Matches known test vector"

  -- Verify naive and table-driven agree
  let crcNaive := crc32Naive testData
  if crcTable.toNat != crcNaive.toNat then
    throw (IO.userError "FAIL: table-driven and naive disagree")
  IO.println "  ✓ Table-driven matches bit-by-bit reference"

  -- Empty data
  let crcEmpty := crc32 ByteArray.empty
  IO.println s!"  CRC-32(\"\") = {toHex32 crcEmpty}"

  -- Single byte
  let crcZero := crc32 (ByteArray.mk #[0])
  IO.println s!"  CRC-32([0x00]) = {toHex32 crcZero}"

  -- Detect 1-bit corruption
  IO.println ""
  IO.println "  Properties:"
  let original := "Hello, World!".toUTF8
  let crcOrig := crc32 original
  let mut corrupted := original
  let byte0 := corrupted.get! 0
  corrupted := corrupted.set! 0 (byte0 ^^^ 1)
  let crcCorrupted := crc32 corrupted
  IO.println s!"    Original CRC:  {toHex32 crcOrig}"
  IO.println s!"    Corrupted CRC: {toHex32 crcCorrupted}"
  IO.println s!"    1-bit error detected: {crcOrig.toNat != crcCorrupted.toNat}"

  -- Polynomial analysis using Radix bit scan
  IO.println ""
  IO.println "  Polynomial analysis:"
  IO.println s!"    Polynomial (reversed): {toHex32 crc32Poly}"
  IO.println s!"    Popcount: {(Radix.UInt32.popcount crc32Poly).toNat} set bits"
  IO.println s!"    CLZ: {(Radix.UInt32.clz crc32Poly).toNat}"
  IO.println s!"    CTZ: {(Radix.UInt32.ctz crc32Poly).toNat}"
  IO.println ""

end Examples.Crc32
