import Radix.Binary.Leb128

/-!
# Example: Variable-Length Integer Encoding (LEB128)

Demonstrates LEB128 (Little Endian Base 128) encoding, the same
format used in DWARF debug info, WebAssembly, and Protocol Buffers.
Shows:

- Unsigned and signed LEB128 encoding/decoding
- Space efficiency analysis
- Protocol Buffers-style message encoding
-/

namespace Examples.Varint

/-- Right-pad a string with spaces to the given width. -/
private def rightpad (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- Format byte array as hex. -/
private def bytesToHex (ba : ByteArray) : String :=
  let hexList := ba.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    let padded := List.replicate (2 - digits.length) '0' ++ digits
    String.ofList padded
  " ".intercalate hexList

def run : IO Unit := do
  IO.println "=== Variable-Length Integer Encoding (LEB128) ==="
  IO.println ""

  -- 1. Unsigned LEB128 basics
  IO.println "  1. Unsigned LEB128"
  IO.println "  ---"

  let testValues : List (Radix.UInt32 × String) := [
    (⟨0⟩, "0"),
    (⟨127⟩, "127"),
    (⟨128⟩, "128"),
    (⟨255⟩, "255"),
    (⟨256⟩, "256"),
    (⟨624485⟩, "624485"),
    (⟨16384⟩, "16384"),
    (⟨2097152⟩, "2097152")
  ]

  IO.println "    Value       | Bytes | Encoded"
  IO.println "    ------------|-------|--------"
  for (val, name) in testValues do
    let encoded := Radix.Binary.Leb128.encodeU32 val
    IO.println s!"    {rightpad name 12}| {encoded.size}     | [{bytesToHex encoded}]"

  -- Verify round-trip
  IO.println ""
  IO.println "    Round-trip verification:"
  for (val, name) in testValues do
    let encoded := Radix.Binary.Leb128.encodeU32 val
    match Radix.Binary.Leb128.decodeU32 encoded 0 with
    | some (decoded, consumed) =>
      let ok := decoded.toNat == val.toNat
      IO.println s!"    {name}: encode→decode = {decoded.toNat}, consumed={consumed} bytes {if ok then "✓" else "✗"}"
    | none =>
      IO.println s!"    {name}: decode failed ✗"
  IO.println ""

  -- 2. Signed LEB128
  IO.println "  2. Signed LEB128"
  IO.println "  ---"

  let signedValues : List (Radix.Int32 × String) := [
    (Radix.Int32.fromInt 0, "0"),
    (Radix.Int32.fromInt 1, "1"),
    (Radix.Int32.fromInt (-1), "-1"),
    (Radix.Int32.fromInt 63, "63"),
    (Radix.Int32.fromInt (-64), "-64"),
    (Radix.Int32.fromInt 127, "127"),
    (Radix.Int32.fromInt (-128), "-128"),
    (Radix.Int32.fromInt (-123456), "-123456")
  ]

  IO.println "    Value       | Bytes | Encoded"
  IO.println "    ------------|-------|--------"
  for (val, name) in signedValues do
    let encoded := Radix.Binary.Leb128.encodeS32 val
    IO.println s!"    {rightpad name 12}| {encoded.size}     | [{bytesToHex encoded}]"

  -- Verify signed round-trip
  IO.println ""
  IO.println "    Round-trip verification:"
  for (val, name) in signedValues do
    let encoded := Radix.Binary.Leb128.encodeS32 val
    match Radix.Binary.Leb128.decodeS32 encoded 0 with
    | some (decoded, consumed) =>
      let ok := decoded.toInt == val.toInt
      IO.println s!"    {name}: encode→decode = {decoded.toInt}, consumed={consumed} bytes {if ok then "✓" else "✗"}"
    | none =>
      IO.println s!"    {name}: decode failed ✗"
  IO.println ""

  -- 3. Space efficiency analysis
  IO.println "  3. Space Efficiency"
  IO.println "  ---"
  IO.println "    LEB128 uses fewer bytes for smaller values:"
  IO.println "    Range              | LEB128 | Fixed u32"
  IO.println "    -------------------|--------|----------"
  let ranges : List (Radix.UInt32 × String) := [
    (⟨0⟩, "0"),
    (⟨127⟩, "0-127"),
    (⟨128⟩, "128"),
    (⟨16383⟩, "128-16383"),
    (⟨16384⟩, "16384"),
    (⟨2097151⟩, "up to 2097151"),
    (⟨268435455⟩, "up to 268435455"),
    (⟨4294967295⟩, "max u32")
  ]
  for (val, desc) in ranges do
    let encoded := Radix.Binary.Leb128.encodeU32 val
    IO.println s!"    {rightpad desc 19}| {encoded.size}      | 4"

  -- 4. 64-bit encoding
  IO.println ""
  IO.println "  4. 64-bit LEB128"
  IO.println "  ---"
  let val64 : Radix.UInt64 := ⟨0x0000FFFFFFFFFFFF⟩
  let enc64 := Radix.Binary.Leb128.encodeU64 val64
  IO.println s!"    Value: {val64.toNat}"
  IO.println s!"    Encoded: {enc64.size} bytes [{bytesToHex enc64}]"

  match Radix.Binary.Leb128.decodeU64 enc64 0 with
  | some (dec64, consumed64) =>
    IO.println s!"    Decoded: {dec64.toNat}, consumed: {consumed64} bytes"
    if dec64.toNat == val64.toNat then
      IO.println "    ✓ Round-trip verified"
  | none =>
    IO.println "    Decode failed"

  IO.println ""

end Examples.Varint
