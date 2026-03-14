import Radix.Memory
import Radix.Bytes.Slice

/-!
# Example: Hex Dump Utility

A classic hex dump tool that displays binary data in the traditional
format: offset | hex bytes | ASCII. Demonstrates:

- `Radix.Memory.Buffer` for data storage
- Bounds-checked byte reads
- Formatting binary data for display
-/

namespace Examples.HexDump

/-- Convert a nibble (0-15) to a hex character. -/
private def nibbleToHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'a'.toNat)

/-- Format a byte as two hex characters. -/
private def byteToHex (b : Nat) : String :=
  let hi := nibbleToHex (b / 16)
  let lo := nibbleToHex (b % 16)
  String.ofList [hi, lo]

/-- Format an offset as an 8-character hex string. -/
private def offsetToHex (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  let padded := List.replicate (8 - digits.length) '0' ++ digits
  String.ofList padded

/-- Check if a byte value represents a printable ASCII character. -/
private def isPrintable (b : Nat) : Bool :=
  b >= 0x20 && b < 0x7F

/-- Produce hex dump lines from a Buffer.
    Each line shows: offset | 16 hex bytes (split 8|8) | ASCII -/
def hexDump (buf : Radix.Memory.Buffer) : List String := Id.run do
  let mut lines : List String := []
  let mut offset := 0
  while offset < buf.size do
    -- Offset column
    let mut line := offsetToHex offset ++ "  "

    -- Hex bytes column (up to 16 bytes)
    let mut ascii := "|"
    let bytesThisLine := min 16 (buf.size - offset)
    for i in [:16] do
      if i < bytesThisLine then
        match Radix.Memory.Buffer.checkedReadU8 buf (offset + i) with
        | some v =>
          let n := v.toNat
          line := line ++ byteToHex n ++ " "
          ascii := ascii ++ String.ofList [if isPrintable n then Char.ofNat n else '.']
        | none =>
          line := line ++ "   "
          ascii := ascii ++ " "
      else
        line := line ++ "   "
    -- Add separator between byte groups and ASCII
    ascii := ascii ++ "|"
    line := line ++ " " ++ ascii
    lines := lines ++ [line]
    offset := offset + 16
  return lines

def run : IO Unit := do
  IO.println "=== Hex Dump Utility ==="
  IO.println ""

  -- Create a buffer with mixed data
  let mut buf := Radix.Memory.Buffer.zeros 64

  -- Write some ASCII text
  let text := "Hello, Radix!"
  let textBytes := text.toUTF8
  for i in [:textBytes.size] do
    match Radix.Memory.Buffer.checkedWriteU8 buf i ⟨textBytes.get! i⟩ with
    | some buf' => buf := buf'
    | none => pure ()

  -- Write some binary data at offset 32
  let binData : List Nat := [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE,
                              0x00, 0x01, 0x02, 0x03, 0xFF, 0xFE, 0xFD, 0xFC]
  for i in [:binData.length] do
    match binData[i]? with
    | some v =>
      match Radix.Memory.Buffer.checkedWriteU8 buf (32 + i) ⟨v.toUInt8⟩ with
      | some buf' => buf := buf'
      | none => pure ()
    | none => pure ()

  -- Generate and display hex dump
  IO.println s!"  Buffer: {buf.size} bytes"
  IO.println ""
  let lines := hexDump buf
  for line in lines do
    IO.println s!"  {line}"

  -- Also demonstrate a 32-bit write and its hex layout
  IO.println ""
  IO.println "  --- Multi-byte write test ---"
  let mut buf2 := Radix.Memory.Buffer.zeros 8
  match Radix.Memory.Buffer.checkedWriteU32BE buf2 0 ⟨0x01020304⟩ with
  | some buf2' =>
    buf2 := buf2'
    match Radix.Memory.Buffer.checkedWriteU32BE buf2 4 ⟨0xDEADBEEF⟩ with
    | some buf2'' =>
      for line in hexDump buf2'' do
        IO.println s!"  {line}"
    | none => IO.println "  write failed"
  | none => IO.println "  write failed"

  IO.println ""

end Examples.HexDump
