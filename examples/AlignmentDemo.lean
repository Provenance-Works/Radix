import Radix.Alignment

/-!
# Example: Alignment Utilities

Demonstrates the `Radix.Alignment` module for memory alignment operations:

- Align up/down to arbitrary boundaries
- Power-of-two fast paths
- Alignment checking and padding computation
- Type-level alignment via `HasAlignment` typeclass
- Practical use case: struct layout calculation
-/

namespace Examples.AlignmentDemo

open Radix.Alignment in

/-- Demonstrate basic alignment operations. -/
def exampleBasicAlignment : IO Unit := do
  IO.println "=== Alignment: Basic Operations ==="

  -- alignUp: round up to next multiple of alignment
  let addr := 1000
  let aligned4 := alignUp addr 4
  let aligned8 := alignUp addr 8
  let aligned16 := alignUp addr 16
  IO.println s!"  alignUp {addr} to 4-byte: {aligned4}"    -- 1000
  IO.println s!"  alignUp {addr} to 8-byte: {aligned8}"    -- 1000
  IO.println s!"  alignUp {addr} to 16-byte: {aligned16}"  -- 1008

  -- alignDown: round down to previous multiple of alignment
  let addr2 := 1023
  IO.println s!"  alignDown {addr2} to 4-byte: {alignDown addr2 4}"    -- 1020
  IO.println s!"  alignDown {addr2} to 8-byte: {alignDown addr2 8}"    -- 1016
  IO.println s!"  alignDown {addr2} to 16-byte: {alignDown addr2 16}"  -- 1008

  -- isAligned: check if already aligned
  IO.println s!"  isAligned 1024 4: {isAligned 1024 4}"   -- true
  IO.println s!"  isAligned 1023 4: {isAligned 1023 4}"   -- false
  IO.println s!"  isAligned 0 8: {isAligned 0 8}"         -- true

  -- alignPadding: how many bytes to add
  IO.println s!"  padding for {addr} to 16: {alignPadding addr 16}"  -- 8

  IO.println ""

open Radix.Alignment in

/-- Demonstrate power-of-two fast path alignment. -/
def examplePow2Alignment : IO Unit := do
  IO.println "=== Alignment: Power-of-Two Fast Path ==="

  -- isPowerOfTwo check
  IO.println s!"  isPowerOfTwo 1: {isPowerOfTwo 1}"    -- true
  IO.println s!"  isPowerOfTwo 4: {isPowerOfTwo 4}"    -- true
  IO.println s!"  isPowerOfTwo 6: {isPowerOfTwo 6}"    -- false
  IO.println s!"  isPowerOfTwo 64: {isPowerOfTwo 64}"  -- true

  -- Power-of-two fast paths use bitwise ops instead of division
  let addr := 12345
  IO.println s!"  alignUpPow2 {addr} 256: {alignUpPow2 addr 256}"      -- 12544
  IO.println s!"  alignDownPow2 {addr} 256: {alignDownPow2 addr 256}"  -- 12288
  IO.println s!"  isAlignedPow2 {addr} 256: {isAlignedPow2 addr 256}"  -- false
  IO.println s!"  isAlignedPow2 4096 256: {isAlignedPow2 4096 256}"    -- true

  IO.println ""

open Radix.Alignment in

/-- Demonstrate type-level alignment with HasAlignment typeclass. -/
def exampleTypeAlignment : IO Unit := do
  IO.println "=== Alignment: Type-Level Alignment ==="

  -- Built-in alignment values for standard types
  IO.println s!"  alignmentOf UInt8:  {alignmentOfU8}"
  IO.println s!"  alignmentOf UInt16: {alignmentOfU16}"
  IO.println s!"  alignmentOf UInt32: {alignmentOfU32}"
  IO.println s!"  alignmentOf UInt64: {alignmentOfU64}"

  IO.println ""

open Radix.Alignment in

/-- Practical example: compute struct layout with padding.
    Simulates C struct layout rules for:
    ```
    struct Packet {
        uint8_t  tag;      // 1 byte, align 1
        uint32_t length;   // 4 bytes, align 4
        uint16_t checksum; // 2 bytes, align 2
        uint64_t payload;  // 8 bytes, align 8
    };
    ```
-/
def exampleStructLayout : IO Unit := do
  IO.println "=== Alignment: Struct Layout Calculation ==="

  -- Compute layout: (fieldName, fieldSize, fieldAlignment)
  let fields : List (String × Nat × Nat) := [
    ("tag",      1, alignmentOfU8),
    ("length",   4, alignmentOfU32),
    ("checksum", 2, alignmentOfU16),
    ("payload",  8, alignmentOfU64)
  ]

  let mut offset : Nat := 0
  let mut maxAlign : Nat := 1

  for (name, size, align) in fields do
    -- Pad to alignment
    let paddedOffset := alignUp offset align
    let padding := paddedOffset - offset
    IO.println s!"  {name}: offset {paddedOffset} (size {size}, align {align}, padding {padding})"
    offset := paddedOffset + size
    maxAlign := max maxAlign align

  -- Final struct size: align to max alignment
  let structSize := alignUp offset maxAlign
  let tailPadding := structSize - offset
  IO.println s!"  Struct size: {structSize} bytes (max align {maxAlign}, tail padding {tailPadding})"
  IO.println s!"  Utilization: {offset - tailPadding}/{structSize} bytes used"

  IO.println ""

/-- Main entry point for alignment examples. -/
def main : IO Unit := do
  IO.println "━━━ Alignment Examples ━━━"
  IO.println ""
  exampleBasicAlignment
  examplePow2Alignment
  exampleTypeAlignment
  exampleStructLayout
  IO.println "Alignment examples complete."

end Examples.AlignmentDemo
