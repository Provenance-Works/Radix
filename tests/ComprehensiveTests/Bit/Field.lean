import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Field
import Radix.Bit.Scan

/-!
# Bit Field Comprehensive Tests (testBit, setBit, clearBit, toggleBit, extract, insert)
## Spec References
- FR-002: Bit field operations
-/

open ComprehensiveTests

def runBitFieldTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bit field tests..."

  -- ## UInt8 testBit exhaustive for each position
  for i in [:8] do
    let v : UInt8 := (1 <<< i.toUInt8)
    -- Only bit i should be set
    for j in [:8] do
      let expected := (i == j)
      assert (Radix.UInt8.testBit ⟨v⟩ j == expected) s!"u8 testBit 2^{i}[{j}]"

  -- ## UInt8 setBit creates correct value
  for i in [:8] do
    let expected := (1 <<< i.toUInt8 : UInt8)
    assert ((Radix.UInt8.setBit ⟨0⟩ i).toNat == expected.toNat) s!"u8 setBit 0[{i}]"

  -- ## UInt8 clearBit removes correct bit
  for i in [:8] do
    let expected := ((0xFF : UInt8) ^^^ (1 <<< i.toUInt8))
    assert ((Radix.UInt8.clearBit ⟨0xFF⟩ i).toNat == expected.toNat) s!"u8 clearBit FF[{i}]"

  -- ## UInt8 toggleBit: double toggle = identity
  for v in [(0x00 : UInt8), 0xFF, 0xAA, 0x55, 0x42] do
    for i in [:8] do
      let toggled := Radix.UInt8.toggleBit ⟨v⟩ i
      let restored := Radix.UInt8.toggleBit toggled i
      assert (restored == ⟨v⟩) s!"u8 double toggle {v}[{i}]"

  -- ## UInt8 setBit already-set = no change
  assert ((Radix.UInt8.setBit ⟨0xFF⟩ 3).toNat == 0xFF) "u8 setBit idempotent"
  assert ((Radix.UInt8.clearBit ⟨0x00⟩ 3).toNat == 0x00) "u8 clearBit idempotent"

  -- ## UInt16 field operations
  for i in [:16] do
    assert (Radix.UInt16.testBit ⟨(1 <<< i.toUInt16 : UInt16)⟩ i == true) s!"u16 testBit {i}"
    assert ((Radix.UInt16.setBit ⟨0⟩ i).toNat == (1 <<< i.toUInt16 : UInt16).toNat)
      s!"u16 setBit {i}"

  -- ## UInt32 field operations
  for i in [:32] do
    assert (Radix.UInt32.testBit ⟨(1 <<< i.toUInt32 : UInt32)⟩ i == true) s!"u32 testBit {i}"

  -- ## UInt64 field operations
  for i in [:64] do
    assert (Radix.UInt64.testBit ⟨(1 <<< i.toUInt64 : UInt64)⟩ i == true) s!"u64 testBit {i}"

  -- ## extractBits / insertBits round-trips on UInt8
  -- Extract high nibble then insert back
  let v8 : Radix.UInt8 := ⟨0xAB⟩
  let hi := Radix.UInt8.extractBits v8 4 8 ⟨by omega, by omega⟩
  let lo := Radix.UInt8.extractBits v8 0 4 ⟨by omega, by omega⟩
  assert (hi.toNat == 0x0A) "u8 extract hi nibble"
  assert (lo.toNat == 0x0B) "u8 extract lo nibble"
  -- Reconstruct from parts
  let rebuilt := Radix.UInt8.insertBits (Radix.UInt8.insertBits ⟨0⟩ lo 0 4 ⟨by omega, by omega⟩)
    hi 4 8 ⟨by omega, by omega⟩
  assert (rebuilt == v8) "u8 extract+insert round-trip"

  -- ## extractBits / insertBits on UInt16
  let v16 : Radix.UInt16 := ⟨0xABCD⟩
  let hi16 := Radix.UInt16.extractBits v16 8 16 ⟨by omega, by omega⟩
  let lo16 := Radix.UInt16.extractBits v16 0 8 ⟨by omega, by omega⟩
  assert (hi16.toNat == 0xAB) "u16 extract hi byte"
  assert (lo16.toNat == 0xCD) "u16 extract lo byte"

  -- ## extractBits / insertBits on UInt32
  let v32 : Radix.UInt32 := ⟨0x12345678⟩
  assert ((Radix.UInt32.extractBits v32 24 32 ⟨by omega, by omega⟩).toNat == 0x12)
    "u32 extract byte3"
  assert ((Radix.UInt32.extractBits v32 16 24 ⟨by omega, by omega⟩).toNat == 0x34)
    "u32 extract byte2"
  assert ((Radix.UInt32.extractBits v32 8 16 ⟨by omega, by omega⟩).toNat == 0x56)
    "u32 extract byte1"
  assert ((Radix.UInt32.extractBits v32 0 8 ⟨by omega, by omega⟩).toNat == 0x78)
    "u32 extract byte0"

  -- ## Rotate properties via bit field
  -- After rotl, bit positions shift correctly
  let rv : Radix.UInt8 := ⟨0x81⟩  -- bits 7 and 0 set
  let rotated := Radix.UInt8.rotl rv ⟨1⟩
  assert (Radix.UInt8.testBit rotated 0 == true) "u8 rotl 81: bit 7→bit 0"
  assert (Radix.UInt8.testBit rotated 1 == true) "u8 rotl 81: bit 0→bit 1"

  -- ## bitReverse via field: reversed bits should be at mirrored positions
  for i in [:8] do
    let single : Radix.UInt8 := ⟨(1 <<< i.toUInt8 : UInt8)⟩
    let reversed := Radix.UInt8.bitReverse single
    assert (Radix.UInt8.testBit reversed (7 - i) == true) s!"u8 bitReverse single bit {i}"

  c.get
