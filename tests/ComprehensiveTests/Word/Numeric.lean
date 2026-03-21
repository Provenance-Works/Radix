import tests.ComprehensiveTests.Framework
import Radix.Word.Numeric

/-!
# Numeric Typeclasses Tests
## Spec References
- v0.2.0: Generic numeric typeclasses for width-agnostic code
-/

open ComprehensiveTests

def runNumericTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Numeric typeclass tests..."

  -- ## BoundedUInt: UInt8
  assert (Radix.Word.BoundedUInt.minVal (α := Radix.UInt8) == ⟨0⟩) "UInt8 minVal"
  assert (Radix.Word.BoundedUInt.maxVal (α := Radix.UInt8) == ⟨255⟩) "UInt8 maxVal"
  assert (Radix.Word.BoundedUInt.toNat (⟨42⟩ : Radix.UInt8) == 42) "UInt8 toNat"
  assert ((Radix.Word.BoundedUInt.wrappingAdd (⟨200⟩ : Radix.UInt8) ⟨100⟩).toNat == 44)
    "UInt8 generic wrappingAdd"
  assert ((Radix.Word.BoundedUInt.saturatingAdd (⟨200⟩ : Radix.UInt8) ⟨100⟩).toNat == 255)
    "UInt8 generic saturatingAdd"

  -- ## BoundedUInt: UInt16
  assert (Radix.Word.BoundedUInt.minVal (α := Radix.UInt16) == ⟨0⟩) "UInt16 minVal"
  assert (Radix.Word.BoundedUInt.maxVal (α := Radix.UInt16) == ⟨65535⟩) "UInt16 maxVal"
  assert ((Radix.Word.BoundedUInt.wrappingAdd (⟨60000⟩ : Radix.UInt16) ⟨10000⟩).toNat == 4464)
    "UInt16 generic wrappingAdd"

  -- ## BoundedUInt: UInt32
  assert (Radix.Word.BoundedUInt.minVal (α := Radix.UInt32) == ⟨0⟩) "UInt32 minVal"
  assert (Radix.Word.BoundedUInt.toNat (⟨1000000⟩ : Radix.UInt32) == 1000000)
    "UInt32 toNat"

  -- ## BoundedUInt: UInt64
  assert (Radix.Word.BoundedUInt.minVal (α := Radix.UInt64) == ⟨0⟩) "UInt64 minVal"
  assert (Radix.Word.BoundedUInt.toNat (⟨123456789⟩ : Radix.UInt64) == 123456789)
    "UInt64 toNat"

  -- ## Generic helpers
  assert (Radix.Word.genericZero (α := Radix.UInt8) == ⟨0⟩) "genericZero UInt8"
  assert (Radix.Word.genericMaxVal (α := Radix.UInt8) == ⟨255⟩) "genericMaxVal UInt8"
  assert (Radix.Word.isZero (⟨0⟩ : Radix.UInt8) == true) "isZero true"
  assert (Radix.Word.isZero (⟨1⟩ : Radix.UInt8) == false) "isZero false"
  assert (Radix.Word.isMax (⟨255⟩ : Radix.UInt8) == true) "isMax true"
  assert (Radix.Word.isMax (⟨0⟩ : Radix.UInt8) == false) "isMax false"

  -- ## BoundedInt: Int8
  assert (Radix.Word.BoundedInt.minVal (α := Radix.Int8) == ⟨-128⟩) "Int8 minVal"
  assert (Radix.Word.BoundedInt.maxVal (α := Radix.Int8) == ⟨127⟩) "Int8 maxVal"
  assert (Radix.Word.BoundedInt.isNeg (⟨-1⟩ : Radix.Int8) == true) "Int8 isNeg true"
  assert (Radix.Word.BoundedInt.isNeg (⟨0⟩ : Radix.Int8) == false) "Int8 isNeg false"
  assert (Radix.Word.BoundedInt.isNeg (⟨1⟩ : Radix.Int8) == false) "Int8 isNeg pos"

  -- ## BitwiseOps: UInt8
  assert ((Radix.Word.BitwiseOps.band (⟨0xAA⟩ : Radix.UInt8) ⟨0x0F⟩).toNat == 0x0A)
    "UInt8 generic band"
  assert ((Radix.Word.BitwiseOps.bor (⟨0xA0⟩ : Radix.UInt8) ⟨0x0F⟩).toNat == 0xAF)
    "UInt8 generic bor"
  assert ((Radix.Word.BitwiseOps.bxor (⟨0xFF⟩ : Radix.UInt8) ⟨0xAA⟩).toNat == 0x55)
    "UInt8 generic bxor"

  -- ## Checked arithmetic
  assert (Radix.Word.BoundedUInt.checkedAdd (⟨200⟩ : Radix.UInt8) ⟨100⟩ == none)
    "UInt8 generic checkedAdd overflow"
  assert (Radix.Word.BoundedUInt.checkedAdd (⟨100⟩ : Radix.UInt8) ⟨50⟩ == some ⟨150⟩)
    "UInt8 generic checkedAdd ok"

  c.get
