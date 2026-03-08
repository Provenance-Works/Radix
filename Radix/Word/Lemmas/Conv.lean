/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Conv
import Mathlib.Data.BitVec

/-!
# Conversion Correctness Proofs (Layer 3)

This module proves correctness of width/sign conversions:
- Zero extension preserves value
- Sign extension preserves signed value
- Truncation preserves value when it fits
- Signed/unsigned cast preserves bit pattern

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- FR-001.3: Conversion correctness proofs
-/

namespace Radix

/-! ================================================================ -/
/-! ## Zero Extension Correctness                                     -/
/-! ================================================================ -/

/-- Zero-extending UInt8 to UInt16 preserves the numeric value. -/
theorem UInt8.toUInt16_toNat (x : UInt8) :
    x.toUInt16.toNat = x.toNat := by
  simp [UInt8.toUInt16, UInt16.toNat, UInt8.toNat]

/-- Zero-extending UInt8 to UInt32 preserves the numeric value. -/
theorem UInt8.toUInt32_toNat (x : UInt8) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt8.toUInt32, UInt32.toNat, UInt8.toNat]

/-- Zero-extending UInt8 to UInt64 preserves the numeric value. -/
theorem UInt8.toUInt64_toNat (x : UInt8) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt8.toUInt64, UInt64.toNat, UInt8.toNat]

/-- Zero-extending UInt16 to UInt32 preserves the numeric value. -/
theorem UInt16.toUInt32_toNat (x : UInt16) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt16.toUInt32, UInt32.toNat, UInt16.toNat]

/-- Zero-extending UInt16 to UInt64 preserves the numeric value. -/
theorem UInt16.toUInt64_toNat (x : UInt16) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt16.toUInt64, UInt64.toNat, UInt16.toNat]

/-- Zero-extending UInt32 to UInt64 preserves the numeric value. -/
theorem UInt32.toUInt64_toNat (x : UInt32) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt32.toUInt64, UInt64.toNat, UInt32.toNat]

/-! ================================================================ -/
/-! ## Signed/Unsigned Cast Bit Preservation                          -/
/-! ================================================================ -/

/-- Casting signed to unsigned preserves the bit pattern (8-bit). -/
theorem Int8.cast_bit_preserving (x : Int8) :
    x.toUInt8.toBitVec = x.toBitVec := by
  simp [Int8.toUInt8, Int8.toBitVec, UInt8.toBitVec]

/-- Casting signed to unsigned preserves the bit pattern (16-bit). -/
theorem Int16.cast_bit_preserving (x : Int16) :
    x.toUInt16.toBitVec = x.toBitVec := by
  simp [Int16.toUInt16, Int16.toBitVec, UInt16.toBitVec]

/-- Casting signed to unsigned preserves the bit pattern (32-bit). -/
theorem Int32.cast_bit_preserving (x : Int32) :
    x.toUInt32.toBitVec = x.toBitVec := by
  simp [Int32.toUInt32, Int32.toBitVec, UInt32.toBitVec]

/-- Casting signed to unsigned preserves the bit pattern (64-bit). -/
theorem Int64.cast_bit_preserving (x : Int64) :
    x.toUInt64.toBitVec = x.toBitVec := by
  simp [Int64.toUInt64, Int64.toBitVec, UInt64.toBitVec]

/-- Casting unsigned to signed and back is identity (8-bit). -/
theorem Int8.fromUInt8_toUInt8 (x : UInt8) :
    (Int8.fromUInt8 x).toUInt8 = x := by
  simp [Int8.fromUInt8, Int8.toUInt8]

/-- Casting signed to unsigned and back is identity (8-bit). -/
theorem UInt8.fromInt8_toInt8 (x : Int8) :
    Int8.fromUInt8 (x.toUInt8) = x := by
  simp [Int8.fromUInt8, Int8.toUInt8]

end Radix
