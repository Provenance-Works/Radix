/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int
import Radix.Word.Size
import Radix.Word.Arith
import Radix.Bit.Ops

/-!
# Numeric Typeclasses (Layer 2)

This module defines generic numeric typeclasses that abstract over all
10 integer types in Radix:
- `BoundedUInt`: Unsigned integers with known min/max bounds
- `BoundedInt`: Signed integers with known min/max bounds
- `BitwiseOps`: Bitwise operations abstraction

These typeclasses enable downstream libraries to write code once over
"any integer width" rather than duplicating logic for each concrete type.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Builds on `FixedWidth` and `LawfulFixedWidth` from `Word.UInt`.
- Provides instances for all 10 integer types.

## References

- v0.2.0 Roadmap: Numeric Typeclasses
- FR-001: Fixed-Width Integer Arithmetic
-/

namespace Radix

/-! ## BoundedUInt Typeclass -/

/-- Typeclass for unsigned fixed-width integers with known bounds.
    Provides `minVal`, `maxVal`, `toNat`, and wrapping/saturating/checked
    arithmetic in a width-generic way. -/
class BoundedUInt (α : Type) extends LawfulFixedWidth α where
  /-- The minimum value (always 0 for unsigned). -/
  minVal : α
  /-- The maximum value (`2^bitWidth - 1`). -/
  maxVal : α
  /-- Convert to `Nat`. -/
  toNat : α → Nat
  /-- Wrapping addition: `(x + y) mod 2^bitWidth`. -/
  wrappingAdd : α → α → α
  /-- Wrapping subtraction: `(x - y) mod 2^bitWidth`. -/
  wrappingSub : α → α → α
  /-- Wrapping multiplication: `(x * y) mod 2^bitWidth`. -/
  wrappingMul : α → α → α
  /-- Saturating addition: `min(x + y, maxVal)`. -/
  saturatingAdd : α → α → α
  /-- Saturating subtraction: `max(x - y, 0)`. -/
  saturatingSub : α → α → α
  /-- Checked addition: `none` on overflow. -/
  checkedAdd : α → α → Option α
  /-- Checked subtraction: `none` on underflow. -/
  checkedSub : α → α → Option α
  /-- Checked multiplication: `none` on overflow. -/
  checkedMul : α → α → Option α
  /-- `minVal` has `toNat = 0`. -/
  toNat_minVal : toNat minVal = 0
  /-- `maxVal` has `toNat = 2^bitWidth - 1`. -/
  toNat_maxVal : toNat maxVal = 2 ^ FixedWidth.bitWidth - 1
  /-- Wrapping addition is the same as `+`. -/
  wrappingAdd_eq_add : ∀ x y : α, wrappingAdd x y = x + y

instance : BoundedUInt UInt8 where
  minVal := UInt8.minVal
  maxVal := UInt8.maxVal
  toNat := UInt8.toNat
  wrappingAdd := UInt8.wrappingAdd
  wrappingSub := UInt8.wrappingSub
  wrappingMul := UInt8.wrappingMul
  saturatingAdd := UInt8.saturatingAdd
  saturatingSub := UInt8.saturatingSub
  checkedAdd := UInt8.checkedAdd
  checkedSub := UInt8.checkedSub
  checkedMul := UInt8.checkedMul
  toNat_minVal := by native_decide
  toNat_maxVal := by native_decide
  wrappingAdd_eq_add := by intro x y; rfl

instance : BoundedUInt UInt16 where
  minVal := UInt16.minVal
  maxVal := UInt16.maxVal
  toNat := UInt16.toNat
  wrappingAdd := UInt16.wrappingAdd
  wrappingSub := UInt16.wrappingSub
  wrappingMul := UInt16.wrappingMul
  saturatingAdd := UInt16.saturatingAdd
  saturatingSub := UInt16.saturatingSub
  checkedAdd := UInt16.checkedAdd
  checkedSub := UInt16.checkedSub
  checkedMul := UInt16.checkedMul
  toNat_minVal := by native_decide
  toNat_maxVal := by native_decide
  wrappingAdd_eq_add := by intro x y; rfl

instance : BoundedUInt UInt32 where
  minVal := UInt32.minVal
  maxVal := UInt32.maxVal
  toNat := UInt32.toNat
  wrappingAdd := UInt32.wrappingAdd
  wrappingSub := UInt32.wrappingSub
  wrappingMul := UInt32.wrappingMul
  saturatingAdd := UInt32.saturatingAdd
  saturatingSub := UInt32.saturatingSub
  checkedAdd := UInt32.checkedAdd
  checkedSub := UInt32.checkedSub
  checkedMul := UInt32.checkedMul
  toNat_minVal := by native_decide
  toNat_maxVal := by native_decide
  wrappingAdd_eq_add := by intro x y; rfl

instance : BoundedUInt UInt64 where
  minVal := UInt64.minVal
  maxVal := UInt64.maxVal
  toNat := UInt64.toNat
  wrappingAdd := UInt64.wrappingAdd
  wrappingSub := UInt64.wrappingSub
  wrappingMul := UInt64.wrappingMul
  saturatingAdd := UInt64.saturatingAdd
  saturatingSub := UInt64.saturatingSub
  checkedAdd := UInt64.checkedAdd
  checkedSub := UInt64.checkedSub
  checkedMul := UInt64.checkedMul
  toNat_minVal := by native_decide
  toNat_maxVal := by native_decide
  wrappingAdd_eq_add := by intro x y; rfl

/-! ## BoundedInt Typeclass -/

/-- Typeclass for signed fixed-width integers with known bounds.
    Uses two's complement representation. -/
class BoundedInt (α : Type) extends FixedWidth α, Add α, Sub α, Mul α, Neg α where
  /-- The minimum value (`-2^(bitWidth-1)`). -/
  minVal : α
  /-- The maximum value (`2^(bitWidth-1) - 1`). -/
  maxVal : α
  /-- Convert to `Int` (two's complement interpretation). -/
  toInt : α → Int
  /-- Is the value negative? (MSB = 1) -/
  isNeg : α → Bool
  /-- Convert from `Int`, truncating to `bitWidth` bits. -/
  fromInt : Int → α
  /-- `toInt minVal = -2^(bitWidth-1)`. -/
  toInt_minVal : toInt minVal = -(2 ^ (FixedWidth.bitWidth - 1) : Nat)
  /-- `toInt maxVal = 2^(bitWidth-1) - 1`. -/
  toInt_maxVal : toInt maxVal = 2 ^ (FixedWidth.bitWidth - 1) - 1

instance : BoundedInt Int8 where
  minVal := Int8.minVal
  maxVal := Int8.maxVal
  toInt := Int8.toInt
  isNeg := Int8.isNeg
  fromInt := Int8.fromInt
  toInt_minVal := by native_decide
  toInt_maxVal := by native_decide

instance : BoundedInt Int16 where
  minVal := Int16.minVal
  maxVal := Int16.maxVal
  toInt := Int16.toInt
  isNeg := Int16.isNeg
  fromInt := Int16.fromInt
  toInt_minVal := by native_decide
  toInt_maxVal := by native_decide

instance : BoundedInt Int32 where
  minVal := Int32.minVal
  maxVal := Int32.maxVal
  toInt := Int32.toInt
  isNeg := Int32.isNeg
  fromInt := Int32.fromInt
  toInt_minVal := by native_decide
  toInt_maxVal := by native_decide

instance : BoundedInt Int64 where
  minVal := Int64.minVal
  maxVal := Int64.maxVal
  toInt := Int64.toInt
  isNeg := Int64.isNeg
  fromInt := Int64.fromInt
  toInt_minVal := by native_decide
  toInt_maxVal := by native_decide

/-! ## BitwiseOps Typeclass -/

/-- Typeclass for types supporting bitwise operations.
    Extends `FixedWidth` with AND, OR, XOR, NOT, shifts, and rotates. -/
class BitwiseOps (α : Type) extends FixedWidth α where
  /-- Bitwise AND. -/
  band : α → α → α
  /-- Bitwise OR. -/
  bor  : α → α → α
  /-- Bitwise XOR. -/
  bxor : α → α → α
  /-- Bitwise NOT (complement). -/
  bnot : α → α
  /-- Test a specific bit position. -/
  testBit : α → Nat → Bool
  /-- Population count (number of 1-bits). -/
  popcount : α → α

instance : BitwiseOps UInt8 where
  band := UInt8.band
  bor := UInt8.bor
  bxor := UInt8.bxor
  bnot := UInt8.bnot
  testBit := UInt8.testBit
  popcount := UInt8.popcount

instance : BitwiseOps UInt16 where
  band := UInt16.band
  bor := UInt16.bor
  bxor := UInt16.bxor
  bnot := UInt16.bnot
  testBit := UInt16.testBit
  popcount := UInt16.popcount

instance : BitwiseOps UInt32 where
  band := UInt32.band
  bor := UInt32.bor
  bxor := UInt32.bxor
  bnot := UInt32.bnot
  testBit := UInt32.testBit
  popcount := UInt32.popcount

instance : BitwiseOps UInt64 where
  band := UInt64.band
  bor := UInt64.bor
  bxor := UInt64.bxor
  bnot := UInt64.bnot
  testBit := UInt64.testBit
  popcount := UInt64.popcount

instance : BitwiseOps Int8 where
  band := Int8.band
  bor := Int8.bor
  bxor := Int8.bxor
  bnot := Int8.bnot
  testBit := Int8.testBit
  popcount := Int8.popcount

instance : BitwiseOps Int16 where
  band := Int16.band
  bor := Int16.bor
  bxor := Int16.bxor
  bnot := Int16.bnot
  testBit := Int16.testBit
  popcount := Int16.popcount

instance : BitwiseOps Int32 where
  band := Int32.band
  bor := Int32.bor
  bxor := Int32.bxor
  bnot := Int32.bnot
  testBit := Int32.testBit
  popcount := Int32.popcount

instance : BitwiseOps Int64 where
  band := Int64.band
  bor := Int64.bor
  bxor := Int64.bxor
  bnot := Int64.bnot
  testBit := Int64.testBit
  popcount := Int64.popcount

/-! ## Generic Functions -/

/-- Generic zero (minVal for unsigned). -/
@[inline] def genericZero [BoundedUInt α] : α := BoundedUInt.minVal

/-- Generic maximum value. -/
@[inline] def genericMaxVal [BoundedUInt α] : α := BoundedUInt.maxVal

/-- Generic popcount via `BitwiseOps`. -/
@[inline] def genericPopcount [BitwiseOps α] (x : α) : α := BitwiseOps.popcount x

/-- Check if a value is zero using `toNat`. -/
@[inline] def isZero [BoundedUInt α] (x : α) : Bool := BoundedUInt.toNat x == 0

/-- Check if a value is the maximum using `toNat`. -/
@[inline] def isMax [BoundedUInt α] (x : α) : Bool :=
  BoundedUInt.toNat x == BoundedUInt.toNat (BoundedUInt.maxVal (α := α))

end Radix
