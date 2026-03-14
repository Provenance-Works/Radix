/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int

/-!
# Width and Sign Conversions (Layer 2)

This module provides:
- Zero extension (8->16, 16->32, 32->64, etc.)
- Sign extension (signed types)
- Truncation (64->32, 32->16, 16->8, etc.)
- Sign/unsigned conversions (bit-pattern preserving)
- Propositions about information preservation/loss

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-001.1: Fixed-width integer types
- ADR-003: Signed via unsigned wrapper (free cast)
-/

namespace Radix

/-! ================================================================ -/
/-! ## Zero Extension (Unsigned Widening)                              -/
/-! ================================================================ -/

/-- Zero-extend `UInt8` to `UInt16`. -/
@[inline] def UInt8.toUInt16 (x : UInt8) : UInt16 := ⟨x.val.toUInt16⟩

/-- Zero-extend `UInt8` to `UInt32`. -/
@[inline] def UInt8.toUInt32 (x : UInt8) : UInt32 := ⟨x.val.toUInt32⟩

/-- Zero-extend `UInt8` to `UInt64`. -/
@[inline] def UInt8.toUInt64 (x : UInt8) : UInt64 := ⟨x.val.toUInt64⟩

/-- Zero-extend `UInt16` to `UInt32`. -/
@[inline] def UInt16.toUInt32 (x : UInt16) : UInt32 := ⟨x.val.toUInt32⟩

/-- Zero-extend `UInt16` to `UInt64`. -/
@[inline] def UInt16.toUInt64 (x : UInt16) : UInt64 := ⟨x.val.toUInt64⟩

/-- Zero-extend `UInt32` to `UInt64`. -/
@[inline] def UInt32.toUInt64 (x : UInt32) : UInt64 := ⟨x.val.toUInt64⟩

/-! ================================================================ -/
/-! ## Sign Extension (Signed Widening)                               -/
/-! ================================================================ -/

-- Branchless sign extension using the XOR-subtract trick:
-- (val ^ sign_bit) - sign_bit extends the sign bit to all upper positions.
-- This avoids the expensive BitVec.signExtend → Nat pathway.

@[inline] private def signExtend8to16_fast (x : Radix.Int8) : Radix.Int16 :=
  let val := x.val.toUInt16
  ⟨(val ^^^ 0x80) - 0x80⟩

@[inline] private def signExtend8to32_fast (x : Radix.Int8) : Radix.Int32 :=
  let val := x.val.toUInt32
  ⟨(val ^^^ 0x80) - 0x80⟩

@[inline] private def signExtend8to64_fast (x : Radix.Int8) : Radix.Int64 :=
  let val := x.val.toUInt64
  ⟨(val ^^^ 0x80) - 0x80⟩

@[inline] private def signExtend16to32_fast (x : Radix.Int16) : Radix.Int32 :=
  let val := x.val.toUInt32
  ⟨(val ^^^ 0x8000) - 0x8000⟩

@[inline] private def signExtend16to64_fast (x : Radix.Int16) : Radix.Int64 :=
  let val := x.val.toUInt64
  ⟨(val ^^^ 0x8000) - 0x8000⟩

@[inline] private def signExtend32to64_fast (x : Radix.Int32) : Radix.Int64 :=
  let val := x.val.toUInt64
  ⟨(val ^^^ 0x80000000) - 0x80000000⟩

/-- Sign-extend `Int8` to `Int16`. -/
@[implemented_by signExtend8to16_fast, inline]
def Int8.toInt16 (x : Int8) : Int16 :=
  Int16.fromBitVec (BitVec.signExtend 16 x.toBitVec)

/-- Sign-extend `Int8` to `Int32`. -/
@[implemented_by signExtend8to32_fast, inline]
def Int8.toInt32 (x : Int8) : Int32 :=
  Int32.fromBitVec (BitVec.signExtend 32 x.toBitVec)

/-- Sign-extend `Int8` to `Int64`. -/
@[implemented_by signExtend8to64_fast, inline]
def Int8.toInt64 (x : Int8) : Int64 :=
  Int64.fromBitVec (BitVec.signExtend 64 x.toBitVec)

/-- Sign-extend `Int16` to `Int32`. -/
@[implemented_by signExtend16to32_fast, inline]
def Int16.toInt32 (x : Int16) : Int32 :=
  Int32.fromBitVec (BitVec.signExtend 32 x.toBitVec)

/-- Sign-extend `Int16` to `Int64`. -/
@[implemented_by signExtend16to64_fast, inline]
def Int16.toInt64 (x : Int16) : Int64 :=
  Int64.fromBitVec (BitVec.signExtend 64 x.toBitVec)

/-- Sign-extend `Int32` to `Int64`. -/
@[implemented_by signExtend32to64_fast, inline]
def Int32.toInt64 (x : Int32) : Int64 :=
  Int64.fromBitVec (BitVec.signExtend 64 x.toBitVec)

/-! ================================================================ -/
/-! ## Truncation (Narrowing)                                         -/
/-! ================================================================ -/

/-- Truncate `UInt16` to `UInt8`. -/
@[inline] def UInt16.toUInt8 (x : UInt16) : UInt8 := ⟨x.val.toUInt8⟩

/-- Truncate `UInt32` to `UInt8`. -/
@[inline] def UInt32.toUInt8 (x : UInt32) : UInt8 := ⟨x.val.toUInt8⟩

/-- Truncate `UInt32` to `UInt16`. -/
@[inline] def UInt32.toUInt16 (x : UInt32) : UInt16 := ⟨x.val.toUInt16⟩

/-- Truncate `UInt64` to `UInt8`. -/
@[inline] def UInt64.toUInt8 (x : UInt64) : UInt8 := ⟨x.val.toUInt8⟩

/-- Truncate `UInt64` to `UInt16`. -/
@[inline] def UInt64.toUInt16 (x : UInt64) : UInt16 := ⟨x.val.toUInt16⟩

/-- Truncate `UInt64` to `UInt32`. -/
@[inline] def UInt64.toUInt32 (x : UInt64) : UInt32 := ⟨x.val.toUInt32⟩

-- Truncation fast paths: just narrow the underlying unsigned value.
-- Narrowing keeps the lower bits, which is exactly what truncation does.

@[inline] private def truncateI16toI8_fast (x : Radix.Int16) : Radix.Int8 := ⟨x.val.toUInt8⟩
@[inline] private def truncateI32toI8_fast (x : Radix.Int32) : Radix.Int8 := ⟨x.val.toUInt8⟩
@[inline] private def truncateI32toI16_fast (x : Radix.Int32) : Radix.Int16 := ⟨x.val.toUInt16⟩
@[inline] private def truncateI64toI8_fast (x : Radix.Int64) : Radix.Int8 := ⟨x.val.toUInt8⟩
@[inline] private def truncateI64toI16_fast (x : Radix.Int64) : Radix.Int16 := ⟨x.val.toUInt16⟩
@[inline] private def truncateI64toI32_fast (x : Radix.Int64) : Radix.Int32 := ⟨x.val.toUInt32⟩

/-- Truncate `Int16` to `Int8`. -/
@[implemented_by truncateI16toI8_fast, inline]
def Int16.toInt8 (x : Int16) : Int8 :=
  Int8.fromBitVec (x.toBitVec.truncate 8)

/-- Truncate `Int32` to `Int8`. -/
@[implemented_by truncateI32toI8_fast, inline]
def Int32.toInt8 (x : Int32) : Int8 :=
  Int8.fromBitVec (x.toBitVec.truncate 8)

/-- Truncate `Int32` to `Int16`. -/
@[implemented_by truncateI32toI16_fast, inline]
def Int32.toInt16 (x : Int32) : Int16 :=
  Int16.fromBitVec (x.toBitVec.truncate 16)

/-- Truncate `Int64` to `Int8`. -/
@[implemented_by truncateI64toI8_fast, inline]
def Int64.toInt8 (x : Int64) : Int8 :=
  Int8.fromBitVec (x.toBitVec.truncate 8)

/-- Truncate `Int64` to `Int16`. -/
@[implemented_by truncateI64toI16_fast, inline]
def Int64.toInt16 (x : Int64) : Int16 :=
  Int16.fromBitVec (x.toBitVec.truncate 16)

/-- Truncate `Int64` to `Int32`. -/
@[implemented_by truncateI64toI32_fast, inline]
def Int64.toInt32 (x : Int64) : Int32 :=
  Int32.fromBitVec (x.toBitVec.truncate 32)

/-! ================================================================ -/
/-! ## Signed <-> Unsigned Conversion (Bit-Pattern Preserving)        -/
/-! ================================================================ -/

-- These are free casts: the underlying UIntN value is the same.
-- ADR-003: `Int8.val : UInt8` and `UInt8.val : UInt8` share the same bits.

-- Already defined in Int.lean:
--   Int8.toUInt8, Int8.fromUInt8
--   Int16.toUInt16, Int16.fromUInt16
--   Int32.toUInt32, Int32.fromUInt32
--   Int64.toUInt64, Int64.fromUInt64

/-! ================================================================ -/
/-! ## Information Preservation Propositions                           -/
/-! ================================================================ -/

/-- Zero extension preserves the numeric value. -/
def zeroExtendPreserves8to16 (x : UInt8) : Prop :=
  x.toUInt16.toNat = x.toNat

def zeroExtendPreserves8to32 (x : UInt8) : Prop :=
  x.toUInt32.toNat = x.toNat

def zeroExtendPreserves8to64 (x : UInt8) : Prop :=
  x.toUInt64.toNat = x.toNat

def zeroExtendPreserves16to32 (x : UInt16) : Prop :=
  x.toUInt32.toNat = x.toNat

def zeroExtendPreserves16to64 (x : UInt16) : Prop :=
  x.toUInt64.toNat = x.toNat

def zeroExtendPreserves32to64 (x : UInt32) : Prop :=
  x.toUInt64.toNat = x.toNat

/-- Sign extension preserves the signed value. -/
def signExtendPreserves8to16 (x : Int8) : Prop :=
  x.toInt16.toInt = x.toInt

def signExtendPreserves8to32 (x : Int8) : Prop :=
  x.toInt32.toInt = x.toInt

def signExtendPreserves8to64 (x : Int8) : Prop :=
  x.toInt64.toInt = x.toInt

def signExtendPreserves16to32 (x : Int16) : Prop :=
  x.toInt32.toInt = x.toInt

def signExtendPreserves16to64 (x : Int16) : Prop :=
  x.toInt64.toInt = x.toInt

def signExtendPreserves32to64 (x : Int32) : Prop :=
  x.toInt64.toInt = x.toInt

/-- Truncation may lose information: the value is only preserved if it fits. -/
def truncateLossy16to8 (x : UInt16) : Prop :=
  x.toNat < 2 ^ 8 → x.toUInt8.toNat = x.toNat

def truncateLossy32to16 (x : UInt32) : Prop :=
  x.toNat < 2 ^ 16 → x.toUInt16.toNat = x.toNat

def truncateLossy64to32 (x : UInt64) : Prop :=
  x.toNat < 2 ^ 32 → x.toUInt32.toNat = x.toNat

/-- Signed-unsigned cast preserves the bit pattern. -/
def castBitPreserving8 (x : Int8) : Prop :=
  x.toUInt8.toBitVec = x.toBitVec

def castBitPreserving16 (x : Int16) : Prop :=
  x.toUInt16.toBitVec = x.toBitVec

def castBitPreserving32 (x : Int32) : Prop :=
  x.toUInt32.toBitVec = x.toBitVec

def castBitPreserving64 (x : Int64) : Prop :=
  x.toUInt64.toBitVec = x.toBitVec

/-! ================================================================ -/
/-! ## Register-Width Sign Extension                                  -/
/-! ================================================================ -/

-- In-register sign extension: interpret the low N bits of a wide register
-- as a signed value and sign-extend to the full register width.
-- Useful for packed-type loads and bit field signed interpretation.

/-- Sign-extend the low 8 bits of a UInt32 to 32 bits. -/
@[inline] def UInt32.signExtend8 (x : UInt32) : UInt32 :=
  let bv := x.toBitVec
  let low := bv &&& 0xFF#32
  UInt32.fromBitVec (if low &&& 0x80#32 != 0#32 then low ||| 0xFFFFFF00#32 else low)

/-- Sign-extend the low 16 bits of a UInt32 to 32 bits. -/
@[inline] def UInt32.signExtend16 (x : UInt32) : UInt32 :=
  let bv := x.toBitVec
  let low := bv &&& 0xFFFF#32
  UInt32.fromBitVec (if low &&& 0x8000#32 != 0#32 then low ||| 0xFFFF0000#32 else low)

/-- Sign-extend the low 8 bits of a UInt64 to 64 bits. -/
@[inline] def UInt64.signExtend8 (x : UInt64) : UInt64 :=
  let bv := x.toBitVec
  let low := bv &&& 0xFF#64
  UInt64.fromBitVec (if low &&& 0x80#64 != 0#64 then low ||| 0xFFFFFFFFFFFFFF00#64 else low)

/-- Sign-extend the low 16 bits of a UInt64 to 64 bits. -/
@[inline] def UInt64.signExtend16 (x : UInt64) : UInt64 :=
  let bv := x.toBitVec
  let low := bv &&& 0xFFFF#64
  UInt64.fromBitVec (if low &&& 0x8000#64 != 0#64 then low ||| 0xFFFFFFFFFFFF0000#64 else low)

/-- Sign-extend the low 32 bits of a UInt64 to 64 bits. -/
@[inline] def UInt64.signExtend32 (x : UInt64) : UInt64 :=
  let bv := x.toBitVec
  let low := bv &&& 0xFFFFFFFF#64
  UInt64.fromBitVec (if low &&& 0x80000000#64 != 0#64 then low ||| 0xFFFFFFFF00000000#64 else low)

/-- Register-width sign extension matches `BitVec.signExtend` on the truncated input. -/
def signExtend8To32Spec (x : UInt32) : Prop :=
  x.signExtend8.toBitVec = BitVec.signExtend 32 (x.toBitVec.truncate 8)

def signExtend16To32Spec (x : UInt32) : Prop :=
  x.signExtend16.toBitVec = BitVec.signExtend 32 (x.toBitVec.truncate 16)

def signExtend8To64Spec (x : UInt64) : Prop :=
  x.signExtend8.toBitVec = BitVec.signExtend 64 (x.toBitVec.truncate 8)

def signExtend16To64Spec (x : UInt64) : Prop :=
  x.signExtend16.toBitVec = BitVec.signExtend 64 (x.toBitVec.truncate 16)

def signExtend32To64Spec (x : UInt64) : Prop :=
  x.signExtend32.toBitVec = BitVec.signExtend 64 (x.toBitVec.truncate 32)

end Radix
