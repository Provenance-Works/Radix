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
/-! ## Zero Extension Correctness                                    -/
/-! ================================================================ -/

/-- Zero-extending UInt8 to UInt16 preserves the numeric value. -/
theorem UInt8.toUInt16_toNat (x : UInt8) :
    x.toUInt16.toNat = x.toNat := by
  simp [UInt8.toUInt16, UInt16.toNat, UInt8.toNat]

theorem zeroExtendPreserves8to16_proof (x : UInt8) : zeroExtendPreserves8to16 x := by
  unfold zeroExtendPreserves8to16
  exact UInt8.toUInt16_toNat x

/-- Zero-extending UInt8 to UInt32 preserves the numeric value. -/
theorem UInt8.toUInt32_toNat (x : UInt8) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt8.toUInt32, UInt32.toNat, UInt8.toNat]

theorem zeroExtendPreserves8to32_proof (x : UInt8) : zeroExtendPreserves8to32 x := by
  unfold zeroExtendPreserves8to32
  exact UInt8.toUInt32_toNat x

/-- Zero-extending UInt8 to UInt64 preserves the numeric value. -/
theorem UInt8.toUInt64_toNat (x : UInt8) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt8.toUInt64, UInt64.toNat, UInt8.toNat]

theorem zeroExtendPreserves8to64_proof (x : UInt8) : zeroExtendPreserves8to64 x := by
  unfold zeroExtendPreserves8to64
  exact UInt8.toUInt64_toNat x

/-- Zero-extending UInt16 to UInt32 preserves the numeric value. -/
theorem UInt16.toUInt32_toNat (x : UInt16) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt16.toUInt32, UInt32.toNat, UInt16.toNat]

theorem zeroExtendPreserves16to32_proof (x : UInt16) : zeroExtendPreserves16to32 x := by
  unfold zeroExtendPreserves16to32
  exact UInt16.toUInt32_toNat x

/-- Zero-extending UInt16 to UInt64 preserves the numeric value. -/
theorem UInt16.toUInt64_toNat (x : UInt16) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt16.toUInt64, UInt64.toNat, UInt16.toNat]

theorem zeroExtendPreserves16to64_proof (x : UInt16) : zeroExtendPreserves16to64 x := by
  unfold zeroExtendPreserves16to64
  exact UInt16.toUInt64_toNat x

/-- Zero-extending UInt32 to UInt64 preserves the numeric value. -/
theorem UInt32.toUInt64_toNat (x : UInt32) :
    x.toUInt64.toNat = x.toNat := by
  simp [UInt32.toUInt64, UInt64.toNat, UInt32.toNat]

theorem zeroExtendPreserves32to64_proof (x : UInt32) : zeroExtendPreserves32to64 x := by
  unfold zeroExtendPreserves32to64
  exact UInt32.toUInt64_toNat x

/-! ================================================================ -/
/-! ## Sign Extension Correctness                                    -/
/-! ================================================================ -/

/-- Sign-extending Int8 to Int16 preserves the numeric value. -/
theorem Int8.toInt16_toInt (x : Int8) :
    x.toInt16.toInt = x.toInt := by
  simp [Int8.toInt16, Int16.toInt, Int8.toInt, Int16.fromBitVec, Int8.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 8 <= 16)]

theorem signExtendPreserves8to16_proof (x : Int8) : signExtendPreserves8to16 x := by
  unfold signExtendPreserves8to16
  exact Int8.toInt16_toInt x

/-- Sign-extending Int8 to Int32 preserves the numeric value. -/
theorem Int8.toInt32_toInt (x : Int8) :
    x.toInt32.toInt = x.toInt := by
  simp [Int8.toInt32, Int32.toInt, Int8.toInt, Int32.fromBitVec, Int8.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 8 <= 32)]

theorem signExtendPreserves8to32_proof (x : Int8) : signExtendPreserves8to32 x := by
  unfold signExtendPreserves8to32
  exact Int8.toInt32_toInt x

/-- Sign-extending Int8 to Int64 preserves the numeric value. -/
theorem Int8.toInt64_toInt (x : Int8) :
    x.toInt64.toInt = x.toInt := by
  simp [Int8.toInt64, Int64.toInt, Int8.toInt, Int64.fromBitVec, Int8.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 8 <= 64)]

theorem signExtendPreserves8to64_proof (x : Int8) : signExtendPreserves8to64 x := by
  unfold signExtendPreserves8to64
  exact Int8.toInt64_toInt x

/-- Sign-extending Int16 to Int32 preserves the numeric value. -/
theorem Int16.toInt32_toInt (x : Int16) :
    x.toInt32.toInt = x.toInt := by
  simp [Int16.toInt32, Int32.toInt, Int16.toInt, Int32.fromBitVec, Int16.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 16 <= 32)]

theorem signExtendPreserves16to32_proof (x : Int16) : signExtendPreserves16to32 x := by
  unfold signExtendPreserves16to32
  exact Int16.toInt32_toInt x

/-- Sign-extending Int16 to Int64 preserves the numeric value. -/
theorem Int16.toInt64_toInt (x : Int16) :
    x.toInt64.toInt = x.toInt := by
  simp [Int16.toInt64, Int64.toInt, Int16.toInt, Int64.fromBitVec, Int16.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 16 <= 64)]

theorem signExtendPreserves16to64_proof (x : Int16) : signExtendPreserves16to64 x := by
  unfold signExtendPreserves16to64
  exact Int16.toInt64_toInt x

/-- Sign-extending Int32 to Int64 preserves the numeric value. -/
theorem Int32.toInt64_toInt (x : Int32) :
    x.toInt64.toInt = x.toInt := by
  simp [Int32.toInt64, Int64.toInt, Int32.toInt, Int64.fromBitVec, Int32.toBitVec, BitVec.toInt_signExtend_of_le (by decide : 32 <= 64)]

theorem signExtendPreserves32to64_proof (x : Int32) : signExtendPreserves32to64 x := by
  unfold signExtendPreserves32to64
  exact Int32.toInt64_toInt x

/-! ================================================================ -/
/-! ## Lossy Truncation Correctness                                  -/
/-! ================================================================ -/

/-- Truncating UInt16 to UInt8 preserves the numeric value if it fits. -/
theorem UInt16.truncate_8_preserves_if_fits (x : UInt16) (h : x.toNat < 2 ^ 8) :
    x.toUInt8.toNat = x.toNat := by
  simp [UInt16.toUInt8, UInt16.toNat, UInt8.toNat]
  exact h

theorem truncateLossy16to8_proof (x : UInt16) : truncateLossy16to8 x := by
  unfold truncateLossy16to8
  intro h
  exact UInt16.truncate_8_preserves_if_fits x h

/-- Truncating UInt32 to UInt16 preserves the numeric value if it fits. -/
theorem UInt32.truncate_16_preserves_if_fits (x : UInt32) (h : x.toNat < 2 ^ 16) :
    x.toUInt16.toNat = x.toNat := by
  simp [UInt32.toUInt16, UInt32.toNat, UInt16.toNat]
  exact h

theorem truncateLossy32to16_proof (x : UInt32) : truncateLossy32to16 x := by
  unfold truncateLossy32to16
  intro h
  exact UInt32.truncate_16_preserves_if_fits x h

/-- Truncating UInt64 to UInt32 preserves the numeric value if it fits. -/
theorem UInt64.truncate_32_preserves_if_fits (x : UInt64) (h : x.toNat < 2 ^ 32) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt64.toUInt32, UInt64.toNat, UInt32.toNat]
  exact h

theorem truncateLossy64to32_proof (x : UInt64) : truncateLossy64to32 x := by
  unfold truncateLossy64to32
  intro h
  exact UInt64.truncate_32_preserves_if_fits x h

/-! ================================================================ -/
/-! ## Signed/Unsigned Cast Bit Preservation                         -/
/-! ================================================================ -/

/-- Casting signed to unsigned preserves the bit pattern (8-bit). -/
theorem Int8.cast_bit_preserving (x : Int8) :
    x.toUInt8.toBitVec = x.toBitVec := by
  simp [Int8.toUInt8, Int8.toBitVec, UInt8.toBitVec]

theorem castBitPreserving8_proof (x : Int8) : castBitPreserving8 x := by
  unfold castBitPreserving8
  exact Int8.cast_bit_preserving x

/-- Casting signed to unsigned preserves the bit pattern (16-bit). -/
theorem Int16.cast_bit_preserving (x : Int16) :
    x.toUInt16.toBitVec = x.toBitVec := by
  simp [Int16.toUInt16, Int16.toBitVec, UInt16.toBitVec]

theorem castBitPreserving16_proof (x : Int16) : castBitPreserving16 x := by
  unfold castBitPreserving16
  exact Int16.cast_bit_preserving x

/-- Casting signed to unsigned preserves the bit pattern (32-bit). -/
theorem Int32.cast_bit_preserving (x : Int32) :
    x.toUInt32.toBitVec = x.toBitVec := by
  simp [Int32.toUInt32, Int32.toBitVec, UInt32.toBitVec]

theorem castBitPreserving32_proof (x : Int32) : castBitPreserving32 x := by
  unfold castBitPreserving32
  exact Int32.cast_bit_preserving x

/-- Casting signed to unsigned preserves the bit pattern (64-bit). -/
theorem Int64.cast_bit_preserving (x : Int64) :
    x.toUInt64.toBitVec = x.toBitVec := by
  simp [Int64.toUInt64, Int64.toBitVec, UInt64.toBitVec]

theorem castBitPreserving64_proof (x : Int64) : castBitPreserving64 x := by
  unfold castBitPreserving64
  exact Int64.cast_bit_preserving x

/-- Casting unsigned to signed and back is identity (8-bit). -/
theorem Int8.fromUInt8_toUInt8 (x : UInt8) :
    (Int8.fromUInt8 x).toUInt8 = x := by
  simp [Int8.fromUInt8, Int8.toUInt8]

/-- Casting signed to unsigned and back is identity (8-bit). -/
theorem UInt8.fromInt8_toInt8 (x : Int8) :
    Int8.fromUInt8 (x.toUInt8) = x := by
  simp [Int8.fromUInt8, Int8.toUInt8]

/-- Casting unsigned to signed and back is identity (16-bit). -/
theorem Int16.fromUInt16_toUInt16 (x : UInt16) :
    (Int16.fromUInt16 x).toUInt16 = x := by
  simp [Int16.fromUInt16, Int16.toUInt16]

/-- Casting signed to unsigned and back is identity (16-bit). -/
theorem UInt16.fromInt16_toInt16 (x : Int16) :
    Int16.fromUInt16 (x.toUInt16) = x := by
  simp [Int16.fromUInt16, Int16.toUInt16]

/-- Casting unsigned to signed and back is identity (32-bit). -/
theorem Int32.fromUInt32_toUInt32 (x : UInt32) :
    (Int32.fromUInt32 x).toUInt32 = x := by
  simp [Int32.fromUInt32, Int32.toUInt32]

/-- Casting signed to unsigned and back is identity (32-bit). -/
theorem UInt32.fromInt32_toInt32 (x : Int32) :
    Int32.fromUInt32 (x.toUInt32) = x := by
  simp [Int32.fromUInt32, Int32.toUInt32]

/-- Casting unsigned to signed and back is identity (64-bit). -/
theorem Int64.fromUInt64_toUInt64 (x : UInt64) :
    (Int64.fromUInt64 x).toUInt64 = x := by
  simp [Int64.fromUInt64, Int64.toUInt64]

/-- Casting signed to unsigned and back is identity (64-bit). -/
theorem UInt64.fromInt64_toInt64 (x : Int64) :
    Int64.fromUInt64 (x.toUInt64) = x := by
  simp [Int64.fromUInt64, Int64.toUInt64]

/-! ================================================================ -/
/-! ## Register-Width Sign Extension Correctness                     -/
/-! ================================================================ -/

-- Strategy (same pattern as Bytes/Lemmas.lean bswap proofs):
-- 1. Define pure BitVec functions
-- 2. Bridge: `Radix.UInt.signExtendN = fromBitVec (bv_fn ...)` by `rfl`
-- 3. Round-trip: `(fromBitVec bv).val.toBitVec = bv` by `rfl`
-- 4. BitVec spec: `bv_fn x = BitVec.signExtend ...` by `bv_decide`
-- 5. Final: combine with `simp`

/-! ### Pure BitVec Functions -/

private def signExtend8_bv32 (x : BitVec 32) : BitVec 32 :=
  let low := x &&& 0xFF#32
  if low &&& 0x80#32 != 0#32 then low ||| 0xFFFFFF00#32 else low

private def signExtend16_bv32 (x : BitVec 32) : BitVec 32 :=
  let low := x &&& 0xFFFF#32
  if low &&& 0x8000#32 != 0#32 then low ||| 0xFFFF0000#32 else low

private def signExtend8_bv64 (x : BitVec 64) : BitVec 64 :=
  let low := x &&& 0xFF#64
  if low &&& 0x80#64 != 0#64 then low ||| 0xFFFFFFFFFFFFFF00#64 else low

private def signExtend16_bv64 (x : BitVec 64) : BitVec 64 :=
  let low := x &&& 0xFFFF#64
  if low &&& 0x8000#64 != 0#64 then low ||| 0xFFFFFFFFFFFF0000#64 else low

private def signExtend32_bv64 (x : BitVec 64) : BitVec 64 :=
  let low := x &&& 0xFFFFFFFF#64
  if low &&& 0x80000000#64 != 0#64 then low ||| 0xFFFFFFFF00000000#64 else low

/-! ### Bridge Lemmas (definitional) -/

private theorem signExtend8_32_eq (x : UInt32) :
    x.signExtend8 = UInt32.fromBitVec (signExtend8_bv32 x.toBitVec) := by
  unfold UInt32.signExtend8 signExtend8_bv32 UInt32.toBitVec UInt32.fromBitVec
  rfl

private theorem signExtend16_32_eq (x : UInt32) :
    x.signExtend16 = UInt32.fromBitVec (signExtend16_bv32 x.toBitVec) := by
  unfold UInt32.signExtend16 signExtend16_bv32 UInt32.toBitVec UInt32.fromBitVec
  rfl

private theorem signExtend8_64_eq (x : UInt64) :
    x.signExtend8 = UInt64.fromBitVec (signExtend8_bv64 x.toBitVec) := by
  unfold UInt64.signExtend8 signExtend8_bv64 UInt64.toBitVec UInt64.fromBitVec
  rfl

private theorem signExtend16_64_eq (x : UInt64) :
    x.signExtend16 = UInt64.fromBitVec (signExtend16_bv64 x.toBitVec) := by
  unfold UInt64.signExtend16 signExtend16_bv64 UInt64.toBitVec UInt64.fromBitVec
  rfl

private theorem signExtend32_64_eq (x : UInt64) :
    x.signExtend32 = UInt64.fromBitVec (signExtend32_bv64 x.toBitVec) := by
  unfold UInt64.signExtend32 signExtend32_bv64 UInt64.toBitVec UInt64.fromBitVec
  rfl

/-! ### Round-trip Lemmas -/

private theorem fromBitVec32_roundtrip (bv : BitVec 32) :
    (UInt32.fromBitVec bv).val.toBitVec = bv := rfl

private theorem fromBitVec64_roundtrip (bv : BitVec 64) :
    (UInt64.fromBitVec bv).val.toBitVec = bv := rfl

/-! ### BitVec-Level Specification (proven by SAT solver) -/

private theorem signExtend8_bv32_spec (x : BitVec 32) :
    signExtend8_bv32 x = BitVec.signExtend 32 (x.truncate 8) := by
  unfold signExtend8_bv32; bv_decide

private theorem signExtend16_bv32_spec (x : BitVec 32) :
    signExtend16_bv32 x = BitVec.signExtend 32 (x.truncate 16) := by
  unfold signExtend16_bv32; bv_decide

private theorem signExtend8_bv64_spec (x : BitVec 64) :
    signExtend8_bv64 x = BitVec.signExtend 64 (x.truncate 8) := by
  unfold signExtend8_bv64; bv_decide

private theorem signExtend16_bv64_spec (x : BitVec 64) :
    signExtend16_bv64 x = BitVec.signExtend 64 (x.truncate 16) := by
  unfold signExtend16_bv64; bv_decide

private theorem signExtend32_bv64_spec (x : BitVec 64) :
    signExtend32_bv64 x = BitVec.signExtend 64 (x.truncate 32) := by
  unfold signExtend32_bv64; bv_decide

/-! ### Final Theorems -/

/-- `UInt32.signExtend8` matches `BitVec.signExtend` on the truncated input. -/
theorem UInt32.signExtend8_spec (x : UInt32) :
    signExtend8To32Spec x := by
  unfold signExtend8To32Spec
  simp only [signExtend8_32_eq, Radix.UInt32.toBitVec,
             fromBitVec32_roundtrip, signExtend8_bv32_spec]

/-- `UInt32.signExtend16` matches `BitVec.signExtend` on the truncated input. -/
theorem UInt32.signExtend16_spec (x : UInt32) :
    signExtend16To32Spec x := by
  unfold signExtend16To32Spec
  simp only [signExtend16_32_eq, Radix.UInt32.toBitVec,
             fromBitVec32_roundtrip, signExtend16_bv32_spec]

/-- `UInt64.signExtend8` matches `BitVec.signExtend` on the truncated input. -/
theorem UInt64.signExtend8_spec (x : UInt64) :
    signExtend8To64Spec x := by
  unfold signExtend8To64Spec
  simp only [signExtend8_64_eq, Radix.UInt64.toBitVec,
             fromBitVec64_roundtrip, signExtend8_bv64_spec]

/-- `UInt64.signExtend16` matches `BitVec.signExtend` on the truncated input. -/
theorem UInt64.signExtend16_spec (x : UInt64) :
    signExtend16To64Spec x := by
  unfold signExtend16To64Spec
  simp only [signExtend16_64_eq, Radix.UInt64.toBitVec,
             fromBitVec64_roundtrip, signExtend16_bv64_spec]

/-- `UInt64.signExtend32` matches `BitVec.signExtend` on the truncated input. -/
theorem UInt64.signExtend32_spec (x : UInt64) :
    signExtend32To64Spec x := by
  unfold signExtend32To64Spec
  simp only [signExtend32_64_eq, Radix.UInt64.toBitVec,
             fromBitVec64_roundtrip, signExtend32_bv64_spec]

end Radix
