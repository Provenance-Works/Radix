/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Arith
import Radix.Word.Spec
import Mathlib.Data.BitVec

/-!
# BitVec Equivalence Proofs (Layer 3)

This module proves that `toBitVec`/`fromBitVec` conversions and
the Layer 2 operations match the Layer 3 `BitVec`-based specifications.

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- ADR-002: Build on Mathlib BitVec
- FR-001.3: Each operation must be proven equivalent to spec
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 BitVec Equivalence                                   -/
/-! ================================================================ -/

namespace UInt8

/-- `fromBitVec (toBitVec x) = x` (round-trip). -/
theorem fromBitVec_toBitVec (x : UInt8) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

/-- `toBitVec (fromBitVec bv) = bv` (round-trip). -/
theorem toBitVec_fromBitVec (bv : BitVec 8) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

/-- Wrapping addition matches `BitVec` addition. -/
theorem wrappingAdd_toBitVec (x y : UInt8) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

/-- Wrapping subtraction matches `BitVec` subtraction. -/
theorem wrappingSub_toBitVec (x y : UInt8) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

/-- Wrapping multiplication matches `BitVec` multiplication. -/
theorem wrappingMul_toBitVec (x y : UInt8) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

end UInt8

/-! ================================================================ -/
/-! ## UInt16 BitVec Equivalence                                  -/
/-! ================================================================ -/

namespace UInt16

theorem fromBitVec_toBitVec (x : UInt16) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_fromBitVec (bv : BitVec 16) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

theorem wrappingAdd_toBitVec (x y : UInt16) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : UInt16) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : UInt16) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

end UInt16

/-! ================================================================ -/
/-! ## UInt32 BitVec Equivalence                                  -/
/-! ================================================================ -/

namespace UInt32

theorem fromBitVec_toBitVec (x : UInt32) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_fromBitVec (bv : BitVec 32) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

theorem wrappingAdd_toBitVec (x y : UInt32) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : UInt32) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : UInt32) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

end UInt32

/-! ================================================================ -/
/-! ## UInt64 BitVec Equivalence                                  -/
/-! ================================================================ -/

namespace UInt64

theorem fromBitVec_toBitVec (x : UInt64) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_fromBitVec (bv : BitVec 64) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

theorem wrappingAdd_toBitVec (x y : UInt64) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : UInt64) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : UInt64) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

end UInt64

/-! ================================================================ -/
/-! ## Int8 BitVec Equivalence                                    -/
/-! ================================================================ -/

namespace Int8

/-- Round-trip through `BitVec 8`. -/
theorem fromBitVec_toBitVec (x : Int8) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

/-- Signed-unsigned cast preserves bit pattern. -/
theorem toBitVec_eq_toUInt8_toBitVec (x : Int8) :
    x.toBitVec = x.toUInt8.toBitVec := by
  simp [toBitVec, toUInt8, UInt8.toBitVec]

end Int8

/-! ================================================================ -/
/-! ## Int16 BitVec Equivalence                                   -/
/-! ================================================================ -/

namespace Int16

theorem fromBitVec_toBitVec (x : Int16) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_eq_toUInt16_toBitVec (x : Int16) :
    x.toBitVec = x.toUInt16.toBitVec := by
  simp [toBitVec, toUInt16, UInt16.toBitVec]

end Int16

/-! ================================================================ -/
/-! ## Int32 BitVec Equivalence                                   -/
/-! ================================================================ -/

namespace Int32

theorem fromBitVec_toBitVec (x : Int32) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_eq_toUInt32_toBitVec (x : Int32) :
    x.toBitVec = x.toUInt32.toBitVec := by
  simp [toBitVec, toUInt32, UInt32.toBitVec]

end Int32

/-! ================================================================ -/
/-! ## Int64 BitVec Equivalence                                   -/
/-! ================================================================ -/

namespace Int64

theorem fromBitVec_toBitVec (x : Int64) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_eq_toUInt64_toBitVec (x : Int64) :
    x.toBitVec = x.toUInt64.toBitVec := by
  simp [toBitVec, toUInt64, UInt64.toBitVec]

end Int64

end Radix
