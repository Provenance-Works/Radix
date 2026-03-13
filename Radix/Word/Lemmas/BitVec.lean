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

/-- Wrapping addition matches `BitVec` addition. -/
theorem wrappingAdd_toBitVec (x y : Int8) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

/-- Wrapping subtraction matches `BitVec` subtraction. -/
theorem wrappingSub_toBitVec (x y : Int8) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

/-- Wrapping multiplication matches `BitVec` multiplication. -/
theorem wrappingMul_toBitVec (x y : Int8) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

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

theorem wrappingAdd_toBitVec (x y : Int16) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : Int16) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : Int16) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

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

theorem wrappingAdd_toBitVec (x y : Int32) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : Int32) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : Int32) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

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

theorem wrappingAdd_toBitVec (x y : Int64) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : Int64) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : Int64) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

end Int64

/-! ================================================================ -/
/-! ## UWord BitVec Equivalence                                       -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

theorem fromBitVec_toBitVec (x : UWord w) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_fromBitVec (bv : BitVec w) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

theorem wrappingAdd_toBitVec (x y : UWord w) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : UWord w) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : UWord w) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

/-- Checked addition returns the BitVec sum when it succeeds. -/
theorem checkedAdd_toBitVec (x y : UWord w) {r : UWord w} (h : checkedAdd x y = some r) :
    r.toBitVec = x.toBitVec + y.toBitVec := by
  simp only [checkedAdd] at h
  split at h
  · simp_all
  · cases r; simp_all [toBitVec]

/-- Checked subtraction returns the BitVec difference when it succeeds. -/
theorem checkedSub_toBitVec (x y : UWord w) {r : UWord w} (h : checkedSub x y = some r) :
    r.toBitVec = x.toBitVec - y.toBitVec := by
  simp only [checkedSub] at h
  split at h
  · simp_all
  · cases r; simp_all [toBitVec]

/-- Overflowing addition's first element is the BitVec sum. -/
theorem overflowingAdd_fst_toBitVec (x y : UWord w) :
    (overflowingAdd x y).1.toBitVec = x.toBitVec + y.toBitVec := by
  simp [overflowingAdd, toBitVec]

/-- Overflowing subtraction's first element is the BitVec difference. -/
theorem overflowingSub_fst_toBitVec (x y : UWord w) :
    (overflowingSub x y).1.toBitVec = x.toBitVec - y.toBitVec := by
  simp [overflowingSub, toBitVec]

end UWord

/-! ================================================================ -/
/-! ## IWord BitVec Equivalence                                       -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

theorem fromBitVec_toBitVec (x : IWord w) : fromBitVec (toBitVec x) = x := by
  cases x; simp [fromBitVec, toBitVec]

theorem toBitVec_fromBitVec (bv : BitVec w) : toBitVec (fromBitVec bv) = bv := by
  simp [fromBitVec, toBitVec]

theorem wrappingAdd_toBitVec (x y : IWord w) :
    (wrappingAdd x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [wrappingAdd, toBitVec]

theorem wrappingSub_toBitVec (x y : IWord w) :
    (wrappingSub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [wrappingSub, toBitVec]

theorem wrappingMul_toBitVec (x y : IWord w) :
    (wrappingMul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [wrappingMul, toBitVec]

/-- Checked addition returns the BitVec sum when it succeeds. -/
theorem checkedAdd_toBitVec (x y : IWord w) {r : IWord w} (h : checkedAdd x y = some r) :
    r.toBitVec = x.toBitVec + y.toBitVec := by
  simp only [checkedAdd] at h
  split at h
  · simp_all
  · cases r; simp_all [toBitVec]

/-- Checked subtraction returns the BitVec difference when it succeeds. -/
theorem checkedSub_toBitVec (x y : IWord w) {r : IWord w} (h : checkedSub x y = some r) :
    r.toBitVec = x.toBitVec - y.toBitVec := by
  simp only [checkedSub] at h
  split at h
  · simp_all
  · cases r; simp_all [toBitVec]

/-- Overflowing addition's first element matches BitVec addition. -/
theorem overflowingAdd_fst_toBitVec (x y : IWord w) :
    (overflowingAdd x y).1.toBitVec = x.toBitVec + y.toBitVec := by
  simp [overflowingAdd, toBitVec]

/-- Overflowing subtraction's first element matches BitVec subtraction. -/
theorem overflowingSub_fst_toBitVec (x y : IWord w) :
    (overflowingSub x y).1.toBitVec = x.toBitVec - y.toBitVec := by
  simp [overflowingSub, toBitVec]

end IWord

end Radix
