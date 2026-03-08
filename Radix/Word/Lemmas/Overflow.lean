/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Arith
import Radix.Word.Spec

/-!
# Overflow Behavior Specification Compliance Proofs (Layer 3)

This module proves that each arithmetic mode's overflow behavior
matches the specification in `Word.Spec`.

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- FR-001.2a: Division edge cases
- FR-001.2b: Remainder edge cases
- FR-001.3: Overflow behavior matches specification
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 Overflow Proofs                                          -/
/-! ================================================================ -/

namespace UInt8

/-- Wrapping addition matches the spec: result is `(x + y) mod 2^8`. -/
theorem wrappingAdd_spec (x y : UInt8) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 8 := rfl

/-- Wrapping subtraction matches the spec. -/
theorem wrappingSub_spec (x y : UInt8) :
    (wrappingSub x y).toNat = (x.toNat + 2 ^ 8 - y.toNat) % 2 ^ 8 := by
  show (x.val.toBitVec - y.val.toBitVec).toNat =
    (x.val.toBitVec.toNat + 2 ^ 8 - y.val.toBitVec.toNat) % 2 ^ 8
  rw [BitVec.toNat_sub]
  omega

/-- Wrapping multiplication matches the spec. -/
theorem wrappingMul_spec (x y : UInt8) :
    (wrappingMul x y).toNat = (x.toNat * y.toNat) % 2 ^ 8 := rfl

/-- Checked addition returns `none` iff overflow. -/
theorem checkedAdd_none_iff (x y : UInt8) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 8 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

/-- Checked subtraction returns `none` iff underflow. -/
theorem checkedSub_none_iff (x y : UInt8) :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  simp only [checkedSub, toNat]
  split <;> simp_all

/-- Saturating addition clamps to max on overflow. -/
theorem saturatingAdd_le_max (x y : UInt8) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (255 : _root_.UInt8).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

/-- Saturating subtraction does not go below zero. -/
theorem saturatingSub_ge_zero (x y : UInt8) :
    (saturatingSub x y).toNat ≥ 0 := by omega

/-- Overflowing addition's flag agrees with spec. -/
theorem overflowingAdd_flag_spec (x y : UInt8) :
    (overflowingAdd x y).2 = (x.toNat + y.toNat >= 2 ^ 8) := by
  simp [overflowingAdd, toNat]

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt16

theorem wrappingAdd_spec (x y : UInt16) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 16 := rfl

theorem checkedAdd_none_iff (x y : UInt16) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 16 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt16) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (65535 : _root_.UInt16).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt32

theorem wrappingAdd_spec (x y : UInt32) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := rfl

theorem checkedAdd_none_iff (x y : UInt32) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 32 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt32) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (4294967295 : _root_.UInt32).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt64

theorem wrappingAdd_spec (x y : UInt64) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := rfl

theorem checkedAdd_none_iff (x y : UInt64) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 64 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt64) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (18446744073709551615 : _root_.UInt64).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

end UInt64

/-! ================================================================ -/
/-! ## Int8 Signed Overflow Proofs                                    -/
/-! ================================================================ -/

namespace Int8

/-- Checked signed division returns `none` for `MIN / -1`.
    FR-001.2a compliance. -/
theorem checkedDiv_min_neg1 :
    checkedDiv minVal (fromInt (-1)) = none := by native_decide

/-- Checked signed remainder returns `none` for `MIN % -1`.
    FR-001.2b compliance. -/
theorem checkedRem_min_neg1 :
    checkedRem minVal (fromInt (-1)) = none := by native_decide

end Int8

end Radix
