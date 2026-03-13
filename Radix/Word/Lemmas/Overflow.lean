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

## Design Note: `native_decide` usage

Signed-integer edge-case proofs (e.g. `MIN / -1`, wrapping at boundaries) use
`native_decide` because they assert equalities on specific concrete values.
These are ground-truth checks where `bv_decide` or `omega` would be overkill
or unable to reduce the custom struct definitions.  `native_decide` is safe
here because the statements are closed propositions on fixed literals.

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

/-- Checked multiplication returns `none` iff overflow. -/
theorem checkedMul_none_iff (x y : UInt8) :
    checkedMul x y = none ↔ x.toNat * y.toNat ≥ 2 ^ 8 := by
  simp only [checkedMul, toNat]
  split <;> simp_all

/-- Checked division returns `none` iff divisor is zero. -/
theorem checkedDiv_none_iff (x y : UInt8) :
    checkedDiv x y = none ↔ y = ⟨0⟩ := by
  simp only [checkedDiv]
  constructor
  · intro h; split at h <;> simp_all [BEq.beq]; cases y; simp_all
  · intro h; subst h; simp [BEq.beq]

/-- Overflowing subtraction's flag agrees with spec. -/
theorem overflowingSub_flag_spec (x y : UInt8) :
    (overflowingSub x y).2 = (x.toNat < y.toNat) := by
  simp [overflowingSub, toNat]

/-- Overflowing multiplication's flag agrees with spec. -/
theorem overflowingMul_flag_spec (x y : UInt8) :
    (overflowingMul x y).2 = (x.toNat * y.toNat >= 2 ^ 8) := by
  simp [overflowingMul, toNat]

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt16

theorem wrappingAdd_spec (x y : UInt16) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 16 := rfl

theorem wrappingSub_spec (x y : UInt16) :
    (wrappingSub x y).toNat = (x.toNat + 2 ^ 16 - y.toNat) % 2 ^ 16 := by
  show (x.val - y.val).toBitVec.toNat =
    (x.val.toBitVec.toNat + 2 ^ 16 - y.val.toBitVec.toNat) % 2 ^ 16
  rw [_root_.UInt16.toBitVec_sub]
  rw [BitVec.toNat_sub]
  omega

theorem wrappingMul_spec (x y : UInt16) :
    (wrappingMul x y).toNat = (x.toNat * y.toNat) % 2 ^ 16 := rfl

theorem checkedAdd_none_iff (x y : UInt16) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 16 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem checkedSub_none_iff (x y : UInt16) :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  simp only [checkedSub, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt16) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (65535 : _root_.UInt16).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

theorem saturatingSub_ge_zero (x y : UInt16) :
    (saturatingSub x y).toNat ≥ 0 := by omega

theorem overflowingAdd_flag_spec (x y : UInt16) :
    (overflowingAdd x y).2 = (x.toNat + y.toNat >= 2 ^ 16) := by
  simp [overflowingAdd, toNat]

theorem checkedMul_none_iff (x y : UInt16) :
    checkedMul x y = none ↔ x.toNat * y.toNat ≥ 2 ^ 16 := by
  simp only [checkedMul, toNat]
  split <;> simp_all

theorem checkedDiv_none_iff (x y : UInt16) :
    checkedDiv x y = none ↔ y = ⟨0⟩ := by
  simp only [checkedDiv]
  constructor
  · intro h; split at h <;> simp_all [BEq.beq]; cases y; simp_all
  · intro h; subst h; simp [BEq.beq]

theorem overflowingSub_flag_spec (x y : UInt16) :
    (overflowingSub x y).2 = (x.toNat < y.toNat) := by
  simp [overflowingSub, toNat]

theorem overflowingMul_flag_spec (x y : UInt16) :
    (overflowingMul x y).2 = (x.toNat * y.toNat >= 2 ^ 16) := by
  simp [overflowingMul, toNat]

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt32

theorem wrappingAdd_spec (x y : UInt32) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := rfl

theorem wrappingSub_spec (x y : UInt32) :
    (wrappingSub x y).toNat = (x.toNat + 2 ^ 32 - y.toNat) % 2 ^ 32 := by
  show (x.val - y.val).toBitVec.toNat =
    (x.val.toBitVec.toNat + 2 ^ 32 - y.val.toBitVec.toNat) % 2 ^ 32
  rw [_root_.UInt32.toBitVec_sub]
  rw [BitVec.toNat_sub]
  omega

theorem wrappingMul_spec (x y : UInt32) :
    (wrappingMul x y).toNat = (x.toNat * y.toNat) % 2 ^ 32 := rfl

theorem checkedAdd_none_iff (x y : UInt32) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 32 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem checkedSub_none_iff (x y : UInt32) :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  simp only [checkedSub, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt32) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (4294967295 : _root_.UInt32).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

theorem saturatingSub_ge_zero (x y : UInt32) :
    (saturatingSub x y).toNat ≥ 0 := by omega

theorem overflowingAdd_flag_spec (x y : UInt32) :
    (overflowingAdd x y).2 = (x.toNat + y.toNat >= 2 ^ 32) := by
  simp [overflowingAdd, toNat]

theorem checkedMul_none_iff (x y : UInt32) :
    checkedMul x y = none ↔ x.toNat * y.toNat ≥ 2 ^ 32 := by
  simp only [checkedMul, toNat]
  split <;> simp_all

theorem checkedDiv_none_iff (x y : UInt32) :
    checkedDiv x y = none ↔ y = ⟨0⟩ := by
  simp only [checkedDiv]
  constructor
  · intro h; split at h <;> simp_all [BEq.beq]; cases y; simp_all
  · intro h; subst h; simp [BEq.beq]

theorem overflowingSub_flag_spec (x y : UInt32) :
    (overflowingSub x y).2 = (x.toNat < y.toNat) := by
  simp [overflowingSub, toNat]

theorem overflowingMul_flag_spec (x y : UInt32) :
    (overflowingMul x y).2 = (x.toNat * y.toNat >= 2 ^ 32) := by
  simp [overflowingMul, toNat]

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Overflow Proofs                                      -/
/-! ================================================================ -/

namespace UInt64

theorem wrappingAdd_spec (x y : UInt64) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := rfl

theorem wrappingSub_spec (x y : UInt64) :
    (wrappingSub x y).toNat = (x.toNat + 2 ^ 64 - y.toNat) % 2 ^ 64 := by
  show (x.val - y.val).toBitVec.toNat =
    (x.val.toBitVec.toNat + 2 ^ 64 - y.val.toBitVec.toNat) % 2 ^ 64
  rw [_root_.UInt64.toBitVec_sub]
  rw [BitVec.toNat_sub]
  omega

theorem wrappingMul_spec (x y : UInt64) :
    (wrappingMul x y).toNat = (x.toNat * y.toNat) % 2 ^ 64 := rfl

theorem checkedAdd_none_iff (x y : UInt64) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ 64 := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

theorem checkedSub_none_iff (x y : UInt64) :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  simp only [checkedSub, toNat]
  split <;> simp_all

theorem saturatingAdd_le_max (x y : UInt64) :
    (saturatingAdd x y).toNat ≤ maxVal.toNat := by
  unfold saturatingAdd
  split
  · exact Nat.le_refl _
  · change (x.val + y.val).toBitVec.toNat ≤ (18446744073709551615 : _root_.UInt64).toBitVec.toNat
    exact Nat.lt_succ_iff.mp (BitVec.isLt _)

theorem saturatingSub_ge_zero (x y : UInt64) :
    (saturatingSub x y).toNat ≥ 0 := by omega

theorem overflowingAdd_flag_spec (x y : UInt64) :
    (overflowingAdd x y).2 = (x.toNat + y.toNat >= 2 ^ 64) := by
  simp [overflowingAdd, toNat]

theorem checkedMul_none_iff (x y : UInt64) :
    checkedMul x y = none ↔ x.toNat * y.toNat ≥ 2 ^ 64 := by
  simp only [checkedMul, toNat]
  split <;> simp_all

theorem checkedDiv_none_iff (x y : UInt64) :
    checkedDiv x y = none ↔ y = ⟨0⟩ := by
  simp only [checkedDiv]
  constructor
  · intro h; split at h <;> simp_all [BEq.beq]; cases y; simp_all
  · intro h; subst h; simp [BEq.beq]

theorem overflowingSub_flag_spec (x y : UInt64) :
    (overflowingSub x y).2 = (x.toNat < y.toNat) := by
  simp [overflowingSub, toNat]

theorem overflowingMul_flag_spec (x y : UInt64) :
    (overflowingMul x y).2 = (x.toNat * y.toNat >= 2 ^ 64) := by
  simp [overflowingMul, toNat]

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

/-- Wrapping addition wraps correctly (modular). -/
theorem wrappingAdd_wraps : wrappingAdd maxVal ⟨1⟩ = minVal := by native_decide

/-- Overflowing division `MIN / -1` flags true. -/
theorem overflowingDiv_min_neg1 :
    (overflowingDiv minVal (fromInt (-1)) (by decide)).2 = true := by native_decide

/-- Wrapping subtraction wraps correctly: 0 - 1 wraps to -1. -/
theorem wrappingSub_zero_one : wrappingSub ⟨0⟩ ⟨1⟩ = fromInt (-1) := by native_decide

/-- Overflowing subtraction for MIN - 1 flags true. -/
theorem overflowingSub_min_one :
    (overflowingSub minVal ⟨1⟩).2 = true := by native_decide

end Int8

/-! ================================================================ -/
/-! ## Int16 Signed Overflow Proofs                                   -/
/-! ================================================================ -/

namespace Int16

theorem checkedDiv_min_neg1 :
    checkedDiv minVal (fromInt (-1)) = none := by native_decide

theorem checkedRem_min_neg1 :
    checkedRem minVal (fromInt (-1)) = none := by native_decide

theorem wrappingAdd_wraps : wrappingAdd maxVal ⟨1⟩ = minVal := by native_decide

theorem overflowingDiv_min_neg1 :
    (overflowingDiv minVal (fromInt (-1)) (by decide)).2 = true := by native_decide

theorem wrappingSub_zero_one : wrappingSub ⟨0⟩ ⟨1⟩ = fromInt (-1) := by native_decide

end Int16

/-! ================================================================ -/
/-! ## Int32 Signed Overflow Proofs                                   -/
/-! ================================================================ -/

namespace Int32

theorem checkedDiv_min_neg1 :
    checkedDiv minVal (fromInt (-1)) = none := by native_decide

theorem checkedRem_min_neg1 :
    checkedRem minVal (fromInt (-1)) = none := by native_decide

theorem wrappingAdd_wraps : wrappingAdd maxVal ⟨1⟩ = minVal := by native_decide

theorem overflowingDiv_min_neg1 :
    (overflowingDiv minVal (fromInt (-1)) (by decide)).2 = true := by native_decide

theorem wrappingSub_zero_one : wrappingSub ⟨0⟩ ⟨1⟩ = fromInt (-1) := by native_decide

end Int32

/-! ================================================================ -/
/-! ## Int64 Signed Overflow Proofs                                   -/
/-! ================================================================ -/

namespace Int64

theorem checkedDiv_min_neg1 :
    checkedDiv minVal (fromInt (-1)) = none := by native_decide

theorem checkedRem_min_neg1 :
    checkedRem minVal (fromInt (-1)) = none := by native_decide

theorem wrappingAdd_wraps : wrappingAdd maxVal ⟨1⟩ = minVal := by native_decide

theorem overflowingDiv_min_neg1 :
    (overflowingDiv minVal (fromInt (-1)) (by decide)).2 = true := by native_decide

theorem wrappingSub_zero_one : wrappingSub ⟨0⟩ ⟨1⟩ = fromInt (-1) := by native_decide

end Int64

/-! ================================================================ -/
/-! ## UWord Overflow Proofs                                          -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

/-- Wrapping addition is modular `2^w`. -/
theorem wrappingAdd_spec (x y : UWord w) :
    (wrappingAdd x y).toNat = (x.toNat + y.toNat) % 2 ^ w := rfl

/-- Wrapping subtraction is modular `2^w`. -/
theorem wrappingSub_spec (x y : UWord w) :
    (wrappingSub x y).toNat = (2 ^ w - y.toNat + x.toNat) % 2 ^ w :=
  BitVec.toNat_sub x.val y.val

/-- Wrapping multiplication is modular `2^w`. -/
theorem wrappingMul_spec (x y : UWord w) :
    (wrappingMul x y).toNat = (x.toNat * y.toNat) % 2 ^ w := rfl

/-- Checked addition returns `none` iff sum overflows. -/
theorem checkedAdd_none_iff (x y : UWord w) :
    checkedAdd x y = none ↔ x.toNat + y.toNat ≥ 2 ^ w := by
  simp only [checkedAdd, toNat]
  split <;> simp_all

/-- Checked subtraction returns `none` iff underflow. -/
theorem checkedSub_none_iff (x y : UWord w) :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  simp only [checkedSub, toNat]
  split <;> simp_all

/-- Overflowing addition flag agrees with overflow predicate. -/
theorem overflowingAdd_flag_spec (x y : UWord w) :
    (overflowingAdd x y).2 = (x.toNat + y.toNat >= 2 ^ w) := by
  simp [overflowingAdd, toNat]

/-- Overflowing subtraction flag agrees with spec. -/
theorem overflowingSub_flag_spec (x y : UWord w) :
    (overflowingSub x y).2 = (x.toNat < y.toNat) := by
  simp [overflowingSub, toNat]

/-- Checked multiplication returns `none` iff overflow. -/
theorem checkedMul_none_iff (x y : UWord w) :
    checkedMul x y = none ↔ x.toNat * y.toNat ≥ 2 ^ w := by
  simp only [checkedMul, toNat]
  split <;> simp_all

/-- Overflowing multiplication flag agrees with spec. -/
theorem overflowingMul_flag_spec (x y : UWord w) :
    (overflowingMul x y).2 = (x.toNat * y.toNat >= 2 ^ w) := by
  simp [overflowingMul, toNat]

end UWord

/-! ================================================================ -/
/-! ## IWord Overflow Proofs                                          -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

/-- Wrapping addition is modular on the underlying bits. -/
theorem wrappingAdd_val (x y : IWord w) :
    (wrappingAdd x y).val = x.val + y.val := rfl

/-- Wrapping subtraction is modular on the underlying bits. -/
theorem wrappingSub_val (x y : IWord w) :
    (wrappingSub x y).val = x.val - y.val := rfl

/-- Wrapping multiplication is modular on the underlying bits. -/
theorem wrappingMul_val (x y : IWord w) :
    (wrappingMul x y).val = x.val * y.val := rfl

/-- Checked addition returns `none` iff the sign bits detect overflow. -/
theorem checkedAdd_none_iff_overflows (x y : IWord w) :
    checkedAdd x y = none ↔ overflowsAdd x y = true := by
  simp [checkedAdd]

/-- Checked subtraction returns `none` iff overflow detected. -/
theorem checkedSub_none_iff_overflows (x y : IWord w) :
    checkedSub x y = none ↔ overflowsSub x y = true := by
  simp [checkedSub]

/-- Overflowing addition flag matches overflow predicate. -/
theorem overflowingAdd_flag_spec (x y : IWord w) :
    (overflowingAdd x y).2 = overflowsAdd x y := by
  simp [overflowingAdd]

/-- Overflowing subtraction flag matches overflow predicate. -/
theorem overflowingSub_flag_spec (x y : IWord w) :
    (overflowingSub x y).2 = overflowsSub x y := by
  simp [overflowingSub]

end IWord

end Radix
