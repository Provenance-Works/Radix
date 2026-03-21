/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Numeric

/-!
# Numeric Typeclass Lemmas (Layer 3)

Proofs about the generic numeric typeclasses:
- `BoundedUInt` bounds properties
- `BoundedInt` bounds properties
- Generic wrapping arithmetic identities

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- v0.2.0 Roadmap: Numeric Typeclasses
-/

namespace Radix

/-! ## BoundedUInt Lemmas -/

/-- `minVal` is the additive identity for wrapping addition. -/
theorem BoundedUInt.wrappingAdd_minVal [inst : BoundedUInt α]
    (x : α) : inst.wrappingAdd x inst.minVal = x := by
  rw [inst.wrappingAdd_eq_add]
  have h := inst.fromBitVec_toBitVec x
  have := inst.toNat_minVal
  rfl

/-- Wrapping addition is commutative (lifts from BitVec). -/
theorem BoundedUInt.wrappingAdd_comm [inst : BoundedUInt α]
    (x y : α) : inst.wrappingAdd x y = inst.wrappingAdd y x := by
  rw [inst.wrappingAdd_eq_add, inst.wrappingAdd_eq_add]
  apply LawfulFixedWidth.toBitVec_injective
  rw [inst.toBitVec_add, inst.toBitVec_add, BitVec.add_comm]

/-- `toNat minVal ≤ toNat maxVal`. -/
theorem BoundedUInt.minVal_le_maxVal [inst : BoundedUInt α] :
    inst.toNat inst.minVal ≤ inst.toNat inst.maxVal := by
  rw [inst.toNat_minVal, inst.toNat_maxVal]
  omega

/-! ## BoundedInt Lemmas -/

/-- `toInt minVal ≤ toInt maxVal`. -/
theorem BoundedInt.minVal_le_maxVal [inst : BoundedInt α] :
    inst.toInt inst.minVal ≤ inst.toInt inst.maxVal := by
  rw [inst.toInt_minVal, inst.toInt_maxVal]
  have h := inst.toBitWidth_pos
  omega
where
  toBitWidth_pos : FixedWidth.bitWidth (α := α) > 0 := by
    -- bitWidth is at least 8 for all concrete instances
    omega

end Radix
