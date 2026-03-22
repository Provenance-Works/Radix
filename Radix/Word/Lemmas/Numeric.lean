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
theorem BoundedUInt.wrappingAdd_minVal {α : Type} [inst : BoundedUInt α]
    (x : α) : inst.wrappingAdd x inst.minVal = x := by
  rw [inst.wrappingAdd_eq_add]
  apply LawfulFixedWidth.toBitVec_injective
  rw [inst.toBitVec_add, inst.toBitVec_minVal]
  simp [BitVec.add_zero]

/-- Wrapping addition is commutative (lifts from BitVec). -/
theorem BoundedUInt.wrappingAdd_comm {α : Type} [inst : BoundedUInt α]
    (x y : α) : inst.wrappingAdd x y = inst.wrappingAdd y x := by
  simp only [inst.wrappingAdd_eq_add]
  apply LawfulFixedWidth.toBitVec_injective
  rw [inst.toBitVec_add, inst.toBitVec_add, BitVec.add_comm]

/-- `toNat minVal ≤ toNat maxVal`. -/
theorem BoundedUInt.minVal_le_maxVal {α : Type} [inst : BoundedUInt α] :
    inst.toNat inst.minVal ≤ inst.toNat inst.maxVal := by
  rw [inst.toNat_minVal, inst.toNat_maxVal]
  omega

/-! ## BoundedInt Lemmas -/

/-- `toInt minVal ≤ toInt maxVal` for any signed type with bitWidth > 0. -/
theorem BoundedInt.minVal_le_maxVal {α : Type} [inst : BoundedInt α]
    (_hbw : FixedWidth.bitWidth (α := α) > 0) :
    inst.toInt inst.minVal ≤ inst.toInt inst.maxVal := by
  rw [inst.toInt_minVal, inst.toInt_maxVal]
  -- Goal: -(↑(2^(bitWidth-1) : Nat) : Int) ≤ (2 : Int)^(bitWidth-1) - 1
  -- Unify Nat and Int exponentiation so omega can handle it
  set k := FixedWidth.bitWidth (α := α) - 1
  have hpow_nat : (2 : Nat) ^ k ≥ 1 := Nat.one_le_two_pow
  -- Show (2 : Int)^k = ↑((2 : Nat)^k) by norm_cast
  have hpow_eq : (2 : Int) ^ k = ↑((2 : Nat) ^ k) := by
    norm_cast
  rw [hpow_eq]
  omega

end Radix
