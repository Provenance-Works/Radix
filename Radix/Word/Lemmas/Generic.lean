/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Mathlib.Data.BitVec

/-!
# Generic Wrapping Arithmetic Proofs (Layer 3)

This module proves ring-structure properties for **any** `LawfulFixedWidth`
type.  Because the `LawfulFixedWidth` laws lift addition, subtraction, and
multiplication into `BitVec`, the proofs here work once for all concrete
widths (UInt8, UInt16, UInt32, UInt64) instead of being repeated four times.

## Proof Strategy

Every proof follows the same pattern:
1. Show the goal at the `BitVec` level using the `toBitVec_add/sub/mul` laws.
2. Apply the corresponding `BitVec`-level algebraic lemma (from Mathlib or
   the Lean 4 kernel).
3. Conclude at the concrete type by injectivity (`toBitVec_injective`).

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- FR-001.3: Wrapping arithmetic forms a commutative ring (mod 2^n)
-/

set_option autoImplicit false

namespace Radix

section Generic

variable {α : Type} [inst : LawfulFixedWidth α]

/-! ## Additive Properties -/

/-- Wrapping addition is commutative for every lawful fixed-width type. -/
theorem Generic.add_comm (x y : α) : x + y = y + x := by
  have h : inst.toBitVec (x + y) = inst.toBitVec (y + x) := by
    rw [inst.toBitVec_add, inst.toBitVec_add, _root_.add_comm]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Wrapping addition is associative for every lawful fixed-width type. -/
theorem Generic.add_assoc (x y z : α) : x + y + z = x + (y + z) := by
  have h : inst.toBitVec (x + y + z) = inst.toBitVec (x + (y + z)) := by
    rw [inst.toBitVec_add, inst.toBitVec_add, inst.toBitVec_add, inst.toBitVec_add,
        _root_.add_assoc]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ## Multiplicative Properties -/

/-- Wrapping multiplication is commutative. -/
theorem Generic.mul_comm (x y : α) : x * y = y * x := by
  have h : inst.toBitVec (x * y) = inst.toBitVec (y * x) := by
    rw [inst.toBitVec_mul, inst.toBitVec_mul, _root_.mul_comm]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Wrapping multiplication is associative. -/
theorem Generic.mul_assoc (x y z : α) : x * y * z = x * (y * z) := by
  have h : inst.toBitVec (x * y * z) = inst.toBitVec (x * (y * z)) := by
    rw [inst.toBitVec_mul, inst.toBitVec_mul, inst.toBitVec_mul, inst.toBitVec_mul,
        _root_.mul_assoc]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ## Distributivity -/

/-- Left distributivity of multiplication over addition. -/
theorem Generic.mul_add (x y z : α) : x * (y + z) = x * y + x * z := by
  have h : inst.toBitVec (x * (y + z)) = inst.toBitVec (x * y + x * z) := by
    rw [inst.toBitVec_mul, inst.toBitVec_add, inst.toBitVec_add,
        inst.toBitVec_mul, inst.toBitVec_mul, _root_.mul_add]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Right distributivity of multiplication over addition. -/
theorem Generic.add_mul (x y z : α) : (x + y) * z = x * z + y * z := by
  have h : inst.toBitVec ((x + y) * z) = inst.toBitVec (x * z + y * z) := by
    rw [inst.toBitVec_mul, inst.toBitVec_add, inst.toBitVec_add,
        inst.toBitVec_mul, inst.toBitVec_mul, _root_.add_mul]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ## Subtraction Properties -/

/-- Wrapping subtraction: `x - y + y = x` (additive inverse relation). -/
theorem Generic.sub_add_cancel (x y : α) : x - y + y = x := by
  have h : inst.toBitVec (x - y + y) = inst.toBitVec x := by
    rw [inst.toBitVec_add, inst.toBitVec_sub, BitVec.sub_add_cancel]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Wrapping subtraction: `x + y - y = x`. -/
theorem Generic.add_sub_cancel (x y : α) : x + y - y = x := by
  have h : inst.toBitVec (x + y - y) = inst.toBitVec x := by
    rw [inst.toBitVec_sub, inst.toBitVec_add, BitVec.add_sub_cancel]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ## Embedding Laws (convenience re-exports) -/

/-- `toBitVec` is injective: same bit-vector ↔ same value. -/
theorem Generic.toBitVec_injective (x y : α)
    (h : FixedWidth.toBitVec x = FixedWidth.toBitVec y) : x = y :=
  LawfulFixedWidth.toBitVec_injective h

/-- Round-trip: `fromBitVec (toBitVec x) = x`. -/
theorem Generic.fromBitVec_toBitVec (x : α) :
    FixedWidth.fromBitVec (FixedWidth.toBitVec x) = x :=
  inst.fromBitVec_toBitVec x

/-- Round-trip: `toBitVec (fromBitVec bv) = bv`. -/
theorem Generic.toBitVec_fromBitVec (bv : BitVec inst.bitWidth) :
    FixedWidth.toBitVec (FixedWidth.fromBitVec bv : α) = bv :=
  inst.toBitVec_fromBitVec bv

end Generic

end Radix
