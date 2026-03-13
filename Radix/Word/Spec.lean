/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.BitVec

/-!
# Word Operations Specification (Layer 3)

This module defines the formal specification of fixed-width integer arithmetic
using Mathlib's `BitVec n`. All arithmetic modes (wrapping, saturating, checked,
overflowing) are specified here as pure mathematical definitions.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 1 or Layer 2 modules.
- Defines the canonical semantics that Layer 2 implementations must satisfy.

## References

- FR-001: Fixed-Width Integer Arithmetic
- FR-001.2a: Division Edge Cases
- FR-001.2b: Remainder Edge Cases
- ADR-002: Build on Mathlib BitVec
-/

namespace Radix.Word.Spec

open BitVec

variable {n : Nat}

/-! ## 1. Overflow Predicates -/

/-- Unsigned addition overflows when the true sum exceeds `2^n - 1`. -/
def addOverflows (x y : BitVec n) : Prop :=
  x.toNat + y.toNat >= 2 ^ n

/-- Unsigned subtraction underflows when `y > x`. -/
def subUnderflows (x y : BitVec n) : Prop :=
  x.toNat < y.toNat

/-- Unsigned multiplication overflows when the product exceeds `2^n - 1`. -/
def mulOverflows (x y : BitVec n) : Prop :=
  x.toNat * y.toNat >= 2 ^ n

/-- Decidable instance for unsigned addition overflow. -/
instance (x y : BitVec n) : Decidable (addOverflows x y) := inferInstanceAs (Decidable (_ >= _))

/-- Decidable instance for unsigned subtraction underflow. -/
instance (x y : BitVec n) : Decidable (subUnderflows x y) := inferInstanceAs (Decidable (_ < _))

/-- Decidable instance for unsigned multiplication overflow. -/
instance (x y : BitVec n) : Decidable (mulOverflows x y) := inferInstanceAs (Decidable (_ >= _))

/-! ### Signed Overflow Predicates -/

/-- Signed addition overflows when the true signed sum is outside `[-2^(n-1), 2^(n-1) - 1]`. -/
def signedAddOverflows (x y : BitVec n) : Prop :=
  x.toInt + y.toInt < -(2 ^ (n - 1 : Nat) : Int) ∨ x.toInt + y.toInt > 2 ^ (n - 1 : Nat) - 1

/-- Signed subtraction overflows when the true signed difference is out of range. -/
def signedSubOverflows (x y : BitVec n) : Prop :=
  x.toInt - y.toInt < -(2 ^ (n - 1 : Nat) : Int) ∨ x.toInt - y.toInt > 2 ^ (n - 1 : Nat) - 1

/-- Signed multiplication overflows when the true signed product is out of range. -/
def signedMulOverflows (x y : BitVec n) : Prop :=
  x.toInt * y.toInt < -(2 ^ (n - 1 : Nat) : Int) ∨ x.toInt * y.toInt > 2 ^ (n - 1 : Nat) - 1

/-- Signed MIN / -1 overflow: occurs when `x = -2^(n-1)` and `y = -1` (all ones). -/
def signedDivOverflows (x y : BitVec n) : Prop :=
  x.toInt = -(2 ^ (n - 1 : Nat) : Int) ∧ y.toInt = -1

instance (x y : BitVec n) : Decidable (signedAddOverflows x y) := by
  unfold signedAddOverflows; infer_instance

instance (x y : BitVec n) : Decidable (signedSubOverflows x y) := by
  unfold signedSubOverflows; infer_instance

instance (x y : BitVec n) : Decidable (signedMulOverflows x y) := by
  unfold signedMulOverflows; infer_instance

instance (x y : BitVec n) : Decidable (signedDivOverflows x y) := by
  unfold signedDivOverflows; infer_instance

/-! ## 2. Wrapping Arithmetic Specification

Wrapping arithmetic computes modulo `2^n`, which is exactly what `BitVec`
arithmetic does by default. -/

/-- Wrapping addition: `(x + y) mod 2^n`. -/
def wrappingAdd (x y : BitVec n) : BitVec n := x + y

/-- Wrapping subtraction: `(x - y) mod 2^n`. -/
def wrappingSub (x y : BitVec n) : BitVec n := x - y

/-- Wrapping multiplication: `(x * y) mod 2^n`. -/
def wrappingMul (x y : BitVec n) : BitVec n := x * y

/-! ## 3. Saturating Arithmetic Specification -/

/-- Unsigned saturating addition: clamps to `2^n - 1` on overflow. -/
def saturatingAdd (x y : BitVec n) : BitVec n :=
  if addOverflows x y then BitVec.allOnes n
  else x + y

/-- Unsigned saturating subtraction: clamps to `0` on underflow. -/
def saturatingSub (x y : BitVec n) : BitVec n :=
  if subUnderflows x y then 0#n
  else x - y

/-- Unsigned saturating multiplication: clamps to `2^n - 1` on overflow. -/
def saturatingMul (x y : BitVec n) : BitVec n :=
  if mulOverflows x y then BitVec.allOnes n
  else x * y

/-! ### Signed Saturating Arithmetic -/

/-- Signed minimum value: `-2^(n-1)` as `BitVec n`. -/
def signedMin (n : Nat) : BitVec n :=
  BitVec.intMin n

/-- Signed maximum value: `2^(n-1) - 1` as `BitVec n`. -/
def signedMax (n : Nat) : BitVec n :=
  BitVec.intMax n

/-- Signed saturating addition: clamps to MIN/MAX on overflow.
    Positive overflow -> MAX, negative overflow -> MIN. -/
def signedSaturatingAdd (x y : BitVec n) : BitVec n :=
  let sum := x.toInt + y.toInt
  if sum > 2 ^ (n - 1 : Nat) - 1 then signedMax n
  else if sum < -(2 ^ (n - 1 : Nat) : Int) then signedMin n
  else x + y

/-- Signed saturating subtraction: clamps to MIN/MAX on overflow. -/
def signedSaturatingSub (x y : BitVec n) : BitVec n :=
  let diff := x.toInt - y.toInt
  if diff > 2 ^ (n - 1 : Nat) - 1 then signedMax n
  else if diff < -(2 ^ (n - 1 : Nat) : Int) then signedMin n
  else x - y

/-- Signed saturating multiplication: clamps to MIN/MAX on overflow. -/
def signedSaturatingMul (x y : BitVec n) : BitVec n :=
  let prod := x.toInt * y.toInt
  if prod > 2 ^ (n - 1 : Nat) - 1 then signedMax n
  else if prod < -(2 ^ (n - 1 : Nat) : Int) then signedMin n
  else x * y

/-! ## 4. Checked Arithmetic Specification -/

/-- Unsigned checked addition: returns `none` on overflow. -/
def checkedAdd (x y : BitVec n) : Option (BitVec n) :=
  if addOverflows x y then none else some (x + y)

/-- Unsigned checked subtraction: returns `none` on underflow. -/
def checkedSub (x y : BitVec n) : Option (BitVec n) :=
  if subUnderflows x y then none else some (x - y)

/-- Unsigned checked multiplication: returns `none` on overflow. -/
def checkedMul (x y : BitVec n) : Option (BitVec n) :=
  if mulOverflows x y then none else some (x * y)

/-- Unsigned checked division: returns `none` when divisor is zero. -/
def checkedDiv (x y : BitVec n) : Option (BitVec n) :=
  if y == 0#n then none else some (x / y)

/-- Unsigned checked remainder: returns `none` when divisor is zero. -/
def checkedRem (x y : BitVec n) : Option (BitVec n) :=
  if y == 0#n then none else some (x % y)

/-! ### Signed Checked Arithmetic -/

/-- Signed checked addition: returns `none` on signed overflow. -/
def signedCheckedAdd (x y : BitVec n) : Option (BitVec n) :=
  if signedAddOverflows x y then none else some (x + y)

/-- Signed checked subtraction: returns `none` on signed overflow. -/
def signedCheckedSub (x y : BitVec n) : Option (BitVec n) :=
  if signedSubOverflows x y then none else some (x - y)

/-- Signed checked multiplication: returns `none` on signed overflow. -/
def signedCheckedMul (x y : BitVec n) : Option (BitVec n) :=
  if signedMulOverflows x y then none else some (x * y)

/-- Signed checked division: returns `none` on zero divisor OR `MIN / -1`.
    (FR-001.2a: Checked mode) -/
def signedCheckedDiv (x y : BitVec n) : Option (BitVec n) :=
  if y == 0#n then none
  else if signedDivOverflows x y then none
  else some (BitVec.sdiv x y)

/-- Signed checked remainder: returns `none` on zero divisor OR `MIN % -1`.
    (FR-001.2b: Checked mode) -/
def signedCheckedRem (x y : BitVec n) : Option (BitVec n) :=
  if y == 0#n then none
  else if signedDivOverflows x y then none
  else some (BitVec.srem x y)

/-! ## 5. Overflowing Arithmetic Specification -/

/-- Unsigned overflowing addition: returns `(result, overflowed)`. -/
def overflowingAdd (x y : BitVec n) : BitVec n × Bool :=
  (x + y, decide (addOverflows x y))

/-- Unsigned overflowing subtraction: returns `(result, overflowed)`. -/
def overflowingSub (x y : BitVec n) : BitVec n × Bool :=
  (x - y, decide (subUnderflows x y))

/-- Unsigned overflowing multiplication: returns `(result, overflowed)`. -/
def overflowingMul (x y : BitVec n) : BitVec n × Bool :=
  (x * y, decide (mulOverflows x y))

/-! ### Signed Overflowing Arithmetic -/

/-- Signed overflowing addition: returns `(wrapping result, overflowed)`. -/
def signedOverflowingAdd (x y : BitVec n) : BitVec n × Bool :=
  (x + y, decide (signedAddOverflows x y))

/-- Signed overflowing subtraction: returns `(wrapping result, overflowed)`. -/
def signedOverflowingSub (x y : BitVec n) : BitVec n × Bool :=
  (x - y, decide (signedSubOverflows x y))

/-- Signed overflowing multiplication: returns `(wrapping result, overflowed)`. -/
def signedOverflowingMul (x y : BitVec n) : BitVec n × Bool :=
  (x * y, decide (signedMulOverflows x y))

/-- Signed overflowing division: returns `(wrapping result, overflowed)`.
    For `MIN / -1`: returns `(MIN, true)` per FR-001.2a. -/
def signedOverflowingDiv (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n × Bool :=
  if signedDivOverflows x y then (x, true)
  else (BitVec.sdiv x y, false)

/-- Signed overflowing remainder: returns `(result, overflowed)`.
    For `MIN % -1`: returns `(0, true)` per FR-001.2b. -/
def signedOverflowingRem (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n × Bool :=
  if signedDivOverflows x y then (0#n, true)
  else (BitVec.srem x y, false)

/-! ## 6. Tier 1 Proof-Carrying Division/Remainder Specification -/

/-- Unsigned division with proof of nonzero divisor. -/
def div (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n := x / y

/-- Unsigned remainder with proof of nonzero divisor. -/
def rem (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n := x % y

/-- Signed division with proof of nonzero divisor.
    (Wrapping mode: `MIN / -1 = MIN` per FR-001.2a) -/
def signedDiv (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  BitVec.sdiv x y

/-- Signed remainder with proof of nonzero divisor.
    (Wrapping mode: `MIN % -1 = 0` per FR-001.2b) -/
def signedRem (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  BitVec.srem x y

/-! ## 7. Signed Saturating Division/Remainder -/

/-- Signed saturating division: `MIN / -1 = MAX` per FR-001.2a. -/
def signedSaturatingDiv (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  if signedDivOverflows x y then signedMax n
  else BitVec.sdiv x y

/-- Signed saturating remainder: `MIN % -1 = 0` (fits, no saturation needed).
    Per FR-001.2b. -/
def signedSaturatingRem (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  if signedDivOverflows x y then 0#n
  else BitVec.srem x y

/-! ## 8. Wrapping Signed Division/Remainder -/

/-- Wrapping signed division: `MIN / -1 = MIN` (wraps) per FR-001.2a. -/
def signedWrappingDiv (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  BitVec.sdiv x y

/-- Wrapping signed remainder: `MIN % -1 = 0` per FR-001.2b. -/
def signedWrappingRem (x y : BitVec n) (_h : y ≠ 0#n) : BitVec n :=
  BitVec.srem x y

/-! ## 9. Comparison Specifications -/

/-- Unsigned less-than. -/
def ult (x y : BitVec n) : Bool := x.toNat < y.toNat

/-- Unsigned less-than-or-equal. -/
def ule (x y : BitVec n) : Bool := x.toNat <= y.toNat

/-- Signed less-than. -/
def slt (x y : BitVec n) : Bool := x.toInt < y.toInt

/-- Signed less-than-or-equal. -/
def sle (x y : BitVec n) : Bool := x.toInt <= y.toInt

/-- Signed greater-than: symmetric to `slt`. -/
def sgt (x y : BitVec n) : Bool := slt y x

/-- Signed greater-than-or-equal: symmetric to `sle`. -/
def sge (x y : BitVec n) : Bool := sle y x

end Radix.Word.Spec
