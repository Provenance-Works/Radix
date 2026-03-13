/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int
import Radix.Word.Size

/-!
# Multi-Mode Arithmetic (Layer 2)

This module provides all arithmetic modes for all integer types:
- **Tier 1 (Proof-Carrying)**: `add`, `sub`, `mul`, `div`, `rem` with preconditions
- **Tier 2 Wrapping**: `wrappingAdd`, `wrappingSub`, `wrappingMul`
- **Tier 2 Saturating**: `saturatingAdd`, `saturatingSub`, `saturatingMul`
- **Tier 2 Checked**: `checkedAdd`, `checkedSub`, `checkedMul`, `checkedDiv`, `checkedRem`
- **Tier 2 Overflowing**: `overflowingAdd`, `overflowingSub`, `overflowingMul`

Division and remainder for Wrapping/Saturating/Overflowing modes require
a proof of nonzero divisor (FR-001.2a: Lean 4 cannot panic safely).

All Tier 2 functions are marked `@[inline]` for zero-cost abstraction (NFR-002).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-001.2: Arithmetic operations
- FR-001.2a: Division edge cases
- FR-001.2b: Remainder edge cases
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 Arithmetic                                               -/
/-! ================================================================ -/

namespace UInt8

/-! ### Tier 1: Proof-Carrying

Unsigned Tier 1 operations use `*Checked` (precondition: natural-number bound).
Signed Tier 1 operations use `*Proof` (precondition: overflow predicate).
The naming difference reflects different precondition styles, not semantics. -/

/-- Addition with proof of no overflow. -/
@[inline] def addChecked (x y : UInt8) (_h : x.toNat + y.toNat < 2 ^ 8) : UInt8 :=
  ⟨x.val + y.val⟩

/-- Subtraction with proof of no underflow. -/
@[inline] def subChecked (x y : UInt8) (_h : y.toNat ≤ x.toNat) : UInt8 :=
  ⟨x.val - y.val⟩

/-- Multiplication with proof of no overflow. -/
@[inline] def mulChecked (x y : UInt8) (_h : x.toNat * y.toNat < 2 ^ 8) : UInt8 :=
  ⟨x.val * y.val⟩

/-- Division with proof of nonzero divisor. -/
@[inline] def div (x y : UInt8) (_h : y ≠ ⟨0⟩) : UInt8 :=
  ⟨x.val / y.val⟩

/-- Remainder with proof of nonzero divisor. -/
@[inline] def rem (x y : UInt8) (_h : y ≠ ⟨0⟩) : UInt8 :=
  ⟨x.val % y.val⟩

/-! ### Tier 2: Wrapping -/

@[inline] def wrappingAdd (x y : UInt8) : UInt8 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : UInt8) : UInt8 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : UInt8) : UInt8 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : UInt8) : UInt8 := ⟨0 - x.val⟩

/-! ### Tier 2: Saturating -/

@[inline] def saturatingAdd (x y : UInt8) : UInt8 :=
  if x.toNat + y.toNat >= 2 ^ 8 then maxVal else ⟨x.val + y.val⟩

@[inline] def saturatingSub (x y : UInt8) : UInt8 :=
  if x.toNat < y.toNat then minVal else ⟨x.val - y.val⟩

@[inline] def saturatingMul (x y : UInt8) : UInt8 :=
  if x.toNat * y.toNat >= 2 ^ 8 then maxVal else ⟨x.val * y.val⟩

/-! ### Tier 2: Checked -/

@[inline] def checkedAdd (x y : UInt8) : Option UInt8 :=
  if x.toNat + y.toNat >= 2 ^ 8 then none else some ⟨x.val + y.val⟩

@[inline] def checkedSub (x y : UInt8) : Option UInt8 :=
  if x.toNat < y.toNat then none else some ⟨x.val - y.val⟩

@[inline] def checkedMul (x y : UInt8) : Option UInt8 :=
  if x.toNat * y.toNat >= 2 ^ 8 then none else some ⟨x.val * y.val⟩

@[inline] def checkedDiv (x y : UInt8) : Option UInt8 :=
  if y == ⟨0⟩ then none else some ⟨x.val / y.val⟩

@[inline] def checkedRem (x y : UInt8) : Option UInt8 :=
  if y == ⟨0⟩ then none else some ⟨x.val % y.val⟩

/-! ### Tier 2: Overflowing -/

@[inline] def overflowingAdd (x y : UInt8) : UInt8 × Bool :=
  (⟨x.val + y.val⟩, x.toNat + y.toNat >= 2 ^ 8)

@[inline] def overflowingSub (x y : UInt8) : UInt8 × Bool :=
  (⟨x.val - y.val⟩, x.toNat < y.toNat)

@[inline] def overflowingMul (x y : UInt8) : UInt8 × Bool :=
  (⟨x.val * y.val⟩, x.toNat * y.toNat >= 2 ^ 8)

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Arithmetic                                              -/
/-! ================================================================ -/

namespace UInt16

@[inline] def addChecked (x y : UInt16) (_h : x.toNat + y.toNat < 2 ^ 16) : UInt16 :=
  ⟨x.val + y.val⟩
@[inline] def subChecked (x y : UInt16) (_h : y.toNat ≤ x.toNat) : UInt16 :=
  ⟨x.val - y.val⟩
@[inline] def mulChecked (x y : UInt16) (_h : x.toNat * y.toNat < 2 ^ 16) : UInt16 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : UInt16) (_h : y ≠ ⟨0⟩) : UInt16 :=
  ⟨x.val / y.val⟩
@[inline] def rem (x y : UInt16) (_h : y ≠ ⟨0⟩) : UInt16 :=
  ⟨x.val % y.val⟩

@[inline] def wrappingAdd (x y : UInt16) : UInt16 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : UInt16) : UInt16 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : UInt16) : UInt16 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : UInt16) : UInt16 := ⟨0 - x.val⟩

@[inline] def saturatingAdd (x y : UInt16) : UInt16 :=
  if x.toNat + y.toNat >= 2 ^ 16 then maxVal else ⟨x.val + y.val⟩
@[inline] def saturatingSub (x y : UInt16) : UInt16 :=
  if x.toNat < y.toNat then minVal else ⟨x.val - y.val⟩
@[inline] def saturatingMul (x y : UInt16) : UInt16 :=
  if x.toNat * y.toNat >= 2 ^ 16 then maxVal else ⟨x.val * y.val⟩

@[inline] def checkedAdd (x y : UInt16) : Option UInt16 :=
  if x.toNat + y.toNat >= 2 ^ 16 then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : UInt16) : Option UInt16 :=
  if x.toNat < y.toNat then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : UInt16) : Option UInt16 :=
  if x.toNat * y.toNat >= 2 ^ 16 then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : UInt16) : Option UInt16 :=
  if y == ⟨0⟩ then none else some ⟨x.val / y.val⟩
@[inline] def checkedRem (x y : UInt16) : Option UInt16 :=
  if y == ⟨0⟩ then none else some ⟨x.val % y.val⟩

@[inline] def overflowingAdd (x y : UInt16) : UInt16 × Bool :=
  (⟨x.val + y.val⟩, x.toNat + y.toNat >= 2 ^ 16)
@[inline] def overflowingSub (x y : UInt16) : UInt16 × Bool :=
  (⟨x.val - y.val⟩, x.toNat < y.toNat)
@[inline] def overflowingMul (x y : UInt16) : UInt16 × Bool :=
  (⟨x.val * y.val⟩, x.toNat * y.toNat >= 2 ^ 16)

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Arithmetic                                              -/
/-! ================================================================ -/

namespace UInt32

@[inline] def addChecked (x y : UInt32) (_h : x.toNat + y.toNat < 2 ^ 32) : UInt32 :=
  ⟨x.val + y.val⟩
@[inline] def subChecked (x y : UInt32) (_h : y.toNat ≤ x.toNat) : UInt32 :=
  ⟨x.val - y.val⟩
@[inline] def mulChecked (x y : UInt32) (_h : x.toNat * y.toNat < 2 ^ 32) : UInt32 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : UInt32) (_h : y ≠ ⟨0⟩) : UInt32 :=
  ⟨x.val / y.val⟩
@[inline] def rem (x y : UInt32) (_h : y ≠ ⟨0⟩) : UInt32 :=
  ⟨x.val % y.val⟩

@[inline] def wrappingAdd (x y : UInt32) : UInt32 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : UInt32) : UInt32 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : UInt32) : UInt32 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : UInt32) : UInt32 := ⟨0 - x.val⟩

@[inline] def saturatingAdd (x y : UInt32) : UInt32 :=
  if x.toNat + y.toNat >= 2 ^ 32 then maxVal else ⟨x.val + y.val⟩
@[inline] def saturatingSub (x y : UInt32) : UInt32 :=
  if x.toNat < y.toNat then minVal else ⟨x.val - y.val⟩
@[inline] def saturatingMul (x y : UInt32) : UInt32 :=
  if x.toNat * y.toNat >= 2 ^ 32 then maxVal else ⟨x.val * y.val⟩

@[inline] def checkedAdd (x y : UInt32) : Option UInt32 :=
  if x.toNat + y.toNat >= 2 ^ 32 then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : UInt32) : Option UInt32 :=
  if x.toNat < y.toNat then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : UInt32) : Option UInt32 :=
  if x.toNat * y.toNat >= 2 ^ 32 then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : UInt32) : Option UInt32 :=
  if y == ⟨0⟩ then none else some ⟨x.val / y.val⟩
@[inline] def checkedRem (x y : UInt32) : Option UInt32 :=
  if y == ⟨0⟩ then none else some ⟨x.val % y.val⟩

@[inline] def overflowingAdd (x y : UInt32) : UInt32 × Bool :=
  (⟨x.val + y.val⟩, x.toNat + y.toNat >= 2 ^ 32)
@[inline] def overflowingSub (x y : UInt32) : UInt32 × Bool :=
  (⟨x.val - y.val⟩, x.toNat < y.toNat)
@[inline] def overflowingMul (x y : UInt32) : UInt32 × Bool :=
  (⟨x.val * y.val⟩, x.toNat * y.toNat >= 2 ^ 32)

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Arithmetic                                              -/
/-! ================================================================ -/

namespace UInt64

@[inline] def addChecked (x y : UInt64) (_h : x.toNat + y.toNat < 2 ^ 64) : UInt64 :=
  ⟨x.val + y.val⟩
@[inline] def subChecked (x y : UInt64) (_h : y.toNat ≤ x.toNat) : UInt64 :=
  ⟨x.val - y.val⟩
@[inline] def mulChecked (x y : UInt64) (_h : x.toNat * y.toNat < 2 ^ 64) : UInt64 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : UInt64) (_h : y ≠ ⟨0⟩) : UInt64 :=
  ⟨x.val / y.val⟩
@[inline] def rem (x y : UInt64) (_h : y ≠ ⟨0⟩) : UInt64 :=
  ⟨x.val % y.val⟩

@[inline] def wrappingAdd (x y : UInt64) : UInt64 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : UInt64) : UInt64 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : UInt64) : UInt64 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : UInt64) : UInt64 := ⟨0 - x.val⟩

@[inline] def saturatingAdd (x y : UInt64) : UInt64 :=
  if x.toNat + y.toNat >= 2 ^ 64 then maxVal else ⟨x.val + y.val⟩
@[inline] def saturatingSub (x y : UInt64) : UInt64 :=
  if x.toNat < y.toNat then minVal else ⟨x.val - y.val⟩
@[inline] def saturatingMul (x y : UInt64) : UInt64 :=
  if x.toNat * y.toNat >= 2 ^ 64 then maxVal else ⟨x.val * y.val⟩

@[inline] def checkedAdd (x y : UInt64) : Option UInt64 :=
  if x.toNat + y.toNat >= 2 ^ 64 then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : UInt64) : Option UInt64 :=
  if x.toNat < y.toNat then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : UInt64) : Option UInt64 :=
  if x.toNat * y.toNat >= 2 ^ 64 then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : UInt64) : Option UInt64 :=
  if y == ⟨0⟩ then none else some ⟨x.val / y.val⟩
@[inline] def checkedRem (x y : UInt64) : Option UInt64 :=
  if y == ⟨0⟩ then none else some ⟨x.val % y.val⟩

@[inline] def overflowingAdd (x y : UInt64) : UInt64 × Bool :=
  (⟨x.val + y.val⟩, x.toNat + y.toNat >= 2 ^ 64)
@[inline] def overflowingSub (x y : UInt64) : UInt64 × Bool :=
  (⟨x.val - y.val⟩, x.toNat < y.toNat)
@[inline] def overflowingMul (x y : UInt64) : UInt64 × Bool :=
  (⟨x.val * y.val⟩, x.toNat * y.toNat >= 2 ^ 64)

end UInt64

/-! ================================================================ -/
/-! ## Int8 Arithmetic (Signed)                                       -/
/-! ================================================================ -/

namespace Int8

def overflowsAdd (x y : Int8) : Bool :=
  let sum := x.val + y.val
  -- Overflow iff signs of x and y match but sign of sum differs
  (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 128

def overflowsSub (x y : Int8) : Bool :=
  let diff := x.val - y.val
  -- Overflow iff signs of x and y differ and sign of diff differs from x
  (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 128

def overflowsMul (x y : Int8) : Bool :=
  let prod := x.toInt * y.toInt
  prod < -128 || prod > 127

def divOverflows (x y : Int8) : Bool :=
  x == minVal && y == ⟨255⟩  -- y.toInt == -1

/-! ### Tier 1: Proof-Carrying -/

@[inline] def addProof (x y : Int8) (_h : ¬(overflowsAdd x y = true)) : Int8 :=
  ⟨x.val + y.val⟩
@[inline] def subProof (x y : Int8) (_h : ¬(overflowsSub x y = true)) : Int8 :=
  ⟨x.val - y.val⟩
@[inline] def mulProof (x y : Int8) (_h : ¬(overflowsMul x y = true)) : Int8 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : Int8) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int8 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def rem (x y : Int8) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int8 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Wrapping -/

@[inline] def wrappingAdd (x y : Int8) : Int8 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : Int8) : Int8 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : Int8) : Int8 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : Int8) : Int8 := ⟨0 - x.val⟩
-- FR-001.2a: Wrapping signed div requires proof of nonzero (no wrapping for /0)
-- MIN / -1 = MIN (wraps)
@[inline] def wrappingDiv (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
-- FR-001.2b: MIN % -1 = 0
@[inline] def wrappingRem (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Saturating -/

@[inline] def saturatingAdd (x y : Int8) : Int8 :=
  let sum := x.val + y.val
  if (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 128 then
    if x.val >= 128 then minVal else maxVal
  else ⟨sum⟩

@[inline] def saturatingSub (x y : Int8) : Int8 :=
  let diff := x.val - y.val
  if (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 128 then
    if x.val >= 128 then minVal else maxVal
  else ⟨diff⟩

@[inline] def saturatingMul (x y : Int8) : Int8 :=
  let prod := x.toInt * y.toInt
  if prod > 127 then maxVal
  else if prod < -128 then minVal
  else ⟨x.val * y.val⟩

-- FR-001.2a: Saturating: MIN / -1 = MAX
@[inline] def saturatingDiv (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 :=
  if divOverflows x y then maxVal
  else fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)

-- FR-001.2b: MIN % -1 = 0 (fits, no saturation)
@[inline] def saturatingRem (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 :=
  if divOverflows x y then ⟨0⟩
  else fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Checked -/

@[inline] def checkedAdd (x y : Int8) : Option Int8 :=
  if overflowsAdd x y then none else some ⟨x.val + y.val⟩

@[inline] def checkedSub (x y : Int8) : Option Int8 :=
  if overflowsSub x y then none else some ⟨x.val - y.val⟩

@[inline] def checkedMul (x y : Int8) : Option Int8 :=
  if overflowsMul x y then none else some ⟨x.val * y.val⟩

-- FR-001.2a: Checked: MIN / -1 = none
@[inline] def checkedDiv (x y : Int8) : Option Int8 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec))

-- FR-001.2b: Checked: MIN % -1 = none
@[inline] def checkedRem (x y : Int8) : Option Int8 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.srem x.toBitVec y.toBitVec))

/-! ### Tier 2: Overflowing -/

@[inline] def overflowingAdd (x y : Int8) : Int8 × Bool :=
  (⟨x.val + y.val⟩, overflowsAdd x y)

@[inline] def overflowingSub (x y : Int8) : Int8 × Bool :=
  (⟨x.val - y.val⟩, overflowsSub x y)

@[inline] def overflowingMul (x y : Int8) : Int8 × Bool :=
  (⟨x.val * y.val⟩, overflowsMul x y)

-- FR-001.2a: Overflowing: MIN / -1 = (MIN, true)
@[inline] def overflowingDiv (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 × Bool :=
  if divOverflows x y then (minVal, true)
  else (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec), false)

-- FR-001.2b: Overflowing: MIN % -1 = (0, true)
@[inline] def overflowingRem (x y : Int8) (_h : y ≠ ⟨0⟩) : Int8 × Bool :=
  if divOverflows x y then (⟨0⟩, true)
  else (fromBitVec (BitVec.srem x.toBitVec y.toBitVec), false)

end Int8

/-! ================================================================ -/
/-! ## Int16 Arithmetic (Signed)                                      -/
/-! ================================================================ -/

namespace Int16

def overflowsAdd (x y : Int16) : Bool :=
  let sum := x.val + y.val
  (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 32768

def overflowsSub (x y : Int16) : Bool :=
  let diff := x.val - y.val
  (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 32768

def overflowsMul (x y : Int16) : Bool :=
  let prod := x.toInt * y.toInt
  prod < -(2 ^ 15 : Int) || prod > 2 ^ 15 - 1

def divOverflows (x y : Int16) : Bool :=
  x == minVal && y == ⟨65535⟩

/-! ### Tier 1: Proof-Carrying -/

@[inline] def addProof (x y : Int16) (_h : ¬(overflowsAdd x y = true)) : Int16 :=
  ⟨x.val + y.val⟩
@[inline] def subProof (x y : Int16) (_h : ¬(overflowsSub x y = true)) : Int16 :=
  ⟨x.val - y.val⟩
@[inline] def mulProof (x y : Int16) (_h : ¬(overflowsMul x y = true)) : Int16 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : Int16) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int16 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def rem (x y : Int16) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int16 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Wrapping -/

@[inline] def wrappingAdd (x y : Int16) : Int16 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : Int16) : Int16 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : Int16) : Int16 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : Int16) : Int16 := ⟨0 - x.val⟩
@[inline] def wrappingDiv (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def wrappingRem (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def saturatingAdd (x y : Int16) : Int16 :=
  let sum := x.val + y.val
  if (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 32768 then
    if x.val >= 32768 then minVal else maxVal
  else ⟨sum⟩

@[inline] def saturatingSub (x y : Int16) : Int16 :=
  let diff := x.val - y.val
  if (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 32768 then
    if x.val >= 32768 then minVal else maxVal
  else ⟨diff⟩

@[inline] def saturatingMul (x y : Int16) : Int16 :=
  let prod := x.toInt * y.toInt
  if prod > 2 ^ 15 - 1 then maxVal
  else if prod < -(2 ^ 15 : Int) then minVal
  else ⟨x.val * y.val⟩

@[inline] def saturatingDiv (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 :=
  if divOverflows x y then maxVal
  else fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)

@[inline] def saturatingRem (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 :=
  if divOverflows x y then ⟨0⟩
  else fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def checkedAdd (x y : Int16) : Option Int16 :=
  if overflowsAdd x y then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : Int16) : Option Int16 :=
  if overflowsSub x y then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : Int16) : Option Int16 :=
  if overflowsMul x y then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : Int16) : Option Int16 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec))
@[inline] def checkedRem (x y : Int16) : Option Int16 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.srem x.toBitVec y.toBitVec))

@[inline] def overflowingAdd (x y : Int16) : Int16 × Bool :=
  (⟨x.val + y.val⟩, overflowsAdd x y)
@[inline] def overflowingSub (x y : Int16) : Int16 × Bool :=
  (⟨x.val - y.val⟩, overflowsSub x y)
@[inline] def overflowingMul (x y : Int16) : Int16 × Bool :=
  (⟨x.val * y.val⟩, overflowsMul x y)
@[inline] def overflowingDiv (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 × Bool :=
  if divOverflows x y then (minVal, true)
  else (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec), false)
@[inline] def overflowingRem (x y : Int16) (_h : y ≠ ⟨0⟩) : Int16 × Bool :=
  if divOverflows x y then (⟨0⟩, true)
  else (fromBitVec (BitVec.srem x.toBitVec y.toBitVec), false)

end Int16

/-! ================================================================ -/
/-! ## Int32 Arithmetic (Signed)                                      -/
/-! ================================================================ -/

namespace Int32

def overflowsAdd (x y : Int32) : Bool :=
  let sum := x.val + y.val
  (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 2147483648

def overflowsSub (x y : Int32) : Bool :=
  let diff := x.val - y.val
  (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 2147483648

def overflowsMul (x y : Int32) : Bool :=
  let prod := x.toInt * y.toInt
  prod < -(2 ^ 31 : Int) || prod > 2 ^ 31 - 1

def divOverflows (x y : Int32) : Bool :=
  x == minVal && y == ⟨4294967295⟩

/-! ### Tier 1: Proof-Carrying -/

@[inline] def addProof (x y : Int32) (_h : ¬(overflowsAdd x y = true)) : Int32 :=
  ⟨x.val + y.val⟩
@[inline] def subProof (x y : Int32) (_h : ¬(overflowsSub x y = true)) : Int32 :=
  ⟨x.val - y.val⟩
@[inline] def mulProof (x y : Int32) (_h : ¬(overflowsMul x y = true)) : Int32 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : Int32) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int32 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def rem (x y : Int32) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int32 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Wrapping -/

@[inline] def wrappingAdd (x y : Int32) : Int32 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : Int32) : Int32 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : Int32) : Int32 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : Int32) : Int32 := ⟨0 - x.val⟩
@[inline] def wrappingDiv (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def wrappingRem (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def saturatingAdd (x y : Int32) : Int32 :=
  let sum := x.val + y.val
  if (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 2147483648 then
    if x.val >= 2147483648 then minVal else maxVal
  else ⟨sum⟩

@[inline] def saturatingSub (x y : Int32) : Int32 :=
  let diff := x.val - y.val
  if (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 2147483648 then
    if x.val >= 2147483648 then minVal else maxVal
  else ⟨diff⟩

@[inline] def saturatingMul (x y : Int32) : Int32 :=
  let prod := x.toInt * y.toInt
  if prod > 2 ^ 31 - 1 then maxVal
  else if prod < -(2 ^ 31 : Int) then minVal
  else ⟨x.val * y.val⟩

@[inline] def saturatingDiv (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 :=
  if divOverflows x y then maxVal
  else fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)

@[inline] def saturatingRem (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 :=
  if divOverflows x y then ⟨0⟩
  else fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def checkedAdd (x y : Int32) : Option Int32 :=
  if overflowsAdd x y then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : Int32) : Option Int32 :=
  if overflowsSub x y then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : Int32) : Option Int32 :=
  if overflowsMul x y then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : Int32) : Option Int32 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec))
@[inline] def checkedRem (x y : Int32) : Option Int32 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.srem x.toBitVec y.toBitVec))

@[inline] def overflowingAdd (x y : Int32) : Int32 × Bool :=
  (⟨x.val + y.val⟩, overflowsAdd x y)
@[inline] def overflowingSub (x y : Int32) : Int32 × Bool :=
  (⟨x.val - y.val⟩, overflowsSub x y)
@[inline] def overflowingMul (x y : Int32) : Int32 × Bool :=
  (⟨x.val * y.val⟩, overflowsMul x y)
@[inline] def overflowingDiv (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 × Bool :=
  if divOverflows x y then (minVal, true)
  else (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec), false)
@[inline] def overflowingRem (x y : Int32) (_h : y ≠ ⟨0⟩) : Int32 × Bool :=
  if divOverflows x y then (⟨0⟩, true)
  else (fromBitVec (BitVec.srem x.toBitVec y.toBitVec), false)

end Int32

/-! ================================================================ -/
/-! ## Int64 Arithmetic (Signed)                                      -/
/-! ================================================================ -/

namespace Int64

def overflowsAdd (x y : Int64) : Bool :=
  let sum := x.val + y.val
  (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 9223372036854775808

def overflowsSub (x y : Int64) : Bool :=
  let diff := x.val - y.val
  (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 9223372036854775808

def overflowsMul (x y : Int64) : Bool :=
  let prod := x.toInt * y.toInt
  prod < -(2 ^ 63 : Int) || prod > 2 ^ 63 - 1

def divOverflows (x y : Int64) : Bool :=
  x == minVal && y == ⟨18446744073709551615⟩

/-! ### Tier 1: Proof-Carrying -/

@[inline] def addProof (x y : Int64) (_h : ¬(overflowsAdd x y = true)) : Int64 :=
  ⟨x.val + y.val⟩
@[inline] def subProof (x y : Int64) (_h : ¬(overflowsSub x y = true)) : Int64 :=
  ⟨x.val - y.val⟩
@[inline] def mulProof (x y : Int64) (_h : ¬(overflowsMul x y = true)) : Int64 :=
  ⟨x.val * y.val⟩
@[inline] def div (x y : Int64) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int64 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def rem (x y : Int64) (_h : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : Int64 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

/-! ### Tier 2: Wrapping -/

@[inline] def wrappingAdd (x y : Int64) : Int64 := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : Int64) : Int64 := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : Int64) : Int64 := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : Int64) : Int64 := ⟨0 - x.val⟩
@[inline] def wrappingDiv (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 :=
  fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)
@[inline] def wrappingRem (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 :=
  fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def saturatingAdd (x y : Int64) : Int64 :=
  let sum := x.val + y.val
  if (x.val ^^^ sum) &&& (y.val ^^^ sum) >= 9223372036854775808 then
    if x.val >= 9223372036854775808 then minVal else maxVal
  else ⟨sum⟩

@[inline] def saturatingSub (x y : Int64) : Int64 :=
  let diff := x.val - y.val
  if (x.val ^^^ y.val) &&& (x.val ^^^ diff) >= 9223372036854775808 then
    if x.val >= 9223372036854775808 then minVal else maxVal
  else ⟨diff⟩

@[inline] def saturatingMul (x y : Int64) : Int64 :=
  let prod := x.toInt * y.toInt
  if prod > 2 ^ 63 - 1 then maxVal
  else if prod < -(2 ^ 63 : Int) then minVal
  else ⟨x.val * y.val⟩

@[inline] def saturatingDiv (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 :=
  if divOverflows x y then maxVal
  else fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec)

@[inline] def saturatingRem (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 :=
  if divOverflows x y then ⟨0⟩
  else fromBitVec (BitVec.srem x.toBitVec y.toBitVec)

@[inline] def checkedAdd (x y : Int64) : Option Int64 :=
  if overflowsAdd x y then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : Int64) : Option Int64 :=
  if overflowsSub x y then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : Int64) : Option Int64 :=
  if overflowsMul x y then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : Int64) : Option Int64 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec))
@[inline] def checkedRem (x y : Int64) : Option Int64 :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some (fromBitVec (BitVec.srem x.toBitVec y.toBitVec))

@[inline] def overflowingAdd (x y : Int64) : Int64 × Bool :=
  (⟨x.val + y.val⟩, overflowsAdd x y)
@[inline] def overflowingSub (x y : Int64) : Int64 × Bool :=
  (⟨x.val - y.val⟩, overflowsSub x y)
@[inline] def overflowingMul (x y : Int64) : Int64 × Bool :=
  (⟨x.val * y.val⟩, overflowsMul x y)
@[inline] def overflowingDiv (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 × Bool :=
  if divOverflows x y then (minVal, true)
  else (fromBitVec (BitVec.sdiv x.toBitVec y.toBitVec), false)
@[inline] def overflowingRem (x y : Int64) (_h : y ≠ ⟨0⟩) : Int64 × Bool :=
  if divOverflows x y then (⟨0⟩, true)
  else (fromBitVec (BitVec.srem x.toBitVec y.toBitVec), false)

end Int64

/-! ================================================================ -/
/-! ## UWord Arithmetic                                               -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

@[inline] def addChecked (x y : UWord w) (_h : x.toNat + y.toNat < 2 ^ w) : UWord w := ⟨x.val + y.val⟩
@[inline] def subChecked (x y : UWord w) (_h : y.toNat ≤ x.toNat) : UWord w := ⟨x.val - y.val⟩
@[inline] def mulChecked (x y : UWord w) (_h : x.toNat * y.toNat < 2 ^ w) : UWord w := ⟨x.val * y.val⟩
@[inline] def div (x y : UWord w) (_h : y ≠ ⟨0⟩) : UWord w := ⟨x.val / y.val⟩
@[inline] def rem (x y : UWord w) (_h : y ≠ ⟨0⟩) : UWord w := ⟨x.val % y.val⟩

@[inline] def wrappingAdd (x y : UWord w) : UWord w := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : UWord w) : UWord w := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : UWord w) : UWord w := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : UWord w) : UWord w := ⟨0 - x.val⟩

@[inline] def saturatingAdd (x y : UWord w) : UWord w :=
  if x.toNat + y.toNat >= 2 ^ w then maxVal else ⟨x.val + y.val⟩
@[inline] def saturatingSub (x y : UWord w) : UWord w :=
  if x.toNat < y.toNat then minVal else ⟨x.val - y.val⟩
@[inline] def saturatingMul (x y : UWord w) : UWord w :=
  if x.toNat * y.toNat >= 2 ^ w then maxVal else ⟨x.val * y.val⟩

@[inline] def checkedAdd (x y : UWord w) : Option (UWord w) :=
  if x.toNat + y.toNat >= 2 ^ w then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : UWord w) : Option (UWord w) :=
  if x.toNat < y.toNat then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : UWord w) : Option (UWord w) :=
  if x.toNat * y.toNat >= 2 ^ w then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : UWord w) : Option (UWord w) :=
  if y == ⟨0⟩ then none else some ⟨x.val / y.val⟩
@[inline] def checkedRem (x y : UWord w) : Option (UWord w) :=
  if y == ⟨0⟩ then none else some ⟨x.val % y.val⟩

@[inline] def overflowingAdd (x y : UWord w) : UWord w × Bool :=
  (⟨x.val + y.val⟩, x.toNat + y.toNat >= 2 ^ w)
@[inline] def overflowingSub (x y : UWord w) : UWord w × Bool :=
  (⟨x.val - y.val⟩, x.toNat < y.toNat)
@[inline] def overflowingMul (x y : UWord w) : UWord w × Bool :=
  (⟨x.val * y.val⟩, x.toNat * y.toNat >= 2 ^ w)

end UWord

/-! ================================================================ -/
/-! ## IWord Arithmetic                                               -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

@[inline] def addProof (x y : IWord w) (_h : ¬(overflowsAdd x y = true)) : IWord w := ⟨x.val + y.val⟩
@[inline] def subProof (x y : IWord w) (_h : ¬(overflowsSub x y = true)) : IWord w := ⟨x.val - y.val⟩
@[inline] def mulProof (x y : IWord w) (_h : ¬(overflowsMul x y = true)) : IWord w := ⟨x.val * y.val⟩
@[inline] def div (x y : IWord w) (_hy : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : IWord w :=
  ⟨BitVec.sdiv x.toBitVec y.toBitVec⟩
@[inline] def rem (x y : IWord w) (_hy : y ≠ ⟨0⟩) (_hov : ¬(divOverflows x y = true)) : IWord w :=
  ⟨BitVec.srem x.toBitVec y.toBitVec⟩

@[inline] def wrappingAdd (x y : IWord w) : IWord w := ⟨x.val + y.val⟩
@[inline] def wrappingSub (x y : IWord w) : IWord w := ⟨x.val - y.val⟩
@[inline] def wrappingMul (x y : IWord w) : IWord w := ⟨x.val * y.val⟩
@[inline] def wrappingNeg (x : IWord w) : IWord w := ⟨0 - x.val⟩

@[inline] def saturatingAdd (x y : IWord w) : IWord w :=
  let sum := x.val + y.val
  if Word.Spec.signedAddOverflows x.val y.val then
    if x.val.msb then minVal else maxVal
  else ⟨sum⟩

@[inline] def saturatingSub (x y : IWord w) : IWord w :=
  let diff := x.val - y.val
  if Word.Spec.signedSubOverflows x.val y.val then
    if x.val.msb then minVal else maxVal
  else ⟨diff⟩

@[inline] def saturatingMul (x y : IWord w) : IWord w :=
  let prod := x.val * y.val
  if Word.Spec.signedMulOverflows x.val y.val then
    -- Determine direction: overflow is positive if sign(x) XOR sign(y) = positive
    if x.val.msb != y.val.msb then minVal else maxVal
  else ⟨prod⟩

@[inline] def checkedAdd (x y : IWord w) : Option (IWord w) :=
  if overflowsAdd x y then none else some ⟨x.val + y.val⟩
@[inline] def checkedSub (x y : IWord w) : Option (IWord w) :=
  if overflowsSub x y then none else some ⟨x.val - y.val⟩
@[inline] def checkedMul (x y : IWord w) : Option (IWord w) :=
  if overflowsMul x y then none else some ⟨x.val * y.val⟩
@[inline] def checkedDiv (x y : IWord w) : Option (IWord w) :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some ⟨BitVec.sdiv x.toBitVec y.toBitVec⟩
@[inline] def checkedRem (x y : IWord w) : Option (IWord w) :=
  if y == ⟨0⟩ then none
  else if divOverflows x y then none
  else some ⟨BitVec.srem x.toBitVec y.toBitVec⟩

@[inline] def overflowingAdd (x y : IWord w) : IWord w × Bool :=
  (⟨x.val + y.val⟩, overflowsAdd x y)
@[inline] def overflowingSub (x y : IWord w) : IWord w × Bool :=
  (⟨x.val - y.val⟩, overflowsSub x y)
@[inline] def overflowingMul (x y : IWord w) : IWord w × Bool :=
  (⟨x.val * y.val⟩, overflowsMul x y)
@[inline] def wrappingDiv (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w :=
  ⟨BitVec.sdiv x.toBitVec y.toBitVec⟩
@[inline] def wrappingRem (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w :=
  ⟨BitVec.srem x.toBitVec y.toBitVec⟩

-- FR-001.2a: Saturating: MIN / -1 = MAX
@[inline] def saturatingDiv (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w :=
  if divOverflows x y then maxVal
  else ⟨BitVec.sdiv x.toBitVec y.toBitVec⟩

-- FR-001.2b: MIN % -1 = 0 (fits, no saturation)
@[inline] def saturatingRem (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w :=
  if divOverflows x y then ⟨0⟩
  else ⟨BitVec.srem x.toBitVec y.toBitVec⟩

-- FR-001.2a: Overflowing: MIN / -1 = (MIN, true)
@[inline] def overflowingDiv (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w × Bool :=
  if divOverflows x y then (minVal, true)
  else (⟨BitVec.sdiv x.toBitVec y.toBitVec⟩, false)

-- FR-001.2b: Overflowing: MIN % -1 = (0, true)
@[inline] def overflowingRem (x y : IWord w) (_h : y ≠ ⟨0⟩) : IWord w × Bool :=
  if divOverflows x y then (⟨0⟩, true)
  else (⟨BitVec.srem x.toBitVec y.toBitVec⟩, false)

end IWord

end Radix
