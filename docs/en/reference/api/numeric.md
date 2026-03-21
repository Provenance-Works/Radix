# Numeric Typeclasses API Reference

> **Module**: `Radix.Word.Numeric`
> **Source**: `Radix/Word/Numeric.lean`, `Radix/Word/Lemmas/Numeric.lean`

## Overview

Generic numeric typeclasses that abstract over all 10 integer types in Radix. Enables writing width-generic code once instead of duplicating logic for each concrete type. Three typeclasses cover unsigned bounds, signed bounds, and bitwise operations.

## Typeclasses

### `BoundedUInt`

Generic unsigned fixed-width integer trait. Extends `LawfulFixedWidth`.

```lean
class BoundedUInt (α : Type) extends LawfulFixedWidth α where
  minVal        : α                    -- Minimum value (always 0)
  maxVal        : α                    -- Maximum value (2^bitWidth - 1)
  toNat         : α → Nat             -- Convert to natural number
  wrappingAdd   : α → α → α           -- (x + y) mod 2^bitWidth
  wrappingSub   : α → α → α           -- (x - y) mod 2^bitWidth
  wrappingMul   : α → α → α           -- (x * y) mod 2^bitWidth
  saturatingAdd : α → α → α           -- min(x + y, maxVal)
  saturatingSub : α → α → α           -- max(x - y, 0)
  checkedAdd    : α → α → Option α    -- none on overflow
  checkedSub    : α → α → Option α    -- none on underflow
  checkedMul    : α → α → Option α    -- none on overflow
```

**Instances**: `UInt8`, `UInt16`, `UInt32`, `UInt64`

### `BoundedInt`

Generic signed fixed-width integer trait (two's complement). Extends `FixedWidth`.

```lean
class BoundedInt (α : Type) extends FixedWidth α, Add α, Sub α, Mul α, Neg α where
  minVal   : α             -- Minimum value (-2^(bitWidth-1))
  maxVal   : α             -- Maximum value (2^(bitWidth-1) - 1)
  toInt    : α → Int       -- Two's complement interpretation
  isNeg    : α → Bool      -- MSB = 1
  fromInt  : Int → α       -- Truncating conversion from Int
```

**Instances**: `Int8`, `Int16`, `Int32`, `Int64`

### `BitwiseOps`

Generic bitwise operations trait. Extends `FixedWidth`.

```lean
class BitwiseOps (α : Type) extends FixedWidth α where
  band     : α → α → α        -- Bitwise AND
  bor      : α → α → α        -- Bitwise OR
  bxor     : α → α → α        -- Bitwise XOR
  bnot     : α → α            -- Bitwise NOT
  testBit  : α → Nat → Bool   -- Test specific bit position
  popcount : α → α            -- Population count
```

**Instances**: `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Int8`, `Int16`, `Int32`, `Int64`

## Generic Utility Functions

```lean
def genericZero {α : Type} [BoundedUInt α] : α           -- Zero (minVal)
def genericMaxVal {α : Type} [BoundedUInt α] : α         -- Maximum value
def genericPopcount {α : Type} [BitwiseOps α] (x : α) : α  -- Population count
def isZero {α : Type} [BoundedUInt α] (x : α) : Bool     -- Check if zero
def isMax {α : Type} [BoundedUInt α] (x : α) : Bool      -- Check if max value
```

## Verified Properties (`Word.Lemmas.Numeric`)

| Theorem | Statement |
|---------|-----------|
| `wrappingAdd_minVal` | `wrappingAdd x minVal = x` (additive identity) |
| `wrappingAdd_comm` | `wrappingAdd x y = wrappingAdd y x` (commutativity) |
| `minVal_le_maxVal` | `toNat minVal ≤ toNat maxVal` (unsigned bounds ordering) |
| `BoundedInt.minVal_le_maxVal` | `toInt minVal ≤ toInt maxVal` (signed bounds ordering, bitWidth > 0) |

## Usage Example

```lean
import Radix.Word.Numeric
open Radix

-- Generic function that works with any unsigned integer width
def showBounds {α : Type} [inst : BoundedUInt α] (name : String) : IO Unit := do
  IO.println s!"{name}: min={inst.toNat inst.minVal}, max={inst.toNat inst.maxVal}"

-- Use with concrete types
#eval showBounds (α := UInt8)  "UInt8"   -- UInt8: min=0, max=255
#eval showBounds (α := UInt32) "UInt32"  -- UInt32: min=0, max=4294967295

-- Generic popcount via BitwiseOps
def countOnes {α : Type} [BitwiseOps α] (x : α) : α := BitwiseOps.popcount x
```

## Architecture

- **Layer 2** (Verified Implementation): Typeclass definitions and instances in `Radix.Word.Numeric`
- **Layer 3** (Verified Specification): Proofs in `Radix.Word.Lemmas.Numeric`

Note: Numeric typeclasses do not have a separate Layer 3 Spec module because they are inherently implementation-level abstractions (typeclasses over concrete types). The specification obligations are inherited from `LawfulFixedWidth` and `FixedWidth`.
