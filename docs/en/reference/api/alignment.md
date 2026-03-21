# Alignment Module API Reference

> **Module**: `Radix.Alignment`
> **Source**: `Radix/Alignment/`

## Overview

Provides address and offset alignment operations for systems programming. Supports both general-purpose modular alignment and optimized bitwise fast paths for power-of-two alignments. Includes a typeclass for associating alignment requirements with types, and a full set of verified lemmas guaranteeing correctness.

## Specification (`Alignment.Spec`)

Pure mathematical definitions used as ground truth for verification:

```lean
def isAligned (offset align : Nat) : Prop      -- offset is divisible by align
def alignUp (offset align : Nat) : Nat          -- Round up to next multiple of align
def alignDown (offset align : Nat) : Nat        -- Round down to previous multiple of align
def isPowerOfTwo (n : Nat) : Prop               -- n is a power of two
def alignPadding (offset align : Nat) : Nat     -- Bytes needed to reach next aligned offset
```

## Operations (`Alignment.Ops`)

Executable implementations matching the spec:

### Core Alignment

```lean
def isAligned (offset align : Nat) : Bool       -- Check divisibility
def alignUp (offset align : Nat) : Nat          -- Round up to next multiple
def alignDown (offset align : Nat) : Nat        -- Round down to previous multiple
def alignPadding (offset align : Nat) : Nat     -- Padding to next aligned offset
def isPowerOfTwo (n : Nat) : Bool               -- Check power-of-two property
```

### Power-of-Two Fast Paths

Bitwise implementations that avoid division when the alignment is a known power of two:

```lean
def alignUpPow2 (offset align : Nat) : Nat      -- (offset + align - 1) &&& ~~~(align - 1)
def alignDownPow2 (offset align : Nat) : Nat     -- offset &&& ~~~(align - 1)
def isAlignedPow2 (offset align : Nat) : Bool    -- offset &&& (align - 1) == 0
```

> **Note:** These functions assume `align` is a power of two. Behavior is undefined for non-power-of-two values.

### Type Alignment Constants

Standard alignment values for common integer types:

```lean
def alignmentOfU8  : Nat    -- 1
def alignmentOfU16 : Nat    -- 2
def alignmentOfU32 : Nat    -- 4
def alignmentOfU64 : Nat    -- 8
```

### Typeclass

```lean
class HasAlignment (α : Type) where
  alignment : Nat

def alignmentOf (α : Type) [HasAlignment α] : Nat
```

Allows generic code to query the natural alignment of a type:

```lean
-- Example usage
#eval alignmentOf Radix.UInt32    -- 4
#eval alignmentOf Radix.UInt64    -- 8
```

## Proofs (`Alignment.Lemmas`)

### Sandwich Properties

- `alignUp_ge`: `offset ≤ alignUp offset align`
- `alignDown_le`: `alignDown offset align ≤ offset`
- `alignDown_le_alignUp`: `alignDown offset align ≤ alignUp offset align`

### Alignment Correctness

- `alignUp_isAligned`: `isAligned (alignUp offset align) align`
- `isAligned_zero`: `isAligned 0 align`
- `isAligned_mul`: `isAligned (n * align) align`

### Padding and Equivalence

- `alignPadding_spec`: `alignUp offset align = offset + alignPadding offset align`
- `pow2_equivalence`: `isPowerOfTwo align → alignUpPow2 offset align = alignUp offset align`

## Examples

```lean
-- Basic alignment operations
#eval Radix.Alignment.Ops.alignUp 13 4        -- 16
#eval Radix.Alignment.Ops.alignDown 13 4      -- 12
#eval Radix.Alignment.Ops.alignPadding 13 4   -- 3
#eval Radix.Alignment.Ops.isAligned 16 4       -- true

-- Power-of-two fast paths
#eval Radix.Alignment.Ops.alignUpPow2 13 4    -- 16
#eval Radix.Alignment.Ops.isAlignedPow2 16 8  -- true
```

## Related Documents

- [Memory](memory.md) — Buffer and layout operations that depend on alignment
- [Memory Pool](memorypool.md) — Allocators using aligned allocation
