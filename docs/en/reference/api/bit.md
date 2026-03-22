# Bit Module API Reference

> **Module**: `Radix.Bit`
> **Source**: `Radix/Bit/`

## Overview

Provides bitwise operations, bit scanning, and bit field manipulation for all 10 Radix integer types. All shift/rotate operations normalize the count by `count % bitWidth` (Rust semantics).

## Bitwise Operations (`Bit.Ops`)

All operations are `@[inline]` and defined for all 10 types. Examples use `UInt32`:

```lean
@[inline] def band (x y : UInt32) : UInt32       -- Bitwise AND
@[inline] def bor  (x y : UInt32) : UInt32       -- Bitwise OR
@[inline] def bxor (x y : UInt32) : UInt32       -- Bitwise XOR
@[inline] def bnot (x : UInt32) : UInt32          -- Bitwise NOT

-- Operator instances: &&&, |||, ^^^, ~~~
```

### Shift Operations

```lean
@[inline] def shl (x : UInt32) (count : UInt32) : UInt32        -- Left shift
@[inline] def shrLogical (x : UInt32) (count : UInt32) : UInt32  -- Logical right shift
@[inline] def shrArith (x : UInt32) (count : UInt32) : UInt32    -- Arithmetic right shift (sign-preserving)
```

> **Important:** When `count >= bitWidth`, the shift amount is `count % bitWidth` (FR-002.1a).

### Rotate Operations

```lean
@[inline] def rotl (x : UInt32) (count : UInt32) : UInt32  -- Rotate left
@[inline] def rotr (x : UInt32) (count : UInt32) : UInt32  -- Rotate right
```

## Bit Scanning (`Bit.Scan`)

```lean
def clz (x : UInt32) : Nat        -- Count leading zeros (0 to 32)
def ctz (x : UInt32) : Nat        -- Count trailing zeros (0 to 32)
def popcount (x : UInt32) : Nat   -- Population count / Hamming weight (0 to 32)
def bitReverse (x : UInt32) : UInt32  -- Reverse bit order
def hammingDistance (x y : UInt32) : UInt32  -- Hamming distance = popcount(x XOR y)
```

## Bit Field Operations (`Bit.Field`)

```lean
def testBit (x : UInt32) (bit : Nat) : Bool           -- Test bit at position
def setBit (x : UInt32) (bit : Nat) : UInt32           -- Set bit to 1
def clearBit (x : UInt32) (bit : Nat) : UInt32         -- Clear bit to 0
def toggleBit (x : UInt32) (bit : Nat) : UInt32        -- Toggle bit

-- Bit field extraction and insertion with proof of valid range
def extractBits (x : UInt32) (lo hi : Nat) (h : lo < hi ∧ hi ≤ 32) : UInt32
def insertBits (dest val : UInt32) (lo hi : Nat) (h : lo < hi ∧ hi ≤ 32) : UInt32
```

## Proofs (`Bit.Lemmas`)

Proven for all 10 types:

### Boolean Algebra
- Commutativity: `band x y = band y x`, `bor x y = bor y x`, `bxor x y = bxor y x`
- Associativity: `band (band x y) z = band x (band y z)`
- Identity: `band x (allOnes) = x`, `bor x 0 = x`
- Annihilation: `band x 0 = 0`, `bor x (allOnes) = allOnes`
- Self-inverse: `bxor x x = 0`, `bnot (bnot x) = x`
- De Morgan: `bnot (band x y) = bor (bnot x) (bnot y)`

### BitVec Spec Equivalence
- All operations match their `BitVec` specification in `Bit.Spec`

### Shift Properties
- Zero shift identity: `shl x 0 = x`

### Scan Properties
- `popcount 0 = 0`
- `popcount (allOnes) = bitWidth`
- `bitReverse (bitReverse x) = x` (involution)

### Field Round-Trip
- `extractBits (insertBits dest val lo hi h) lo hi h = val` (when val fits)

## Related Documents

- [Word](word.md) — Integer types these operations apply to
- [Architecture: Components](../../architecture/components.md) — Module overview
