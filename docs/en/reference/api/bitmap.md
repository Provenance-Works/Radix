# Bitmap Module API Reference

> **Module**: `Radix.Bitmap`
> **Source**: `Radix/Bitmap/`

## Overview

Provides a dense, verified bitmap backed by `Array Radix.UInt64` (64 bits per word). All single-bit operations are O(1) via word-index and bit-offset computation. Bulk operations (union, intersection, etc.) require matching bitmap sizes and operate word-at-a-time. Includes a spec layer modeling bitmaps as `Nat → Bool` functions.

## Specification (`Bitmap.Spec`)

Abstract specification as a pure function from bit index to boolean:

```lean
def BitmapState := Nat → Bool

def setSpec (bm : BitmapState) (idx : Nat) : BitmapState
def clearSpec (bm : BitmapState) (idx : Nat) : BitmapState
def toggleSpec (bm : BitmapState) (idx : Nat) : BitmapState
def popcountSpec (bm : BitmapState) (n : Nat) : Nat
def findFirstSetSpec (bm : BitmapState) (n : Nat) : Option Nat
```

## Operations (`Bitmap.Ops`)

### Structure

```lean
structure Bitmap where
  numBits : Nat
  words   : Array Radix.UInt64
  hSize   : words.size = (numBits + 63) / 64
```

The `hSize` invariant guarantees the word array has exactly enough 64-bit words to cover `numBits`.

### Construction

```lean
def Bitmap.zeros (n : Nat) : Bitmap     -- All bits clear
def Bitmap.ones (n : Nat) : Bitmap      -- All bits set (up to numBits)
```

### Single-Bit Operations (O(1))

```lean
def Bitmap.test (bm : Bitmap) (idx : Nat) : Bool       -- Read bit at index
def Bitmap.set (bm : Bitmap) (idx : Nat) : Bitmap       -- Set bit to 1
def Bitmap.clear (bm : Bitmap) (idx : Nat) : Bitmap     -- Clear bit to 0
def Bitmap.toggle (bm : Bitmap) (idx : Nat) : Bitmap    -- Flip bit
```

Each operation computes `wordIdx := idx / 64` and `bitIdx := idx % 64`, then applies the corresponding bitwise operation on the target word.

### Scanning

```lean
def Bitmap.popcount (bm : Bitmap) : Nat                  -- Total number of set bits
def Bitmap.findFirstSet (bm : Bitmap) : Option Nat        -- Index of lowest set bit
def Bitmap.findFirstClear (bm : Bitmap) : Option Nat      -- Index of lowest clear bit
```

### Bulk Operations

All bulk operations require matching bitmap sizes:

```lean
def Bitmap.union (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.intersection (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.difference (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.complement (bm : Bitmap) : Bitmap
```

- `union` — bitwise OR of all words
- `intersection` — bitwise AND of all words
- `difference` — `a AND (NOT b)`
- `complement` — bitwise NOT (masks trailing bits in the last word)

### Queries

```lean
def Bitmap.isEmpty (bm : Bitmap) : Bool      -- All bits clear?
def Bitmap.isFull (bm : Bitmap) : Bool        -- All bits set?
def Bitmap.isDisjoint (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bool
```

`isDisjoint` returns `true` when `intersection a b` has no set bits.

## Proofs (`Bitmap.Lemmas`)

### Structural Invariants

- Construction preserves `hSize`: `(Bitmap.zeros n).words.size = (n + 63) / 64`
- All single-bit and bulk operations preserve `numBits` and `hSize`

### Spec-Level Round-Trip

- `set` / `clear` round-trip: `(bm.set idx).clear idx = bm.clear idx`
- `toggle` involution: `(bm.toggle idx).toggle idx = bm`
- `test` after `set`: `(bm.set idx).test idx = true`
- `test` after `clear`: `(bm.clear idx).test idx = false`

### Bulk Operation Properties

- `union` commutativity and associativity
- `intersection` commutativity and associativity
- `complement (complement bm) = bm`

## Examples

```lean
-- Create a 128-bit bitmap and manipulate bits
let bm := Bitmap.zeros 128
let bm := bm.set 0
let bm := bm.set 42
let bm := bm.set 127
#eval bm.popcount              -- 3
#eval bm.test 42               -- true
#eval bm.findFirstSet          -- some 0

-- Bulk operations
let a := Bitmap.zeros 64 |>.set 0 |>.set 1
let b := Bitmap.zeros 64 |>.set 1 |>.set 2
let c := Bitmap.intersection a b (by rfl)
#eval c.test 1                 -- true
#eval c.test 0                 -- false
```

## Related Documents

- [Bit](bit.md) — Underlying bitwise operations on integer types
- [Word](word.md) — `Radix.UInt64` type used as the bitmap word
