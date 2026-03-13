# Word Module API Reference

> **Module**: `Radix.Word`
> **Source**: `Radix/Word/`

## Overview

The Word module provides fixed-width integer types (signed and unsigned) with multiple arithmetic modes and formal proofs of correctness. It is the foundational module of Radix — all other modules depend on it.

## Types

### Unsigned Integers

| Type | Internal Storage | Bit Width | Range |
|------|-----------------|-----------|-------|
| `Radix.UInt8` | `_root_.UInt8` | 8 | 0 to 255 |
| `Radix.UInt16` | `_root_.UInt16` | 16 | 0 to 65,535 |
| `Radix.UInt32` | `_root_.UInt32` | 32 | 0 to 4,294,967,295 |
| `Radix.UInt64` | `_root_.UInt64` | 64 | 0 to 18,446,744,073,709,551,615 |

### Signed Integers (Two's Complement)

| Type | Internal Storage | Bit Width | Range |
|------|-----------------|-----------|-------|
| `Radix.Int8` | `_root_.UInt8` | 8 | -128 to 127 |
| `Radix.Int16` | `_root_.UInt16` | 16 | -32,768 to 32,767 |
| `Radix.Int32` | `_root_.UInt32` | 32 | -2,147,483,648 to 2,147,483,647 |
| `Radix.Int64` | `_root_.UInt64` | 64 | -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807 |

### Platform-Width Integers

| Type | Internal Storage | Bit Width | Constraint |
|------|-----------------|-----------|------------|
| `Radix.UWord` | `BitVec w` | 32 or 64 | `PlatformWidth w` |
| `Radix.IWord` | `BitVec w` | 32 or 64 | `PlatformWidth w` |

## Conversions

### Type Conversions

```lean
@[inline] def toBuiltin (x : UInt32) : _root_.UInt32  -- To Lean 4 built-in
@[inline] def fromBuiltin (x : _root_.UInt32) : UInt32 -- From Lean 4 built-in
@[inline] def toBitVec (x : UInt32) : BitVec 32        -- To BitVec (Layer 3)
@[inline] def fromBitVec (x : BitVec 32) : UInt32      -- From BitVec
@[inline] def toNat (x : UInt32) : Nat                  -- To natural number
```

### Signed-Specific

```lean
@[inline] def toInt (x : Int32) : Int       -- Signed interpretation
@[inline] def fromInt (i : Int) : Int32     -- From Int (truncating)
@[inline] def slt (a b : Int32) : Bool      -- Signed less-than (zero-cost)
@[inline] def sle (a b : Int32) : Bool      -- Signed less-or-equal
@[inline] def sgt (a b : Int32) : Bool      -- Signed greater-than
@[inline] def sge (a b : Int32) : Bool      -- Signed greater-or-equal
```

## Arithmetic (per type)

All 10 types support the following operations. Shown here for `UInt32`:

### Tier 1: Proof-Carrying (Recommended)

```lean
@[inline] def addChecked (x y : UInt32) (h : x.toNat + y.toNat < 2^32) : UInt32
@[inline] def subChecked (x y : UInt32) (h : y.toNat ≤ x.toNat) : UInt32
@[inline] def mulChecked (x y : UInt32) (h : x.toNat * y.toNat < 2^32) : UInt32
```

### Tier 2: Wrapping

```lean
@[inline] def wrappingAdd (x y : UInt32) : UInt32
@[inline] def wrappingSub (x y : UInt32) : UInt32
@[inline] def wrappingMul (x y : UInt32) : UInt32
```

> **Note:** No `wrappingDiv` or `wrappingRem` — division by zero cannot wrap safely. Use `checkedDiv`.

### Tier 2: Saturating

```lean
@[inline] def saturatingAdd (x y : UInt32) : UInt32  -- Clamps to MAX on overflow
@[inline] def saturatingSub (x y : UInt32) : UInt32  -- Clamps to 0 on underflow
@[inline] def saturatingMul (x y : UInt32) : UInt32  -- Clamps to MAX on overflow
```

### Tier 2: Checked

```lean
@[inline] def checkedAdd (x y : UInt32) : Option UInt32  -- none on overflow
@[inline] def checkedSub (x y : UInt32) : Option UInt32  -- none on underflow
@[inline] def checkedMul (x y : UInt32) : Option UInt32  -- none on overflow
@[inline] def checkedDiv (x y : UInt32) : Option UInt32  -- none on y=0
@[inline] def checkedRem (x y : UInt32) : Option UInt32  -- none on y=0
```

### Tier 2: Overflowing

```lean
@[inline] def overflowingAdd (x y : UInt32) : UInt32 × Bool
@[inline] def overflowingSub (x y : UInt32) : UInt32 × Bool
@[inline] def overflowingMul (x y : UInt32) : UInt32 × Bool
```

## Width Conversions (`Word.Conv`)

```lean
-- Zero-extend (unsigned widening)
@[inline] def UInt8.toUInt16 (x : UInt8) : UInt16
@[inline] def UInt8.toUInt32 (x : UInt8) : UInt32
@[inline] def UInt16.toUInt32 (x : UInt16) : UInt32
@[inline] def UInt32.toUInt64 (x : UInt32) : UInt64

-- Truncate (narrowing)
@[inline] def UInt16.toUInt8 (x : UInt16) : UInt8
@[inline] def UInt32.toUInt16 (x : UInt32) : UInt16
@[inline] def UInt64.toUInt32 (x : UInt64) : UInt32

-- Sign-extend (signed widening)
@[inline] def Int8.toInt16 (x : Int8) : Int16
@[inline] def Int8.toInt32 (x : Int8) : Int32
@[inline] def Int16.toInt32 (x : Int16) : Int32
@[inline] def Int32.toInt64 (x : Int32) : Int64

-- Register-internal sign extension (Wasm support)
@[inline] def UInt32.signExtend8 (x : UInt32) : UInt32
@[inline] def UInt32.signExtend16 (x : UInt32) : UInt32
@[inline] def UInt64.signExtend8 (x : UInt64) : UInt64
@[inline] def UInt64.signExtend16 (x : UInt64) : UInt64
@[inline] def UInt64.signExtend32 (x : UInt64) : UInt64
```

## Proofs (`Word.Lemmas`)

### Ring Properties (`Word.Lemmas.Ring`)

All 10 types have proven:
- Commutativity: `wrappingAdd x y = wrappingAdd y x`
- Associativity: `wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z)`
- Identity: `wrappingAdd x 0 = x`, `wrappingMul x 1 = x`
- Distributivity: `wrappingMul x (wrappingAdd y z) = wrappingAdd (wrappingMul x y) (wrappingMul x z)`

### Overflow Properties (`Word.Lemmas.Overflow`)

- Wrapping spec: wrappingAdd matches `(x + y) % 2^n`
- Checked none iff overflow
- Saturating bounds clamping
- Overflowing flag correctness
- Signed `MIN / -1` and `MIN % -1` handling

### BitVec Equivalence (`Word.Lemmas.BitVec`)

- Round-trip: `fromBitVec (toBitVec x) = x` for all 10 types
- Operation equivalence: `wrappingAdd.toBitVec = BitVec.add`

### Conversion Properties (`Word.Lemmas.Conv`)

- Zero-extend preserves value
- Sign-extend preserves signed interpretation
- Truncation is lossy
- Cast bit-preserving
- Register sign-extend spec: `signExtend8.toBitVec = BitVec.signExtend 32 (x.toBitVec.truncate 8)`

## Related Documents

- [Bit](bit.md) — Bitwise operations on these types
- [Architecture: Components](../../en/architecture/components.md#word) — Module overview
