# Memory Module API Reference

> **Module**: `Radix.Memory`
> **Source**: `Radix/Memory/`

## Overview

Provides an abstract memory model built on Lean 4's `ByteArray`. Includes proof-carrying buffers, pointer abstractions, packed struct layout computation, and interval-style region algebra for memory-map reasoning. All operations are GC-friendly — no manual memory management.

## Buffer (`Memory.Model`)

```lean
structure Buffer where
  bytes : ByteArray
```

### Construction

```lean
def Buffer.zeros (size : Nat) : Buffer      -- Zero-initialized buffer
def Buffer.empty : Buffer                     -- Empty (0 bytes)
def Buffer.ofByteArray (ba : ByteArray) : Buffer
```

### Tier 1: Proof-Carrying API

```lean
def Buffer.readU8 (buf : Buffer) (offset : Nat) (h : offset < buf.bytes.size) : UInt8
def Buffer.writeU8 (buf : Buffer) (offset : Nat) (val : UInt8) (h : offset < buf.bytes.size) : Buffer

-- Multi-byte with endianness (separate BE/LE functions)
def Buffer.readU16BE (buf : Buffer) (offset : Nat) (h : offset + 2 ≤ buf.bytes.size) : UInt16
def Buffer.readU16LE (buf : Buffer) (offset : Nat) (h : offset + 2 ≤ buf.bytes.size) : UInt16
def Buffer.readU32BE (buf : Buffer) (offset : Nat) (h : offset + 4 ≤ buf.bytes.size) : UInt32
def Buffer.readU32LE (buf : Buffer) (offset : Nat) (h : offset + 4 ≤ buf.bytes.size) : UInt32
def Buffer.readU64BE (buf : Buffer) (offset : Nat) (h : offset + 8 ≤ buf.bytes.size) : UInt64
def Buffer.readU64LE (buf : Buffer) (offset : Nat) (h : offset + 8 ≤ buf.bytes.size) : UInt64

def Buffer.writeU16BE (buf : Buffer) (offset : Nat) (val : UInt16) (h : offset + 2 ≤ buf.bytes.size) : Buffer
def Buffer.writeU16LE (buf : Buffer) (offset : Nat) (val : UInt16) (h : offset + 2 ≤ buf.bytes.size) : Buffer
def Buffer.writeU32BE (buf : Buffer) (offset : Nat) (val : UInt32) (h : offset + 4 ≤ buf.bytes.size) : Buffer
def Buffer.writeU32LE (buf : Buffer) (offset : Nat) (val : UInt32) (h : offset + 4 ≤ buf.bytes.size) : Buffer
def Buffer.writeU64BE (buf : Buffer) (offset : Nat) (val : UInt64) (h : offset + 8 ≤ buf.bytes.size) : Buffer
def Buffer.writeU64LE (buf : Buffer) (offset : Nat) (val : UInt64) (h : offset + 8 ≤ buf.bytes.size) : Buffer
```

### Tier 2: Checked API

```lean
def Buffer.checkedReadU8 (buf : Buffer) (offset : Nat) : Option UInt8
def Buffer.checkedWriteU8 (buf : Buffer) (offset : Nat) (val : UInt8) : Option Buffer
-- etc. for U16, U32, U64
```

## Pointer Abstraction (`Memory.Ptr`)

```lean
structure Ptr (n : Nat) where
  buf : Buffer
  offset : Nat
  h : offset + n ≤ buf.size
```

### Operations

```lean
def Ptr.ofBuffer (buf : Buffer) (offset : Nat) (h : offset + n ≤ buf.size) : Ptr n
def Ptr.advance (p : Ptr n) (delta : Nat) (h : p.offset + delta + n ≤ p.buf.size) : Ptr n
def Ptr.retreat (p : Ptr n) (delta : Nat) (h : delta ≤ p.offset) : Ptr n
def Ptr.readU8 (p : Ptr n) (h : 1 ≤ n) : UInt8
def Ptr.readU16 (p : Ptr n) (endian : Endian) (h : 2 ≤ n) : UInt16
def Ptr.readU32 (p : Ptr n) (endian : Endian) (h : 4 ≤ n) : UInt32
def Ptr.readU64 (p : Ptr n) (endian : Endian) (h : 8 ≤ n) : UInt64
```

## Layout (`Memory.Layout`)

```lean
structure FieldDesc where
  name : String
  offset : Nat
  size : Nat

structure LayoutDesc where
  fields : List FieldDesc
  totalSize : Nat
```

### Operations

```lean
def LayoutDesc.appendField (layout : LayoutDesc) (name : String) (size : Nat) : LayoutDesc
def LayoutDesc.appendAligned (layout : LayoutDesc) (name : String) (size align : Nat) : LayoutDesc
def LayoutDesc.isNonOverlapping (layout : LayoutDesc) : Bool
def LayoutDesc.allFieldsFit (layout : LayoutDesc) : Bool
```

## Specification (`Memory.Spec`)

```lean
structure Region where
  start : Nat
  size : Nat

def Region.endOffset (r : Region) : Nat
def Region.intersects (a b : Region) : Prop
def Region.disjoint (a b : Region) : Prop
def Region.adjacent (a b : Region) : Prop
def Region.mergeable (a b : Region) : Prop
def Region.contains (outer inner : Region) : Prop
def Region.inBounds (r : Region) (addr : Nat) : Prop
def Region.span (a b : Region) : Region
def Region.intersection (a b : Region) : Region
def Region.union? (a b : Region) : Option Region
def Region.difference (a b : Region) : List Region
def isAligned (addr align : Nat) : Prop
```

### Region Algebra Notes

- `span` returns the smallest interval containing both input regions.
- `intersection` returns a zero-length region at the overlap boundary when the inputs do not overlap.
- `union?` succeeds only when two regions overlap or are exactly adjacent.
- `difference` returns zero, one, or two residual regions because subtracting one interval from another can split the source.

## Proofs (`Memory.Lemmas`)

- **Buffer size preservation**: `(Buffer.zeros n).size = n`, `(buf.writeU8 ..).size = buf.size`
- **Region disjointness**: commutativity, `empty_left`, `empty_right`, `intersects_comm`, `adjacent_comm`
- **Region algebra**: `span_contains_left`, `span_contains_right`, `span_comm`, `intersection_comm`, `union?_isSome_iff_mergeable`, `span_least_upper_bound`
- **Alignment**: `isAligned_zero`, `isAligned_mul`
- **Layout**: `empty_totalSize`, `appendField_totalSize`
- **Checked API**: `checkedReadU8_some` (when in bounds), `checkedReadU8_none` (when out of bounds)

## Related Documents

- [Bytes](bytes.md) — ByteSlice for zero-copy views
- [Binary](binary.md) — Format-driven memory access
