# Bytes Module API Reference

> **Module**: `Radix.Bytes`
> **Source**: `Radix/Bytes/`

## Overview

Provides endianness-aware byte manipulation: byte swapping, big/little-endian conversions, and bounds-checked byte array views.

## Byte Order (`Bytes.Order`)

### Byte Swap

```lean
@[inline] def UInt16.bswap (x : UInt16) : UInt16  -- Reverse 2 bytes
@[inline] def UInt32.bswap (x : UInt32) : UInt32  -- Reverse 4 bytes
@[inline] def UInt64.bswap (x : UInt64) : UInt64  -- Reverse 8 bytes
```

### Endianness Conversion

Defined for all unsigned and signed multi-byte types:

```lean
def UInt32.toBigEndian (x : UInt32) : UInt32
def UInt32.fromBigEndian (x : UInt32) : UInt32
def UInt32.toLittleEndian (x : UInt32) : UInt32
def UInt32.fromLittleEndian (x : UInt32) : UInt32
def UInt32.toEndian (endian : Endian) (x : UInt32) : UInt32  -- Generic
def UInt32.fromEndian (endian : Endian) (x : UInt32) : UInt32

-- Also available for: UInt16, UInt64, Int16, Int32, Int64
```

### Native Endianness Detection

```lean
def nativeEndian : Endian  -- Returns .little on x86_64
```

## ByteSlice (`Bytes.Slice`)

A bounds-checked, zero-copy view into a `ByteArray`:

```lean
structure ByteSlice where
  data : ByteArray
  start : Nat
  len : Nat
  valid : start + len ≤ data.size
```

### Tier 1: Proof-Carrying Read

```lean
def readU8 (s : ByteSlice) (offset : Nat) (h : offset < s.len) : UInt8
def readU16 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 2 ≤ s.len) : UInt16
def readU32 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 4 ≤ s.len) : UInt32
def readU64 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 8 ≤ s.len) : UInt64
```

### Tier 2: Checked Read

```lean
def checkedReadU8 (s : ByteSlice) (offset : Nat) : Option UInt8
def checkedReadU16 (s : ByteSlice) (offset : Nat) (endian : Endian) : Option UInt16
-- etc.
```

### Slicing

```lean
def subslice (s : ByteSlice) (offset len : Nat) (h : offset + len ≤ s.len) : ByteSlice
def checkedSubslice (s : ByteSlice) (offset len : Nat) : Option ByteSlice
```

## Proofs (`Bytes.Lemmas`)

- **bswap involution**: `bswap (bswap x) = x` for all widths
- **BE round-trip**: `fromBigEndian (toBigEndian x) = x`
- **LE round-trip**: `fromLittleEndian (toLittleEndian x) = x`
- **BE/LE relationship**: `toBigEndian = bswap ∘ toLittleEndian`
- **Signed BE round-trip**: for `Int16`, `Int32`, `Int64`
- **ByteSlice properties**: `subslice_len`, `zeros_len`, `empty_len`, `ofByteArray_len`

## Related Documents

- [Word](word.md) — Integer types for endianness conversion
- [Memory](memory.md) — Buffer-based read/write with endianness
