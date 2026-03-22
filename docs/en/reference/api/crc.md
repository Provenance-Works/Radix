# CRC Module API Reference

> **Module**: `Radix.CRC`
> **Source**: `Radix/CRC/`

## Overview

Provides CRC (Cyclic Redundancy Check) computation with both reference and optimized implementations. Includes CRC-32 (ISO 3309 / ITU-T V.42) and CRC-16/CCITT variants. The spec layer models CRC as polynomial division over GF(2), while the ops layer provides a 256-entry table-driven implementation. A streaming API allows incremental computation over chunked data.

## Specification (`CRC.Spec`)

Mathematical model based on GF(2) polynomial arithmetic:

```lean
structure CRCParams where
  poly   : Nat        -- Generator polynomial
  init   : Nat        -- Initial register value
  width  : Nat        -- Bit width (16, 32, etc.)

def crcCompute (params : CRCParams) (data : List UInt8) : Nat
```

The spec-level `crcCompute` processes data bit-by-bit as polynomial long division over GF(2), serving as the ground truth for verification.

## Operations — CRC-32 (`CRC.Ops`)

### Constants

```lean
def CRC32.poly : UInt32         -- 0xEDB88320 (reflected polynomial)
def CRC32.initVal : UInt32      -- 0xFFFFFFFF
```

### Lookup Table

```lean
def CRC32.table : Array UInt32   -- 256-entry precomputed table
```

The table is computed at initialization from `CRC32.poly`. Each entry `table[i]` holds the CRC of the single byte `i`.

### Byte-Level Update

```lean
def CRC32.updateByte (crc : UInt32) (byte : UInt8) : UInt32
```

Single byte update: `table[(crc XOR byte) AND 0xFF] XOR (crc >>> 8)`.

### One-Shot API

```lean
def CRC32.compute (data : ByteArray) : Radix.UInt32
```

Computes the CRC-32 of the entire input in one call. Equivalent to `finalize (update init data)`.

### Streaming API

```lean
def CRC32.init : UInt32
def CRC32.update (crc : UInt32) (data : ByteArray) : UInt32
def CRC32.finalize (crc : UInt32) : Radix.UInt32
```

For incremental computation over chunked data:

```lean
-- Example: streaming CRC over two chunks
let crc := CRC32.init
let crc := CRC32.update crc chunk1
let crc := CRC32.update crc chunk2
let result := CRC32.finalize crc
```

### Reference Implementation

```lean
def CRC32.computeNaive (data : ByteArray) : Radix.UInt32
```

Bit-by-bit reference implementation matching the spec. Used for testing and verification, not performance.

## Operations — CRC-16 (`CRC.Ops`)

Same API pattern for CRC-16/CCITT:

```lean
def CRC16.poly : UInt16          -- 0x1021 (CCITT polynomial)
def CRC16.initVal : UInt16       -- 0xFFFF
def CRC16.table : Array UInt16   -- 256-entry precomputed table
def CRC16.updateByte (crc : UInt16) (byte : UInt8) : UInt16
def CRC16.compute (data : ByteArray) : Radix.UInt16
def CRC16.init : UInt16
def CRC16.update (crc : UInt16) (data : ByteArray) : UInt16
def CRC16.finalize (crc : UInt16) : Radix.UInt16
def CRC16.computeNaive (data : ByteArray) : Radix.UInt16
```

## Proofs (`CRC.Lemmas`)

### Table Properties

- `CRC32.table.size = 256`
- `CRC16.table.size = 256`
- Table entries are consistent with bit-by-bit computation

### Streaming Consistency

- `CRC32.compute data = CRC32.finalize (CRC32.update CRC32.init data)`
- `CRC32.update crc (a ++ b) = CRC32.update (CRC32.update crc a) b`

### Reference Equivalence

- `CRC32.compute data = CRC32.computeNaive data`
- `CRC16.compute data = CRC16.computeNaive data`

### GF(2) Algebra

- Linearity properties of the CRC polynomial model
- Spec-to-ops correspondence proofs

## Examples

```lean
-- One-shot CRC-32
let data := ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]   -- "Hello"
#eval CRC32.compute data

-- Streaming CRC-32 over two chunks
let crc := CRC32.init
let crc := CRC32.update crc (ByteArray.mk #[0x48, 0x65])     -- "He"
let crc := CRC32.update crc (ByteArray.mk #[0x6C, 0x6C, 0x6F]) -- "llo"
#eval CRC32.finalize crc    -- same result as one-shot

-- CRC-16/CCITT
let data := ByteArray.mk #[0x31, 0x32, 0x33, 0x34]           -- "1234"
#eval CRC16.compute data
```

## Related Documents

- [Binary](binary.md) — Binary serialization and parsing
- [Bytes](bytes.md) — Byte-level data handling
