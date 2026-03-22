# Quickstart

> **Audience**: Users

Get Radix working in under 5 minutes.

## 1. Import Radix

```lean
import Radix
open Radix
```

## 2. Integer Arithmetic

```lean
-- Wrapping arithmetic (mod 2^n)
#eval UInt32.wrappingAdd 4000000000 4000000000  -- 3705032704

-- Saturating arithmetic (clamp to bounds)
#eval UInt8.saturatingAdd 200 100  -- 255

-- Checked arithmetic (returns Option)
#eval UInt8.checkedAdd 200 100     -- none
#eval UInt8.checkedAdd 100 50      -- some 150

-- Overflowing arithmetic (result + flag)
#eval UInt8.overflowingAdd 200 100 -- (44, true)
```

## 3. Signed Integers

```lean
-- Two's complement signed types
#eval Int8.fromInt (-42)        -- -42
#eval Int32.toInt (Int32.fromInt (-1))  -- -1

-- Signed comparison (zero-cost, no Int allocation)
#eval Int32.slt (Int32.fromInt (-1)) (Int32.fromInt 0)  -- true
```

## 4. Bitwise Operations

```lean
-- AND, OR, XOR, NOT
#eval UInt8.band 0xAA 0x0F      -- 0x0A
#eval UInt8.bor  0xA0 0x0F      -- 0xAF
#eval UInt8.bnot 0x00            -- 0xFF

-- Shifts and rotates (count % bitWidth semantics)
#eval UInt32.shl 1 10            -- 1024
#eval UInt8.rotl 0x81 1          -- 0x03

-- Bit scanning
#eval UInt32.clz 1               -- 31
#eval UInt32.popcount 0xFF       -- 8
```

## 5. Byte Order

```lean
-- Endianness conversions
#eval UInt32.bswap 0x12345678           -- 0x78563412
#eval UInt32.toBigEndian 0x12345678     -- (platform-dependent)

-- Round-trip
-- fromBigEndian (toBigEndian x) = x  (proven!)
```

## 6. LEB128

```lean
-- Variable-length integer encoding (used in WebAssembly, DWARF, protobuf)
#eval Binary.Leb128.encodeU32 624485  -- ByteArray [0xE5, 0x8E, 0x26]
-- Round-trip is formally proven
```

## 7. Binary Format DSL

```lean
-- Define a packet format
def myFormat : Binary.Format :=
  .seq (.uint16 .big) (.seq (.uint32 .little) (.padding 2))

-- Parse and serialize with the same format
-- parse ∘ serialize = id  (proven!)
```

## 8. Memory Buffer

```lean
-- Create and use a verified memory buffer
let buf := Memory.Buffer.zeros 64
-- Tier 1: proof-carrying read/write (zero-cost, bounds proved at compile time)
-- Tier 2: checked read/write (returns Option on out-of-bounds)
```

## 9. Alignment

```lean
open Radix.Alignment

#eval alignUp 1000 16        -- 1008
#eval alignDown 1023 16      -- 1008
#eval isAligned 1024 64      -- true
#eval alignPadding 1000 16   -- 8
```

## 10. Ring Buffer and Bitmap

```lean
open Radix.RingBuffer
open Radix.Bitmap

let rb := RingBuf.new 4
let some rb := rb.push ⟨10⟩ | unreachable!
let some rb := rb.push ⟨20⟩ | unreachable!
#eval rb.peek.map UInt8.toNat        -- some 10

let bm := Bitmap.zeros 64 |>.set 0 |>.set 7
#eval bm.test 7                      -- true
#eval bm.popcount                    -- 2
```

## 11. CRC and Memory Pools

```lean
open Radix.CRC
open Radix.MemoryPool

#eval CRC32.compute "123456789".toUTF8  -- 0xCBF43926

let pool := BumpPool.new 1024
#eval pool.remaining                          -- 1024
#eval (pool.alloc 64).map (fun (off, p) => (off, p.remaining))
```

## 12. Numeric Typeclasses

```lean
import Radix
import Radix.Word.Numeric

open Radix

#eval isZero (α := UInt8) UInt8.minVal -- true
#eval isMax (α := UInt16) UInt16.maxVal -- true
#eval BitwiseOps.popcount (⟨0xFF⟩ : UInt8).toNat -- 8
```

## 13. System I/O

```lean
-- File I/O with automatic resource management
System.FD.withFile "output.bin" .write fun fd => do
  System.IO.sysWrite fd data
-- File is automatically closed even on error
```

## Next Steps

- [Examples](examples.md) — More detailed usage examples
- [API Reference](../reference/api/) — Complete API documentation
- [Architecture](../architecture/README.md) — Understand the design

## See Also

- [日本語版](../../ja/getting-started/quickstart.md) — Japanese version
