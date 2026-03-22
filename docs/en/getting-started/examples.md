# Examples

> **Audience**: Users, Developers

All examples below are grounded in the project's `examples/Main.lean` runner and the focused example modules under `examples/`. In v0.2.0 the examples split into three groups: 13 built-in walkthrough sections, 11 focused application-style demos, and 4 new feature demos for Bitmap, Alignment, MemoryPool, and Numeric typeclasses.

## Word Arithmetic

```lean
open Radix

-- Wrapping: mod 2^n
let a := UInt32.wrappingAdd 4000000000 4000000000  -- 3705032704
let b := UInt8.wrappingMul 16 17                    -- 16

-- Saturating: clamp to bounds
let c := UInt8.saturatingAdd 255 1                  -- 255
let d := UInt8.saturatingSub 10 20                  -- 0

-- Checked: returns Option
let e := UInt32.checkedMul 100000 100000            -- none (overflow)
let f := UInt32.checkedAdd 100 200                  -- some 300

-- Overflowing: result + overflow flag
let (g, ov) := UInt32.overflowingAdd 4000000000 4000000000
-- g = 3705032704, ov = true
```

## Signed Integers

```lean
-- Two's complement, wrapping built-in UInt types
let x := Int32.fromInt (-42)
assert (x.toInt == -42)

-- Boundary values
let minVal := Int8.fromInt (-128)
let maxVal := Int8.fromInt 127
assert (minVal.toInt == -128)
assert (maxVal.toInt == 127)

-- Signed comparison (zero-cost, no heap allocation)
assert (Int32.slt (Int32.fromInt (-1)) (Int32.fromInt 0) == true)
assert (Int32.sge (Int32.fromInt 0) (Int32.fromInt (-1)) == true)
```

## Bitwise Operations

```lean
-- Boolean algebra
assert (UInt32.band 0xFF00 0x0FF0 == 0x0F00)
assert (UInt32.bor  0xFF00 0x0FF0 == 0xFFF0)
assert (UInt32.bxor 0xFF00 0x0FF0 == 0xF0F0)
assert (UInt32.bnot 0x00000000 == 0xFFFFFFFF)

-- Shifts (count % bitWidth)
assert (UInt32.shl 1 31 == 0x80000000)  -- logical left shift
assert (UInt8.shrArith 0x80 1 == 0xC0)  -- arithmetic right shift (sign-preserving)

-- Rotates
assert (UInt32.rotl 0x80000001 1 == 0x00000003)
assert (UInt32.rotr 0x80000001 1 == 0xC0000000)
```

## Bit Scanning

```lean
assert (UInt32.clz 1 == 31)           -- count leading zeros
assert (UInt32.ctz 8 == 3)            -- count trailing zeros
assert (UInt32.popcount 0xFF == 8)    -- population count
assert (UInt8.bitReverse 0x80 == 0x01) -- bit reverse
```

## Bit Fields

```lean
-- Test, set, clear, toggle individual bits
assert (UInt32.testBit 5 0 == true)
assert (UInt32.testBit 5 1 == false)
assert (UInt32.setBit 0 3 == 8)
assert (UInt32.clearBit 0xFF 0 == 0xFE)
assert (UInt32.toggleBit 0xFF 0 == 0xFE)

-- Extract and insert bit fields
-- extractBits value low high proof → extracted field
-- insertBits dest value low high proof → modified dest
```

## Width Conversions

```lean
-- Zero-extend (smaller → larger, preserves value)
let a : UInt16 := UInt8.toUInt16 255   -- 255

-- Truncate (larger → smaller, loses high bits)
let b : UInt8 := UInt16.toUInt8 256    -- 0

-- Sign-extend (preserves signed interpretation)
let c : Int32 := Int8.toInt32 (Int8.fromInt (-1))
assert (c.toInt == -1)

-- Register-internal sign extension (Wasm support)
let d := UInt32.signExtend8 0x000000FF   -- 0xFFFFFFFF
```

## Byte Order

```lean
-- Byte swap (involution: bswap(bswap(x)) = x, proven!)
assert (UInt32.bswap 0x12345678 == 0x78563412)

-- Endianness conversions (round-trip proven!)
let be := UInt32.toBigEndian 0x12345678
let orig := UInt32.fromBigEndian be
assert (orig == 0x12345678)
```

## LEB128

```lean
-- Unsigned encode/decode (round-trip proven!)
let encoded := Binary.Leb128.encodeU32 624485
-- encoded = [0xE5, 0x8E, 0x26]

let decoded := Binary.Leb128.decodeU32 encoded 0
-- decoded = some (624485, 3)

-- Signed LEB128
let sEncoded := Binary.Leb128.encodeS32 (Int32.fromInt (-123456))
let sDecoded := Binary.Leb128.decodeS32 sEncoded 0
-- Round-trip: sDecoded = some (Int32.fromInt (-123456), _)

-- Size upper bounds (proven!)
-- encodeU32 size ≤ 5, encodeU64 size ≤ 10
```

## Binary Format DSL

```lean
-- Define a network packet format
def packetFormat : Binary.Format :=
  .seq (.uint16 .big)           -- 2-byte header (big-endian)
      (.seq (.uint32 .little)   -- 4-byte payload (little-endian)
           (.padding 2))        -- 2 bytes padding

-- Serialize fields to ByteArray
-- Parse ByteArray back to fields
-- parse ∘ serialize = id  (proven!)
```

## Memory Buffer

```lean
-- Create a zero-initialized buffer
let buf := Memory.Buffer.zeros 64

-- Tier 2 (Checked): returns Option on OOB
let val := buf.checkedReadU8 0    -- some 0
let bad := buf.checkedReadU8 100  -- none

-- Write and read back
let buf2 := (buf.checkedWriteU8 0 42).get!
let read := buf2.checkedReadU8 0  -- some 42
```

## System I/O

```lean
-- Write and read a file with automatic resource management
System.FD.withFile "test.bin" .write fun fd => do
  let _ ← System.IO.sysWrite fd (ByteArray.mk #[1, 2, 3])

-- Convenience functions
let _ ← System.IO.writeFileBytes "out.bin" data
let bytes ← System.IO.readFileBytes "out.bin"
let exists ← System.IO.sysFileExists "out.bin"
```

## Alignment Utilities

```lean
open Radix.Alignment

#eval alignUp 1000 16         -- 1008
#eval alignDown 1023 16       -- 1008
#eval isPowerOfTwo 64         -- true
#eval alignUpPow2 12345 256   -- 12544
#eval alignmentOf UInt64      -- 8
```

## Bitmap / Bitset

```lean
open Radix.Bitmap

let bm := Bitmap.zeros 128 |>.set 0 |>.set 7 |>.set 42
#eval bm.popcount             -- 3
#eval bm.test 42              -- true
#eval bm.findFirstSet         -- some 0

let full := Bitmap.ones 8 |>.clear 5
#eval full.findFirstClear     -- some 5
```

## Ring Buffer

```lean
open Radix.RingBuffer

let rb := RingBuf.new 8
let some rb := rb.push ⟨10⟩ | unreachable!
let some rb := rb.push ⟨20⟩ | unreachable!
let some (front, rb) := rb.pop | unreachable!

#eval front.toNat             -- 10
#eval rb.peek.map UInt8.toNat -- some 20
```

## CRC-32 / CRC-16

```lean
open Radix.CRC

#eval CRC32.compute "123456789".toUTF8   -- 0xCBF43926

let crc := CRC32.init
let crc := CRC32.update crc "1234".toUTF8
let crc := CRC32.update crc "56789".toUTF8
#eval CRC32.finalize crc                  -- same result as compute
```

## Memory Pools

```lean
open Radix.MemoryPool

let pool := BumpPool.new 1024
#eval pool.remaining
#eval (pool.alloc 64).map (fun (off, p) => (off, p.remaining))
```

## Numeric Typeclasses

```lean
import Radix.Word.Numeric

open Radix

#eval isZero (α := UInt8) UInt8.minVal
#eval isMax (α := UInt16) UInt16.maxVal
#eval BitwiseOps.popcount (⟨0xDEADBEEF⟩ : UInt32).toNat
```

## See Also

- [Quickstart](quickstart.md) — Minimal getting-started guide
- [API Reference](../reference/api/) — Complete API documentation
- [日本語版](../../ja/getting-started/examples.md) — Japanese version
