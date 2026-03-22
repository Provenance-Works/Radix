# API Reference

> **Audience**: Developers

Per-module API documentation for all Radix v0.2.0 modules and extension surfaces.

## Module Index

| Module | Description | Source |
|--------|-------------|--------|
| [Word](word.md) | Fixed-width integers, arithmetic modes, conversions | `Radix/Word/` |
| [Numeric](numeric.md) | Width-generic numeric typeclasses over Word and Bit | `Radix/Word/Numeric.lean` |
| [Bit](bit.md) | Bitwise operations, scanning, bit fields | `Radix/Bit/` |
| [Bytes](bytes.md) | Byte order, endianness, ByteSlice | `Radix/Bytes/` |
| [Memory](memory.md) | Buffer, Ptr, Layout | `Radix/Memory/` |
| [Binary](binary.md) | Format DSL, Parser, Serializer, LEB128 | `Radix/Binary/` |
| [System](system.md) | Error, FD, IO, Assumptions | `Radix/System/` |
| [Concurrency](concurrency.md) | Atomic operations model, memory ordering | `Radix/Concurrency/` |
| [BareMetal](baremetal.md) | Bare metal support, linker, startup, GC-free | `Radix/BareMetal/` |
| [Alignment](alignment.md) | Address alignment, padding, power-of-two fast paths | `Radix/Alignment/` |
| [RingBuffer](ringbuffer.md) | Fixed-capacity FIFO queue backed by Memory.Buffer | `Radix/RingBuffer/` |
| [Bitmap](bitmap.md) | Dense bitset backed by `Array UInt64` | `Radix/Bitmap/` |
| [CRC](crc.md) | CRC-32 and CRC-16 implementations with streaming API | `Radix/CRC/` |
| [MemoryPool](memorypool.md) | Bump and slab allocator models | `Radix/MemoryPool/` |

## See Also

- [Architecture Components](../../architecture/components.md) — High-level component overview
- [日本語版](../../../ja/reference/api/) — Japanese version
