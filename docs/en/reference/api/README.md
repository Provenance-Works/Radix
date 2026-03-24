# API Reference

> **Audience**: Developers

Per-module API documentation for the current Radix surface, including the v0.3.0 composable additions.

## Module Index

| Module | Description | Source |
|--------|-------------|--------|
| [Word](word.md) | Fixed-width integers, arithmetic modes, conversions | `Radix/Word/` |
| [Numeric](numeric.md) | Width-generic numeric typeclasses over Word and Bit | `Radix/Word/Numeric.lean` |
| [Bit](bit.md) | Bitwise operations, scanning, bit fields | `Radix/Bit/` |
| [Bytes](bytes.md) | Byte order, endianness, ByteSlice | `Radix/Bytes/` |
| [Memory](memory.md) | Buffer, Ptr, Layout, and region algebra | `Radix/Memory/` |
| [Binary](binary.md) | Format DSL, Parser, Serializer, LEB128 | `Radix/Binary/` |
| [System](system.md) | Error, FD, IO, Assumptions | `Radix/System/` |
| [Concurrency](concurrency.md) | Atomic operations model, memory ordering | `Radix/Concurrency/` |
| [BareMetal](baremetal.md) | Bare metal support, linker, startup, GC-free | `Radix/BareMetal/` |
| [Alignment](alignment.md) | Address alignment, padding, power-of-two fast paths | `Radix/Alignment/` |
| [RingBuffer](ringbuffer.md) | Fixed-capacity FIFO queue backed by Memory.Buffer | `Radix/RingBuffer/` |
| [Bitmap](bitmap.md) | Dense bitset backed by `Array UInt64` | `Radix/Bitmap/` |
| [CRC](crc.md) | CRC-32 and CRC-16 implementations with streaming API | `Radix/CRC/` |
| [MemoryPool](memorypool.md) | Bump and slab allocator models | `Radix/MemoryPool/` |
| [UTF8](utf8.md) | Verified UTF-8 scalar model and executable codecs | `Radix/UTF8/` |
| [ECC](ecc.md) | Hamming(7,4) parity and single-bit correction helpers | `Radix/ECC/` |
| [DMA](dma.md) | DMA descriptor validation and copy simulation | `Radix/DMA/` |
| [Timer](timer.md) | Monotonic clock and deadline helpers | `Radix/Timer/` |
| [ProofAutomation](proofautomation.md) | Radix-specific tactic macros | `Radix/ProofAutomation.lean` |

## See Also

- [Architecture Components](../../architecture/components.md) — High-level component overview
- [日本語版](../../../ja/reference/api/) — Japanese version
