# CHANGELOG

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2026-03-14

### Added

#### Core Types — Word Module
- `UInt8`, `UInt16`, `UInt32`, `UInt64` wrapping Lean 4 built-ins (zero-cost)
- `Int8`, `Int16`, `Int32`, `Int64` via two's complement wrapper (ADR-003)
- `UWord`, `IWord` — platform-width parametric types (32/64-bit)
- Four arithmetic modes: wrapping, saturating, checked, overflowing
- Width conversions: zero-extend, sign-extend, truncate, bit-pattern cast
- 52+ BitVec equivalence proofs, 130+ overflow proofs, 80+ ring proofs, 70+ conversion proofs

#### Bitwise Operations — Bit Module
- AND, OR, XOR, NOT with Boolean algebra proofs
- Shifts and rotates with Rust-style `count % bitWidth` normalization (FR-002.1a)
- Bit scanning: `clz`, `ctz`, `popcount`, `bitReverse`, `hammingDistance`
- Bit fields: `testBit`, `setBit`, `clearBit`, `toggleBit`, `extractBits`, `insertBits`
- 264 bitwise operation proofs (De Morgan, shift identities, field round-trips)

#### Byte Order — Bytes Module
- Endianness model (`big`, `little`)
- `bswap` for 16/32/64-bit values
- `toBigEndian`/`fromBigEndian`, `toLittleEndian`/`fromLittleEndian`
- `ByteSlice` — bounds-checked `ByteArray` view with endian-aware reads
- 60 proofs (bswap involution, BE/LE round-trips, Spec Prop proofs, ByteSlice properties)

#### Memory Model — Memory Module
- `Region` with disjointness and containment specifications
- `Buffer` — `ByteArray`-based memory with proof-carrying read/write
- `Ptr n` — byte-width-parametric pointer abstraction
- `FieldDesc`, `LayoutDesc` — packed struct layout computation
- 43 proofs (buffer size preservation, read-after-write, region disjointness, alignment, layout)

#### Binary Format DSL — Binary Module
- `Format` inductive — declarative binary layout description
- Format-driven parser with endianness support
- Format-driven serializer
- LEB128 variable-length integer encoding/decoding (unsigned and signed)
- LEB128 mathematical specification with 77 proofs (round-trips, size bounds, encoding validity)
- 15 format validity proofs

#### System Call Interface — System Module
- `FileState` state machine (open → use → close lifecycle)
- `SysError` (10 POSIX error variants) with `fromIOError` mapping
- `FD` (file descriptor), `Ownership`, `OpenMode`
- `withFile` bracket pattern for resource safety
- `sysRead`, `sysWrite`, `sysSeek` with pre/postcondition specs
- POSIX.1-2024 trust assumptions
- 34 proofs (file state machine, lifecycle validation, IO faithfulness)

#### Concurrency Model — Concurrency Module
- C11/C++11 memory ordering model (Relaxed through SeqCst)
- `AtomicCell` with atomic load/store/CAS/fetch operations
- `happensBefore` partial order, `isDataRace`, `isLinearizable` definitions
- 46 proofs (ordering strength, DRF, linearizability)

#### Bare Metal Support — BareMetal Module
- Platform model (x86_64, aarch64, riscv64)
- Memory region kinds (Flash, RAM, MMIO, Reserved) with non-overlap invariants
- Boot invariant specification (stack pointer, entry point, BSS zeroed)
- Startup phase state machine with validation
- `GCFreeConstraint` — GC-free allocation analysis
- Linker script model (`LinkerScript`, `Section`, `Symbol`)
- 34 proofs (region disjointness, alignment, GC-free, startup sequence)

#### Infrastructure
- Three-layer architecture (Spec → Impl → Bridge) with ADRs
- Mathlib `BitVec n` as specification-level canonical representation (ADR-002)
- Comprehensive test suite (unit + property-based + comprehensive)
- Microbenchmark suite with C baseline comparison
- Documentation in English and Japanese
- 11 usage examples demonstrating all modules

[Unreleased]: https://github.com/provenance-works/radix/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/provenance-works/radix/releases/tag/v0.1.0
