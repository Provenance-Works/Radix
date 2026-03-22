# CHANGELOG

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### v0.3.0 Composable Modules
- Added `Radix.UTF8` with a verified UTF-8 scalar model, executable encoding/decoding helpers, well-formedness checks, and round-trip proofs.
- Added `Radix.ECC` with Hamming(7,4) codewords, parity helpers, syndrome computation, and single-bit correction proofs.
- Added `Radix.DMA` with source/destination region descriptors, coherence and atomicity constraints, and a checked DMA copy simulator.
- Added region algebra to `Radix.Memory.Spec.Region`: `intersects`, `adjacent`, `mergeable`, `span`, `intersection`, `union?`, and `difference`, with supporting lemmas.
- Added `Radix.Timer` with monotonic clocks, deadlines, elapsed-time helpers, and expiry proofs.
- Added `Radix.ProofAutomation` with `radix_decide` and `radix_omega` tactic macros for common Radix proof patterns.

#### Tests, Examples, and Documentation
- Added execution, comprehensive, and property tests covering all v0.3.0 modules and the new memory region algebra surface.
- Added six new runnable examples: UTF-8, ECC, DMA, region algebra, timer, and proof automation.
- Added English and Japanese API reference coverage for the v0.3.0 modules and updated development docs for the expanded module set.

## [0.2.1] - 2026-03-22

### Changed

- Replaced all remaining `native_decide` usages in library proofs with kernel-reduced proofs using `decide`, `simp`, or existing host-width lemmas.
- Updated memory pointer and platform-width tests to remove the last `native_decide`-based proof witnesses.
- Updated GitHub Actions and GitLab CI trust-audit checks to stop treating `native_decide` as a tracked trusted item.
- Clarified README wording for trusted-boundary modules and documented `BareMetal` as a verification model rather than a hardware runtime implementation.

## [0.2.0] - 2026-03-21

### Added

#### Ring Buffer (`Radix.RingBuffer`)
- Fixed-capacity circular queue backed by `Memory.Buffer`
- O(1) `push`, `pop`, `peek` with bounds-checked access
- `pushForce` (overwrite-on-full), `pushMany`, `popMany`, `drain`, `clear`
- Formal specification (`RingBufferState`) with FIFO ordering proofs
- 24 theorems: invariant preservation, push/pop round-trip, capacity conservation

#### Bitmap / Bitset (`Radix.Bitmap`)
- Dense bit-array backed by `Array UInt64` (64 bits per word)
- O(1) `set`, `clear`, `test`, `toggle`
- Bulk operations: `popcount`, `findFirstSet`, `findFirstClear`
- Set operations: `union`, `intersection`, `difference`, `complement`
- Query operations: `isEmpty`, `isFull`, `isDisjoint`, `isSubsetOf`
- Abstract specification (`BitmapState`) with set/clear round-trip proofs
- 33 theorems: structural invariant preservation, boolean algebra properties

#### CRC-32 / CRC-16 (`Radix.CRC`)
- Table-driven CRC-32/ISO-HDLC (Ethernet, gzip, PNG)
- Table-driven CRC-16/CCITT (X.25, HDLC, Bluetooth)
- Streaming API: `init`/`update`/`finalize` for chunked processing
- Mathematical specification via GF(2) polynomial division
- Bit-by-bit reference implementations (`computeNaive`) for verification
- 10 theorems: table size, streaming consistency, GF(2) algebra, empty data CRC

#### Numeric Typeclasses (`Radix.Word.Numeric`)
- `BoundedUInt`: generic unsigned integer trait (minVal, maxVal, toNat, wrapping/saturating/checked arithmetic)
- `BoundedInt`: generic signed integer trait (minVal, maxVal, toInt, isNeg, fromInt)
- `BitwiseOps`: generic bitwise operations trait (band, bor, bxor, bnot, testBit, popcount)
- Instances for all 8 concrete types (UInt8/16/32/64, Int8/16/32/64)
- Generic utility functions: `genericZero`, `genericMaxVal`, `isZero`, `isMax`
- 4 theorems: wrapping addition identity/commutativity, min/max bounds

#### Memory Pool Model (`Radix.MemoryPool`)
- **Bump Allocator** (`BumpPool`): O(1) allocation, bulk reset, aligned allocation
- **Slab Allocator** (`SlabPool`): O(1) fixed-size block allocation/deallocation
- Abstract specification (`BumpState`, `SlabState`) with safety proofs
- Double-free detection, capacity tracking, allocation offset correctness
- 36 theorems: no double-free, capacity tracking, offset bounds, reset correctness

#### Alignment Utilities (`Radix.Alignment`)
- `alignUp`, `alignDown`, `isAligned`, `alignPadding` for general alignment
- Power-of-two fast paths: `alignUpPow2`, `alignDownPow2`, `isAlignedPow2`
- `HasAlignment` typeclass with instances for UInt8/16/32/64
- 18 theorems: alignment sandwich (alignDown <= x <= alignUp), round-trip,
  padding bounds, ops-vs-spec equivalence

#### Testing & Benchmarks
- Comprehensive tests for all 6 new modules (1,280 assertions)
- Property-based tests for all 6 new modules
- CRC-32 and Ring Buffer benchmarks with C baseline comparison
- 3 new examples: `BitmapDemo`, `AlignmentDemo`, `MemoryPoolDemo`

#### Documentation
- English and Japanese API reference for all new modules
- Three-layer architecture maintained across all new modules

### Changed

- Updated theorem count from 937+ to 1062+
- Updated barrel file (`Radix.lean`) with all v0.2.0 module imports

## [0.1.3] - 2026-03-17

### Fixed

- **BareMetal axioms**: Replace trivially-provable axioms with genuinely unprovable
  ones using opaque hardware types (`HWMemoryState`, `hwReadByte`). Axioms now
  express real hardware contracts: `trust_reset_entry` (∃ aligned reset address),
  `trust_static_allocation_stable` (memory stability across snapshots),
  `trust_mmio_volatile` (side effects exist), `trust_bss_zeroed`,
  `trust_stack_grows_down`.
- **System axioms**: Fix circular `trust_lean_io_faithful` (previously presupposed
  its own conclusion) and incorrect `trust_read_bounded` (was false for
  `actual > 0 → actual ≤ count`). Now uses opaque `OSReadResult` type.
- **System Spec**: Expand from trivial 2-state model (open/closed) to rich
  model tracking file position, access mode (`readOnly`/`writeOnly`/`readWrite`/
  `appendOnly`), cumulative bytes read/written. Pre/postconditions now enforce
  mode-specific access control.
- **System Lemmas**: Complete rewrite with 53 substantive theorems including
  mode-aware preconditions, position-tracking postconditions, lifecycle validity
  with access control, and axiom-based proofs.
- **Concurrency axioms**: Replace trivially-provable `trust_atomic_word_access`,
  `trust_cas_atomicity`, and `trust_fence_ordering` with genuinely unprovable
  axioms using opaque `HWConcurrencyState` and `hwObservedAtomic`.
- **Theorem count**: Corrected from inflated 914+ to accurate 854+.

### Added

- **Concurrency Lemmas**: 10 new proofs including `loads_not_conflicting`,
  `sameThread_no_dataRace`, `ordered_no_dataRace`, `allLoads_isDataRaceFree`,
  `atomicCAS_dichotomy`, `fetchAdd_compose`, `exchange_eq_successful_cas`,
  `Trace.empty_isWellFormed`, `Trace.empty_isValid`.
- **Memory Lemmas**: 4 new region algebra proofs: `contains_trans`,
  `disjoint_of_contains`, `disjoint_sub`, `not_contains_empty_of_pos`.

## [0.1.2] - 2026-03-16

### Fixed

- **GCFree.Lifetime**: Add `heap` variant so `isBounded` is no longer trivially `true`
  for all cases. `Lifetime.heap.isBounded = false` correctly models GC-managed lifetimes.
- **AllocStrategy**: Add `heap` variant so `isGCFree` is no longer trivially `true`
  for all cases. `AllocStrategy.heap.isGCFree = false` correctly models heap allocation.
- **Theorem counts**: All module-level counts now match actual verified proof counts.

### Added

- **Bytes module**: 9 new proofs (signed type LE round-trips, signed BE/LE relationships,
  signed bswap involution for Int16/Int32/Int64)
- **Memory module**: 8 new proofs (checkedReadU32BE/LE some/none, checkedReadU64BE/LE some/none)
- **BareMetal module**: `heap_not_isGCFree`, `gcfree_strategies_isGCFree`, `default_forbids_heap` proofs

### Changed

- **README/CHANGELOG**: Clarify Concurrency and BareMetal modules as specification models
- Updated theorem count from 907+ to 914+

## [0.1.1] - 2026-03-16

### Fixed

- **Concurrency axioms**: Replace 5 trivial `True` axioms with meaningful propositions
  (`trust_atomic_word_access`, `trust_seqcst_total_order`, `trust_acquire_release_sync`,
  `trust_cas_semantics`, `trust_fence_ordering`)
- **BareMetal axioms**: Replace 5 trivial `True` axioms with meaningful propositions
  (`trust_reset_entry`, `trust_mmio_volatile`, `trust_interrupt_vector_table`,
  `trust_stack_grows_down`, `trust_alignment_fault`)

### Added

- **System module**: 34 proofs for file state machine (lifecycle validation,
  IO faithfulness, read/write/close pre/postconditions)
- **Bytes module**: 29 new proofs (bswap involution, BE/LE round-trips,
  Spec Prop completeness, ByteSlice multi-byte write length preservation)
- **Memory module**: 24 new proofs (read-after-write for different offsets,
  region disjointness/containment, BufferSpec, alignment properties)

### Changed

- Updated theorem count from 721+ to 907+
- Corrected module-level theorem counts in README and CHANGELOG

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

#### Concurrency Specification Model — Concurrency Module
- C11/C++11 memory ordering specification model (Relaxed through SeqCst)
- `AtomicCell` with atomic load/store/CAS/fetch operations (pure state-machine model)
- `happensBefore` partial order, `isDataRace`, `isLinearizable` definitions
- 46 proofs (ordering strength, DRF, linearizability)

#### Bare Metal Specification — BareMetal Module
- Platform specification model (x86_64, aarch64, riscv64)
- Memory region kinds (Flash, RAM, MMIO, Reserved) with non-overlap invariants
- Boot invariant specification (stack pointer, entry point, BSS zeroed)
- Startup phase state machine with validation
- `GCFreeConstraint` — GC-free allocation analysis with `heap` variant for non-GC-free detection
- Linker script model (`LinkerScript`, `Section`, `Symbol`)
- 36 proofs (region disjointness, alignment, GC-free, startup sequence)

#### Infrastructure
- Three-layer architecture (Spec → Impl → Bridge) with ADRs
- Mathlib `BitVec n` as specification-level canonical representation (ADR-002)
- Comprehensive test suite (unit + property-based + comprehensive)
- Microbenchmark suite with C baseline comparison
- Documentation in English and Japanese
- 11 usage examples demonstrating all modules

[Unreleased]: https://github.com/provenance-works/radix/compare/v0.2.1...HEAD
[0.2.1]: https://github.com/provenance-works/radix/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/provenance-works/radix/compare/v0.1.3...v0.2.0
[0.1.3]: https://github.com/provenance-works/radix/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/provenance-works/radix/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/provenance-works/radix/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/provenance-works/radix/releases/tag/v0.1.0
